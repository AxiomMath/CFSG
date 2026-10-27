module

public import CFSG.CGT.Timmesfeld75.Sec3Lift
public import CFSG.CGT.Timmesfeld75.Sec3TwelveIrr

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups

section Counting

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_card_sub_one_of_free {K A : Subgroup G}
    (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hfree : ∀ k ∈ K, k ≠ 1 → ∀ a ∈ A, a ≠ 1 → k * a * k⁻¹ ≠ a) :
    Nat.card K ∣ Nat.card A - 1 := by
  let _ : MulAction K A :=
    MulAction.compHom A (A.normalizerMonoidHom.comp (Subgroup.inclusion hKA))
  have hsmul : ∀ (k : K) (a : A), ((k • a : A) : G) = (k : G) * a * (k : G)⁻¹ :=
    fun k a => rfl
  refine irr_card_dvd_sub_one (1 : A) (fun k => Subtype.ext (by rw [hsmul]; simp))
    (fun k a hk ha => ?_)
  by_contra hne
  have hk' : (k : G) ≠ 1 := fun h1 => hk (Subtype.ext h1)
  have ha' : (a : G) ≠ 1 := fun h1 => hne (Subtype.ext (by rw [h1]; rfl))
  exact hfree k k.2 hk' a a.2 ha' (by rw [← hsmul, ha])

end Counting

section SchurZassenhaus

theorem osg_exists_section {P Q : Type*} [Group P] [Group Q] [Finite P] (φ : P →* Q)
    (hφ : Function.Surjective φ) (hcop : Nat.Coprime (Nat.card φ.ker) (Nat.card Q)) :
    ∃ K : Subgroup P, Disjoint K φ.ker ∧ Nat.card K = Nat.card Q := by
  have hidx : φ.ker.index = Nat.card Q := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ, Subgroup.card_top]
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime (N := φ.ker) (hidx ▸ hcop)
  exact ⟨K, hK.disjoint.symm, hK.card_right.trans hidx⟩

theorem osg_exists_lift {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : IsPGroup 2 N) (H : Subgroup (Y ⧸ N)) (hH : Odd (Nat.card H)) :
    ∃ K : Subgroup Y, Nat.card K = Nat.card H ∧
      (∀ k ∈ K, QuotientGroup.mk' N k ∈ H) ∧
      ∀ k ∈ K, QuotientGroup.mk' N k = 1 → k = 1 := by
  let π : Y →* Y ⧸ N := QuotientGroup.mk' N
  let P : Subgroup Y := H.comap π
  let φ : P →* H := π.subgroupComap H
  have hφ : Function.Surjective φ :=
    MonoidHom.subgroupComap_surjective π H (QuotientGroup.mk'_surjective N)
  have hker : IsPGroup 2 φ.ker := by
    intro z
    have hz : φ z = 1 := z.2
    have hzN : ((z : P) : Y) ∈ N := by
      have h1 : π ((z : P) : Y) = ((φ z : H) : Y ⧸ N) := rfl
      exact (QuotientGroup.eq_one_iff _).1 (h1.trans (by rw [hz]; rfl))
    obtain ⟨n, hn⟩ := hN ⟨_, hzN⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun u : N => (u : Y)) hn
    simpa using this
  have hcop : Nat.Coprime (Nat.card φ.ker) (Nat.card H) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hker
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hH)
  obtain ⟨K₀, hdisj, hcard⟩ := osg_exists_section φ hφ hcop
  refine ⟨K₀.map P.subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hcard]
  · rintro _ ⟨z, -, rfl⟩
    exact (φ z).2
  · rintro _ ⟨z, hz, rfl⟩ h1
    have h2 : φ z = 1 := Subtype.ext h1
    have h3 : z = 1 := Subgroup.disjoint_def.1 hdisj hz h2
    rw [h3]
    simp

end SchurZassenhaus

section Quotient

variable {G : Type} [Group G]

theorem osg_exists_eq_mul_cfgM_of_map_mem_left {T T₁ : Subgroup G}
    [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal] {y : G} (hy : y ∈ T ⊔ T₁)
    (h : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨y, hy⟩ ∈
      (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) :
    ∃ t ∈ T, ∃ m ∈ cfgM T T₁, y = t * m := by
  obtain ⟨z, hz, hzy⟩ := h
  have h1 : (z : G)⁻¹ * y ∈ cfgM T T₁ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hzy)
  exact ⟨z, Subgroup.mem_subgroupOf.1 hz, _, h1, by group⟩

theorem osg_odd_two_pow_sub_one {f : ℕ} (hf : f ≠ 0) : Odd (2 ^ f - 1) := by
  obtain ⟨c, hc⟩ := (dvd_pow_self 2 hf : 2 ∣ 2 ^ f)
  have hpos : 0 < 2 ^ f := by positivity
  exact ⟨c - 1, by omega⟩

variable [Finite G]

theorem Sec3.exists_odd_normalizing_subgroup {T T₁ : Subgroup G}
    [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal] (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* PSL(2, GaloisField 2 f))) :
    ∃ K : Subgroup G, K ≤ T ⊔ T₁ ∧ K ≤ Subgroup.normalizer (T : Set G) ∧
      Nat.card K = 2 ^ f - 1 ∧
      ∀ k ∈ K, k ≠ 1 → ∀ m ∈ cfgM T T₁, k * m * k⁻¹ = m → m = 1 := by
  have hX := hS.isL2Pair_quotient hf h
  obtain ⟨H, hHN, -, hHcard, -, -, -⟩ := hX.exists_complement
  have hodd : Odd (Nat.card H) := by
    rw [hHcard]
    exact osg_odd_two_pow_sub_one hf
  have hM2 : IsPGroup 2 ((cfgM T T₁).subgroupOf (T ⊔ T₁)) :=
    (isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM).comap_subtype
  obtain ⟨K₀, hK₀card, hK₀H, hK₀1⟩ :=
    osg_exists_lift ((cfgM T T₁).subgroupOf (T ⊔ T₁)) hM2 H hodd
  refine ⟨K₀.map (T ⊔ T₁).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rintro _ ⟨y, hy, rfl⟩
    have hyX : (y : G) ∈ T ⊔ T₁ := y.2
    refine mem_normalizer_of_conjSubgroup_eq (hS.conjSubgroup_eq_of_le_mul_cfgM hyX fun z hz => ?_)
    have hzX : z ∈ T ⊔ T₁ := conjSubgroup_le_of_le_of_mem le_sup_left hyX hz
    refine osg_exists_eq_mul_cfgM_of_map_mem_left hzX ?_
    have h1 := map_mem_conjSubgroup_map hyX hzX hz
    have h2 : conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨(y : G), hyX⟩)
        ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) =
        (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) :=
      mem_normalizer_iff_conjSubgroup_eq.1 (hHN (hK₀H y hy))
    rwa [h2] at h1
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hK₀card, hHcard]
  · rintro _ ⟨y, hy, rfl⟩ hy1 m hm hym
    have hyX : (y : G) ∈ T ⊔ T₁ := y.2
    have hy1' : y ≠ 1 := fun h' => hy1 (by rw [h']; rfl)
    have hπ1 : QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨(y : G), hyX⟩ ≠ 1 :=
      fun h' => hy1' (hK₀1 y hy h')
    have hodd' : Odd (orderOf (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))
        ⟨(y : G), hyX⟩)) := by
      have hdvd : orderOf (⟨_, hK₀H y hy⟩ : H) ∣ Nat.card H := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hdvd
      exact Odd.of_dvd_nat hodd hdvd
    exact hS.centralizer_cfgM_eq_bot_of_odd hX hyX hodd' hπ1 m hm hym

theorem Sec3.two_pow_le_card_of_normal_normalizer {T T₁ : Subgroup G}
    [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal] (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* PSL(2, GaloisField 2 f)))
    {A : Subgroup G} (hA1 : A ≠ ⊥) (hAM : A ≤ cfgM T T₁)
    (hAn : ∀ n ∈ Subgroup.normalizer (T : Set G), conjSubgroup n A = A) :
    2 ^ f ≤ Nat.card A := by
  obtain ⟨K, -, hKT, hKcard, hKfree⟩ := hS.exists_odd_normalizing_subgroup hf h
  have hKA : K ≤ Subgroup.normalizer (A : Set G) := fun k hk =>
    mem_normalizer_of_conjSubgroup_eq (hAn k (hKT hk))
  have hdvd := card_dvd_card_sub_one_of_free hKA fun k hk hk1 a ha ha1 hka =>
    ha1 (hKfree k hk hk1 a (hAM ha) hka)
  rw [hKcard] at hdvd
  have hA2 : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 hA1
  have hle : 2 ^ f - 1 ≤ Nat.card A - 1 := Nat.le_of_dvd (by omega) hdvd
  have hpos : 0 < 2 ^ f := by positivity
  omega

end Quotient

end CFSG.CGT.Timmesfeld75
