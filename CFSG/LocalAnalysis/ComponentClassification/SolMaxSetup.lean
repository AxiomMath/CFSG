module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Lemma212Steps
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxQuot

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem le_centralizer_sq {A : Subgroup G} {x : G} (hx2A : x ^ 2 ∈ A) :
    centralizer (A : Set G) ⊔ zpowers x ≤ centralizer ({x ^ 2} : Set G) := by
  refine sup_le (fun c hc => ?_) (zpowers_le.mpr ?_)
  · rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.mp hc) _ hx2A).symm
  · rw [mem_centralizer_singleton_iff]
    exact ((Commute.refl x).pow_right 2).eq

theorem zpowers_sq_le_center {H : Subgroup G} {x : G} (hxH : x ∈ H)
    (hH : H ≤ centralizer ({x ^ 2} : Set G)) :
    zpowers ((⟨x, hxH⟩ : ↥H) ^ 2) ≤ center ↥H := by
  rw [zpowers_le, mem_center_iff]
  intro h
  apply Subtype.ext
  have h1 := mem_centralizer_singleton_iff.mp (hH h.2)
  simpa using h1

theorem orderOf_mk_eq_two {A H : Subgroup G} {x : G} (hxH : x ∈ H) (hx2A : x ^ 2 ∈ A)
    (hxnA : x ∉ A) [(zpowers ((⟨x, hxH⟩ : ↥H) ^ 2)).Normal] :
    orderOf (QuotientGroup.mk' (zpowers ((⟨x, hxH⟩ : ↥H) ^ 2)) ⟨x, hxH⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set xH : ↥H := ⟨x, hxH⟩
  apply orderOf_eq_prime
  · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_zpowers _
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    apply hxnA
    have h1 : (xH : G) ∈ (zpowers (xH ^ 2)).map H.subtype := mem_map_of_mem _ h
    rw [MonoidHom.map_zpowers] at h1
    exact zpowers_le.mpr hx2A h1

theorem centralizer_mk_eq {H : Subgroup G} {x : G} (hxH : x ∈ H) :
    centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H) = (centralizer ({x} : Set G) ⊓ H).subgroupOf H := by
  ext w
  rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨congrArg Subtype.val h, w.2⟩, fun h => Subtype.ext h.1⟩

theorem mem_normalizer_subgroupOf_of_mem {H M : Subgroup G} {t : G} (htH : t ∈ H)
    (htN : t ∈ normalizer (M : Set G)) :
    (⟨t, htH⟩ : ↥H) ∈ normalizer ((M.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
  rw [mem_normalizer_iff]
  intro y
  rw [mem_subgroupOf, mem_subgroupOf]
  simpa using (mem_normalizer_iff.mp htN (y : G))

variable [Finite G]

theorem isPComponent_subgroupOf_of_normal {Y H M : Subgroup G} (hYH : Y ≤ H)
    (hYn : (Y.subgroupOf H).Normal) (hM : IsTwoComponentIn M Y) :
    IsPComponent 2 (M.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hM.1 hYH
    hYn.isSubnormal).mpr hM.2

variable {A : Subgroup G} {x : G}

theorem map_facts_of_component (hxA : x ∈ normalizer (A : Set G)) (hx2A : x ^ 2 ∈ A)
    (hxH : x ∈ centralizer (A : Set G) ⊔ zpowers x)
    [(zpowers ((⟨x, hxH⟩ : ↥(centralizer (A : Set G) ⊔ zpowers x)) ^ 2)).Normal]
    {M : Subgroup G} (hM : IsTwoComponentIn M (centralizer (A : Set G))) :
    IsPComponent 2 ((M.subgroupOf (centralizer (A : Set G) ⊔ zpowers x)).map
      (QuotientGroup.mk' (zpowers ((⟨x, hxH⟩ : ↥(centralizer (A : Set G) ⊔ zpowers x)) ^ 2)))) ∧
    Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃*
      ↥((M.subgroupOf (centralizer (A : Set G) ⊔ zpowers x)).map
        (QuotientGroup.mk' (zpowers ((⟨x, hxH⟩ : ↥(centralizer (A : Set G) ⊔ zpowers x)) ^ 2))))
      ⧸ Open.fusionZStar ↥((M.subgroupOf (centralizer (A : Set G) ⊔ zpowers x)).map
        (QuotientGroup.mk' (zpowers ((⟨x, hxH⟩ : ↥(centralizer (A : Set G) ⊔ zpowers x)) ^ 2)))))
    ∧ ∀ t (htH : t ∈ centralizer (A : Set G) ⊔ zpowers x), t ∈ normalizer (M : Set G) →
      QuotientGroup.mk' (zpowers ((⟨x, hxH⟩ : ↥(centralizer (A : Set G) ⊔ zpowers x)) ^ 2))
        ⟨t, htH⟩ ∈ coreActionKernel ((M.subgroupOf (centralizer (A : Set G) ⊔ zpowers x)).map
          (QuotientGroup.mk' (zpowers ((⟨x, hxH⟩ : ↥(centralizer (A : Set G) ⊔ zpowers x)) ^ 2))))
        → t ∈ coreActionKernel M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer (A : Set G) with hY
  set H := Y ⊔ zpowers x with hH
  set xH : ↥H := ⟨x, hxH⟩
  set N := zpowers (xH ^ 2) with hN
  set f := QuotientGroup.mk' N with hf
  have hYH : Y ≤ H := le_sup_left
  have hHn : H ≤ normalizer (Y : Set G) :=
    sup_le le_normalizer (zpowers_le.mpr (Sol76.le_normalizer_centralizer
      (zpowers_le.mpr hxA) (mem_zpowers x)))
  have hYn : (Y.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hYH).mpr hHn
  have hNc : N ≤ center ↥H := zpowers_sq_le_center hxH (le_centralizer_sq hx2A)
  have hfk : f.ker = N := QuotientGroup.ker_mk' N
  have hfc : ∀ L : Subgroup ↥H, L ≤ centralizer (f.ker : Set ↥H) := fun L l _ =>
    mem_centralizer_iff.mpr fun k hk => (mem_center_iff.mp (hNc (hfk ▸ hk)) l).symm
  have hMH : M ≤ H := hM.1.trans hYH
  have hMpc : IsPComponent 2 (M.subgroupOf H) := isPComponent_subgroupOf_of_normal hYH hYn hM
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hM.1).mp hM.2).2.2
  have hMHq : IsQuasisimple (↥(M.subgroupOf H) ⧸ pPrimeCore 2 ↥(M.subgroupOf H)) :=
    LocalCores.isQuasisimple_of_mulEquiv (Sol78.coreQuotCongr (subgroupOfEquivOfLe hMH)).symm hMq
  refine ⟨?_, ?_, ?_⟩
  · have h := GSThmB.TwoQuot.isPComponent_map_of_le_centralizer f le_top (hfc _)
      ((isPComponent_subgroupOf_top_iff _).mpr hMpc)
    rw [map_top_of_surjective f (QuotientGroup.mk'_surjective N)] at h
    exact (isPComponent_subgroupOf_top_iff _).mp h
  · obtain ⟨e⟩ := GSThmB.TwoQuot.nonempty_fusionZStar_equiv_map f (hfc _) hMHq
    exact ⟨(Sol78.fusionZStarQuotCongr (subgroupOfEquivOfLe hMH)).symm.trans e⟩
  · intro t htH htN ht
    have hMp : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hM.1 hM.2
    have : Group.IsPerfect ↥(M.subgroupOf H) := by
      have : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hMp
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hMH).symm.toMonoidHom)
        (subgroupOfEquivOfLe hMH).symm.surjective
    have h1 := GSThmB.TwoQuot.mem_coreActionKernel_of_map f (hfc _)
      (mem_normalizer_subgroupOf_of_mem htH htN) ht
    exact Sol78.mem_coreActionKernel_of_subgroupOf hMH h1

section Generic

variable {H₀ : Type} [Group H₀] [Finite H₀] {x₀ : H₀} [(zpowers (x₀ ^ 2)).Normal]

theorem map_facts_of_centralizer (hx₀ : IsPGroup 2 (zpowers x₀))
    (hNc : zpowers (x₀ ^ 2) ≤ center H₀) {T₀ : Subgroup H₀}
    (hT₀C : T₀ ≤ centralizer ({x₀} : Set H₀))
    (hT₀ : IsPComponent 2 (T₀.subgroupOf (centralizer ({x₀} : Set H₀))))
    (hT₀E : T₀ ≤ pLayer H₀ 2) :
    T₀.map (QuotientGroup.mk' (zpowers (x₀ ^ 2))) ≤
        centralizer ({QuotientGroup.mk' (zpowers (x₀ ^ 2)) x₀} : Set (H₀ ⧸ zpowers (x₀ ^ 2))) ∧
      IsPComponent 2 ((T₀.map (QuotientGroup.mk' (zpowers (x₀ ^ 2)))).subgroupOf
        (centralizer ({QuotientGroup.mk' (zpowers (x₀ ^ 2)) x₀} : Set (H₀ ⧸ zpowers (x₀ ^ 2))))) ∧
      T₀.map (QuotientGroup.mk' (zpowers (x₀ ^ 2))) ≤ pLayer (H₀ ⧸ zpowers (x₀ ^ 2)) 2 ∧
      Nonempty (↥T₀ ⧸ Open.fusionZStar ↥T₀ ≃*
        ↥(T₀.map (QuotientGroup.mk' (zpowers (x₀ ^ 2)))) ⧸
          Open.fusionZStar ↥(T₀.map (QuotientGroup.mk' (zpowers (x₀ ^ 2))))) ∧
      (Open.fusionZStar ↥T₀ = pPrimeCore 2 ↥T₀ →
        Open.fusionZStar ↥(T₀.map (QuotientGroup.mk' (zpowers (x₀ ^ 2)))) =
          pPrimeCore 2 ↥(T₀.map (QuotientGroup.mk' (zpowers (x₀ ^ 2))))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := zpowers (x₀ ^ 2) with hN
  set f := QuotientGroup.mk' N with hf
  have hfk : f.ker = N := QuotientGroup.ker_mk' N
  have hfc : ∀ L : Subgroup H₀, L ≤ centralizer (f.ker : Set H₀) := fun L l _ =>
    mem_centralizer_iff.mpr fun k hk => (mem_center_iff.mp (hNc (hfk ▸ hk)) l).symm
  have hT₀q : IsQuasisimple (↥T₀ ⧸ pPrimeCore 2 ↥T₀) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T₀ _ hT₀C).mp hT₀).2.2
  have hle : (centralizer ({x₀} : Set H₀)).map f ≤ centralizer ({f x₀} : Set (H₀ ⧸ N)) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hy]
  refine ⟨(map_mono hT₀C).trans hle, ?_, ?_, ?_, ?_⟩
  · have h := GSThmB.TwoQuot.isPComponent_map_of_le_centralizer f hT₀C (hfc _) hT₀
    exact (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal (map_mono hT₀C) hle
      (map_centralizer_normal x₀).isSubnormal).mpr h
  · exact (map_mono hT₀E).trans
      (map_pLayer_le f (QuotientGroup.mk'_surjective N) (hfk.le.trans hNc))
  · exact GSThmB.TwoQuot.nonempty_fusionZStar_equiv_map f (hfc _) hT₀q
  · intro hex
    have hk2 : IsPGroup 2 f.ker := by
      rw [hfk]
      refine hx₀.to_le ?_
      rw [zpowers_le]
      exact pow_mem (mem_zpowers x₀) 2
    have hZ : center (↥T₀ ⧸ pPrimeCore 2 ↥T₀) = ⊥ := (Sol78.fusionZStar_eq_iff _).mp hex
    obtain ⟨e⟩ := GSThmB.TwoQuot.nonempty_pPrimeCore_equiv_map f (hfc _) hk2 hZ
    rw [Sol78.fusionZStar_eq_iff, ← Sol78.map_center_eq_of_mulEquiv e, hZ, Subgroup.map_bot]

end Generic

end CFSG.ComponentClassification.SolMax
