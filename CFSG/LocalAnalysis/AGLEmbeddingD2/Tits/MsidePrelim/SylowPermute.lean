module

public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_smul_eq_map' (g : G) (Y : Subgroup G) :
    (MulAut.conj g : MulAut G) • Y = Subgroup.map (MulAut.conj g).toMonoidHom Y := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem exists_conj_map_eq_of_card {p : ℕ} [Fact p.Prime] {σ P Q : Subgroup G} (hPσ : P ≤ σ)
    (hQσ : Q ≤ σ) {n : ℕ} (hP : Nat.card P = p ^ n) (hQ : Nat.card Q = p ^ n) {m : ℕ}
    (hσm : Nat.card σ = p ^ n * m) (hm : ¬ p ∣ m) :
    ∃ g ∈ σ, Subgroup.map (MulAut.conj g).toMonoidHom P = Q := by
  have hPc : Nat.card (P.subgroupOf σ) = p ^ n := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPσ).toEquiv
  have hQc : Nat.card (Q.subgroupOf σ) = p ^ n := by
    rw [← hQ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQσ).toEquiv
  have hPp : IsPGroup p (P.subgroupOf σ) := IsPGroup.of_card hPc
  have hQp : IsPGroup p (Q.subgroupOf σ) := IsPGroup.of_card hQc
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hPi : ¬ p ∣ (P.subgroupOf σ).index := by
    have h := Subgroup.index_mul_card (H := P.subgroupOf σ)
    rw [hPc, hσm, mul_comm (p ^ n) m] at h
    rw [Nat.eq_of_mul_eq_mul_right hpos h]
    exact hm
  have hQi : ¬ p ∣ (Q.subgroupOf σ).index := by
    have h := Subgroup.index_mul_card (H := Q.subgroupOf σ)
    rw [hQc, hσm, mul_comm (p ^ n) m] at h
    rw [Nat.eq_of_mul_eq_mul_right hpos h]
    exact hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq σ (hPp.toSylow hPi) (hQp.toSylow hQi)
  have hcoe : MulAut.conj g • (P.subgroupOf σ) = Q.subgroupOf σ := by
    have := congrArg (fun S : Sylow p σ => (S : Subgroup σ)) hg
    simpa only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using this
  refine ⟨g, g.2, ?_⟩
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyσ : (⟨y, hPσ hy⟩ : σ) ∈ P.subgroupOf σ := Subgroup.mem_subgroupOf.mpr hy
    have hmem : MulAut.conj g • (⟨y, hPσ hy⟩ : σ) ∈ MulAut.conj g • P.subgroupOf σ :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hyσ
    rw [hcoe, Subgroup.mem_subgroupOf] at hmem
    simpa [MulAut.smul_def] using hmem
  · intro hx
    have hxσ : (⟨x, hQσ hx⟩ : σ) ∈ Q.subgroupOf σ := Subgroup.mem_subgroupOf.mpr hx
    rw [← hcoe, Subgroup.mem_smul_pointwise_iff_exists] at hxσ
    obtain ⟨z, hz, hzx⟩ := hxσ
    refine ⟨z, Subgroup.mem_subgroupOf.mp hz, ?_⟩
    have := congrArg Subtype.val hzx
    simpa [MulAut.smul_def] using this

omit [Finite G] in
theorem map_conj_eq_self_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : X.map (MulAut.conj g).toMonoidHom = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq_self {X : Subgroup G} {g : G}
    (hg : X.map (MulAut.conj g).toMonoidHom = X) : g ∈ Subgroup.normalizer (X : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr hg

omit [Finite G] in
theorem map_conj_sup_of_mem_normalizer {X V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    (X ⊔ V).map (MulAut.conj g).toMonoidHom = X.map (MulAut.conj g).toMonoidHom ⊔ V := by
  rw [Subgroup.map_sup, map_conj_eq_self_of_mem_normalizer hg]

omit [Finite G] in
theorem map_conj_mul' (g₁ g₂ : G) (S : Subgroup G) :
    S.map (MulAut.conj (g₁ * g₂)).toMonoidHom =
      (S.map (MulAut.conj g₂).toMonoidHom).map (MulAut.conj g₁).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_conj_le_normalizer_sup {N₁ V A T : Subgroup G}
    (hN₁V : N₁ ≤ Subgroup.normalizer (V : Set G))
    (hodd : ¬ 2 ∣ (V.subgroupOf N₁).index) (hN₁3 : Nat.Coprime 3 (Nat.card N₁))
    (hA9 : Nat.card A = 9) (hAN : A ≤ Subgroup.normalizer (N₁ : Set G)) (hT : IsPGroup 2 T)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hTN : T ≤ Subgroup.normalizer (N₁ : Set G))
    (hTA : ∀ t ∈ T, A.map (MulAut.conj t).toMonoidHom ≤ A ⊔ N₁) :
    ∃ m ∈ N₁, T ≤ Subgroup.normalizer
      ((A.map (MulAut.conj m).toMonoidHom ⊔ V : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := A ⊔ N₁ with hL
  have hAN₁ : A ⊓ N₁ = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by rw [hA9]; exact Nat.Coprime.pow_left 2 hN₁3)).eq_bot
  have hLc : Nat.card L = 3 ^ 2 * Nat.card N₁ := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAN
    rw [sup_comm, inf_comm, hAN₁, Subgroup.card_bot, mul_one, hA9] at h
    rw [hL, h]
    ring
  have hN₁3' : ¬ 3 ∣ Nat.card N₁ := fun h =>
    absurd (Nat.Coprime.coprime_dvd_left h hN₁3.symm) (by norm_num)
  have hconjL : ∀ E : Subgroup G, E ≤ L → Nat.card E = 9 →
      ∃ m ∈ N₁, A.map (MulAut.conj m).toMonoidHom = E := by
    intro E hEL hE
    obtain ⟨g, hgL, hg⟩ := exists_conj_map_eq_of_card (p := 3) (n := 2) (le_sup_left : A ≤ L)
      hEL (by rw [hA9]; norm_num) (by rw [hE]; norm_num) hLc hN₁3'
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N₁ A hAN,
      Set.mem_mul] at hgL
    obtain ⟨m, hm, a, ha, rfl⟩ := hgL
    refine ⟨m, hm, ?_⟩
    rw [← hg, map_conj_mul', map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer ha)]
  let actN : MulAction N₁ (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp N₁.subtype)
  set x₀ : Subgroup G := A ⊔ V with hx₀
  have hsmulN : ∀ (m : N₁) (Y : Subgroup G),
      m • Y = Y.map (MulAut.conj (m : G)).toMonoidHom := fun m Y => conj_smul_eq_map' (m : G) Y
  set Ω := MulAction.orbit N₁ x₀ with hΩ
  have hstab : V.subgroupOf N₁ ≤ MulAction.stabilizer N₁ x₀ := by
    intro v hv
    rw [MulAction.mem_stabilizer_iff, hsmulN]
    have hvx : (v : G) ∈ x₀ := Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hv)
    exact map_conj_eq_self_of_mem_normalizer (Subgroup.le_normalizer hvx)
  have hΩdvd : Ω.ncard ∣ (V.subgroupOf N₁).index := by
    have h := Subgroup.index_dvd_of_le hstab
    rwa [MulAction.index_stabilizer] at h
  have hΩodd : ¬ 2 ∣ Ω.ncard := fun h => hodd (h.trans hΩdvd)
  have hmemΩ : ∀ Y ∈ Ω, ∃ m ∈ N₁, Y = A.map (MulAut.conj m).toMonoidHom ⊔ V := by
    rintro Y ⟨m, rfl⟩
    refine ⟨m, m.2, ?_⟩
    show m • x₀ = _
    rw [hsmulN, hx₀, map_conj_sup_of_mem_normalizer (hN₁V m.2)]
  have hmemΩ' : ∀ m ∈ N₁, A.map (MulAut.conj m).toMonoidHom ⊔ V ∈ Ω := by
    intro m hm
    refine ⟨⟨m, hm⟩, ?_⟩
    show (⟨m, hm⟩ : N₁) • x₀ = _
    rw [hsmulN, hx₀, map_conj_sup_of_mem_normalizer (hN₁V hm)]
  let actT : MulAction T (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp T.subtype)
  have hsmulT : ∀ (t : T) (Y : Subgroup G),
      t • Y = Y.map (MulAut.conj (t : G)).toMonoidHom := fun t Y => conj_smul_eq_map' (t : G) Y
  let S : SubMulAction T (Subgroup G) :=
    { carrier := Ω
      smul_mem' := fun t Y hY => by
        obtain ⟨m, hm, rfl⟩ := hmemΩ Y hY
        rw [hsmulT, map_conj_sup_of_mem_normalizer (hTV t.2), ← map_conj_mul']
        have hm' : (t : G) * m * (t : G)⁻¹ ∈ N₁ :=
          (Subgroup.mem_normalizer_iff.mp (hTN t.2) m).mp hm
        have he : A.map (MulAut.conj ((t : G) * m)).toMonoidHom =
            (A.map (MulAut.conj (t : G)).toMonoidHom).map
              (MulAut.conj ((t : G) * m * (t : G)⁻¹)).toMonoidHom := by
          rw [← map_conj_mul']
          congr 2
          group
        have hEL : A.map (MulAut.conj ((t : G) * m)).toMonoidHom ≤ L := by
          rw [he]
          rintro _ ⟨x, hx, rfl⟩
          have hxL := hTA t t.2 hx
          have hm'L : (t : G) * m * (t : G)⁻¹ ∈ L := Subgroup.mem_sup_right hm'
          exact L.mul_mem (L.mul_mem hm'L hxL) (L.inv_mem hm'L)
        have hEc : Nat.card (A.map (MulAut.conj ((t : G) * m)).toMonoidHom) = 9 := by
          rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hA9]
        obtain ⟨m'', hm'', he''⟩ := hconjL _ hEL hEc
        rw [← he'']
        exact hmemΩ' m'' hm'' }
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hfix := hT.card_modEq_card_fixedPoints S
  have hSc : Nat.card S = Ω.ncard := Nat.card_coe_set_eq Ω
  obtain ⟨Y₁, hY₁⟩ : (MulAction.fixedPoints T S).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hE
    apply hΩodd
    rw [← hSc]
    have h0 : Nat.card (MulAction.fixedPoints T S) = 0 := by rw [hE]; simp
    have h2 : Nat.card (MulAction.fixedPoints T S) ≡ 0 [MOD 2] := by rw [h0]
    exact (Nat.modEq_zero_iff_dvd).mp (hfix.trans h2)
  obtain ⟨m, hm, hY₁eq⟩ := hmemΩ (Y₁ : Subgroup G) Y₁.2
  refine ⟨m, hm, fun t ht => ?_⟩
  have hfixt : (⟨t, ht⟩ : T) • Y₁ = Y₁ := MulAction.mem_fixedPoints.mp hY₁ ⟨t, ht⟩
  have h1 : ((⟨t, ht⟩ : T) • (Y₁ : Subgroup G)) = (Y₁ : Subgroup G) :=
    congrArg Subtype.val hfixt
  rw [hsmulT] at h1
  rw [← hY₁eq]
  exact mem_normalizer_of_map_conj_eq_self h1

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
