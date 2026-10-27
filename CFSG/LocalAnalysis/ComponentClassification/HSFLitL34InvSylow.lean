module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_mul_self {x : G} (hx : x * x = 1) : IsPGroup 2 (zpowers x) := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem le_of_isSylowTwoIn {S H X : Subgroup G} (hS : IsSylowTwoIn S H) (hXH : X ≤ H)
    (hX : IsPGroup 2 X) (hSX : S ≤ normalizer (X : Set G)) : X ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := GrS5.IsSylowTwoIn.isPGroup hS
  obtain ⟨hSH, P, hP⟩ := hS
  have hsup : IsPGroup 2 ↥(S ⊔ X) := hS2.to_sup_of_normal_right' hX hSX
  have hle : S ⊔ X ≤ H := sup_le hSH hXH
  have h1 : IsPGroup 2 ((S ⊔ X).subgroupOf H) := hsup.of_equiv (subgroupOfEquivOfLe hle).symm
  have h2 : (P : Subgroup ↥H) ≤ (S ⊔ X).subgroupOf H := by
    rw [hP]; exact subgroupOf_mono _ le_sup_left
  have h3 := P.is_maximal' h1 h2
  intro x hx
  have hxm : (⟨x, hXH hx⟩ : ↥H) ∈ (S ⊔ X).subgroupOf H :=
    mem_subgroupOf.mpr (mem_sup_right hx)
  rw [h3, hP] at hxm
  exact mem_subgroupOf.mp hxm

theorem mem_of_isSylowTwoIn [Finite G] {S H : Subgroup G} (hS : IsSylowTwoIn S H) {x : G}
    (hxH : x ∈ H) (hx2 : x * x = 1) (hxS : ∀ s ∈ S, s * x = x * s) : x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : IsPGroup 2 (zpowers x) := isPGroup_zpowers_of_mul_self hx2
  refine le_of_isSylowTwoIn hS (zpowers_le.mpr hxH) hx (fun s hs => ?_) (mem_zpowers x)
  refine mem_normalizer_iff.mpr fun y => ?_
  have hsx : Commute s x := hxS s hs
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [(hsx.zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers x) k
  · intro hy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy
    have e : y = s⁻¹ * x ^ k * s := by rw [hk]; group
    rw [e, ((hsx.inv_left).zpow_right k).eq, inv_mul_cancel_right]
    exact zpow_mem (mem_zpowers x) k

theorem exists_isSylowTwoIn_normalized [Finite G] {H X : Subgroup G} (hX : IsPGroup 2 X)
    (hXN : X ≤ normalizer (H : Set G)) :
    ∃ D : Subgroup G, IsSylowTwoIn D H ∧ X ≤ normalizer (D : Set G) ∧ X ⊓ H ≤ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := H ⊔ X with hN
  have hHN : H ≤ N := le_sup_left
  have hXN' : X ≤ N := le_sup_right
  have hnorm : (H.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer hHN).mpr (sup_le le_normalizer hXN)
  have hX' : IsPGroup 2 (X.subgroupOf N) := hX.of_equiv (subgroupOfEquivOfLe hXN').symm
  obtain ⟨Sg0, hSg0⟩ := hX'.exists_le_sylow
  set Sg : Subgroup G := (Sg0 : Subgroup ↥N).map N.subtype with hSg
  have hSg0N : Sg ≤ N := map_subtype_le _
  have hSyl : IsSylowTwoIn Sg N := ⟨hSg0N, Sg0, by rw [hSg, subgroupOf_map_subtype_eq]⟩
  have hXSg0 : X ≤ Sg := fun x hx => ⟨⟨x, hXN' hx⟩, hSg0 (mem_subgroupOf.mpr hx), rfl⟩
  refine ⟨Sg ⊓ H, isSylowTwoIn_inf_of_isSubnormal hSyl hHN hnorm.isSubnormal, fun x hx => ?_,
    inf_le_inf_right H hXSg0⟩
  refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
    exact mem_inf.mpr ⟨mul_mem (mul_mem (hXSg0 hx) hy1) (inv_mem (hXSg0 hx)),
      (mem_normalizer_iff.mp (hXN hx) y).mp hy2⟩
  · obtain ⟨hy1, hy2⟩ := mem_inf.mp hy
    have e : y = x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ := by group
    rw [e]
    exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem (hXSg0 hx)) hy1) (inv_mem (inv_mem (hXSg0 hx))),
      (mem_normalizer_iff.mp (inv_mem (hXN hx)) _).mp hy2⟩

theorem not_isCyclic_of_perfect [Finite G] {K P : Subgroup G} (hperf : ⁅K, K⁆ = K)
    (hP : IsSylowTwoIn P K) (hP1 : P ≠ ⊥) : ¬ IsCyclic P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcyc
  obtain ⟨hPK, P₀, hP₀⟩ := hP
  have e₀ : ↥(P₀ : Subgroup ↥K) ≃* ↥P := by
    rw [hP₀]; exact subgroupOfEquivOfLe hPK
  have hcyc₀ : IsCyclic ↥(P₀ : Subgroup ↥K) := isCyclic_of_surjective e₀.symm.toMonoidHom
    e₀.symm.surjective
  have : Fintype ↥K := Fintype.ofFinite _
  have heven : Even (Fintype.card ↥K) := by
    rw [← Nat.card_eq_fintype_card]
    have h2 : 2 ∣ Nat.card ↥P := by
      rcases (GrS5.IsSylowTwoIn.isPGroup ⟨hPK, P₀, hP₀⟩).card_eq_or_dvd with h | h
      · exfalso
        have := (Subgroup.card_eq_one).mp h
        exact hP1 this
      · exact h
    have h3 : Nat.card ↥P ∣ Nat.card ↥K := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact even_iff_two_dvd.mpr (h2.trans h3)
  obtain ⟨-, hsurj, -, -⟩ := LinearGroups.cyclic_sylow_index_two heven P₀ hcyc₀
  obtain ⟨g, hg⟩ := hsurj (-1)
  have hcomm : commutator ↥K = ⊤ := by
    apply map_injective K.subtype_injective
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype,
      hperf]
  have hker := Abelianization.commutator_subset_ker
    (Equiv.Perm.sign.comp (MulAction.toPermHom ↥K ↥K))
  rw [hcomm] at hker
  have h1 : g ∈ (Equiv.Perm.sign.comp (MulAction.toPermHom ↥K ↥K)).ker := hker (mem_top g)
  rw [MonoidHom.mem_ker, hg] at h1
  exact absurd h1 (by decide)

theorem exists_conj_mul [Finite G] {D : Subgroup G} (hD : IsPGroup 2 D) {t b : G}
    (ht : t * t = 1) (htD : t ∉ D) (htN : t ∈ normalizer (D : Set G)) (hbD : b ∈ D)
    (hb2 : b * b = 1) (hbt : b * t = t * b)
    (hC : ∀ d ∈ D, d * t = t * d → d = 1 ∨ d = b) (hcard : 4 ≤ Nat.card D) :
    ∃ v ∈ D, v⁻¹ * t * v = t * b ∧ v * b = b * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ∀ x : G, x * x = 1 → IsPGroup 2 (zpowers x) := fun x hx =>
    isPGroup_zpowers_of_mul_self hx
  set H := zpowers t ⊔ D with hH
  set U := zpowers b ⊔ zpowers t with hU
  have htDN : zpowers t ≤ normalizer (D : Set G) := zpowers_le.mpr htN
  have hHp : IsPGroup 2 H := (h2 t ht).to_sup_of_normal_right' hD htDN
  have hUH : U ≤ H := sup_le (zpowers_le.mpr (mem_sup_right hbD)) le_sup_left
  have hUmem : ∀ x ∈ U, x = 1 ∨ x = b ∨ x = t ∨ x = b * t := fun x hx =>
    mem_four_of_mem_sup hb2 ht hbt hx
  have hlt : U.subgroupOf H < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun heq => ?_
    have hDb : D ≤ zpowers b := by
      intro d hd
      have hdU : (⟨d, mem_sup_right hd⟩ : ↥H) ∈ U.subgroupOf H := by rw [heq]; exact mem_top _
      rcases hUmem d (mem_subgroupOf.mp hdU) with h | h | h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers b
      · exact absurd (h ▸ hd) htD
      · exfalso
        apply htD
        have e : t = b⁻¹ * d := by rw [h]; group
        rw [e]
        exact mul_mem (inv_mem hbD) hd
    have hcb : Nat.card (zpowers b) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hb2))
    have := Subgroup.card_le_of_le hDb
    omega
  have : Group.IsNilpotent ↥H := hHp.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥H) (U.subgroupOf H) hlt
  obtain ⟨h, hhN, hhU⟩ := IsConcreteLE.exists_of_lt hnc
  have hh : (h : G) ∈ ((zpowers t ⊔ D : Subgroup G) : Set G) := h.2
  rw [coe_mul_of_left_le_normalizer_right _ _ htDN] at hh
  obtain ⟨a, ha, d, hd, had0⟩ := hh
  have had : a * d = (h : G) := had0
  have haU : a ∈ U := mem_sup_right ha
  have hat : a * t = t * a := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact ((Commute.refl t).zpow_left k).eq
  have htU : (⟨t, mem_sup_left (mem_zpowers t)⟩ : ↥H) ∈ U.subgroupOf H :=
    mem_subgroupOf.mpr (mem_sup_right (mem_zpowers t))
  have h1 := (mem_normalizer_iff.mp hhN _).mp htU
  rw [mem_subgroupOf] at h1
  simp only [coe_mul, coe_inv] at h1
  rw [← had] at h1
  have h3 : d * t * d⁻¹ ∈ U := by
    have e : d * t * d⁻¹ = a⁻¹ * (a * d * t * (a * d)⁻¹) * a := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem haU) h1) haU
  rcases hUmem _ h3 with h4 | h4 | h4 | h4
  · exfalso
    apply htD
    have e : t = d⁻¹ * (d * t * d⁻¹) * d := by group
    rw [e, h4, mul_one]
    exact mul_mem (inv_mem hd) hd
  · exfalso
    apply htD
    have e : t = d⁻¹ * (d * t * d⁻¹) * d := by group
    rw [e, h4]
    exact mul_mem (mul_mem (inv_mem hd) hbD) hd
  · exfalso
    have hdt : d * t = t * d := by
      calc d * t = d * t * d⁻¹ * d := by group
        _ = t * d := by rw [h4]
    apply hhU
    rw [mem_subgroupOf, ← had]
    rcases hC d hd hdt with h5 | h5
    · rw [h5, mul_one]; exact haU
    · rw [h5]; exact mul_mem haU (mem_sup_left (mem_zpowers b))
  ·
    have hbU : (⟨b, hUH (mem_sup_left (mem_zpowers b))⟩ : ↥H) ∈ U.subgroupOf H :=
      mem_subgroupOf.mpr (mem_sup_left (mem_zpowers b))
    have h6 := (mem_normalizer_iff.mp hhN _).mp hbU
    rw [mem_subgroupOf] at h6
    simp only [coe_mul, coe_inv] at h6
    rw [← had] at h6
    have hab : a * b = b * a := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      exact ((Commute.symm hbt).zpow_left k).eq
    have h7 : d * b * d⁻¹ ∈ U := by
      have e : d * b * d⁻¹ = a⁻¹ * (a * d * b * (a * d)⁻¹) * a := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem haU) h6) haU
    have h8 : d * b * d⁻¹ ∈ D := mul_mem (mul_mem hd hbD) (inv_mem hd)
    have hdb : d * b = b * d := by
      rcases hUmem _ h7 with h9 | h9 | h9 | h9
      · have hb1 : b = 1 := by
          have e : b = d⁻¹ * (d * b * d⁻¹) * d := by group
          rw [e, h9]; group
        rw [hb1]; group
      · calc d * b = d * b * d⁻¹ * d := by group
          _ = b * d := by rw [h9]
      · exact absurd (h9 ▸ h8) htD
      · exfalso
        apply htD
        have e : t = b⁻¹ * (d * b * d⁻¹) := by rw [h9]; group
        rw [e]
        exact mul_mem (inv_mem hbD) h8
    refine ⟨d⁻¹, inv_mem hd, ?_, ?_⟩
    · rw [inv_inv, h4, hbt]
    · calc d⁻¹ * b = d⁻¹ * (b * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * b) * d⁻¹ := by rw [hdb]
        _ = b * d⁻¹ := by group

end CFSG.ComponentClassification.HSFLit.L34Inv
