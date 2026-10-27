module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

theorem tableX_K_facts [Finite G] {X : Subgroup G} (hK : IsShapeK ↥(_root_.commutator G ⊓ X))
    (hR : Nat.card ↥(CFSG.Open.pCoreOf 2 X) = 256)
    (hDR : Nat.card ↥(derivedOf X ⊓ CFSG.Open.pCoreOf 2 X) = 128) :
    _root_.commutator G ⊓ X ≠ derivedOf X ⊔ CFSG.Open.pCoreOf 2 X ∧
      CFSG.Open.pCoreOf 2 (derivedOf X) = derivedOf X ⊓ CFSG.Open.pCoreOf 2 X ∧
      CFSG.Open.pCoreOf 2 (_root_.commutator G ⊓ X) = derivedOf X ⊓ CFSG.Open.pCoreOf 2 X := by
  have hRn : ∀ x ∈ X, ∀ r ∈ CFSG.Open.pCoreOf 2 X, x * r * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
    fun x hx r hr => pCoreOf_two_normalized X hx hr
  have hDn : ∀ x ∈ X, ∀ d ∈ derivedOf X, x * d * x⁻¹ ∈ derivedOf X :=
    fun x hx d hd => conj_mem_derivedOf hx hd
  have hO2 : Nat.card ↥(CFSG.Open.pCoreOf 2 (_root_.commutator G ⊓ X)) = 2 ^ 7 :=
    (isShapeZ2Z4StarExtra_pCoreOf hK).2.1
  have hP2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 X) := isPGroup_pCoreOf_two X
  have hDK : derivedOf X ≤ _root_.commutator G ⊓ X :=
    le_inf (derivedOf_le_commutator X) (derivedOf_le X)
  have hDRK : derivedOf X ⊓ CFSG.Open.pCoreOf 2 X ≤
      CFSG.Open.pCoreOf 2 (_root_.commutator G ⊓ X) :=
    le_pCoreOf_two_of_normalized (inf_le_left.trans hDK)
      (fun l hl q hq => ⟨hDn l hl.2 q hq.1, hRn l hl.2 q hq.2⟩) (hP2.to_le inf_le_right)
  refine ⟨?_, ?_, ?_⟩
  · intro hKe
    have hRK : CFSG.Open.pCoreOf 2 X ≤ _root_.commutator G ⊓ X := by
      rw [hKe]
      exact le_sup_right
    have hle : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (_root_.commutator G ⊓ X) :=
      le_pCoreOf_two_of_normalized hRK (fun l hl q hq => hRn l hl.2 q hq) hP2
    have := Subgroup.card_le_of_le hle
    rw [hO2, hR] at this
    omega
  · apply le_antisymm
    · refine le_inf (pCoreOf_two_le _) ?_
      refine le_pCoreOf_two_of_normalized ((pCoreOf_two_le _).trans (derivedOf_le X))
        (fun x hx q hq => ?_) (isPGroup_pCoreOf_two _)
      exact conj_mem_pCoreOf_two (map_conj_eq_of_normalized hx hDn) hq
    · exact le_pCoreOf_two_of_normalized inf_le_left
        (fun l hl q hq => ⟨(derivedOf X).mul_mem ((derivedOf X).mul_mem hl hq.1)
          ((derivedOf X).inv_mem hl), hRn l (derivedOf_le X hl) q hq.2⟩)
        (hP2.to_le inf_le_right)
  · symm
    exact Subgroup.eq_of_le_of_card_ge hDRK (by rw [hO2, hDR]; norm_num)

theorem tableX_three [Finite G] {X R D : Subgroup G} (hX : Nat.card ↥X = 30720)
    (hR : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R) (hD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    {T : Set G} (hT : ∀ k ∈ X, ∀ c ∈ T, k * c * k⁻¹ ∈ T) {c₀ σ₀ t : G} (hc₀ : c₀ ∈ T)
    (hσ₀ : σ₀ ∈ X) (hσ₀o : orderOf σ₀ = 3) (ht : t ∈ X) (htσ : t * σ₀ * t⁻¹ = σ₀⁻¹)
    (h1 : R ⊓ Gx σ₀ = Subgroup.closure ((centerOf D : Set G) ∪ {c₀}))
    (h2 : D ⊓ R ⊓ Gx σ₀ = centerOf D) :
    ∀ σ ∈ X, orderOf σ = 3 → ∃ c ∈ T,
      R ⊓ Gx σ = Subgroup.closure ((centerOf D : Set G) ∪ {c}) ∧ D ⊓ R ⊓ Gx σ = centerOf D := by
  intro σ hσ hσo
  obtain ⟨k, hk, rfl⟩ := exists_conj_of_orderOf_three hX hσ₀ hσ₀o ht htσ hσ hσo
  have hGx : (Gx σ₀).map (MulAut.conj k).toMonoidHom = Gx (k * σ₀ * k⁻¹) :=
    TwoHSData.map_centralizer_singleton (MulAut.conj k) σ₀
  have hZ : (centerOf D).map (MulAut.conj k).toMonoidHom = centerOf D := map_conj_centerOf hk hD
  refine ⟨k * c₀ * k⁻¹, hT k hk c₀ hc₀, ?_, ?_⟩
  · have h := congrArg (Subgroup.map (MulAut.conj k).toMonoidHom) h1
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective, map_conj_eq_of_normalized hk hR,
      hGx, MonoidHom.map_closure, Set.image_union, Set.image_singleton, ← Subgroup.coe_map,
      hZ] at h
    exact h
  · have h := congrArg (Subgroup.map (MulAut.conj k).toMonoidHom) h2
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective,
      Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective, map_conj_eq_of_normalized hk hR,
      map_conj_eq_of_normalized hk hD, hGx, hZ] at h
    exact h

theorem tableX_of_data [Finite G] {a z b z₁ : G} (ha : a ∈ Subgroup.center G)
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j))
    (hK : IsShapeK ↥(_root_.commutator G ⊓ Gx z)) (hX : Nat.card ↥(Gx z) = 30720)
    (hB : {c | IsConj b c ∧ c ∈ Gx z}.ncard = 120)
    (c : Fin 2 → G) (hc : ∀ i, c i ∈ tabXSet a z b z₁ i)
    (hstab : ∀ i, Nat.card ↥(Gx z ⊓ Gx (c i)) = ![768, 384] i)
    (hR : Nat.card ↥(CFSG.Open.pCoreOf 2 (Gx z)) = 256)
    (hD : Nat.card ↥(derivedOf (Gx z)) = 7680)
    (hDR : Nat.card ↥(derivedOf (Gx z) ⊓ CFSG.Open.pCoreOf 2 (Gx z)) = 128)
    (hDRs : Nat.card ↥(derivedOf (Gx z) ⊔ CFSG.Open.pCoreOf 2 (Gx z)) = 15360)
    {g₁ g₂ : G} (hg₁ : g₁ ∈ Gx z) (hg₂ : g₂ ∈ Gx z) (hs₁ : g₁ * g₁ ∈ derivedOf (Gx z))
    (hs₂ : g₂ * g₂ ∈ derivedOf (Gx z)) (hn₁ : g₁ ∉ derivedOf (Gx z))
    (hn₂ : g₂ ∉ derivedOf (Gx z)) (hn₁₂ : g₁ * g₂⁻¹ ∉ derivedOf (Gx z))
    (h0R : c 0 ∈ CFSG.Open.pCoreOf 2 (Gx z))
    (h0a : Nat.card ↥(Gx z ⊓ Gx (c 0) ⊓ CFSG.Open.pCoreOf 2 (Gx z)) = 2 ^ 7)
    (h0b : Nat.card ↥(Gx z ⊓ Gx (c 0) ⊓ CFSG.Open.pCoreOf 2 (Gx z) ⊓ derivedOf (Gx z)) = 2 ^ 6)
    (h0c : Nat.card ↥(Gx z ⊓ Gx (c 0) ⊓ derivedOf (Gx z)) = 2 ^ 6 * 3)
    (h1R : c 1 ∉ CFSG.Open.pCoreOf 2 (Gx z))
    (h1a : IsElemTwo 5 (Gx z ⊓ Gx (c 1) ⊓ CFSG.Open.pCoreOf 2 (Gx z)))
    (h1b : IsElemTwo 4 (Gx z ⊓ Gx (c 1) ⊓ CFSG.Open.pCoreOf 2 (Gx z) ⊓ derivedOf (Gx z)))
    (h1c : Nat.card ↥(Gx z ⊓ Gx (c 1) ⊓ derivedOf (Gx z)) = 2 ^ 5 * 3)
    {m₁ m₂ : G} (hm₁ : m₁ ∈ Gx z ⊓ Gx (c 1) ⊓ derivedOf (Gx z))
    (hm₂ : m₂ ∈ Gx z ⊓ Gx (c 1) ⊓ derivedOf (Gx z))
    (hcomm : m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∉ CFSG.Open.pCoreOf 2 (Gx z))
    (hZ : centerOf (derivedOf (Gx z)) = centerOf (derivedOf (Gx z) ⊓ CFSG.Open.pCoreOf 2 (Gx z)) ∧
      Nonempty (↥(centerOf (derivedOf (Gx z))) ≃* Z 2 × Z 4))
    {σ₀ t : G} (hσ₀ : σ₀ ∈ Gx z) (hσ₀o : orderOf σ₀ = 3) (ht : t ∈ Gx z)
    (htσ : t * σ₀ * t⁻¹ = σ₀⁻¹)
    (hCR : CFSG.Open.pCoreOf 2 (Gx z) ⊓ Gx σ₀ =
      Subgroup.closure ((centerOf (derivedOf (Gx z)) : Set G) ∪ {c 0}))
    (hCD : derivedOf (Gx z) ⊓ CFSG.Open.pCoreOf 2 (Gx z) ⊓ Gx σ₀ = centerOf (derivedOf (Gx z))) :
    TableXData a z b z₁ := by
  obtain ⟨hpart, hcard⟩ := tableX_orbits ha hnc hX hB c hc hstab
  have hRn : ∀ x ∈ Gx z, ∀ r ∈ CFSG.Open.pCoreOf 2 (Gx z),
      x * r * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (Gx z) :=
    fun x hx r hr => pCoreOf_two_normalized (Gx z) hx hr
  have hDn : ∀ x ∈ Gx z, ∀ d ∈ derivedOf (Gx z), x * d * x⁻¹ ∈ derivedOf (Gx z) :=
    fun x hx d hd => conj_mem_derivedOf hx hd
  obtain ⟨hKne, hpc1, hpc2⟩ := tableX_K_facts hK hR hDR
  have r0 := tableX_row0 hRn hDn (hpart.orbit 0) (hc 0) h0R h0a h0b h0c
  have r1 := tableX_row1 hRn hDn (hpart.orbit 1) (hc 1) h1R h1a h1b h1c hm₁ hm₂ hcomm
  have hle : derivedOf (Gx z) ⊔ CFSG.Open.pCoreOf 2 (Gx z) ≤ Gx z :=
    sup_le (derivedOf_le _) (pCoreOf_two_le _)
  refine ⟨hK, hpart, hcard, fun c' hc' => (r0 c' hc').1, fun c' hc' => (r0 c' hc').2.1,
    fun c' hc' => (r0 c' hc').2.2.1, fun c' hc' => (r0 c' hc').2.2.2.1,
    fun c' hc' => (r0 c' hc').2.2.2.2, fun c' hc' => (r1 c' hc').1, fun c' hc' => (r1 c' hc').2.1,
    fun c' hc' => (r1 c' hc').2.2.1, fun c' hc' => (r1 c' hc').2.2.2.1,
    fun c' hc' => (r1 c' hc').2.2.2.2, ?_, ?_, hKne, ⟨hpc1, hpc2⟩, ⟨?_, hZ.2⟩, ?_⟩
  · exact quotShape_elem2_two (derivedOf_le _) hDn (by omega) hg₁ hg₂ hs₁ hs₂ hn₁ hn₂ hn₁₂
  · have h := Subgroup.relIndex_mul_card (H := derivedOf (Gx z) ⊔ CFSG.Open.pCoreOf 2 (Gx z))
      (K := Gx z)
    rw [inf_eq_left.mpr hle, hDRs, hX] at h
    omega
  · rw [hpc1]
    exact hZ.1
  · exact tableX_three hX hRn hDn (T := tabXSet a z b z₁ 0)
      (fun k hk c' hc' => tabXSet_conj_mem ha hk 0 hc') (hc 0) hσ₀ hσ₀o ht htσ hCR hCD

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
