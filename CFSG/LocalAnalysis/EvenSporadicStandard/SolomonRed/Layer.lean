module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup CFSG CFSG.LocalCores

variable {K : Type*} [Group K] [Finite K]

theorem component_center_eq_bot (hF : fittingSubgroup K = ⊥) {L : Subgroup K}
    (hL : IsComponent L) : Subgroup.center ↥L = ⊥ := by
  have h1 := CFSG.ComponentClassification.SmallLocal.fitting_subnormal_intersection hL.2
  rw [hF, inf_bot_eq] at h1
  have h2 : fittingSubgroup ↥L = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _
    L.subtype_injective).1 h1
  have h3 : Subgroup.center ↥L ≤ fittingSubgroup ↥L :=
    (fitting_characteristic (G := ↥L)).2.2 _ inferInstance inferInstance
  rw [h2] at h3
  exact le_bot_iff.1 h3

theorem component_isSimple (hF : fittingSubgroup K = ⊥) {L : Subgroup K} (hL : IsComponent L) :
    IsSimpleGroup ↥L := by
  have hc := component_center_eq_bot hF hL
  have := hL.1.2.1
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem component_nonab (hF : fittingSubgroup K = ⊥) {L : Subgroup K} (hL : IsComponent L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  have hc := component_center_eq_bot hF hL
  let e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  refine ⟨(e a : K), (e a).2, (e b : K), (e b).2, fun h => hab (e.injective ?_)⟩
  rw [map_mul, map_mul]
  exact Subtype.ext h

omit [Finite K] in
theorem isComponent_conj {L : Subgroup K} (hL : IsComponent L) (g : K) :
    IsComponent (L.map (MulAut.conj g).toMonoidHom) :=
  isComponent_map_mulEquiv (MulAut.conj g) hL

theorem component_commute {L₁ L₂ : Subgroup K} (h₁ : IsComponent L₁) (h₂ : IsComponent L₂)
    (hne : L₁ ≠ L₂) : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := by
  rcases distinct_components_commute h₁ h₂ with h | h
  · exact absurd h hne
  · intro a ha b hb
    exact (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h ha) b hb).symm

theorem component_inf_eq_bot (hF : fittingSubgroup K = ⊥) {L₁ L₂ : Subgroup K}
    (h₁ : IsComponent L₁) (h₂ : IsComponent L₂) (hne : L₁ ≠ L₂) : L₁ ⊓ L₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hc := component_commute h₁ h₂ hne
  rw [mem_bot]
  exact eq_one_of_commute_of_simple (component_isSimple hF h₁) (component_nonab hF h₁) hx.1
    fun b hb => hc b hb x hx.2

theorem centralizer_layer_eq_bot (hF : fittingSubgroup K = ⊥) :
    centralizer (layer K : Set K) = ⊥ := by
  have hEc : (layer K).Characteristic := layer_characteristic
  have hEn : (layer K).Normal := inferInstance
  set C : Subgroup K := centralizer (layer K : Set K) with hC
  have hCn : C.Normal := Subgroup.normal_centralizer
  by_contra hCne
  obtain ⟨N, ⟨hNn, hNne, hNC⟩, hNmin⟩ :=
    (Set.toFinite {M : Subgroup K | M.Normal ∧ M ≠ ⊥ ∧ M ≤ C}).exists_minimal
      ⟨C, hCn, hCne, le_rfl⟩
  have hmin : ∀ M : Subgroup K, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
    intro M hM hMN
    by_cases hM1 : M = ⊥
    · exact Or.inl hM1
    · exact Or.inr (le_antisymm hMN (hNmin ⟨hM, hM1, hMN.trans hNC⟩ hMN))
  have hNF := le_generalizedFitting_of_minimal hNn hNne hmin
  have hgf : generalizedFitting K = layer K := by rw [generalizedFitting, hF, bot_sup_eq]
  rw [hgf] at hNF
  have hcomm : IsMulCommutative ↥N :=
    ⟨⟨fun x y => Subtype.ext ((mem_centralizer_iff.1 (hNC x.2) y (hNF y.2)).symm)⟩⟩
  have hle : N ≤ fittingSubgroup K := (fitting_characteristic (G := K)).2.2 N hNn inferInstance
  rw [hF] at hle
  exact hNne (le_bot_iff.1 hle)

theorem exists_component (hF : fittingSubgroup K = ⊥) (hK : ∃ x : K, x ≠ 1) :
    ∃ L : Subgroup K, IsComponent L := by
  by_contra hcon
  push Not at hcon
  have hE : layer K = ⊥ := layer_eq_bot_of_forall hcon
  have h := centralizer_layer_eq_bot hF
  rw [hE] at h
  obtain ⟨x, hx⟩ := hK
  apply hx
  have hx' : x ∈ centralizer ((⊥ : Subgroup K) : Set K) := by
    rw [mem_centralizer_iff]
    intro y hy
    have : y = 1 := hy
    rw [this]; simp
  rw [h] at hx'
  exact mem_bot.1 hx'

@[expose] def Rest (K : Type*) [Group K] (L₁ L₂ : Subgroup K) : Subgroup K :=
  sSup {L : Subgroup K | IsComponent L ∧ L ≠ L₁ ∧ L ≠ L₂}

theorem rest_le_centralizer {L₁ L₂ : Subgroup K} (h₁ : IsComponent L₁) (h₂ : IsComponent L₂) :
    Rest K L₁ L₂ ≤ centralizer ((L₁ ⊔ L₂ : Subgroup K) : Set K) := by
  refine sSup_le fun L ⟨hL, hL1, hL2⟩ => ?_
  rw [Subgroup.le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [← Subgroup.le_centralizer_iff]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact (component_commute hL h₁ hL1 a ha b hb).symm
  · rw [← Subgroup.le_centralizer_iff]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact (component_commute hL h₂ hL2 a ha b hb).symm

omit [Finite K] in
theorem rest_perfect (L₁ L₂ : Subgroup K) : ⁅Rest K L₁ L₂, Rest K L₁ L₂⁆ = Rest K L₁ L₂ := by
  refine le_antisymm (commutator_le_self _) (sSup_le fun L ⟨hL, _, _⟩ => ?_)
  calc L = ⁅L, L⁆ := (isPerfect_iff.mp hL.1.1).symm
    _ ≤ ⁅Rest K L₁ L₂, Rest K L₁ L₂⁆ :=
      commutator_mono (le_sSup ⟨hL, ‹_›, ‹_›⟩) (le_sSup ⟨hL, ‹_›, ‹_›⟩)

omit [Finite K] in
theorem layer_eq_sup_rest {L₁ L₂ : Subgroup K} (h₁ : IsComponent L₁) (h₂ : IsComponent L₂) :
    layer K = (L₁ ⊔ L₂) ⊔ Rest K L₁ L₂ := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    by_cases hL1 : L = L₁
    · exact hL1 ▸ le_sup_of_le_left le_sup_left
    by_cases hL2 : L = L₂
    · exact hL2 ▸ le_sup_of_le_left le_sup_right
    exact le_sup_of_le_right (le_sSup ⟨hL, hL1, hL2⟩)
  · refine sup_le (sup_le (component_le_layer h₁) (component_le_layer h₂)) (sSup_le ?_)
    rintro L ⟨hL, -, -⟩
    exact component_le_layer hL

section Involution

variable {z : K}

omit [Finite K] in
theorem map_conj_conj (hz : z * z = 1) (L : Subgroup K) :
    (L.map (MulAut.conj z).toMonoidHom).map (MulAut.conj z).toMonoidHom = L := by
  ext x
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have h := conj_conj_of_mul_self_eq_one hz w
    show z * (z * w * z⁻¹) * z⁻¹ ∈ L
    rw [h]
    exact hw
  · intro hx
    refine ⟨(MulAut.conj z) x, ⟨x, hx, rfl⟩, ?_⟩
    exact conj_conj_of_mul_self_eq_one hz x

omit [Finite K] in
theorem rest_conj (hz : z * z = 1) {L₁ L₂ : Subgroup K}
    (hL₂ : L₂ = L₁.map (MulAut.conj z).toMonoidHom) :
    ∀ x ∈ Rest K L₁ L₂, z * x * z⁻¹ ∈ Rest K L₁ L₂ := by
  have hle : Rest K L₁ L₂ ≤ (Rest K L₁ L₂).comap (MulAut.conj z).toMonoidHom := by
    refine sSup_le fun L ⟨hL, hL1, hL2⟩ => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨isComponent_conj hL z, ?_, ?_⟩
    · intro h
      apply hL2
      calc L = (L.map (MulAut.conj z).toMonoidHom).map (MulAut.conj z).toMonoidHom :=
            (map_conj_conj hz L).symm
        _ = L₁.map (MulAut.conj z).toMonoidHom := by rw [h]
        _ = L₂ := hL₂.symm
    · intro h
      apply hL1
      exact Subgroup.map_injective (MulAut.conj z).injective (h.trans hL₂)
  intro x hx
  exact hle hx

end Involution

end CFSG.EvenSporadicStandard.SolomonRed
