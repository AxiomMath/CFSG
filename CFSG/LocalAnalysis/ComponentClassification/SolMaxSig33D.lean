module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Cited
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxGen

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

theorem commutator_sup_le {C N A B₁ B₂ : Subgroup X} (hCN : C ≤ normalizer (N : Set X))
    (hB₁C : B₁ ≤ C) (hB₂C : B₂ ≤ C) (h₁ : ⁅A, B₁⁆ ≤ N) (h₂ : ⁅A, B₂⁆ ≤ N) :
    ⁅A, B₁ ⊔ B₂⁆ ≤ N := by
  rw [commutator_le]
  intro a ha g hg
  let S : Subgroup X :=
    { carrier := {g | g ∈ C ∧ ⁅a, g⁆ ∈ N}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
        refine ⟨mul_mem hg hh, ?_⟩
        have h1 : g * ⁅a, h⁆ * g⁻¹ ∈ N := (mem_normalizer_iff.mp (hCN hg) _).mp hh'
        have h2 : ⁅a, g * h⁆ = ⁅a, g⁆ * (g * ⁅a, h⁆ * g⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [h2]
        exact mul_mem hg' h1
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        refine ⟨inv_mem hg, ?_⟩
        have h1 : g⁻¹ * ⁅a, g⁆⁻¹ * g⁻¹⁻¹ ∈ N :=
          (mem_normalizer_iff.mp (hCN (inv_mem hg)) _).mp (inv_mem hg')
        have h2 : ⁅a, g⁻¹⁆ = g⁻¹ * ⁅a, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [h2]
        exact h1 }
  have hB₁S : B₁ ≤ S := fun g hg => ⟨hB₁C hg, h₁ (commutator_mem_commutator ha hg)⟩
  have hB₂S : B₂ ≤ S := fun g hg => ⟨hB₂C hg, h₂ (commutator_mem_commutator ha hg)⟩
  exact ((sup_le hB₁S hB₂S) hg).2

theorem commutator_le_coreActionKernel {L Y E : Subgroup X} (hY : Y ≤ normalizer (L : Set X))
    (hE : E ≤ UnbalancedLayer.coreActionKernel L) :
    ⁅Y, E⁆ ≤ UnbalancedLayer.coreActionKernel L := by
  rw [commutator_le]
  intro y hy e he
  rw [commutatorElement_def]
  exact mul_mem (conj_mem_coreActionKernel (hY hy) (hE he)) (inv_mem (hE he))

theorem le_core_of_forall_commutator (hbal : Sol78.BalanceTwoComponentInput) [Finite X]
    {S T : Subgroup X} (hS : S ≠ ⊥) (hT : T ≠ ⊥) (hSel : IsElementaryAbelian 2 S)
    (hTel : IsElementaryAbelian 2 T) (hST : S ≤ centralizer (T : Set X)) {Y : Subgroup X}
    (hY : Y ≤ (pPrimeCore 2 ↥(centralizer (S : Set X))).map (centralizer (S : Set X)).subtype ⊓
      centralizer (T : Set X))
    (hL : ∀ L : Subgroup X, GH74.GLS.IsPCompIn 2 (centralizer (T : Set X)) L →
      ⁅L, Y⁆ ≤ (pPrimeCore 2 ↥(centralizer (T : Set X))).map (centralizer (T : Set X)).subtype) :
    Y ≤ (pPrimeCore 2 ↥(centralizer (T : Set X))).map (centralizer (T : Set X)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CT : Subgroup X := centralizer (T : Set X) with hCTdef
  set OT := (pPrimeCore 2 ↥CT).map CT.subtype with hOTdef
  obtain ⟨ha, -, -⟩ := hbal X S T hS hT hSel hTel hST
  have hYC : Y ≤ CT := hY.trans inf_le_right
  set D : Subgroup ↥CT := Y.subgroupOf CT with hDdef
  have hOS : Odd (Nat.card ((pPrimeCore 2 ↥(centralizer (S : Set X))).map
      (centralizer (S : Set X)).subtype)) := by
    rw [card_map_of_injective (centralizer (S : Set X)).subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hDodd : Odd (Nat.card D) := by
    have h1 : Nat.card D = Nat.card Y := by
      rw [hDdef]
      exact Nat.card_congr (subgroupOfEquivOfLe hYC).toEquiv
    rw [h1]
    exact hOS.of_dvd_nat (card_dvd_of_le (hY.trans inf_le_left))
  have hOmem : ∀ z : ↥CT, (z : X) ∈ OT → z ∈ pPrimeCore 2 ↥CT := by
    rintro z ⟨w, hw, hwz⟩
    have : w = z := Subtype.ext hwz
    rwa [← this]
  have hD : D ≤ pPrimeCore 2 ↥CT := by
    refine GrSLit.le_pPrimeCore_of_commutators hDodd ?_ ?_
    · intro y hy d hd
      apply hOmem
      have hyX : (y : X) ∈ (GH74.GLS.pPrimePCore 2 ↥CT).map CT.subtype := ⟨y, hy, rfl⟩
      have hdX : (d : X) ∈ GH74.GLS.pPrimeCoreOf 2 (centralizer (S : Set X)) ⊓ CT :=
        hY (mem_subgroupOf.mp hd)
      have h1 := ha (commutator_mem_commutator (inv_mem hyX) (inv_mem hdX))
      have h2 : ((y⁻¹ * d⁻¹ * y * d : ↥CT) : X) = ⁅(y : X)⁻¹, (d : X)⁻¹⁆ := by
        simp [commutatorElement_def]
      rw [h2]
      exact h1
    · intro M hM y hy d hd
      apply hOmem
      have hLpc : GH74.GLS.IsPCompIn 2 CT (M.map CT.subtype) := by
        refine ⟨map_subtype_le _, ?_⟩
        change IsPComponent 2 ((M.map CT.subtype).comap CT.subtype)
        rw [comap_map_eq_self_of_injective CT.subtype_injective]
        exact hM
      have h1 := hL _ hLpc (commutator_mem_commutator (inv_mem (mem_map_of_mem CT.subtype hy))
        (inv_mem (mem_subgroupOf.mp hd)))
      have h2 : ((y⁻¹ * d⁻¹ * y * d : ↥CT) : X) = ⁅(CT.subtype y)⁻¹, (d : X)⁻¹⁆ := by
        simp [commutatorElement_def]
      rw [h2]
      exact h1
  intro x hx
  exact ⟨⟨x, hYC hx⟩, hD (mem_subgroupOf.mpr hx), rfl⟩

end CFSG.ComponentClassification.SolMax
