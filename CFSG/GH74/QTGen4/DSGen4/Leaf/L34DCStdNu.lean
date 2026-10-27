module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem nuNF_dd (τ : ↥(torus3 F)) :
    ((nuNFEquiv F (0, 0, 0, τ) : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = (τ : projectiveSL 3 F) := by
  rw [nuNFEquiv_val]
  simp [uElt, xP_zero, yP_zero, wP_zero]

theorem nuNF_xS : ((nuNFEquiv F (1, 0, 0, 1) : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = xP 1 := by
  rw [nuNFEquiv_val]
  simp [uElt, yP_zero, wP_zero]

theorem nuNF_yS : ((nuNFEquiv F (0, 1, 0, 1) : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = yP 1 := by
  rw [nuNFEquiv_val]
  simp [uElt, xP_zero, wP_zero]

theorem nuNF_sxw (s κ : F) :
    ((nuNFEquiv F (s, 0, κ, 1) : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = xP s * wP κ := by
  rw [nuNFEquiv_val]
  simp [uElt, yP_zero, wP_zero]

theorem nuNF_tyw (t κ : F) :
    ((nuNFEquiv F (0, t, κ, 1) : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = yP t * wP κ := by
  rw [nuNFEquiv_val]
  simp [uElt, xP_zero, wP_zero]

theorem nuNF_dd_inv (τ : ↥(torus3 F)) :
    nuNFEquiv F (0, 0, 0, τ⁻¹) = (nuNFEquiv F (0, 0, 0, τ))⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv, nuNF_dd, nuNF_dd, Subgroup.coe_inv]

theorem nuCoord_dd (s t : Fˣ) (ε : Bool) (τ : ↥(torus3 F)) :
    nuCoord s t 0 0 ε (0, 0, 0, τ) = (0, 0, 0, if ε then τ⁻¹ else τ) := by
  cases ε <;> simp [nuCoord, nuFrob]

theorem nuCoord_xS (s t : Fˣ) (ε : Bool) :
    nuCoord s t 0 0 ε (1, 0, 0, 1) = ((s : F), 0, 0, 1) := by
  cases ε <;> simp [nuCoord, nuFrob]

theorem nuCoord_yS (s t : Fˣ) (ε : Bool) :
    nuCoord s t 0 0 ε (0, 1, 0, 1) = (0, (t : F), 0, 1) := by
  cases ε <;> simp [nuCoord, nuFrob]

theorem nuCoord_one_dd (κ κ' : F) (τ : ↥(torus3 F)) (ε : Bool) :
    nuCoord 1 1 κ 0 false (0, 0, 0, if ε then τ⁻¹ else τ) = (0, 0, 0, if ε then τ⁻¹ else τ) ∧
    nuCoord 1 1 0 κ' false (0, 0, 0, if ε then τ⁻¹ else τ) = (0, 0, 0, if ε then τ⁻¹ else τ) := by
  constructor <;> simp [nuCoord, nuFrob]

theorem nuCoord_one_xS (κ : F) (s : Fˣ) :
    nuCoord 1 1 κ 0 false ((s : F), 0, 0, 1) = ((s : F), 0, κ * (s : F) ^ 2, 1) := by
  simp [nuCoord, nuFrob]

theorem nuCoord_one_xS' (κ' κ₁ : F) (s : F) :
    nuCoord 1 1 0 κ' false (s, 0, κ₁, 1) = (s, 0, κ₁, 1) := by
  simp [nuCoord, nuFrob]

theorem nuCoord_one_yS (κ : F) (t : F) :
    nuCoord 1 1 κ 0 false (0, t, 0, 1) = (0, t, 0, 1) := by
  simp [nuCoord, nuFrob]

theorem nuCoord_one_yS' (κ' : F) (t : Fˣ) :
    nuCoord 1 1 0 κ' false (0, (t : F), 0, 1) = (0, (t : F), κ' * (t : F) ^ 2, 1) := by
  simp [nuCoord, nuFrob]

theorem phi_dd (s t : Fˣ) (κ κ' : F) (ε : Bool) (τ : ↥(torus3 F)) :
    nuMap 1 1 0 κ' false (nuMap 1 1 κ 0 false (nuMap s t 0 0 ε
      (nuNFEquiv F (0, 0, 0, τ)))) = nuNFEquiv F (0, 0, 0, if ε then τ⁻¹ else τ) := by
  rw [nuMap_nuNFEquiv, nuCoord_dd, nuMap_nuNFEquiv, (nuCoord_one_dd κ κ' τ ε).1, nuMap_nuNFEquiv,
    (nuCoord_one_dd κ κ' τ ε).2]

theorem phi_xS (s t : Fˣ) (κ κ' : F) (ε : Bool) :
    nuMap 1 1 0 κ' false (nuMap 1 1 κ 0 false (nuMap s t 0 0 ε (nuNFEquiv F (1, 0, 0, 1)))) =
      nuNFEquiv F ((s : F), 0, κ * (s : F) ^ 2, 1) := by
  rw [nuMap_nuNFEquiv, nuCoord_xS, nuMap_nuNFEquiv, nuCoord_one_xS, nuMap_nuNFEquiv,
    nuCoord_one_xS']

theorem phi_yS (s t : Fˣ) (κ κ' : F) (ε : Bool) :
    nuMap 1 1 0 κ' false (nuMap 1 1 κ 0 false (nuMap s t 0 0 ε (nuNFEquiv F (0, 1, 0, 1)))) =
      nuNFEquiv F (0, (t : F), κ' * (t : F) ^ 2, 1) := by
  rw [nuMap_nuNFEquiv, nuCoord_yS, nuMap_nuNFEquiv, nuCoord_one_yS, nuMap_nuNFEquiv,
    nuCoord_one_yS']

end CFSG.GH74.QTGen4.DSGen4.L34
