module

public import CFSG.GH74.GLS.C3.Prop121.Card7Facts2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.GH74.GLS.Pattern
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.Layer3

theorem numMoved_altY11 : numMoved ((altY11 : A11) : Perm (Fin 11)) = 8 := by
  have h8 : (8 : ℕ) ≤ 11 := by norm_num
  have h := yPerm_cycleType h8
  rw [numMoved_eq_card_support, ← Equiv.Perm.sum_cycleType]
  show (yPerm h8).cycleType.sum = 8
  rw [h]
  rfl

theorem card_cent_altY11 : Nat.card ↥(centralizer ({altY11} : Set A11)) = 1152 := by
  have h := card_centralizer_altY (by norm_num : 8 ≤ 11)
  have e : Nat.card ↥(centralizer ({altY11} : Set A11)) * 2 = 2304 := by
    rw [altY11]; rw [h]; norm_num [Nat.factorial]
  omega

variable {G : Type} [Group G] [Finite G]

theorem numMoved_eq_four_of_card (g : A11) (hg : orderOf g = 2)
    (hc : Nat.card ↥(centralizer ({g} : Set A11)) = 4 * Nat.factorial 7) :
    numMoved (g : Perm (Fin 11)) = 4 := by
  rcases numMoved_eq_of_involution_alternating 11 le_rfl g hg with h4 | h8
  · exact h4
  · exfalso
    have hY : orderOf altY11 = 2 := orderOf_altY _
    have hconj : IsConj g altY11 :=
      isConj_alternating_of_numMoved_eq 11 g altY11 hg hY (by rw [h8, numMoved_altY11])
    rw [card_centralizer_eq_of_isConj hconj, card_cent_altY11] at hc
    norm_num [Nat.factorial] at hc

theorem count_xtype (hSyl : SylFacts) (hap : IsApproxTo G A11) (x : G) (hx : orderOf x = 2)
    (hcx : Nat.card ↥(centralizer ({x} : Set G)) = 4 * Nat.factorial 7) (SS : Sylow 2 G) :
    Nat.card {u : ↥(SS : Subgroup G) // orderOf (u : G) = 2 ∧ IsConj x (u : G)} = 14 := by
  obtain ⟨S0, S', φ, hconj, hcent⟩ := hap.1
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G S0 SS
  obtain ⟨d, hd⟩ := exists_conj_mem_sylow_two S0 hx
  set x0 : ↥(S0 : Subgroup G) := ⟨d * x * d⁻¹, hd⟩ with hx0
  have hx0o : orderOf x0 = 2 := by
    rw [← Subgroup.orderOf_coe]
    show orderOf (d * x * d⁻¹) = 2
    rw [show d * x * d⁻¹ = MulAut.conj d x from rfl, MulEquiv.orderOf_eq]; exact hx
  have hxx0 : IsConj x (x0 : G) := isConj_iff.2 ⟨d, rfl⟩
  have hc0 : Nat.card ↥(centralizer ({(x0 : G)} : Set G)) = 4 * Nat.factorial 7 := by
    rw [← card_centralizer_eq_of_isConj hxx0]; exact hcx
  have hφx0o : orderOf (φ x0 : A11) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hx0o
  have hφx0 : numMoved (((φ x0 : ↥(S' : Subgroup A11)) : A11) : Perm (Fin 11)) = 4 := by
    apply numMoved_eq_four_of_card _ hφx0o
    obtain ⟨e⟩ := hcent x0 hx0o
    rw [← Nat.card_congr e.toEquiv, hc0]
  have hS0 : ∀ u : ↥(S0 : Subgroup G), orderOf u = 2 →
      (IsConj x (u : G) ↔ numMoved (((φ u : ↥(S' : Subgroup A11)) : A11) : Perm (Fin 11)) = 4) := by
    intro u hu
    have hφu : orderOf (φ u : A11) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hu
    have h1 : IsConj x (u : G) ↔ IsConj (x0 : G) (u : G) :=
      ⟨fun hc => hxx0.symm.trans hc, fun hc => hxx0.trans hc⟩
    rw [h1, hconj x0 u hx0o hu]
    constructor
    · intro hc
      rw [← numMoved_eq_of_isConj_alternating 11 hc, hφx0]
    · intro h4
      exact isConj_alternating_of_numMoved_eq 11 _ _ hφx0o hφu (by rw [hφx0, h4])
  have hmem : ∀ u : G, u ∈ (SS : Subgroup G) ↔ h⁻¹ * u * h ∈ (S0 : Subgroup G) := by
    intro u
    rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨u0, hu0, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hu0
    · intro hm
      exact ⟨h⁻¹ * u * h, hm, by simp [MulAut.conj_apply, mul_assoc]⟩
  let e1 : ↥(SS : Subgroup G) ≃ ↥(S0 : Subgroup G) :=
    { toFun := fun u => ⟨h⁻¹ * (u : G) * h, (hmem u).1 u.2⟩
      invFun := fun u => ⟨h * (u : G) * h⁻¹, (hmem _).2 (by simp [mul_assoc])⟩
      left_inv := fun u => by ext; simp [mul_assoc]
      right_inv := fun u => by ext; simp [mul_assoc] }
  have hP1 : ∀ u : ↥(SS : Subgroup G), (orderOf (u : G) = 2 ∧ IsConj x (u : G)) ↔
      (orderOf ((e1 u : ↥(S0 : Subgroup G)) : G) = 2 ∧ IsConj x ((e1 u : ↥(S0 : Subgroup G)) : G)) := by
    intro u
    have hc : IsConj (u : G) (h⁻¹ * (u : G) * h) := isConj_iff.2 ⟨h⁻¹, by simp [mul_assoc]⟩
    have ho : orderOf (h⁻¹ * (u : G) * h) = orderOf (u : G) := (orderOf_eq_of_isConj' hc).symm
    show _ ↔ (orderOf (h⁻¹ * (u : G) * h) = 2 ∧ IsConj x (h⁻¹ * (u : G) * h))
    rw [ho]
    exact and_congr_right (fun _ => ⟨fun h' => h'.trans hc, fun h' => h'.trans hc.symm⟩)
  have hP2 : ∀ u : ↥(S0 : Subgroup G), (orderOf (u : G) = 2 ∧ IsConj x (u : G)) ↔
      (orderOf ((φ u : ↥(S' : Subgroup A11)) : A11) = 2 ∧
        numMoved (((φ u : ↥(S' : Subgroup A11)) : A11) : Perm (Fin 11)) = 4) := by
    intro u
    have ho : orderOf ((φ u : ↥(S' : Subgroup A11)) : A11) = orderOf (u : G) := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
    rw [ho]
    constructor
    · rintro ⟨h2, hc⟩
      refine ⟨h2, (hS0 u ?_).1 hc⟩
      rw [← Subgroup.orderOf_coe]; exact h2
    · rintro ⟨h2, h4⟩
      refine ⟨h2, (hS0 u ?_).2 h4⟩
      rw [← Subgroup.orderOf_coe]; exact h2
  let E1 := Equiv.subtypeEquiv (p := fun u : ↥(SS : Subgroup G) => orderOf (u : G) = 2 ∧ IsConj x (u : G))
    (q := fun u : ↥(S0 : Subgroup G) => orderOf (u : G) = 2 ∧ IsConj x (u : G)) e1 hP1
  let E2 := Equiv.subtypeEquiv (p := fun u : ↥(S0 : Subgroup G) => orderOf (u : G) = 2 ∧ IsConj x (u : G))
    (q := fun v : ↥(S' : Subgroup A11) => orderOf (v : A11) = 2 ∧
      numMoved ((v : A11) : Perm (Fin 11)) = 4) φ.toEquiv hP2
  rw [Nat.card_congr (E1.trans E2)]
  exact hSyl.count14 S'

end CFSG.GH74.GLS.C3.Prop121.Card7
