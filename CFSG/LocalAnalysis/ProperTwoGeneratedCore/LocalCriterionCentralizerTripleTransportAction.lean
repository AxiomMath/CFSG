module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

abbrev rightAct (a : Ω) (g : G) : Ω := MulOpposite.op g • a

abbrev rightStabilizer (a : Ω) : Subgroup G :=
  (MulAction.stabilizer Gᵐᵒᵖ a).unop

abbrev rightFixedSet (A : Subgroup G) : Set Ω :=
  {a | ∀ g : G, g ∈ A → rightAct a g = a}

abbrev tripleStabilizer (z : G) (alpha beta : Ω) : Subgroup G :=
  rightStabilizer alpha ⊓ rightStabilizer beta ⊓ rightStabilizer (rightAct beta z)

theorem rightAct_one (a : Ω) : rightAct a (1 : G) = a := by
  simp only [rightAct, MulOpposite.op_one, one_smul]

theorem rightAct_mul (a : Ω) (g h : G) :
    rightAct (rightAct a g) h = rightAct a (g * h) := by
  simp only [rightAct, MulOpposite.op_mul, mul_smul]

theorem rightAct_inv_cancel (a : Ω) (g : G) :
    rightAct (rightAct a g) g⁻¹ = a := by
  rw [rightAct_mul, mul_inv_cancel, rightAct_one]

theorem rightAct_injective (g : G) : Function.Injective (fun a : Ω => rightAct a g) := by
  intro a b hab
  have hh := congrArg (fun c : Ω => rightAct c g⁻¹) hab
  simpa only [rightAct_inv_cancel] using hh

theorem mem_rightStabilizer (a : Ω) (g : G) :
    g ∈ rightStabilizer a ↔ rightAct a g = a := Iff.rfl

theorem mem_rightFixedSet (A : Subgroup G) (a : Ω) :
    a ∈ rightFixedSet A ↔ A ≤ rightStabilizer a := Iff.rfl

theorem mem_rightConjugate (A : Subgroup G) (g x : G) :
    x ∈ rightConjugate A g ↔ g * x * g⁻¹ ∈ A := by
  change x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]

theorem rightStabilizer_rightConjugate (a : Ω) (g : G) :
    rightConjugate (rightStabilizer a) g = rightStabilizer (rightAct a g) := by
  ext x
  rw [mem_rightConjugate, mem_rightStabilizer, mem_rightStabilizer]
  constructor
  · intro hx
    calc
      rightAct (rightAct a g) x = rightAct a (g * x) := rightAct_mul _ _ _
      _ = rightAct (rightAct a (g * x * g⁻¹)) g := by
        rw [rightAct_mul]
        simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = rightAct a g := by rw [hx]
  · intro hx
    have hh := congrArg (fun b : Ω => rightAct b g⁻¹) hx
    simpa only [rightAct_mul, mul_inv_cancel, rightAct_one] using hh

theorem rightFixedSet_rightConjugate_mem (A : Subgroup G) (g : G)
    {a : Ω} (ha : a ∈ rightFixedSet A) :
    rightAct a g ∈ rightFixedSet (rightConjugate A g) := by
  intro x hx
  have hh := (mem_rightConjugate A g x).mp hx
  calc
    rightAct (rightAct a g) x = rightAct a (g * x) := rightAct_mul _ _ _
    _ = rightAct (rightAct a (g * x * g⁻¹)) g := by
      rw [rightAct_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = rightAct a g := by rw [ha _ hh]

theorem normalizer_preserves_rightFixedSet (A : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (A : Set G)) {a : Ω}
    (ha : a ∈ rightFixedSet A) : rightAct a g ∈ rightFixedSet A := by
  intro x hx
  have hconj : g * x * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  calc
    rightAct (rightAct a g) x = rightAct a (g * x) := rightAct_mul _ _ _
    _ = rightAct (rightAct a (g * x * g⁻¹)) g := by
      rw [rightAct_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = rightAct a g := by rw [ha _ hconj]

theorem rightAct_commute (a : Ω) {g h : G} (hcomm : g * h = h * g) :
    rightAct (rightAct a g) h = rightAct (rightAct a h) g := by
  rw [rightAct_mul, rightAct_mul, hcomm]

theorem centralizer_fixes_unique_point {z : G} {alpha : Ω}
    (hunique : ∀ a : Ω, rightAct a z = a ↔ a = alpha)
    (c : G) (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    rightAct alpha c = alpha := by
  have halpha : rightAct alpha z = alpha := (hunique alpha).mpr rfl
  have hcomm : z * c = c * z := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  apply (hunique _).mp
  rw [← rightAct_commute alpha hcomm, halpha]

theorem three_points_distinct {z : G} {alpha beta : Ω}
    (hz : IsInvolution z)
    (hunique : ∀ a : Ω, rightAct a z = a ↔ a = alpha) (hbeta : beta ≠ alpha) :
    alpha ≠ beta ∧ alpha ≠ rightAct beta z ∧ beta ≠ rightAct beta z := by
  have halpha : rightAct alpha z = alpha := (hunique alpha).mpr rfl
  refine ⟨hbeta.symm, ?_, ?_⟩
  · intro heq
    have hh := congrArg (fun a : Ω => rightAct a z) heq
    rw [halpha, rightAct_mul, ← pow_two, hz.sq_eq_one, rightAct_one] at hh
    exact hbeta hh.symm
  · intro heq
    exact hbeta ((hunique beta).mp heq.symm)

theorem triple_subgroup_fixes_three (z : G) (alpha beta : Ω) (A : Subgroup G)
    (hAE : A ≤ tripleStabilizer z alpha beta) :
    alpha ∈ rightFixedSet A ∧ beta ∈ rightFixedSet A ∧ rightAct beta z ∈ rightFixedSet A := by
  exact ⟨(mem_rightFixedSet A alpha).mpr (hAE.trans (inf_le_left.trans inf_le_left)),
    (mem_rightFixedSet A beta).mpr (hAE.trans (inf_le_left.trans inf_le_right)),
    (mem_rightFixedSet A _).mpr (hAE.trans inf_le_right)⟩

theorem tripleStabilizer_rightConjugate {z : G} {alpha : Ω}
    (hunique : ∀ a : Ω, rightAct a z = a ↔ a = alpha)
    (beta : Ω) (c : G) (hc : c ∈ Subgroup.centralizer ({z} : Set G)) :
    rightConjugate (tripleStabilizer z alpha beta) c =
      tripleStabilizer z alpha (rightAct beta c) := by
  have hcomm : z * c = c * z := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  change ((rightStabilizer alpha ⊓ rightStabilizer beta) ⊓
      rightStabilizer (rightAct beta z)).map (MulAut.conj c⁻¹).toMonoidHom = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj c⁻¹).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj c⁻¹).injective]
  change (rightConjugate (rightStabilizer alpha) c ⊓
    rightConjugate (rightStabilizer beta) c) ⊓
    rightConjugate (rightStabilizer (rightAct beta z)) c = _
  rw [rightStabilizer_rightConjugate, rightStabilizer_rightConjugate,
    rightStabilizer_rightConjugate, centralizer_fixes_unique_point hunique c hc,
    rightAct_commute beta hcomm]

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
