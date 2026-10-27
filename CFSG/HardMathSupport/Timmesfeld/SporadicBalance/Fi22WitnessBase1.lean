
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase

public import CFSG.HardMathSupport.Foote.E27.SporFi22

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Foote.E27.Fi22S0 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native
  CFSG.F3.Native
open scoped Pointwise

theorem rep_regT_of (O : COrbit) (ha : Rep 3510 O.alpha a)
    (hb : Rep 3510 O.beta b) (hbi : Rep 3510 (invT 3510 O.beta) b⁻¹) :
    ∀ k < 3 + ops.size, Rep 3510 (regT O)[k]! (regJ k) := by
  obtain ⟨hops, -, -, -, -, -⟩ := shape_parts
  rw [regT_eq]
  have h := buildN_inv (#[O.alpha, O.beta, invT 3510 O.beta] : Array Table)
    (fun acc k => compT 3510 (acc[(ops[k - 3]!).1]!) (acc[(ops[k - 3]!).2]!))
    (fun k x => Rep 3510 x (regJ k)) ops.size ?_ ?_
  · exact h.2
  · intro k hk
    have hk3 : k < 3 := hk
    interval_cases k
    · rw [regJ_zero]; exact ha
    · rw [regJ_one]; exact hb
    · rw [regJ_two]; exact hbi
  · intro m hm r hr hP
    have hrs : r.size = 3 + m := hr
    obtain ⟨hp1, hp2⟩ := hops m hm
    have e : r.size - 3 = m := by omega
    have hk : 3 ≤ r.size ∧ (ops[r.size - 3]!).1 < r.size ∧ (ops[r.size - 3]!).2 < r.size := by
      rw [e]; omega
    have h1 := hP _ hk.2.1
    have h2 := hP _ hk.2.2
    have h3 := h1.compT h2
    rw [← regJ_succ hk] at h3
    exact h3

theorem rep_genT_of (O : COrbit) (ha : Rep 3510 O.alpha a)
    (hb : Rep 3510 O.beta b) (hbi : Rep 3510 (invT 3510 O.beta) b⁻¹) {j : ℕ} (hj : j < 3) :
    Rep 3510 (genT O)[j]! (gJ j) := by
  obtain ⟨-, hg, -, hgs, -, -⟩ := shape_parts
  have hj' : j < gens.size := by omega
  have hlt : gens[j]! < 3 + ops.size := by have := hg j hj'; omega
  have e1 : genT O = genOf (regT O) := rfl
  have e2 : gJ j = regJ (gens[j]!) := by
    apply matJ_injective
    rw [← (genM_spec hj).2.2, ← (regs_spec.2 _ hlt).2.2]
    rfl
  rw [e1, genOf_get _ hj, e2]
  exact rep_regT_of O ha hb hbi (gens[j]!) hlt

theorem rep_genT {j : ℕ} (hj : j < 3) :
    Rep 3510 (genT orb)[j]! (gJ j) :=
  rep_genT_of orb rep_alpha rep_beta rep_binv hj

theorem rep_eltT_of {G : Array Table}
    (hG : ∀ j < 3, Rep 3510 G[j]! (gJ j)) :
    ∀ i < nS, Rep 3510 (eltT par G i) (tabElt gJ par i) := by
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [eltT_eq]
    rcases hpar i hi with rfl | ⟨hp, hj⟩
    · rw [ite_eq_right (by simp), tabElt_zero]
      exact Rep.idT (by norm_num)
    · have hpos : 0 < i := by omega
      rw [ite_eq_left ⟨hpos, hp⟩, tabElt_succ gJ par hp]
      exact (hG _ hj).compT (ih _ hp (by omega))

theorem rep_eltT :
    ∀ i < nS, Rep 3510 (eltT par (genT orb) i) (tabElt gJ par i) :=
  rep_eltT_of fun _ hj => rep_genT hj

theorem exists_sylow_table :
    ∃ T : Sylow 3 J, ∀ x, x ∈ (T : Subgroup J) ↔ ∃ i < nS, tabElt gJ par i = x := by
  have := finite_J
  obtain ⟨T, hT, -⟩ := tabData.exists_subgroup (by unfold nS; norm_num : 0 < nS)
  have hcard : Nat.card T = 3 ^ (Nat.card J).factorization 3 := by
    rw [tabData.card_subgroup hT, factorization_J]
    rfl
  exact ⟨Sylow.ofCard T hcard, fun x => by rw [Sylow.coe_ofCard]; exact hT x⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
