module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TMu

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise
open MulAction CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.X1

namespace M22Insp

theorem hgens : Subgroup.closure {g | g ∈ data.gens} = ⊤ := by
  have h := closure_pair_eq_top m22_eq m22a.2 m22b.2
  have hg : data.gens = [m22a, m22b] := rfl
  have : {g | g ∈ data.gens} = ({m22a, m22b} : Set ↥NativeSporadic.M22) := by
    rw [hg]
    ext g
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  rw [this]
  exact h

theorem hcard
    : Nat.card ↥NativeSporadic.M22 = data.H.length * (16 * data.T.length) := by
  rw [m22_card, chk_H_len, chk_T_len']

theorem delta_eq : (delta : Equiv.Perm (Fin 22)) = m22Delta := rfl

theorem hAut
    : ∀ α : MulAut ↥NativeSporadic.M22, ∃ B' ∈ data.H,
    (stabilizer ↥NativeSporadic.M22 data.B₀).map α.toMonoidHom =
      stabilizer ↥NativeSporadic.M22 B' := by
  intro α
  obtain ⟨a, rfl⟩ := muA_surjective α
  have horb := orbit_eq_of_reach_closed hgens chk_H_reach chk_H_closed
  have hHmem : ∀ x : ↥NativeSporadic.M22, x • data.B₀ ∈ data.H := fun x =>
    (horb _).1 ⟨x, rfl⟩
  have hmem : (a : Equiv.Perm (Fin 22)) • data.B₀ ∈ data.H := by
    rcases mem_m22A.1 a.2 with ha | ha
    · exact hHmem ⟨a, ha⟩
    · have : (a : Equiv.Perm (Fin 22)) = m22Delta * (m22Delta⁻¹ * a) := by group
      rw [this, mul_smul, ← delta_eq]
      exact chk_delta _ (hHmem ⟨m22Delta⁻¹ * a, ha⟩)
  exact ⟨_, hmem, map_stab_of_conj (muA a) (a : Equiv.Perm (Fin 22)) (muA_apply a)⟩

theorem alt6_not_pgroup : ¬ IsPGroup 2 (alternatingGroup (Fin 6)) := by
  intro h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h
  rw [card_alt_six] at hk
  have hk9 : k < 9 := by
    by_contra hcon
    have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
    omega
  interval_cases k <;> omega

end M22Insp

theorem l239M22Parabolic
    : L239M22Parabolic := by
  intro G _ _ L R hL _ hRN hS
  obtain ⟨φ⟩ := hL
  let e : ↥L ≃* ↥NativeSporadic.M22 := φ
  exact M22Insp.data.parabolic M22Insp.valid M22Insp.hgens M22Insp.hcard M22Insp.hAut
    (alternatingGroup.isSimpleGroup (by simp)) M22Insp.alt6_not_pgroup (Or.inl card_alt_six) e hRN
    hS

end CFSG.QuasithinUnique.Vol2Native.L239
