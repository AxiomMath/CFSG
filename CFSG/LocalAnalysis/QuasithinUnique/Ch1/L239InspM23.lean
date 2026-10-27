module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open scoped Pointwise
open MulAction CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.QuasithinUnique.Setup.X1

namespace M23Insp

theorem hgens : Subgroup.closure {g | g ∈ data.gens} = ⊤ := by
  have h := closure_pair_eq_top m23_eq_closure m23GenA.2 m23GenB.2
  have hg : data.gens = [m23GenA, m23GenB] := rfl
  have : {g | g ∈ data.gens} = ({m23GenA, m23GenB} : Set ↥NativeSporadic.M23) := by
    rw [hg]
    ext g
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  rw [this]
  exact h

theorem hcard
    : Nat.card ↥NativeSporadic.M23 = data.H.length * (16 * data.T.length) := by
  rw [m23_card, chk_H_len, chk_T_len']

theorem hAut
    : ∀ α : MulAut ↥NativeSporadic.M23, ∃ B' ∈ data.H,
    (stabilizer ↥NativeSporadic.M23 data.B₀).map α.toMonoidHom =
      stabilizer ↥NativeSporadic.M23 B' := by
  intro α
  obtain ⟨s, hs⟩ := m23_autInner α
  have horb := orbit_eq_of_reach_closed hgens chk_H_reach chk_H_closed
  have hmem : (s : Equiv.Perm (Fin 23)) • data.B₀ ∈ data.H := (horb _).1 ⟨s, rfl⟩
  refine ⟨_, hmem, map_stab_of_conj α (s : Equiv.Perm (Fin 23)) ?_⟩
  intro x
  have := congrArg Subtype.val (hs x)
  simpa using this

theorem alt7_not_pgroup : ¬ IsPGroup 2 (alternatingGroup (Fin 7)) := by
  intro h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h
  rw [card_alt_seven] at hk
  have hk12 : k < 12 := by
    by_contra hcon
    have : 2 ^ 12 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hcon)
    omega
  interval_cases k <;> omega

end M23Insp

theorem l239M23Parabolic
    : L239M23Parabolic := by
  intro G _ _ L R hL _ hRN hS
  obtain ⟨φ⟩ := hL
  let e : ↥L ≃* ↥NativeSporadic.M23 := φ
  exact M23Insp.data.parabolic M23Insp.valid M23Insp.hgens M23Insp.hcard M23Insp.hAut
    (alternatingGroup.isSimpleGroup (by simp)) M23Insp.alt7_not_pgroup (Or.inr card_alt_seven) e hRN
    hS

end CFSG.QuasithinUnique.Vol2Native.L239
