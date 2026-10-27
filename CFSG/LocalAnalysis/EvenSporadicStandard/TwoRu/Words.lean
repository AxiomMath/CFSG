module

public import CFSG.Sporadic.Recognition.RuMultiplier
public import CFSG.Sporadic.Schreier.RuCentralizer
public import CFSG.Sporadic.Schreier.RuConj
public import Certificates.Certificate15025
public import Certificates.Certificate24361

public section

namespace CFSG.EvenSporadicStandard.TwoRu

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Recognition.RuMultiplier
  CFSG.LieType.Multipliers.Tits CFSG.Sporadic.RuSchreier
  CFSG.Sporadic.Recognition.CoverTransfer

@[expose] noncomputable def ruWE (w : List (Fin gc × Bool)) : RuCover :=
  PresentedGroup.mk _ (FreeGroup.mk w)

theorem ruWE_append (w v : List (Fin gc × Bool)) : ruWE (w ++ v) = ruWE w * ruWE v := by
  rw [ruWE, ruWE, ruWE, ← map_mul, FreeGroup.mul_mk]

theorem ruWE_wordPow (k : ℕ) (w : List (Fin gc × Bool)) : ruWE (wordPow k w) = ruWE w ^ k := by
  induction k with
  | zero =>
    simp only [wordPow, List.replicate_zero, List.flatten_nil, pow_zero, ruWE]
    rw [← FreeGroup.one_eq_mk, map_one]
  | succ k ih =>
    have : wordPow (k + 1) w = w ++ wordPow k w := by simp [wordPow, List.replicate_succ]
    rw [this, ruWE_append, ih, pow_succ']

noncomputable def ruRho' (h : ruRhoCheck = true) : RuCover →* Equiv.Perm (Fin 16240) :=
  PresentedGroup.toGroup (ruRho_rels h)

theorem ruRho'_ruWE (h : ruRhoCheck = true) (w : List (Fin gc × Bool)) :
    ruRho' h (ruWE w) = wordIn gc ruRhoGen (zword w) := by
  rw [ruWE, ruRho', mk_eq_lift_of, ← MonoidHom.comp_apply,
    show (PresentedGroup.toGroup (ruRho_rels h)).comp (FreeGroup.lift PresentedGroup.of) =
      FreeGroup.lift (fun i : Fin gc => ruRhoGen i) from
      FreeGroup.ext_hom _ _ fun j => by
        rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
        exact PresentedGroup.toGroup.of _,
    lift_mk_eq_wordIn]

theorem rep_ruRho_ruWE (h : ruRhoCheck = true) {w : List (Fin gc × Bool)}
    (hw : lettersOK gc (zword w) = true) : Rep 16240 (ruWordArr w) (ruRho' h (ruWE w)) := by
  rw [ruRho'_ruWE]
  exact rep_ruRho h hw

theorem ruFix16240_eq {t : Array ℕ} {g : Equiv.Perm (Fin 16240)} (ht : Rep 16240 t g) :
    ruFix16240 t = (fixSet g).ncard := by
  rw [ruFix16240, ← Sporadic.RuSchreier.ncard_finSet (pointList_fixedList t),
    finSet_fixedList ht]

theorem ruFourthOne_spec (h : ruRhoCheck = true) {w : List (Fin gc × Bool)} {n : ℕ}
    (hz : lettersOK gc (zword ruZWord) = true) (hc : ruFourthOne w n = true) :
    ruRho' h (ruWE w) ^ 8 = 1 ∧ ruRho' h (ruWE w) ^ 4 ≠ 1 ∧
      ruRho' h (ruWE w) ^ 4 ≠ ruRho' h (ruWE ruZWord) ∧
      (fixSet (ruRho' h (ruWE w) ^ 4)).ncard = n := by
  simp only [ruFourthOne, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h8, h4⟩, e8⟩, n1⟩, nz⟩, fx⟩ := hc
  have r8 : Rep 16240 (ruWordArr (wordPow 8 w)) (ruRho' h (ruWE w) ^ 8) := by
    have := rep_ruRho_ruWE h h8
    rwa [ruWE_wordPow, map_pow] at this
  have r4 : Rep 16240 (ruWordArr (wordPow 4 w)) (ruRho' h (ruWE w) ^ 4) := by
    have := rep_ruRho_ruWE h h4
    rwa [ruWE_wordPow, map_pow] at this
  have rz : Rep 16240 (ruWordArr ruZWord) (ruRho' h (ruWE ruZWord)) := rep_ruRho_ruWE h hz
  refine ⟨(eqA_iff r8 rep_idA).1 e8, ?_, ?_, ?_⟩
  · intro h1
    rw [← eqA_iff r4 rep_idA] at h1
    simp [h1] at n1
  · intro h1
    rw [← eqA_iff r4 rz] at h1
    simp [h1] at nz
  · rw [← ruFix16240_eq r4]
    exact fx

theorem ruFourth_facts :
    let ρ := ruRho' Certificates.certificate15025
    ρ (ruWE ruZWord) ≠ 1 ∧
    (ρ (ruWE ruFourthW1) ^ 8 = 1 ∧ ρ (ruWE ruFourthW1) ^ 4 ≠ 1 ∧
      ρ (ruWE ruFourthW1) ^ 4 ≠ ρ (ruWE ruZWord) ∧
      (fixSet (ρ (ruWE ruFourthW1) ^ 4)).ncard = 320) ∧
    (ρ (ruWE ruFourthW2) ^ 8 = 1 ∧ ρ (ruWE ruFourthW2) ^ 4 ≠ 1 ∧
      ρ (ruWE ruFourthW2) ^ 4 ≠ ρ (ruWE ruZWord) ∧
      (fixSet (ρ (ruWE ruFourthW2) ^ 4)).ncard = 48) := by
  have hc := Certificates.certificate24361
  simp only [ruFourthCheck, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨hz, hn⟩, h1⟩, h2⟩ := hc
  refine ⟨?_, ruFourthOne_spec _ hz h1, ruFourthOne_spec _ hz h2⟩
  intro h
  have rz := rep_ruRho_ruWE Certificates.certificate15025 hz
  rw [← eqA_iff rz rep_idA] at h
  simp [h] at hn

end CFSG.EvenSporadicStandard.TwoRu
