module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFam
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
  (blueprintLieModel_cat_E6 blueprintLieModel_cat_E7 blueprintLieModel_cat_E8
    blueprintLieModel_cat_F4 blueprintLieModel_cat_twistedE6)
open CFSG.LieType.SeitzGeneration (Cat chevalleyModel_cat_trialityD4)

theorem t263SelWP_of_gf2 {Q : ℕ → TauCeti.CFSGIndex → Prop}
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X],
      CFSG.Open.IsQuasisimple X → catalogIs (X ⧸ Subgroup.center X) (Q p) →
        p = 3 ∧ GLAMarking X (fun lab _ _ _ _ _ => lab.n = 1)) :
    T263SelWP Q := by
  intro p hp hp2 Ω _ _ _ S B _ hSq _ _ hcat
  intros
  exact Or.inl (Or.inr (h p hp hp2 ↥S hSq hcat))


private theorem gf2Marking_of_catModel {p : ℕ} (hp : p.Prime) {X : Type} [Group X]
    (hX : CFSG.Open.IsQuasisimple X) {t : StatedLieTag}
    (ht : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .F4 ∨ t = .twistedE6 ∨ t = .trialityD4)
    {q : TauCeti.PrimePower} (hq : q.card = 2) (hd : p ∣ q.card ^ 2 - 1)
    {d : TauCeti.ValidLieTypeIndex} (e : X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hM : CFSG.Blueprint.LieModel (Cat d) t 0 q.p q.exponent) :
    p = 3 ∧ GLAMarking X (fun lab _ _ _ _ _ => lab.n = 1) := by
  obtain ⟨hq2, hq1⟩ : q.p = 2 ∧ q.exponent = 1 :=
    Nat.prime_two.pow_eq_iff.1 (by rw [← TauCeti.PrimePower.card_def]; exact hq)
  rw [hq2, hq1] at hM
  rw [hq] at hd
  refine ⟨(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (by simpa using hd), ?_⟩
  refine CFSG.StandardType.largeEvenMarking_mono ?_
    (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hX.1
      (hM.of_mulEquiv e.symm))
  rintro lab _ _ _ _ _ ⟨htag, -, -, hdeg⟩
  obtain ⟨tag, rank, n⟩ := lab
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> cases tag <;>
    simp_all [CFSG.StandardType.markTag, CFSG.StandardType.markDeg] <;>
    split_ifs at htag <;> simp_all

theorem gf2Marking_exc {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsQuasisimple X) (h : catalogIs (X ⧸ Subgroup.center X) (t263GExcGF2 p)) :
    p = 3 ∧ GLAMarking X (fun lab _ _ _ _ _ => lab.n = 1) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d
    case E7 q =>
      exact gf2Marking_of_catModel hp hX (by decide) hi.1 hi.2 e (blueprintLieModel_cat_E7 hv)
    case E8 q =>
      exact gf2Marking_of_catModel hp hX (by decide) hi.1 hi.2 e (blueprintLieModel_cat_E8 hv)
    case F4 q =>
      exact gf2Marking_of_catModel hp hX (by decide) hi.1 hi.2 e (blueprintLieModel_cat_F4 hv)
    case G2 q =>
      have h3 : 3 ≤ q.card :=
        (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      exact absurd hi.1 (by omega)
    all_goals exact False.elim hi
  | cyclic r hr => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi

theorem gf2Marking_e6 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsQuasisimple X) (h : catalogIs (X ⧸ Subgroup.center X) (t263GE6GF2 p)) :
    p = 3 ∧ GLAMarking X (fun lab _ _ _ _ _ => lab.n = 1) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d
    case E6 q =>
      exact gf2Marking_of_catModel hp hX (by decide) hi.1 hi.2 e (blueprintLieModel_cat_E6 hv)
    case twistedE6 q =>
      exact gf2Marking_of_catModel hp hX (by decide) hi.1 hi.2 e
        (blueprintLieModel_cat_twistedE6 hv)
    all_goals exact False.elim hi
  | cyclic r hr => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi

theorem gf2Marking_td4 {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsQuasisimple X) (h : catalogIs (X ⧸ Subgroup.center X) (t263GTD4GF2 p)) :
    p = 3 ∧ GLAMarking X (fun lab _ _ _ _ _ => lab.n = 1) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d
    case trialityD4 q =>
      exact gf2Marking_of_catModel hp hX (by decide) hi.1 hi.2 e
        (Or.inr (Or.inl ⟨rfl, by decide, chevalleyModel_cat_trialityD4 hv⟩))
    all_goals exact False.elim hi
  | cyclic r hr => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi

theorem t263SelWP_excGF2 : T263SelWP t263GExcGF2 :=
  t263SelWP_of_gf2 fun _ hp _ _ _ _ hX h => gf2Marking_exc hp hX h

theorem t263SelWP_e6GF2 : T263SelWP t263GE6GF2 :=
  t263SelWP_of_gf2 fun _ hp _ _ _ _ hX h => gf2Marking_e6 hp hX h

theorem t263SelWP_td4GF2 : T263SelWP t263GTD4GF2 :=
  t263SelWP_of_gf2 fun _ hp _ _ _ _ hX h => gf2Marking_td4 hp hX h

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
