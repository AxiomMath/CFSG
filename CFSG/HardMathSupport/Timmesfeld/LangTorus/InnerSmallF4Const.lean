module

public import CFSG.LieType.Chevalley.RootCommutator

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false

section Transport

variable {τ : Tag}

open _root_.Classical in
@[expose] def ExactCommConst (τ : Tag) (α β : Fin τ.rank → ℤ) (C : ℕ × ℕ → ℤ) : Prop :=
  ∀ p ∈ commPairs τ α β, |C p| = if p = (1, 1) ∧ IsRoot τ (β - α) then 2 else 1

namespace RootOperatorFamily

@[expose] def HasExactCommFormula (F : RootOperatorFamily τ) (α β : Fin τ.rank → ℤ) : Prop :=
  ∃ C : ℕ × ℕ → ℤ, ExactCommConst τ α β C ∧ F.CommFormula α β C

variable {F : RootOperatorFamily τ}

theorem HasExactCommFormula.simple_smul {α β : Fin τ.rank → ℤ}
    (h : F.HasExactCommFormula α β) (i : Fin τ.rank) :
    F.HasExactCommFormula (simple τ i • α) (simple τ i • β) := by
  classical
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨_, fun p hp => ?_, hF.simple_smul i⟩
  rw [commPairs_smul] at hp
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, F.abs_signVec, F.abs_signVec, F.abs_signVec,
    one_pow, one_pow, one_mul, one_mul, one_mul, hC p hp]
  have hiff : IsRoot τ (simple τ i • β - simple τ i • α) ↔ IsRoot τ (β - α) := by
    rw [← smul_sub, isRoot_smul_iff]
  simp only [hiff]

theorem HasExactCommFormula.smul {α β : Fin τ.rank → ℤ}
    (h : F.HasExactCommFormula α β) (w : WeylGroup τ) :
    F.HasExactCommFormula (w • α) (w • β) := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => simpa using h
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul]
    exact ih.simple_smul i

end RootOperatorFamily

end Transport


namespace RootOps

@[expose] def exactRowCheck (r : ℕ × ℕ × List Factor) : Bool :=
  r.2.2.all fun f => f.2.2.2.natAbs ==
    if f.1 == 1 && f.2.1 == 1 &&
        isRootB .F4 ((Tag.rootCertificate .F4).root r.2.1 - (Tag.rootCertificate .F4).root r.1)
      then 2 else 1

theorem exactRowCheck_F4 : (repsOf .F4).all exactRowCheck = true := by
  decide +kernel

open _root_.Classical in
theorem abs_factor_F4_exact {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf .F4) :
    ∀ f ∈ r.2.2, |f.2.2.2| =
      if (f.1, f.2.1) = (1, 1) ∧
          IsRoot .F4 ((Tag.rootCertificate .F4).root r.2.1 - (Tag.rootCertificate .F4).root r.1)
        then 2 else 1 := by
  classical
  have h := exactRowCheck_F4
  rw [List.all_eq_true] at h
  have h' := h r hr
  simp only [exactRowCheck, List.all_eq_true, beq_iff_eq] at h'
  intro f hf
  have hf' := h' f hf
  rw [Int.abs_eq_natAbs, hf']
  by_cases hc : (f.1, f.2.1) = (1, 1) ∧
      IsRoot .F4 ((Tag.rootCertificate .F4).root r.2.1 - (Tag.rootCertificate .F4).root r.1)
  · have hb : (f.1 == 1 && f.2.1 == 1 &&
        isRootB .F4 ((Tag.rootCertificate .F4).root r.2.1 -
          (Tag.rootCertificate .F4).root r.1)) = true := by
      obtain ⟨hp, hR⟩ := hc
      simp only [Prod.mk.injEq] at hp
      simp [hp.1, hp.2, isRootB_iff.2 hR]
    simp [hb, hc]
  · have hb : ¬ (f.1 == 1 && f.2.1 == 1 &&
        isRootB .F4 ((Tag.rootCertificate .F4).root r.2.1 -
          (Tag.rootCertificate .F4).root r.1)) = true := by
      intro hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact hc ⟨by rw [hb.1.1, hb.1.2], isRootB_iff.1 hb.2⟩
    rw [ite_eq_right_of_eq_false _ _ (eq_false hb), ite_eq_right_of_eq_false _ _ (eq_false hc)]
    rfl

theorem hasExactCommFormula_rep_F4 {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf .F4) :
    (rootOperatorFamily .F4).HasExactCommFormula ((Tag.rootCertificate .F4).root r.1)
      ((Tag.rootCertificate .F4).root r.2.1) := by
  obtain ⟨-, -, hkeys, -, -⟩ := repShape_spec hr
  have hnd := keys_nodup_of_mem_repsOf hr
  refine ⟨factorConst r.2.2, fun p hp => ?_, commFormula_rep hr⟩
  rw [← hkeys, List.mem_map] at hp
  obtain ⟨f, hf, rfl⟩ := hp
  rw [factorConst_of_mem hnd hf]
  exact abs_factor_F4_exact hr f hf

end RootOps

open RootOps

open _root_.Classical in
theorem exists_pinnedX_commFormula_F4_exact {α β : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot .F4 α) (hβ : IsRoot .F4 β) (hne : α ≠ β) (hne' : α ≠ -β) :
    ∃ C : ℕ × ℕ → ℤ,
      (∀ p ∈ commPairs .F4 α β, |C p| = if p = (1, 1) ∧ IsRoot .F4 (β - α) then 2 else 1) ∧
      ∀ (R : Type) [CommRing R] (c d : R),
        pinnedX .F4 R α c * pinnedX .F4 R β d * pinnedX .F4 R α (-c) * pinnedX .F4 R β (-d) =
          ((commPairs .F4 α β).map fun p =>
            pinnedX .F4 R (p.1 • α + p.2 • β) ((C p : R) * c ^ p.1 * d ^ p.2)).prod := by
  obtain ⟨r, hr, w, h1, h2⟩ := exists_smul_rep hα hβ hne hne'
  obtain ⟨C, hC, hF⟩ := (hasExactCommFormula_rep_F4 hr).smul w
  rw [h1, h2] at hC hF
  refine ⟨fun p => (rootOperatorFamily .F4).pinnedFamilySign (p.1 • α + p.2 • β) *
      (rootOperatorFamily .F4).pinnedFamilySign α ^ p.1 *
      (rootOperatorFamily .F4).pinnedFamilySign β ^ p.2 * C p, fun p hp => ?_,
    pinnedX_commFormula_of_commFormula hα hβ hF⟩
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pinnedFamilySign, abs_pinnedFamilySign,
    abs_pinnedFamilySign, one_pow, one_pow, one_mul, one_mul, one_mul]
  exact hC p hp

end CFSG.LieType.Chevalley
