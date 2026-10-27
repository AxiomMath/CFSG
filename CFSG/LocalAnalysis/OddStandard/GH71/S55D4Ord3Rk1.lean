module

public import CFSG.RankThree.PartOne.KGD.D4Twist
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame

public noncomputable section

namespace CFSG.OddStandard.GH71.S55

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section SL2

variable {L : Type} [Field L]

theorem sl2Upper_one_pow (n : ℕ) : sl2Upper L 1 ^ n = sl2Upper L n := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, sl2Upper_zero]
  | succ n ih => rw [pow_succ, ih, ← sl2Upper_add, Nat.cast_succ]

theorem map_sl2Upper_one {k : Type} [Field k] [Algebra k L] :
    SpecialLinearGroup.map (algebraMap k L) (sl2Upper k 1) = sl2Upper L 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem conj_sl2Upper_data {p : ℕ} [CharP L p] {k : Type} [Field k] [Algebra k L]
    (Pm : GL (Fin 2) L) :
    conjSL Pm (sl2Upper L 1) ∈ (SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL Pm) ∧
      conjSL Pm (sl2Upper L 1) ∉ Subgroup.center (SL2 L) ∧ conjSL Pm (sl2Upper L 1) ^ p = 1 := by
  refine ⟨⟨sl2Upper L 1, ⟨sl2Upper k 1, map_sl2Upper_one⟩, rfl⟩, fun h => ?_, ?_⟩
  · have h1 := Subgroup.mem_center_iff.1 h (conjSL Pm (sl2Lower L 1))
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg (conjSL Pm⁻¹) h1
    rw [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h2
    have h3 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 0) h2
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h3
  · rw [← map_pow, sl2Upper_one_pow, CharP.cast_eq_zero, sl2Upper_zero, map_one]

end SL2


variable {p f : ℕ} [Fact p.Prime] {L : Type} [Field L] [CharP L p] [IsAlgClosed L]

theorem d4_rk1_pElt (hf : 1 ≤ f) {θ : Fin TwistTag.D4.tag.rank → ℤ}
    (hθ : IsRoot TwistTag.D4.tag θ) (hρθ : permLattice TwistTag.D4.perm θ = θ) :
    ∃ u : ModGL TwistTag.D4.tag L, u ∈ adjointGroup TwistTag.D4.tag L ∧ u ≠ 1 ∧ u ^ p = 1 ∧
      trialityOpposition L * twistHom TwistTag.D4 L (iterateFrobenius L p f) u *
        (trialityOpposition L)⁻¹ = u ∧
      ∀ a : Fin TwistTag.D4.tag.rank → Lˣ, rootChar a θ = 1 →
        rootDiagUnit TwistTag.D4.tag a * u = u * rootDiagUnit TwistTag.D4.tag a := by
  classical
  obtain ⟨k, _, _, _, hk⟩ := exists_finite_field_into p f hf L
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card k := fun c => by
    rw [hk]
    exact iterateFrobenius_def p f c
  have hzM := trialityOpposition_mem_monomialSubgroup (K := L)
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq_twist hzM hθ
  have hγ : weylQuotientHom TwistTag.D4.tag L ⟨_, hzM⟩ • permLattice TwistTag.D4.perm θ = -θ := by
    rw [hρθ, weylQuotientHom_trialityOpposition_smul]
  rw [hγ] at hs
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) hθ
  have hMdef : swapGL * diagUnitOne a * diagUnitOne s =
      (swapGL * diagUnitOne (a * s) : GL (Fin 2) L) := by
    rw [mul_assoc, diagUnitOne_mul]
  obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k) Fr hFr 1 (a * s)
    (swapGL * diagUnitOne a * diagUnitOne s) (by
      rw [hMdef, coe_swapGL_mul_diagUnitOne]
      simp)
  have hiff : ∀ B : SL2 L, trialityOpposition L * twistHom TwistTag.D4 L Fr
      (rootSL2 TwistTag.D4.tag L θ B) * (trialityOpposition L)⁻¹ =
        rootSL2 TwistTag.D4.tag L θ B ↔
      B ∈ (SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL Pm) := by
    refine a1_hS1_of_action Fr hFr Pm (fun B' => ?_)
    rw [hPm]
    change trialityOpposition L * (diagramMap TwistTag.D4 L * Units.map (entrywiseHom Fr)
      (rootSL2 TwistTag.D4.tag L θ B') * (diagramMap TwistTag.D4 L)⁻¹) *
        (trialityOpposition L)⁻¹ = _
    rw [entrywise_rootSL2_of_field Fr θ B']
    calc trialityOpposition L * (diagramMap TwistTag.D4 L * rootSL2 TwistTag.D4.tag L θ
          (SpecialLinearGroup.map Fr B') * (diagramMap TwistTag.D4 L)⁻¹) *
          (trialityOpposition L)⁻¹
        = trialityOpposition L * diagramMap TwistTag.D4 L * rootSL2 TwistTag.D4.tag L θ
            (SpecialLinearGroup.map Fr B') *
            (trialityOpposition L * diagramMap TwistTag.D4 L)⁻¹ := by group
      _ = _ := by rw [hs, ha, ← conjSL_mul]
  obtain ⟨hXmem, hXc, hXp⟩ := conj_sl2Upper_data (p := p) (k := k) Pm
  have hinj := rootSL2_injective_of_field (τ := TwistTag.D4.tag) (K := L) θ
  refine ⟨rootSL2 TwistTag.D4.tag L θ (conjSL Pm (sl2Upper L 1)),
    (exceptional_Lang_root_rank_one_data TwistTag.D4.tag L θ).2.2.2.2.1 _, fun h => ?_, ?_,
    (hiff _).2 hXmem, fun b hb => ?_⟩
  · apply hXc
    rw [hinj (h.trans (map_one _).symm)]
    exact one_mem _
  · rw [← map_pow, hXp, map_one]
  · have hc := (rootDiagUnit_mem_centralizer_iff hθ b).2 hb
    exact (Subgroup.mem_centralizer_iff.1 hc _ ⟨_, rfl⟩).symm

end CFSG.OddStandard.GH71.S55
