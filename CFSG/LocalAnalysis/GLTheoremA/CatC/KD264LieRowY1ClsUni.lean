module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.ComponentInitial.ConjClassSimplicity
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial LinearFlag
  Matrix

variable {K : Type} [Field K]

theorem statedSU_det_eq_one {m q : ℕ} {K : Type} [Field K] (g : GL (Fin m) K)
    (hg : g ∈ StatedSU m q K) : (g : Matrix (Fin m) (Fin m) K).det = 1 := by
  unfold StatedSU at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Matrix.det_mul, hx, hy, one_mul]
  | inv x _ hx =>
    have h := congrArg Matrix.det (Units.inv_mul x)
    rw [Matrix.det_mul, hx, mul_one, Matrix.det_one] at h
    exact h

theorem not_dvd_card_statedScalars_five {p f : ℕ} [Finite K] [CharP K p] [Fact p.Prime] :
    ¬ 3 ∣ Nat.card ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (p ^ f) K)) := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (p ^ f) K)) :=
    Fintype.ofFinite _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 3 (by rwa [Nat.card_eq_fintype_card] at h)
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    norm_num at hz
  have hzS : ((z : StatedSU 5 (p ^ f) K) : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K :=
    (Subgroup.mem_subgroupOf).mp z.2
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hzS
  have h3GL : ((z : StatedSU 5 (p ^ f) K) : GL (Fin 5) K) ^ 3 = 1 := by
    have h' := congrArg (fun g : (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (p ^ f) K) =>
      ((g : StatedSU 5 (p ^ f) K) : GL (Fin 5) K)) hz3
    simpa using h'
  have hc3' : Matrix.GeneralLinearGroup.scalar (Fin 5) (c ^ 3) = 1 := by
    rw [map_pow, hc, h3GL]
  have hc3 : c ^ 3 = 1 := by
    have h' := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) ⟨0, by norm_num⟩
      ⟨0, by norm_num⟩) hc3'
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h'
    apply Units.ext
    simpa using h'
  have hdet := statedSU_det_eq_one (m := 5) (q := p ^ f) _ (z : StatedSU 5 (p ^ f) K).2
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc5 : c ^ 5 = 1 := by
    apply Units.ext
    simpa using hdet
  have h2 : c ^ 2 = 1 := by
    calc c ^ 2 = c ^ 5 * (c ^ 3)⁻¹ := by group
      _ = 1 := by rw [hc5, hc3, inv_one, mul_one]
  have hcu : c = 1 := by
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, h2, inv_one, mul_one]
  apply hz1
  apply Subtype.ext
  apply Subtype.ext
  rw [← hc, hcu]
  simp

theorem statedProj_pRank_ge_four_of_five (ℓ f : ℕ) [hℓ : Fact ℓ.Prime] (hdvd : 3 ∣ ℓ ^ f + 1) :
    4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedSU 5 (ℓ ^ f) (GaloisField ℓ (2 * f))))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      norm_num at hdvd
    · exact h0
  haveI : Finite (GaloisField ℓ (2 * f)) := inferInstance
  haveI : CharP (GaloisField ℓ (2 * f)) ℓ := inferInstance
  have hK : Nat.card (GaloisField ℓ (2 * f)) = (ℓ ^ f) ^ 2 := by
    rw [GaloisField.card ℓ (2 * f) (by omega), pow_mul]
    ring
  rw [CFSG.SectionRank.pRank_quotient_eq
    ((StatedScalars (Fin 5) (GaloisField ℓ (2 * f))).subgroupOf
      (StatedSU 5 (ℓ ^ f) (GaloisField ℓ (2 * f))))
    (not_dvd_card_statedScalars_five (p := ℓ) (f := f))]
  have hsu := RankThreeUC.S15.pRank_statedSU_ge (F := GaloisField ℓ (2 * f)) (q := ℓ ^ f)
    (r := 3) (m := 5) (by norm_num) hK hdvd
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  omega

theorem statedProj_pRank_ge_four_of_five' {m : ℕ} (hm : m = 5) (ℓ f : ℕ) [Fact ℓ.Prime]
    (hdvd : 3 ∣ ℓ ^ f + 1) :
    4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedSU m (ℓ ^ f) (GaloisField ℓ (2 * f))))) := by
  subst hm
  exact statedProj_pRank_ge_four_of_five ℓ f hdvd

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
