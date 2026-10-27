module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBLongCent
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBSolvable
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4LongGen

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped MatrixGroups commutatorElement

section UBCentralizerL


variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem centralizer_le_longSub_sup_N
    (hcen : Subgroup.center (twistedGroup σ) = ⊥) (t : Kˣ)
    (ht : (t : K) * σ t * σ (σ t) = 1) (ht2 : (t : K) ^ 2 ≠ 1) :
    Subgroup.centralizer {slShort σ hσ (HSL t)} ≤
      longSub 6 (hexGroup (twistedX σ)) ⊔ (d4RGD2 σ hσ).N := by
  have R := d4RGD2 σ hσ
  have hz := longCent_slShort_HSL hσ t ht ht2
  have hgen := d4RGD2_gen hσ
  have hZ := RGD2.hZ_of_center_bot R hgen hcen
  intro c hc
  have hc' : (MulAut.conj (slShort σ hσ (HSL t))) c = c := by
    rw [MulAut.conj_apply]
    have := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [← this]
    group
  obtain ⟨v, hv, n, hn, u, hu, rfl⟩ :=
    (FoldStab.conj_of_mem_H (R := R) hz.mem_H).cell hgen hZ hc'
  have hvL : v ∈ longSub 6 (hexGroup (twistedX σ)) :=
    hz.fixed_U_mem_longSub hv.1 (mem_foldFix_conj_iff.1 hv.2)
  have huL : u ∈ longSub 6 (hexGroup (twistedX σ)) :=
    hz.fixed_U_mem_longSub hu.1 (mem_foldFix_conj_iff.1 hu.2)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hvL)
    (Subgroup.mem_sup_right hn.1)) (Subgroup.mem_sup_left huL)

include hσ in
theorem perfect_le_longSub_of_le_centralizer
    (hcen : Subgroup.center (twistedGroup σ) = ⊥) (t : Kˣ) (ht : (t : K) * σ t * σ (σ t) = 1)
    (ht2 : (t : K) ^ 2 ≠ 1) {P : Subgroup (twistedGroup σ)} (hP : ⁅P, P⁆ = P)
    (hPz : P ≤ Subgroup.centralizer {slShort σ hσ (HSL t)}) :
    P ≤ longSub 6 (hexGroup (twistedX σ)) := by
  have R := d4RGD2 σ hσ
  have : Group.IsSolvable ↥(d4RGD2 σ hσ).N := RGD2.isSolvable_N R
  refine le_of_perfect_of_le_sup_normalizing _ (d4RGD2 σ hσ).N P ?_ hP
    (hPz.trans (centralizer_le_longSub_sup_N hσ hcen t ht ht2))
  intro n hn l hl
  exact conj_mem_longSub (by norm_num) (by norm_num) (R.goodActEven_of_mem_N (by norm_num) hn) hl

end UBCentralizerL

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
