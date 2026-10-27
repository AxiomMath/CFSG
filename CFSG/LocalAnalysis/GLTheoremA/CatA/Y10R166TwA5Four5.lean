module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U5R
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open TwA5Four

namespace TwA5Four

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot CFSG.SeitzReduction.LinearPilot
open CFSG.LocalAnalysis.GLTheoremA
open Matrix

variable {K : Type} [Group K] [Finite K]

private theorem innerDiagMarking_of_pow_five_twA_four {B J : Subgroup K} {n : ℕ}
    (hn : 1 ≤ n) (hcop : Nat.Coprime 5 (2 * n))
    (hJ : HasLabel ↥J (fun l : GLALabel => l = ⟨.twA, 4, n⟩))
    (hBN : B ≤ Subgroup.normalizer (J : Set K))
    (hB5 : ∀ b ∈ B, b ^ 5 = 1) :
    InnerDiagMarking B J := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hJ
  obtain ⟨R0, hgR, I0, F0, hQ0⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  letI : Group R0 := hgR
  obtain ⟨-, -, -, hlab_eq⟩ := hQ0
  subst hlab_eq
  obtain ⟨F, hFf, hFfin, hFcard, hQ⟩ :=
    (CFSG.LocalAnalysis.GLTheoremA.rawDatum_twA_four_iff n _).1 hraw
  letI : Field F := hFf
  letI : Finite F := hFfin
  obtain ⟨hs, hna, θ, -⟩ := hQ
  refine ⟨hcomm, ⟨.twA, 4, n⟩, hlab, ?_⟩
  refine (CFSG.LocalAnalysis.GLTheoremA.rawDatum_twA_four_iff n _).2
    ⟨F, hFf, hFfin, hFcard, hs, hna, θ, hBN, ?_⟩
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (J : Set K) := hBN hb
  let γ : Subgroup.normalizer (J : Set K) := ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩
  let α : MulAut ↥J := J.normalizerMonoidHom γ
  have hcenter : (Subgroup.center ↥J).map (α : ↥J →* ↥J) = Subgroup.center ↥J := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact (Subgroup.centerCongr α ⟨y, hy⟩).2
    · intro x hx
      refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
      exact ((Subgroup.centerCongr α).symm ⟨x, hx⟩).2
  let αbar : MulAut (↥J ⧸ Subgroup.center ↥J) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥J) α hcenter
  let φ : MulAut (CFSG.Assembly.LargeEvenProj
      (CFSG.Assembly.LargeEvenSUGroup (Fin 5) F (2 ^ n))) := MulAut.congr θ αbar
  have hstep : ∀ x : ↥J, αbar (QuotientGroup.mk x) = QuotientGroup.mk (α x) := by
    intro x
    exact QuotientGroup.congr_mk _ _ _ _ x
  have hγ5 : γ ^ 5 = 1 := by
    apply Subtype.ext
    change (b⁻¹ : K) ^ 5 = 1
    rw [inv_pow, hB5 b hb, inv_one]
  have hα5 : α ^ 5 = 1 := by
    apply MulEquiv.ext
    intro l
    change (((J.normalizerMonoidHom γ) ^ 5) l) = l
    rw [← map_pow, hγ5, map_one]
    rfl
  have hpow : ∀ (m : ℕ) (l : ↥J),
      (αbar ^ m) (QuotientGroup.mk l) = QuotientGroup.mk ((α ^ m) l) := by
    intro m
    induction m with
    | zero => intro l; simp
    | succ m ih =>
        intro l
        rw [pow_succ]
        change (αbar ^ m) (αbar (QuotientGroup.mk l)) =
          QuotientGroup.mk ((α ^ (m + 1)) l)
        rw [hstep, ih (α l), pow_succ]
        rfl
  have hbar5 : αbar ^ 5 = 1 := by
    apply MulEquiv.ext
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) q
    change (αbar ^ 5) (QuotientGroup.mk l) = QuotientGroup.mk l
    rw [hpow 5 l, hα5]
    simp
  have hφ5 : φ ^ 5 = 1 := by
    change (MulAut.congr θ αbar) ^ 5 = 1
    rw [← map_pow, hbar5, map_one]
  refine ⟨φ, CFSG.LocalAnalysis.GLTheoremA.mem_conjImage_of_pow_five F hn hFcard hcop φ hφ5, ?_⟩
  intro l l' hl
  have hcongr : ∀ x : ↥J ⧸ Subgroup.center ↥J,
      (MulAut.congr θ αbar) (θ x) = θ (αbar x) := by
    intro x
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  change φ (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')
  rw [show φ = MulAut.congr θ αbar from rfl, hcongr]
  congr 1
  have hαl : (α l : K) = l' := by
    rw [show (α l : K) = b⁻¹ * (l : K) * (b⁻¹)⁻¹ from
      Subgroup.normalizerMonoidHom_apply_apply_coe J γ l]
    rw [inv_inv]
    exact hl.symm
  exact hstep l ▸ congrArg (QuotientGroup.mk) (Subtype.ext hαl)

section Unitary

variable {F : Type} [Field F]

private theorem fiveTorus_le_unitaryBlockDiag (h : UnitaryFieldData 2 2 F) :
    unitaryTorusSU h ({0, 1} : Finset (Fin 6)) ≤
      unitaryBlockDiag h ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
  haveI := h.finite
  intro b hb
  obtain ⟨c, hc, rfl⟩ := (mem_unitaryTorusSU h).1 hb
  rw [mem_unitaryBlockDiag]
  intro i j hij
  rw [coe_torusDiagSU]
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.diagonal_apply]

theorem innerDiagMarking_fiveTorus (h : UnitaryFieldData 2 2 F) :
    InnerDiagMarking (unitaryTorusSU h ({0, 1} : Finset (Fin 6)))
      (unitaryBlock h ({0, 1, 2, 3, 4} : Finset (Fin 6))) := by
  haveI := h.finite
  refine innerDiagMarking_of_pow_five_twA_four (n := 2) (by norm_num) (by norm_num)
    (hasLabel_unitaryBlock_four h) ?_ ?_
  · intro b hb
    exact unitaryBlockDiag_le_normalizer_unitaryBlock h
      ({0, 1, 2, 3, 4} : Finset (Fin 6)) (fiveTorus_le_unitaryBlockDiag h hb)
  · intro b hb
    exact (isElemAbelian_unitaryTorusSU_two h).2 b hb

end Unitary

end TwA5Four

end CFSG.LocalAnalysis.GLTheoremA.Y10F
