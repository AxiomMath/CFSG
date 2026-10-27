module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLinMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDSel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.SD
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.ComponentClassification
open scoped commutatorElement

@[expose] noncomputable def projEquivStated (n : ℕ) (K : Type) [Field K] :
    projectiveSL n K ≃* LargeEvenProj (StatedSL n K) :=
  QuotientGroup.congr (scalars n K) ((CFSG.Open.StatedScalars (Fin n) K).subgroupOf (StatedSL n K))
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K)
    (by rw [scalars_eq_center]; exact CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars n K)

variable {n : ℕ} {K : Type} [Field K]

theorem projEquivStated_proj (g : Matrix.SpecialLinearGroup (Fin n) K) :
    projEquivStated n K (proj n K g) =
      LargeEvenProjMk (StatedSL n K) (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K g) :=
  rfl

theorem projEquivStated_conj {A : GL (Fin n) K} {φ : MulAut (LargeEvenProj (StatedSL n K))}
    (hA : ∀ h h' : ↥(StatedSL n K), (h' : GL (Fin n) K) = A * (h : GL (Fin n) K) * A⁻¹ →
      φ (LargeEvenProjMk (StatedSL n K) h) = LargeEvenProjMk (StatedSL n K) h')
    (x : projectiveSL n K) :
    (projEquivStated n K).symm (φ (projEquivStated n K x)) = conjAut n K A x := by
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [projEquivStated_proj, conjAut_proj]
  have h1 := hA (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K g)
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K
      (CatalogueBHigherLinearAction.slConjugation n K A g)) (by
        refine Units.ext ?_
        rw [Units.val_mul, Units.val_mul, CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe,
          CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
        exact coe_slConjugation A g)
  rw [h1]
  exact (MulEquiv.symm_apply_eq _).2 rfl

theorem sdFamModel_linHi (hLD : Y10GInnLin.LinLabelDict) : SDFamModel t263GLinHi := by
  intro p hp hp2 Ω _ _ S B B₀ hSn hSq hSp hSc hQ hF2 hBel hB₀B hInn
  obtain ⟨d, K, instF, instFin, θm, hd, h2, ⟨m, hm1, hKm, hmn⟩, hind⟩ :=
    sd_lin_model hLD hSp hSq hQ hInn
  have hK : p = 3 → 4 ≤ Nat.card K := by
    intro h3
    by_contra hlt
    push Not at hlt
    rw [hKm] at hlt
    have hm : m = 1 := by
      by_contra hne
      have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hF2 h3 (hmn hm)
  refine ⟨projectiveSL d K, inferInstance, inferInstance, θm.trans (projEquivStated d K).symm,
    fun φ => ∃ A : GL (Fin d) K, φ = conjAut d K A, ?_, famSel_linear h2 hd hp hp2 hK⟩
  intro b hb
  obtain ⟨φ, ⟨A, hA⟩, hφ⟩ := hind (b : Ω) hb
  refine ⟨A, ?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨s, rfl⟩ := sdσ_surjective (θm.trans (projEquivStated d K).symm) x
  have h1 := sd_rho_apply (sd_hBN hSn B) (θm.trans (projEquivStated d K).symm) b s
  have h2' := hφ s (CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) b s) (sd_conj_coe (sd_hBN hSn B) b s)
  rw [h1]
  show (projEquivStated d K).symm (θm (QuotientGroup.mk
      (CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) b s))) =
    conjAut d K A ((projEquivStated d K).symm (θm (QuotientGroup.mk s)))
  rw [← h2']
  have h3 := projEquivStated_conj hA ((projEquivStated d K).symm (θm (QuotientGroup.mk s)))
  rw [MulEquiv.apply_symm_apply] at h3
  exact h3

end CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin

end
