module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddSp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddFam
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude)

theorem matrixDichotomy_statedSp {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) :
    MatrixDichotomy (StatedSp r K) := by
  rintro ⟨h, hh⟩ ⟨u, hu⟩ hns
  let A : gsp r K := ⟨h, statedSp_le_gsp hh⟩
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c :=
    fun c hc => hns ⟨c, hc.symm⟩
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAA : M * M = (u : K) • 1 := by
    have := congrArg Units.val hu
    rw [pow_two, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [hM]
    show ((h : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((h : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  have hcent : centralizer ({(⟨h, hh⟩ : StatedSp r K)} : Set (StatedSp r K)) = spCent r K A := by
    ext g
    rw [mem_centralizer_singleton_iff, Burgoyne.Sp.mem_spCent]
    constructor
    · intro hg
      exact (congrArg (fun x : StatedSp r K => ((x : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hg).symm
    · intro hg
      exact Subtype.ext (Units.ext hg.symm)
  have hC : HasCompOrSolv (spCent r K A) :=
    HasCompOrSolv.of_mulEquiv (spCentEquiv A).symm
      (hasCompOrSolv_similitudeCentralizer hp hp2 hf hK hr finrank_standard pairedSympForm_isAlt
        SymplecticFlag.pairedSympForm_nondegenerate
        (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) u.ne_zero (linA_mul_self hAA)
        hAμ)
  exact HasCompOrSolv.of_mulEquiv (MulEquiv.subgroupCongr hcent).symm hC

theorem oddDichotomyFamily_PSp : OddDichotomyFamily .PSp := by
  intro X _ _ n p f hp hp2 hadm hm τ hτ
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  exact solvableOrComponent_of_matrixDichotomy
    (matrixDichotomy_statedSp hadm.2.2.1 hp hp2 hadm.2.1 hK) e τ hτ

end CFSG.ComponentClassification.CatFC.DS81
