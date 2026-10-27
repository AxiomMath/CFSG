module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoFrame
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary45Mono
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.S11c.Sec66TModels

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
open scoped commutatorElement

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem commutator_fixed_conj
    {M : primeFormUnitary h (idGram K n)}
    {x y : primeFormP h (idGram K n)}
    (hx : x ∈ fixSubgroup (primeFormConjHom h (idGram K n) M))
    (hy : y ∈ fixSubgroup (primeFormConjHom h (idGram K n) M)) :
    ∃ w : gramSU h (idGram K n),
      (w : GL (Fin n) K) * (M : GL (Fin n) K) = (M : GL (Fin n) K) * (w : GL (Fin n) K) ∧
        ⁅x, y⁆ = (w : primeFormP h (idGram K n)) := by
  classical
  have key : ∀ g : gramSU h (idGram K n),
      (g : primeFormP h (idGram K n)) ∈ fixSubgroup (primeFormConjHom h (idGram K n) M) →
      ∃ c : Kˣ, (M : GL (Fin n) K) * (g : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹ =
        (g : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
    intro g hg
    have hg' : primeFormConjHom h (idGram K n) M (g : primeFormP h (idGram K n)) = g := hg
    rw [primeFormConjHom_mk, QuotientGroup.eq] at hg'
    obtain ⟨c, -, -, hc⟩ := hg'
    refine ⟨c⁻¹, ?_⟩
    have h1 : ((M : GL (Fin n) K) * (g : GL (Fin n) K) * (M : GL (Fin n) K)⁻¹)⁻¹ *
        (g : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := hc
    rw [map_inv]
    exact eq_mul_inv_of_mul_eq (inv_mul_eq_iff_eq_mul.mp h1).symm
  induction x using QuotientGroup.induction_on with
  | H g =>
  induction y using QuotientGroup.induction_on with
  | H g' =>
  obtain ⟨c, hc⟩ := key g hx
  obtain ⟨d, hd⟩ := key g' hy
  refine ⟨⁅g, g'⁆, ?_, rfl⟩
  have hconj : ∀ a b : GL (Fin n) K, (M : GL (Fin n) K) * ⁅a, b⁆ * (M : GL (Fin n) K)⁻¹ =
      ⁅(M : GL (Fin n) K) * a * (M : GL (Fin n) K)⁻¹,
        (M : GL (Fin n) K) * b * (M : GL (Fin n) K)⁻¹⁆ := fun a b => by
    simp only [commutatorElement_def]
    group
  have hMw : (M : GL (Fin n) K) * ⁅(g : GL (Fin n) K), (g' : GL (Fin n) K)⁆ *
      (M : GL (Fin n) K)⁻¹ = ⁅(g : GL (Fin n) K), (g' : GL (Fin n) K)⁆ := by
    rw [hconj, hc, hd]
    exact commutatorElement_mul_mul' (GeneralLinearGroup.scalar_commute c _)
      (GeneralLinearGroup.scalar_commute c _) (GeneralLinearGroup.scalar_commute d _)
  change ⁅(g : GL (Fin n) K), (g' : GL (Fin n) K)⁆ * (M : GL (Fin n) K) =
    (M : GL (Fin n) K) * ⁅(g : GL (Fin n) K), (g' : GL (Fin n) K)⁆
  exact (mul_inv_eq_iff_eq_mul.mp hMw).symm

@[expose] def cframe6 (i₀ : Fin 6) : Fin 5 → Fin 6 → K := cframe (m := 5) i₀

theorem cframe6_isOrthonormal (i₀ : Fin 6) : IsOrthonormalFamily h (cframe6 (K := K) i₀) :=
  cframe_isOrthonormal h (m := 5) i₀

@[expose] noncomputable def phi6 (i₀ : Fin 6) :
    gramSU h (idGram K 5) →* gramSU h (idGram K 6) :=
  frameSU h (cframe6_isOrthonormal h i₀)

theorem coe_phi6 (i₀ : Fin 6) (Y : gramSU h (idGram K 5)) :
    (((phi6 h i₀ Y : gramSU h (idGram K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      frameEmb h (cframe6 (K := K) i₀) ((Y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) :=
  coe_frameSU (cframe6_isOrthonormal h i₀) Y

theorem phi6_injective (i₀ : Fin 6) : Function.Injective (phi6 h i₀) :=
  frameSU_injective (cframe6_isOrthonormal h i₀)

theorem frameEmb_cframe6_left (i₀ : Fin 6) (Y : Matrix (Fin 5) (Fin 5) K) (l : Fin 6) :
    frameEmb h (cframe6 (K := K) i₀) Y i₀ l = if i₀ = l then 1 else 0 :=
  frameEmb_cframe_left h (m := 5) i₀ Y l

theorem exists_eq_scalar_mul_phi6 (hq : ℓ ^ f = 2) {ν μ : K} (hνμ : ν ≠ μ) (i₀ : Fin 6)
    {w : gramSU h (idGram K 6)}
    (hw : ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * dmat i₀ ν μ =
      dmat i₀ ν μ * ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) :
    ∃ (c : Kˣ) (Y : gramSU h (idGram K 5)), (w : GL (Fin 6) K) =
      GeneralLinearGroup.scalar (Fin 6) c *
        ((phi6 h i₀ Y : gramSU h (idGram K 6)) : GL (Fin 6) K) := by
  classical
  have hu : IsOrthonormalFamily h (cframe6 (K := K) i₀) := cframe6_isOrthonormal h i₀
  have hdet : ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := w.2.2
  have hWu : adj h ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 :=
    mem_primeFormUnitary_iff_adj.1 w.2.1
  have hc : ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i₀ i₀ ≠ 0 := by
    intro h0
    have hrow : ∀ j, ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i₀ j = 0 := by
      intro j
      by_cases hj : j = i₀
      · rw [hj]; exact h0
      · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hj
        exact entry_eq_zero_left hνμ i₀ hw b
    have := Matrix.det_eq_zero_of_row_eq_zero i₀ hrow
    rw [hdet] at this
    exact one_ne_zero this
  have hWeq : ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i₀ i₀) • frameEmb h (cframe6 (K := K) i₀)
        ((((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i₀ i₀)⁻¹ •
          ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).submatrix i₀.succAbove i₀.succAbove) :=
    eq_smul_frameEmb_of_commute h hνμ i₀ hw hc
  obtain ⟨c, Y0, hc0, hWeq⟩ : ∃ (c : K) (Y0 : Matrix (Fin 5) (Fin 5) K), c ≠ 0 ∧
      ((w : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = c • frameEmb h (cframe6 (K := K) i₀) Y0 :=
    ⟨_, _, hc, hWeq⟩
  rw [hWeq] at hWu hdet
  have hc3 : c ^ 3 = 1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.pow_three_eq_one h hq hc0
  have hunit : adj h Y0 * Y0 = 1 := by
    rw [adj_smul, frameEmb_adj (h := h), Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← frameEmb_mul hu] at hWu
    have h1 := congrFun (congrFun hWu i₀) i₀
    rw [Matrix.smul_apply, frameEmb_cframe6_left, if_pos rfl, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at h1
    rw [h1, one_smul, ← frameEmb_one (h := h) (cframe6 (K := K) i₀)] at hWu
    exact frameEmb_injective hu hWu
  have hdet5 : Y0.det = 1 := by
    rw [Matrix.det_smul, det_frameEmb hu, Fintype.card_fin] at hdet
    have : c ^ 6 = 1 := by rw [show 6 = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
    rwa [this, one_mul] at hdet
  have hYY : Y0 * adj h Y0 = 1 := mul_eq_one_comm.mp hunit
  let Ygl : GL (Fin 5) K := ⟨Y0, adj h Y0, hYY, hunit⟩
  have hYmem : Ygl ∈ gramSU h (idGram K 5) :=
    (mem_gramSU_iff_unitary h).2 ⟨mem_primeFormUnitary_iff_adj.2 hunit, hdet5⟩
  refine ⟨Units.mk0 c hc0, ⟨Ygl, hYmem⟩, ?_⟩
  apply Units.ext
  rw [Units.val_mul, coe_phi6, hWeq,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.scalar_coe_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul]
  rfl

end CFSG.HardMathSupport.Dickson.Sec6.I923
