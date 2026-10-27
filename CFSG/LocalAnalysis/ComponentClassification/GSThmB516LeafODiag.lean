module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOX
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOFix
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOFld
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOConf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthMain
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOReduce
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaField

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.Orth516

open Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open CFSG.ComponentClassification.Burgoyne.C (blockP oBlock_le_matrixDerived signGL_empty
  nonempty_blockP_equiv signGL_eq_compl_mul)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)

@[expose] def L4U4Type (X : Type) [Group X] (p f : ℕ) : Prop :=
  (p ^ f % 4 = 3 ∧ Blueprint.LieModel (X ⧸ center X) .PSL 4 p f) ∨
    (p ^ f % 4 = 1 ∧ Blueprint.LieModel (X ⧸ center X) .PSU 4 p f)

theorem L4U4Type.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    (h : L4U4Type Y p f) : L4U4Type X p f := by
  have e' : X ⧸ center X ≃* Y ⧸ center Y := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  rcases h with ⟨h3, h⟩ | ⟨h1, h⟩
  · exact Or.inl ⟨h3, OddQuot.lieModel_of_equiv e'.symm h⟩
  · exact Or.inr ⟨h1, OddQuot.lieModel_of_equiv e'.symm h⟩

variable {K : Type} [Field K] [Finite K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

theorem false_of_diag_conf
    (hK : ringChar K ≠ 2) {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hKc : Nat.card K = p ^ e)
    (hd : 7 ≤ d) (hker : OKer (oQ (diagGL hw))) {g : similarityPairs (oQ (diagGL hw))}
    {P J : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} {J₂ : Finset (Fin d)}
    (hJ₂ : signGL K J₂ ∈ matrixDerived (oQ (diagGL hw)))
    (hNF : 3 ≤ J₂.card → BlockNF w J₂) (hNFc : 3 ≤ J₂ᶜ.card → BlockNF w J₂ᶜ)
    (h : LeafConf (oκ _ g) P (projH _ ⟨signGL K J₂, hJ₂⟩) J) (hPq : IsQuasisimple P) {f : ℕ}
    (hf : 1 ≤ f) (hPm : L4U4Type P p f) : False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hp2 : p ≠ 2 := by rw [← ringChar.eq K p]; exact hK
  set x := projH (matrixDerived (oQ (diagGL hw))) ⟨signGL K J₂, hJ₂⟩ with hx
  have hx1 : x ≠ 1 := by
    intro h1
    have h3 := h.x2
    rw [h1, orderOf_one] at h3
    omega
  have hJne : J₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hJe
    apply hx1
    rw [hx, ← map_one (projH (matrixDerived (oQ (diagGL hw))))]
    congr 1
    apply Subtype.ext
    change signGL K J₂ = 1
    rw [hJe]
    exact signGL_empty
  have hJcne : J₂ᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro hJe
    apply hx1
    have hJu : J₂ = Finset.univ := by rw [← compl_compl J₂, hJe, Finset.compl_empty]
    have hsc : signGL K J₂ = Matrix.GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) := by
      apply Units.ext
      rw [coe_signGL, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hJu]
      ext i j
      simp [signMat, diagonal_apply]
    rw [hx, ← map_one (projH (matrixDerived (oQ (diagGL hw)))), projH_eq_projH_iff, mem_subgroupOf]
    refine ⟨-1, ?_⟩
    change _ = (signGL K J₂)⁻¹ * 1
    rw [hsc, mul_one, ← map_inv, inv_neg_one]
  obtain ⟨hJeq, hJq, hI34, hSI⟩ := x_sign_reduce hw hK hd hJ₂ hJne hJcne hNF hNFc h.JC h.Jc h.JZ
    h.J8
  have hNFI : BlockNF w J₂ᶜ := hNFc (by omega)
  have hIc : J₂ᶜᶜ.Nonempty := by rwa [compl_compl]
  have hPp : ⁅P, P⁆ = P := C.commutator_eq_of_isPComponent h.PF h.Pc
  obtain ⟨M, hMH, hMp, hMP⟩ := X10Orth.exists_perfect_lift hPp
  have hSM : signGL K J₂ ∈ M := by
    have hxP : x ∈ (M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map
        (projH (matrixDerived (oQ (diagGL hw)))) := hMP ▸ h.xP
    obtain ⟨m, hm, hmx⟩ := hxP
    obtain ⟨c, hc⟩ := mem_subgroupOf.1 ((projH_eq_projH_iff).1 hmx)
    have hmc : (m : GL (Fin d) K) = signGL K J₂ * Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ := by
      have e1 : ((m⁻¹ * ⟨signGL K J₂, hJ₂⟩ : matrixDerived (oQ (diagGL hw))) : GL (Fin d) K) =
          Matrix.GeneralLinearGroup.scalar (Fin d) c := hc.symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e1
      rw [map_inv, ← e1]
      group
    have hcH : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ matrixDerived (oQ (diagGL hw)) := by
      rw [hc]
      exact (m⁻¹ * ⟨signGL K J₂, hJ₂⟩ : matrixDerived (oQ (diagGL hw))).2
    have hcc : (c : K) * c = 1 := by
      have hI := matrixDerived_le_isometries _ hcH
      rw [matrixIsometries_oQ h2 _ (diagGL_transpose hw), CatalogueBGraphForm.mem_isometryGroup,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagGL,
        diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal] at hI
      obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
      have := congrFun (congrArg Matrix.diag hI) i
      simp only [diag_diagonal] at this
      have hwi := hw i
      have : ((c : K) * c - 1) * w i = 0 := by linear_combination this
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hwi)
    rcases mul_self_eq_one_iff.1 hcc with hc1 | hc1
    · have : c = 1 := Units.ext hc1
      rw [this, inv_one, map_one, mul_one] at hmc
      rw [← hmc]
      exact mem_subgroupOf.1 hm
    · exfalso
      have : c⁻¹ = -1 := by
        rw [show c = -1 from Units.ext (by rw [hc1]; rfl), inv_neg_one]
      have hcomp : signGL K J₂ * Matrix.GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) =
          signGL K J₂ᶜ := by
        rw [signGL_eq_compl_mul J₂ᶜ, compl_compl]
      rw [this, hcomp] at hmc
      exact hSI (hmc ▸ m.2)
  have hΩp : ⁅oBlock K hw J₂ᶜ, oBlock K hw J₂ᶜ⁆ = oBlock K hw J₂ᶜ := by
    obtain ⟨eB⟩ := nonempty_blockP_equiv hw hIc h2
    have hq : IsQuasisimple (oBlock K hw J₂ᶜ) := LocalCores.isQuasisimple_of_mulEquiv eB hJq
    have : Group.IsPerfect (oBlock K hw J₂ᶜ) := hq.1
    exact Subgroup.isPerfect_iff.1 this
  have hΩM : oBlock K hw J₂ᶜ ≤ M := X10Orth.le_of_map_projH_le (oBlock_le_matrixDerived hw h2 _)
    hΩp (by
      rw [hMP]
      have hJP := h.JP
      rw [hJeq] at hJP
      exact hJP)
  have hfixP : ∀ X ∈ M.subgroupOf (matrixDerived (oQ (diagGL hw))),
      oκ _ g (projH (matrixDerived (oQ (diagGL hw))) X) =
        projH (matrixDerived (oQ (diagGL hw))) X :=
    fun X hX => h.PF (hMP ▸ ⟨X, hX, rfl⟩)
  have hperfH : ⁅M.subgroupOf (matrixDerived (oQ (diagGL hw))),
      M.subgroupOf (matrixDerived (oQ (diagGL hw)))⁆ =
        M.subgroupOf (matrixDerived (oQ (diagGL hw))) := by
    apply Subgroup.map_injective (matrixDerived (oQ (diagGL hw))).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hMH, hMp]
  have hss : oκ _ (g * g) = 1 := by rw [map_mul, h.sq]
  by_cases hσ : g.val.right = 1
  ·
    obtain ⟨c, hc0, hS2, hε, -⟩ := inner_even_data h2 (diagGL_transpose hw) (by omega) hker hσ hss
    have hSXG : ∀ X ∈ M, g.val.left * X = X * g.val.left := by
      intro X hX
      have e := kappa_eq_of_fix g hperfH hfixP (X := ⟨X, hMH hX⟩) (mem_subgroupOf.2 hX)
      rw [hσ, show ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map ⇑(1 : K ≃+* K) =
        (X : Matrix (Fin d) (Fin d) K) from by ext; rfl] at e
      have eG : g.val.left * X * g.val.left⁻¹ = X :=
        Units.ext (by rw [Units.val_mul, Units.val_mul]; exact e)
      calc g.val.left * X = g.val.left * X * g.val.left⁻¹ * g.val.left := by group
        _ = X * g.val.left := by rw [eG]
    have hSX : ∀ X ∈ M, (g.val.left : Matrix (Fin d) (Fin d) K) * X =
        (X : Matrix (Fin d) (Fin d) K) * g.val.left := fun X hX => by
      rw [← Units.val_mul, ← Units.val_mul, hSXG X hX]
    have hDΩ : ∀ X : GL (Fin d) K, X ∈ oBlock K hw J₂ᶜ →
        (g.val.left : Matrix (Fin d) (Fin d) K) * X = (X : Matrix (Fin d) (Fin d) K) *
          g.val.left := fun X hX => hSX X (hΩM hX)
    rcases hε with hε | hε
    swap
    · rw [coe_diagGL] at hε
      exact false_of_skew_commute hw h2 hNFI hc0 hS2 hε hDΩ
    by_cases hsq : IsSquare c
    swap
    · exact hsq (isSquare_of_commute hw h2 hNFI hS2 hDΩ)
    obtain ⟨s₀, hs₀⟩ := hsq
    have hs₀0 : s₀ ≠ 0 := by
      rintro rfl
      exact hc0 (by rw [hs₀, mul_zero])
    set Rm := ((diagGL hw : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hRm
    set Sm := (g.val.left : Matrix (Fin d) (Fin d) K) with hSm
    have hSR : Smᵀ * Rm * Sm = c • Rm := by
      rw [hε, one_smul, Matrix.mul_assoc, hS2, Matrix.mul_smul, Matrix.mul_one]
    obtain ⟨S', hS'def⟩ : ∃ S' : GL (Fin d) K,
        S' = Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 s₀ hs₀0)⁻¹ * g.val.left :=
      ⟨_, rfl⟩
    have hS'c : (S' : Matrix (Fin d) (Fin d) K) = s₀⁻¹ • Sm := by
      rw [hS'def, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
        Units.val_inv_eq_inv_val, Units.val_mk0]
    have hS'R : (S' : Matrix (Fin d) (Fin d) K)ᵀ * Rm * S' = Rm := by
      rw [hS'c, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hSR,
        smul_smul, smul_smul, hs₀]
      rw [show s₀⁻¹ * s₀⁻¹ * (s₀ * s₀) = 1 by field_simp, one_smul]
    have hS'2 : (S' : Matrix (Fin d) (Fin d) K) * S' = 1 := by
      rw [hS'c, Matrix.smul_mul, Matrix.mul_smul, hS2, smul_smul, smul_smul, hs₀]
      rw [show s₀⁻¹ * s₀⁻¹ * (s₀ * s₀) = 1 by field_simp, one_smul]
    have hS' : S' ∈ matrixIsometries (oQ (diagGL hw)) :=
      (mem_matrixIsometries_oQ h2 _ (diagGL_transpose hw) S').2
        ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hS'R)
    have hκ : oκ _ g = oκ _ (linPair S' hS') := by
      refine oκ_eq_of_left_eq (c := Units.mk0 s₀ hs₀0) (by rw [hσ, linPair_right]) ?_
      rw [linPair_left, hS'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
    have hfix' : ∀ X ∈ M, X * S' = S' * X := by
      intro X hX
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hS'c, Matrix.mul_smul, Matrix.smul_mul, hSX X hX]
    obtain ⟨v, hv0, hv⟩ := exists_fixed_vector hK (diagGL_transpose hw) hS' hS'2
      (by rw [← hκ]; exact h.ne) hMH hMp hfix' (by rw [← hκ, hMP]; exact h.PF)
      (by rw [← hκ, hMP]; exact h.Pc)
    have hvI : ∀ i, i ∉ J₂ᶜ → v i = 0 := by
      intro i hi
      rw [Finset.mem_compl, not_not] at hi
      have e := congrFun (hv _ hSM) i
      rw [coe_signGL] at e
      simp only [signMat, mulVec_diagonal, hi, ite_true] at e
      have : (2 : K) * v i = 0 := by linear_combination -e
      exact (mul_eq_zero.1 this).resolve_left h2
    exact hv0 (eq_zero_of_fixed hw h2 hNFI hvI fun X hX => hv X (hΩM hX))
  obtain ⟨hσ2', c, hc⟩ := hker _ hss
  have hσ2 : g.val.right ^ 2 = 1 := by rw [← (sq_val _ g).2]; exact hσ2'
  have hc' : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right g.val.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c := by rw [← (sq_val _ g).1, hc]
  have hdim : d = 2 * (d / 2) + 1 ∧ 3 ≤ d / 2 ∨ d = 2 * (d / 2) ∧ 4 ≤ d / 2 := by omega
  have hQ := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK (diagGL hw)
    (diagGL_transpose hw)
  have hL : IsComponent (P.subgroupOf (autFixed (oκ _ g))) := by
    refine ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe h.PF).symm hPq, ?_⟩
    obtain ⟨-, -, hsub, -, -⟩ := h.Pc
    exact hsub
  have hmod : X10Lin.ModelIn p (X10Lin.orthTuples d (e / 2))
      ↥(P.subgroupOf (autFixed (oκ _ g))) :=
    odd_omega_field_modelIn hp hp2 he hKc hdim hQ g hσ2 hσ c hc' hL
  have hPm' : L4U4Type ↥(P.subgroupOf (autFixed (oκ _ g))) p f :=
    hPm.of_mulEquiv (subgroupOfEquivOfLe h.PF)
  exact false_of_l4u4_of_orthTuples (X := ↥(P.subgroupOf (autFixed (oκ _ g))))
    lieOrderFormulasInput hp2 hf hd hmod hPm'

end CFSG.ComponentClassification.GSThmB.Orth516
