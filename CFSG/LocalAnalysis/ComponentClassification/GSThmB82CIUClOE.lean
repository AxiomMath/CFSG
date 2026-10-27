module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUClBar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOMinA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthMain

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUJ6Cl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat compInd)
open CFSG.ComponentClassification.GSThmB.QPUCl (exists_normal_pair commute_of_kappa_fix
  commutator_oBlock_eq mul_sub_one_of_mem_oIsoBlock mul_sub_one_comm eq_top_of_normal_not_le_core
  oκ_linPair_one signMat_compl')

variable {K : Type} [Field K] {d : ℕ} {w : Fin d → K}

theorem signGL_mem_of_scalar6 (hw : ∀ i, w i ≠ 0) [Finite K] (hK : ringChar K ≠ 2)
    {J : Finset (Fin d)} (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
    {I : Finset (Fin d)} (hI : I = J ∨ I = Jᶜ) (hI3 : 3 ≤ I.card)
    (hIc : Iᶜ.Nonempty) (hNF : BlockNF w I) (hq : IsQuasisimple (Burgoyne.C.blockP K hw I))
    {E : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL hw)))))}
    {L J₀ : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} {p f : ℕ}
    (h : BarData6 E L (projH _ ⟨signGL K J, hJ⟩) (Burgoyne.C.blockP K hw I) J₀ p f)
    (hIL : Burgoyne.C.blockP K hw I ≤ L)
    (hκ : ∀ e ∈ E, ∃ g : similarityPairs (oQ (diagGL hw)), e = oκ _ g)
    (hE1 : ∃ e ∈ E, e ≠ 1)
    (hscal : ∀ g : similarityPairs (oQ (diagGL hw)),
      (∀ x ∈ Burgoyne.C.blockP K hw I, oκ _ g x = x) →
      oκ _ g (projH _ ⟨signGL K J, hJ⟩) = projH _ ⟨signGL K J, hJ⟩ →
      g.val.right = 1 ∧ ∃ c : Kˣ, ∀ i ∈ I, ∀ j : Fin d,
        (g.val.left : Matrix (Fin d) (Fin d) K) i j = (if i = j then (c : K) else 0) ∧
        (g.val.left : Matrix (Fin d) (Fin d) K) j i = (if i = j then (c : K) else 0)) :
    signGL K I ∈ matrixDerived (oQ (diagGL hw)) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hIne : I.Nonempty := Finset.card_pos.1 (by omega)
  have hrep : ∀ e ∈ E, ∃ (D : GL (Fin d) K) (hD : D ∈ matrixIsometries (oQ (diagGL hw))),
      D ∈ oIsoBlock K hw Iᶜ ∧ e = oκ _ (linPair D hD) := by
    intro e he
    obtain ⟨g, rfl⟩ := hκ e he
    obtain ⟨hσ, c, hc⟩ := hscal g (fun x hx => h.hLE (hIL hx) _ he) (h.hLE h.htL _ he)
    obtain ⟨D, hD, hDI, hDe⟩ := exists_normal_pair hw h2 hσ hIne hc
    exact ⟨D, hD, hDI, hDe.symm⟩
  obtain ⟨M, hMH, hMp, hML⟩ := X10Orth.exists_perfect_lift
    (Burgoyne.C.commutator_eq_of_isPComponent h.hLE h.hLc)
  have hcomm : ∀ (D : GL (Fin d) K) (hD : D ∈ matrixIsometries (oQ (diagGL hw))),
      oκ _ (linPair D hD) ∈ E → ∀ X ∈ M, X * D = D * X := fun D hD hDE =>
    commute_of_kappa_fix hMH hMp hD fun Y hY => h.hLE (hML ▸ ⟨Y, hY, rfl⟩) _ hDE
  let S : Set (GL (Fin d) K) := {D | D ∈ oIsoBlock K hw Iᶜ ∧
    ∃ hD : D ∈ matrixIsometries (oQ (diagGL hw)), oκ _ (linPair D hD) ∈ E}
  let Mρ : Subgroup (GL (Fin d) K) :=
    { carrier := {X | X ∈ M ∧ ∀ D ∈ S, (X : Matrix (Fin d) (Fin d) K) *
        ((D : Matrix (Fin d) (Fin d) K) - 1) = (D : Matrix (Fin d) (Fin d) K) - 1}
      one_mem' := ⟨one_mem M, fun D _ => by rw [Units.val_one, Matrix.one_mul]⟩
      mul_mem' := fun {X Y} hX hY => ⟨mul_mem hX.1 hY.1, fun D hD => by
        rw [Units.val_mul, Matrix.mul_assoc, hY.2 D hD, hX.2 D hD]⟩
      inv_mem' := fun {X} hX => ⟨inv_mem hX.1, fun D hD => by
        calc ((X⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
              ((D : Matrix (Fin d) (Fin d) K) - 1) =
            ((X⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
              ((X : Matrix (Fin d) (Fin d) K) * ((D : Matrix (Fin d) (Fin d) K) - 1)) := by
              rw [hX.2 D hD]
          _ = (D : Matrix (Fin d) (Fin d) K) - 1 := by
              rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
                Matrix.one_mul]⟩ }
  have hMρM : Mρ ≤ M := fun X hX => hX.1
  have hOM : oBlock K hw I ≤ M := X10Orth.le_of_map_projH_le
    (Burgoyne.C.oBlock_le_matrixDerived hw h2 I) (commutator_oBlock_eq hw h2 hIc hq)
    (by rw [hML]; exact hIL)
  have hOI : oBlock K hw I ≤ Mρ := fun X hX => ⟨hOM hX, fun D hD =>
    mul_sub_one_of_mem_oIsoBlock hw (oBlock_le_oIsoBlock hw I hX) hD.1⟩
  set N := (Mρ.subgroupOf (matrixDerived (oQ (diagGL hw)))).map (projH _) with hN
  have hNL : N ≤ L := by
    rw [← hML]
    exact map_mono fun x hx => mem_subgroupOf.2 (hMρM (mem_subgroupOf.1 hx))
  have hNn : (N.subgroupOf L).Normal := by
    constructor
    rintro ⟨n, hnL⟩ hn ⟨l, hlL⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨X, hX, rfl⟩ := hn
    have hlM : l ∈ (M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map (projH _) := hML ▸ hlL
    obtain ⟨Y, hY, rfl⟩ := hlM
    replace hX : (X : GL (Fin d) K) ∈ Mρ := mem_subgroupOf.1 hX
    replace hY : (Y : GL (Fin d) K) ∈ M := mem_subgroupOf.1 hY
    refine ⟨Y * X * Y⁻¹, mem_subgroupOf.2 ?_, by rw [map_mul, map_mul, map_inv]; rfl⟩
    refine ⟨mul_mem (mul_mem hY hX.1) (inv_mem hY), fun D hD => ?_⟩
    obtain ⟨hDI, hDm, hDE⟩ := hD
    have h1 := mul_sub_one_comm (hcomm D hDm hDE _ hY)
    have h1' := mul_sub_one_comm (hcomm D hDm hDE _ (inv_mem hY))
    change (((Y : GL (Fin d) K) * X * (Y : GL (Fin d) K)⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) * _ = _
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, h1', ← Matrix.mul_assoc,
      Matrix.mul_assoc ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K), hX.2 D ⟨hDI, hDm, hDE⟩,
      h1,
      Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨I₀, hI₀, hI₀3, hI₀w, -⟩ := hNF
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < I₀.card)
  have hs := signGL_pair_mem_oBlock hw (hI₀ ha) (hI₀ hb) hab (hI₀w a ha b hb)
  have hsΩ := Burgoyne.C.oBlock_le_matrixDerived hw h2 I hs
  have hpc : ({a, b} : Finset (Fin d))ᶜ.Nonempty := by
    obtain ⟨k, hk⟩ := hIc
    refine ⟨k, Finset.mem_compl.2 fun hk' => Finset.mem_compl.1 hk ?_⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hk'
    rcases hk' with rfl | rfl
    · exact hI₀ ha
    · exact hI₀ hb
  have hy2 := Burgoyne.C.orderOf_projH_sign hw hK hsΩ ⟨a, by simp⟩ hpc
  have hyN : projH _ (⟨signGL K {a, b}, hsΩ⟩ : matrixDerived (oQ (diagGL hw))) ∈ N :=
    ⟨_, mem_subgroupOf.2 (hOI hs), rfl⟩
  have hNO : ¬ N.subgroupOf L ≤ pPrimeCore 2 ↥L := fun hle =>
    Burgoyne.C.not_mem_pPrimeCore_of_orderOf (a := ⟨_, hNL hyN⟩)
      (by rw [Subgroup.orderOf_mk]; exact hy2) (hle (mem_subgroupOf.2 hyN))
  have hNtop := eq_top_of_normal_not_le_core h.primeResidual_L h.simple_L (N.subgroupOf L) hNO
  have hLN : L ≤ N := Subgroup.subgroupOf_eq_top.1 hNtop
  have hMMρ : M ≤ Mρ := X10Orth.le_of_map_projH_le hMH hMp (by rw [hML]; exact hLN)
  obtain ⟨e₀, he₀, he₀1⟩ := hE1
  obtain ⟨D₀, hD₀, hD₀I, rfl⟩ := hrep e₀ he₀
  have hne : (D₀ : Matrix (Fin d) (Fin d) K) - 1 ≠ 0 := by
    intro h0
    apply he₀1
    have hD₀1 : D₀ = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h0)
    subst hD₀1
    exact oκ_linPair_one hD₀
  obtain ⟨k, l, hkl⟩ : ∃ k l, ((D₀ : Matrix (Fin d) (Fin d) K) - 1) k l ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (Matrix.ext hall)
  have hkI : k ∉ I := by
    intro hk
    apply hkl
    rw [Matrix.sub_apply, ((mem_oIsoBlock_iff hw).1 hD₀I).2 k l (Or.inl (by simpa using hk)),
      Matrix.one_apply, sub_self]
  have htN : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈
      (M.subgroupOf (matrixDerived (oQ (diagGL hw)))).map (projH _) := hML ▸ h.htL
  obtain ⟨T, hT, hTt⟩ := htN
  obtain ⟨c', hc'⟩ := mem_subgroupOf.1 (projH_eq_projH_iff.1 hTt)
  have hTS : (signGL K J : GL (Fin d) K) =
      (T : GL (Fin d) K) * GeneralLinearGroup.scalar (Fin d) c' := by
    have e : GeneralLinearGroup.scalar (Fin d) c' = ((T : GL (Fin d) K))⁻¹ * signGL K J := hc'
    rw [e, mul_inv_cancel_left]
  have hTm : ((T : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((c'⁻¹ : Kˣ) : K) • signMat K J := by
    have e := congrArg Units.val hTS
    rw [coe_signGL, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at e
    rw [e, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ c'.ne_zero, one_smul]
  have hTD := (hMMρ (mem_subgroupOf.1 hT)).2 D₀ ⟨hD₀I, hD₀, he₀⟩
  have hkk : ((c'⁻¹ : Kˣ) : K) * (if k ∈ J then -1 else 1) = 1 := by
    have e := congrFun (congrFun hTD k) l
    rw [hTm, Matrix.smul_mul, Matrix.smul_apply, signMat, Matrix.diagonal_mul,
      smul_eq_mul, ← mul_assoc] at e
    exact mul_right_cancel₀ hkl (by rw [e, one_mul])
  have hTI : ((T : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = signMat K I := by
    rw [hTm]
    rcases hI with rfl | rfl
    · simp only [hkI, ↓reduceIte, mul_one] at hkk
      rw [hkk, one_smul]
    · have hkJ : k ∈ J := by simpa using hkI
      simp only [hkJ, ↓reduceIte, mul_neg_one, neg_eq_iff_eq_neg] at hkk
      rw [hkk, neg_one_smul, signMat_compl']
  have hTeq : (T : GL (Fin d) K) = signGL K I := Units.ext (by rw [hTI, coe_signGL])
  exact hTeq ▸ T.2

end CFSG.ComponentClassification.GSThmB.QPUJ6Cl
