module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClD4Sign
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4PcSq
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneD4Field

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points pointMk pointMk_submodule
  exists_eq_pointMk)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.D4
open CFSG.ComponentClassification.Burgoyne.U (barEq map_bar_fmap)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL orthComponentData OrthNF
  signMat signMat_mul_self reflGL rotGL mul_conj_mul_inv)
open scoped commutatorElement

section PcSq

variable {K : Type} [Field K] [Finite K]

theorem ClO.d4_cent_fix_gen {d : ℕ} (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R)
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hcd : CompData ⁅isoCent R g.val.left, isoCent R g.val.left⁆)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ r ∈ Ro, r * oκ _ g = oκ _ g * r)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ r ∈ Ro,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ Ro)
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (hy : y ∈ Ro)
    {X : GL (Fin d) K} (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆) :
    y (projH _ ⟨X, commutator_isoCent_le (Ring.two_ne_zero hK) hR _ hX⟩) =
      projH _ ⟨X, commutator_isoCent_le (Ring.two_ne_zero hK) hR _ hX⟩ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set A := g.val.left with hA
  set φ := (matrixDerivedConjugation (oQ R) g).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ R), ((φ Y : matrixDerived (oQ R)) : GL (Fin d) K) =
      A * Y * A⁻¹ := by
    intro Y
    change (matrixDerivedConjugation (oQ R) g Y).val = _
    rw [matrixDerivedConjugation_val, hg1, map_one, MulAut.one_apply]
  refine ClO.fix_of_compData hinj hRodd hRi hRc φ (matrixDerivedConjugation (oQ R) g).injective
    (fun Y => kappa_lift _ Y) (commutator_isoCent_le h2 hR A)
    (fun X hX => ?_) (fun h hh X hX => ?_) hcd hy hX
  · apply Subtype.ext
    rw [hφc]
    have hc := mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (Subgroup.commutator_le_self _ hX)).2
    change A * X * A⁻¹ = X
    rw [← hc, mul_inv_cancel_right]
  · have hh' : A * (h : GL (Fin d) K) * A⁻¹ =
        GeneralLinearGroup.scalar (Fin d) (1 : Kˣ) * h := by
      rw [map_one, one_mul, ← hφc, hh]
    have hhI : (h : GL (Fin d) K) ∈ CatalogueBGraphForm.isometryGroup d K R :=
      Subgroup.commutator_le_self _ (by rw [← matrixDerived_oQ h2 R hR]; exact h.2)
    exact conj_mem_commutator_isoCent hhI hh' hX

theorem ClO.d4_pc_sq_false (hK : ringChar K ≠ 2) {s : K} (hs : s ≠ 0)
    {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (wMat 1 (-(s ^ 2))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right = 1)
    (hgA : (g.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat (s ^ 2)))
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))}
    {y : MulAut (StatedProj (matrixDerived (oQ R)))} (h : ClO.D4Sit (oQ R) (oκ _ g) Ro y) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hRs : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R := by
    rw [hR, blkDiag_transpose', wMat_transpose]
  have hcd := compData_anti h2 hs (by norm_num) hR hgA
  obtain ⟨e₁, hm₁, hv₁⟩ := exists_kron_sign hR hgA (i := 0) (k := 1) (by decide)
  obtain ⟨e₂, hm₂, hv₂⟩ := exists_kron_sign hR hgA (i := 1) (k := 2) (by decide)
  obtain ⟨e₃, hm₃, hv₃⟩ := exists_kron_cyc hR hgA (Equiv.swap 0 1) (Equiv.swap 1 2)
  obtain ⟨e₄, hm₄, hv₄⟩ := exists_kron_cyc hR hgA (Equiv.swap 1 2) (Equiv.swap 2 3)
  have hle := commutator_isoCent_le h2 hRs g.val.left
  obtain ⟨H, hH⟩ : ∃ H : Subgroup (StatedProj (matrixDerived (oQ R))),
      H = closure {projH _ ⟨e₁, hle hm₁⟩, projH _ ⟨e₂, hle hm₂⟩, projH _ ⟨e₃, hle hm₃⟩,
        projH _ ⟨e₄, hle hm₄⟩} := ⟨_, rfl⟩
  have hHfix : ∀ x ∈ H, y x = x := by
    rw [hH]
    refine fix_closure ?_
    rintro _ (rfl | rfl | rfl | rfl)
    · exact ClO.d4_cent_fix_gen hK hRs h.inj hg1 hcd h.odd h.comm h.norm h.mem hm₁
    · exact ClO.d4_cent_fix_gen hK hRs h.inj hg1 hcd h.odd h.comm h.norm h.mem hm₂
    · exact ClO.d4_cent_fix_gen hK hRs h.inj hg1 hcd h.odd h.comm h.norm h.mem hm₃
    · exact ClO.d4_cent_fix_gen hK hRs h.inj hg1 hcd h.odd h.comm h.norm h.mem hm₄
  have hfixV : ∀ {X : GL (Fin (2 * 4)) K} (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆),
      projH _ ⟨X, hle hX⟩ ∈ subStab (oQ R) (LinearMap.range (eigPlusMap s)) := by
    intro X hX
    rw [proj_mem_subStab_iff]
    exact subPerm_eigPlus (by rw [← hgA]; exact commute_of_mem_commutator_isoCent hX)
  have hHV : H ≤ subStab (oQ R) (LinearMap.range (eigPlusMap s)) := by
    rw [hH, closure_le]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hfixV hm₁
    · exact hfixV hm₂
    · exact hfixV hm₃
    · exact hfixV hm₄
  have htri := h.geom y (ClSp.odd_orderOf_of_mem h.odd h.mem) h.move
  obtain ⟨L, hHL⟩ := htri.exists_pt_of_ts hHfix (isTS_eigPlus hR) hHV
  obtain ⟨x, hx, hQx, rfl⟩ := exists_eq_pointMk L
  have hline : ∀ {X : GL (Fin (2 * 4)) K} (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆),
      projH _ ⟨X, hle hX⟩ ∈ H → (X : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ x ∈
        Submodule.span K {x} := by
    intro X hX hXH
    have h1 := hHL hXH
    rw [proj_mem_subStab_iff, pointMk_submodule] at h1
    rw [← h1]
    exact ⟨x, Submodule.mem_span_singleton_self x, rfl⟩
  have hin : ∀ i : Fin 4, ∀ X (hX : X ∈ ⁅isoCent R g.val.left, isoCent R g.val.left⁆),
      (i = 0 ∧ X = e₁) ∨ (i = 1 ∧ X = e₂) ∨ (i = 2 ∧ X = e₃) ∨ (i = 3 ∧ X = e₄) →
      projH _ ⟨X, hle hX⟩ ∈ H := by
    rintro i X hX (⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩) <;> rw [hH] <;>
      exact subset_closure (by simp)
  have l₁ := hline hm₁ (hin 0 _ hm₁ (Or.inl ⟨rfl, rfl⟩))
  have l₂ := hline hm₂ (hin 1 _ hm₂ (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have l₃ := hline hm₃ (hin 2 _ hm₃ (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have l₄ := hline hm₄ (hin 3 _ hm₄ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  rw [hv₁] at l₁
  rw [hv₂] at l₂
  rw [hv₃] at l₃
  rw [hv₄] at l₄
  exact no_line_kron h2 hx l₁ l₂ l₃ l₄

end PcSq

section Field

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem ClO.d4_field_false (hp2 : p ≠ 2) (h2 : (2 : K) ≠ 0) {wF : Fin (2 * 4) → h.fixedField}
    (hwF : OrthNF wF)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF.1))))))}
    {y : MulAut (StatedProj (matrixDerived (oQ (diagGL (wK_ne_zero h hwF.1)))))}
    (hs : ClO.D4Sit (oQ (diagGL (wK_ne_zero h hwF.1))) (oκ _ (barPair h h2 hwF.1)) Ro y) :
    False := by
  have := h.finite
  have : CharP K p := h.charP
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hF2 := two_ne_zero_fixedField h hp2
  have h2F : (2 : h.fixedField) ≠ 0 := Ring.two_ne_zero hF2
  have hw := wK_ne_zero h hwF.1
  obtain ⟨I, hI3, -, hIw⟩ := hwF.2
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (by omega : 2 < I.card)
  have hHeq := matrixDerived_oQ h2 (diagGL hw) (diagGL_transpose _)
  have hF₀H := omegaF_le h h2 hwF.1
  set φ := (matrixDerivedConjugation (oQ (diagGL hw)) (barPair h h2 hwF.1)).toMonoidHom with hφ
  have hφc : ∀ Y : matrixDerived (oQ (diagGL hw)),
      (((φ Y : matrixDerived _) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
        ((Y : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).map h.bar := by
    intro Y
    change ((matrixDerivedConjugation _ (barPair h h2 hwF.1) Y : matrixDerived _) :
      GL (Fin (2 * 4)) K).val = _
    rw [matrixDerivedConjugation_val, barPair_left, barPair_right, inv_one, mul_one, one_mul]
    rfl
  have hcd : CompData (omegaF h hwF.1) :=
    CompData.map (orthComponentData hF2 (by norm_num) (diagGL hwF.1) (diagGL_transpose hwF.1)
      (by omega)) (iotaF_injective h)
  have hfix : ∀ X (hX : X ∈ omegaF h hwF.1), y (projH _ ⟨X, hF₀H hX⟩) = projH _ ⟨X, hF₀H hX⟩ := by
    intro X hX
    refine ClO.fix_of_compData hs.inj hs.odd hs.comm hs.norm φ
      (matrixDerivedConjugation (oQ (diagGL hw)) (barPair h h2 hwF.1)).injective
      (fun Y => kappa_lift _ Y) hF₀H (fun X hX => ?_) (fun g hg X hX => ?_) hcd hs.mem hX
    · obtain ⟨X', -, rfl⟩ := hX
      apply Subtype.ext
      apply Units.ext
      rw [hφc]
      change ((iotaF h X' : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).map h.bar =
        ((iotaF h X' : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)
      rw [coe_iotaF, map_bar_fmap]
    · have hc' : ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).map h.bar =
          (1 : K) • ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := by
        rw [one_smul, ← hφc, hg]
      have hgI : (g : GL (Fin (2 * 4)) K) ∈ CatalogueBGraphForm.isometryGroup (2 * 4) K
          (diagGL hw) := Subgroup.commutator_le_self _ (by rw [← hHeq]; exact g.2)
      exact conj_mem_omegaF h hwF.1 hgI hc' hX
  have hmemF : ∀ {i j : Fin (2 * 4)}, i ∈ I → j ∈ I → i ≠ j →
      signGL K {i, j} ∈ omegaF h hwF.1 := by
    intro i j hi hj hij
    refine ⟨signGL h.fixedField {i, j}, ?_, iotaF_signGL h _⟩
    rw [← matrixDerived_oQ h2F (diagGL hwF.1) (diagGL_transpose _)]
    exact signGL_pair_mem_derived h2F hwF.1 hij (hIw i hi j hj)
  exact ClO.d4_klein_false hw hK hs hab hbc hac (hF₀H (hmemF ha hb hab)) (hF₀H (hmemF hb hc hbc))
    (hfix _ (hmemF ha hb hab)) (hfix _ (hmemF hb hc hbc))

end Field

end CFSG.ComponentClassification.Foote5.OddLieCore
