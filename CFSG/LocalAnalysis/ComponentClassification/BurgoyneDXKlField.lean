module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXKlData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT2

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Kl

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C (omegaR orth_block_cases)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat OrthNF
  commutatorElement_mul_mem_center)
open scoped commutatorElement

variable {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)

theorem false_of_k2_field [Finite K] (hK : ringChar K ≠ 2) (hp2 : p ≠ 2) {d : ℕ} (hd5 : 5 ≤ d)
    {wF : Fin d → h.fixedField}
    (hNF : OrthNF wF) {M : Subgroup (GL (Fin d) K)} (hd : K2Data (diagGL (wK_ne_zero h hNF.1)) M)
    (hQs : (M.subgroupOf (matrixDerived (oQ (diagGL (wK_ne_zero h hNF.1))))).map (projH _) ≤
      autFixed (oκ _ (barPair h (Ring.two_ne_zero hK) hNF.1)))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ (diagGL (wK_ne_zero h hNF.1))))).map
      (projH _)).subgroupOf (autFixed (oκ _ (barPair h (Ring.two_ne_zero hK) hNF.1))))) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hwF := hNF.1
  set H := matrixDerived (oQ (diagGL (wK_ne_zero h hwF))) with hH
  set Qb := (M.subgroupOf H).map (projH H) with hQb
  set s := oκ _ (barPair h h2 hwF) with hs
  have hFK : ringChar h.fixedField ≠ 2 := two_ne_zero_fixedField h hp2
  have h2F : (2 : h.fixedField) ≠ 0 := Ring.two_ne_zero hFK
  have hperfH : ⁅M.subgroupOf H, M.subgroupOf H⁆ = M.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hd.le, hd.perf]
  have hfixP : ∀ X ∈ M.subgroupOf H, s (projH H X) = projH H X :=
    fun X hX => hQs ⟨X, hX, rfl⟩
  have hbar : ∀ X ∈ M, ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar = X := by
    intro X hX
    have e := kappa_eq_of_fix (barPair h h2 hwF) hperfH hfixP (X := ⟨X, hd.le hX⟩)
      (mem_subgroupOf.2 hX)
    rw [barPair_left, barPair_right, inv_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_one] at e
    exact e
  have hiso : ∀ X ∈ M, X ∈ CatalogueBGraphForm.isometryGroup d K (diagGL (wK_ne_zero h hwF)) :=
    fun X hX => C.matrixDerived_le_isometryGroup _ h2 (hd.le hX)
  have hMΩ := le_omegaF h hwF hd.perf hiso hbar
  have hΩH := omegaF_le h h2 hwF
  set Pω := ((omegaF h hwF).subgroupOf H).map (projH H) with hPω
  have hQP : Qb ≤ Pω := map_mono fun g hg => mem_subgroupOf.2 (hMΩ (mem_subgroupOf.1 hg))
  have hPs : Pω ≤ autFixed s := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_autFixed_iff, hs, kappa_proj]
    congr 1
    apply Subtype.ext
    rw [matrixDerivedConjugation_val, barPair_left, barPair_right, inv_one, one_mul, mul_one]
    apply Units.ext
    rw [coe_glFieldAut]
    obtain ⟨g₀, -, hg₀⟩ := mem_subgroupOf.1 hg
    rw [← hg₀, coe_iotaF]
    exact U.map_bar_fmap h _
  have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs hQc
  set ψ : omegaR (diagGL hwF) →* H :=
    { toFun := fun x => ⟨iotaF h x, hΩH ⟨x, x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp } with hψ
  set φ := (projH H).comp ψ with hφ
  have hφr : φ.range = Pω := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ψ x, mem_subgroupOf.2 ⟨x, x.2, rfl⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨g₀, hg₀, hg₀e⟩ := mem_subgroupOf.1 hg
      exact ⟨⟨g₀, hg₀⟩, by
        change projH H (ψ ⟨g₀, hg₀⟩) = projH H g
        congr 1
        exact Subtype.ext hg₀e⟩
  rcases orth_block_cases hFK (by omega : 3 ≤ d) (diagGL hwF)
      (diagGL_transpose hwF) with hsol | hqs | ⟨h84, -⟩
  · have : Group.IsSolvable φ.range := by
      have := hsol
      exact Group.isSolvable_of_surjective φ.rangeRestrict_surjective
    rw [hφr] at this
    exact C.not_le_of_isSolvable hQP hQc' this hQP
  · rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hqs φ with hb | hqr
    · rw [hφr] at hb
      rw [hb] at hQP
      exact C.ne_bot_of_isPComponent hQs hQc (le_bot_iff.1 hQP)
    · rw [hφr] at hqr
      have heq := C.eq_of_le_of_isQuasisimple hQP le_rfl hQc' hqr
      have hlift : ∀ g (hg : g ∈ omegaF h hwF), ∃ m ∈ M.subgroupOf H, ∃ z ∈ center H,
          (⟨g, hΩH hg⟩ : H) = m * z := by
        intro g hg
        have hgP : projH H ⟨g, hΩH hg⟩ ∈ Qb := by
          rw [heq]
          exact ⟨⟨g, hΩH hg⟩, mem_subgroupOf.2 hg, rfl⟩
        obtain ⟨m, hm, hmg⟩ := hgP
        exact ⟨m, hm, m⁻¹ * ⟨g, hΩH hg⟩,
          scalars_subgroupOf_le_center ((projH_eq_projH_iff).1 hmg), by group⟩
      have hperfΩ : ⁅omegaF h hwF, omegaF h hwF⁆ = omegaF h hwF := by
        rw [omegaF, ← Subgroup.map_commutator]
        congr 1
        exact Subgroup.isPerfect_iff.1 hqs.1
      have hΩM : omegaF h hwF ≤ M := by
        rw [← hperfΩ, commutator_le]
        intro a ha b hb
        obtain ⟨m₁, hm₁, z₁, hz₁, e₁⟩ := hlift a ha
        obtain ⟨m₂, hm₂, z₂, hz₂, e₂⟩ := hlift b hb
        have e : ⁅(⟨a, hΩH ha⟩ : H), ⟨b, hΩH hb⟩⁆ = ⁅m₁, m₂⁆ := by
          rw [e₁, e₂, commutatorElement_mul_mem_center m₁ m₂ hz₁ hz₂]
        have e' := congrArg Subtype.val e
        change ⁅a, b⁆ = ⁅(m₁ : GL (Fin d) K), (m₂ : GL (Fin d) K)⁆ at e'
        rw [e', ← hd.perf]
        exact commutator_mem_commutator (mem_subgroupOf.1 hm₁) (mem_subgroupOf.1 hm₂)
      obtain ⟨-, I₀, hI₀3, -, hI₀w⟩ := id hNF
      obtain ⟨T, hTI₀, hT2⟩ := Finset.exists_subset_card_eq (show 2 ≤ I₀.card by omega)
      have hTF := signGL_mem_oBlock_of_even hwF (Finset.subset_univ I₀) hI₀w 1 T hTI₀
        (by omega)
      have hTΩ : iotaF h (signGL h.fixedField T) ∈ omegaF h hwF :=
        ⟨_, oBlock_le hwF _ hTF, rfl⟩
      have hTK : iotaF h (signGL h.fixedField T) = signGL K T := by
        apply Units.ext
        rw [coe_iotaF, coe_signGL, coe_signGL, signMat, signMat, diagonal_map (map_zero _)]
        congr 1
        funext i
        split_ifs <;> simp
      rw [hTK] at hTΩ
      have hTM := hΩM hTΩ
      have hTT : signGL K T * signGL K T = 1 := Units.ext (PSL.signMat_mul_self T)
      obtain ⟨t, ht⟩ : T.Nonempty := by
        rw [← Finset.card_pos]
        omega
      obtain ⟨t', ht'⟩ : Tᶜ.Nonempty := by
        rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
        omega
      rcases hd.inv _ hTM hTT with e | e
      · have e' := congrArg (fun B : GL (Fin d) K => (B : Matrix (Fin d) (Fin d) K) t t) e
        simp only [coe_signGL, Units.val_one, signMat, diagonal_apply_eq, one_apply_eq, ht,
          ↓reduceIte] at e'
        exact h2 (by linear_combination -e')
      · have e' := congrArg (fun B : GL (Fin d) K => (B : Matrix (Fin d) (Fin d) K) t' t') e
        simp only [coe_signGL, Units.val_neg, Units.val_one, signMat, diagonal_apply_eq,
          Matrix.neg_apply, one_apply_eq, Finset.mem_compl.1 ht', ↓reduceIte] at e'
        exact h2 (by linear_combination e')
  · omega

end CFSG.ComponentClassification.Burgoyne.DX.Kl
