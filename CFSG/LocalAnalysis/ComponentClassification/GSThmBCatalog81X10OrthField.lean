module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthSign
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT2

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.DX
open CFSG.ComponentClassification.Burgoyne.C (omegaR orth_block_cases)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat OrthNF)

variable {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)

theorem false_of_field [Finite K] (hK : ringChar K ≠ 2) (hp2 : p ≠ 2) {d : ℕ} (hd : 7 ≤ d)
    {wF : Fin d → h.fixedField} (hNF : OrthNF wF) {M : Subgroup (GL (Fin d) K)} {Q : ℕ}
    (hd' : X10Data (diagGL (wK_ne_zero h hNF.1)) (barPair h (Ring.two_ne_zero hK) hNF.1) M Q) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hwF := hNF.1
  set H := matrixDerived (oQ (diagGL (wK_ne_zero h hwF))) with hH
  set Qb := (M.subgroupOf H).map (projH H) with hQb
  set s := oκ _ (barPair h h2 hwF) with hs
  have hFK : ringChar h.fixedField ≠ 2 := two_ne_zero_fixedField h hp2
  have hperfH : ⁅M.subgroupOf H, M.subgroupOf H⁆ = M.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hd'.le, hd'.perf]
  have hfixP : ∀ X ∈ M.subgroupOf H, s (projH H X) = projH H X :=
    fun X hX => hd'.fix ⟨X, hX, rfl⟩
  have hbar : ∀ X ∈ M, ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar = X := by
    intro X hX
    have e := kappa_eq_of_fix (barPair h h2 hwF) hperfH hfixP (X := ⟨X, hd'.le hX⟩)
      (mem_subgroupOf.2 hX)
    rw [barPair_left, barPair_right, inv_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_one] at e
    exact e
  have hiso : ∀ X ∈ M, X ∈ CatalogueBGraphForm.isometryGroup d K (diagGL (wK_ne_zero h hwF)) :=
    fun X hX => C.matrixDerived_le_isometryGroup _ h2 (hd'.le hX)
  have hMΩ := le_omegaF h hwF hd'.perf hiso hbar
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
  have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs hd'.comp
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
  have heq : Qb = Pω := by
    rcases orth_block_cases hFK (by omega : 3 ≤ d) (diagGL hwF)
        (diagGL_transpose hwF) with hsol | hqs | ⟨h84, -⟩
    · have : Group.IsSolvable φ.range := by
        have := hsol
        exact Group.isSolvable_of_surjective φ.rangeRestrict_surjective
      rw [hφr] at this
      exact (C.not_le_of_isSolvable hQP hQc' this hQP).elim
    · rcases LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hqs φ with hb | hqr
      · rw [hφr] at hb
        rw [hb] at hQP
        exact (C.ne_bot_of_isPComponent hd'.fix hd'.comp (le_bot_iff.1 hQP)).elim
      · rw [hφr] at hqr
        exact C.eq_of_le_of_isQuasisimple hQP le_rfl hQc' hqr
    · omega
  obtain ⟨-, I₀, hI₀3, hI₀c, hI₀w⟩ := id hNF
  have hI₀4 : 4 ≤ I₀.card := by
    have hle : I₀ᶜ.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      exact hI₀c x y (Finset.mem_compl.1 hx) (Finset.mem_compl.1 hy)
    rw [Finset.card_compl, Fintype.card_fin] at hle
    omega
  obtain ⟨T, hTI₀, hT4⟩ := Finset.exists_subset_card_eq hI₀4
  obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩ := Finset.card_eq_four.1 hT4
  have hmem : ∀ x ∈ ({i, j, k, l} : Finset (Fin d)), x ∈ I₀ := fun x hx => hTI₀ hx
  have hi₀ := hmem i (by simp)
  have hj₀ := hmem j (by simp)
  have hk₀ := hmem k (by simp)
  have hl₀ := hmem l (by simp)
  have hsign : ∀ x y : Fin d, x ∈ I₀ → y ∈ I₀ → x ≠ y →
      ∃ hS : signGL K {x, y} ∈ H, projH H ⟨signGL K {x, y}, hS⟩ ∈ Qb := by
    intro x y hx hy hxy
    have hTF := DX.signGL_mem_oBlock_of_even hwF (Finset.subset_univ I₀) hI₀w 1 {x, y}
      (fun z hz => by
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx
        · exact hy) (by rw [Finset.card_pair hxy])
    have hTΩ : iotaF h (signGL h.fixedField {x, y}) ∈ omegaF h hwF :=
      ⟨_, oBlock_le hwF _ hTF, rfl⟩
    have hTK : iotaF h (signGL h.fixedField {x, y}) = signGL K {x, y} := by
      apply Units.ext
      rw [coe_iotaF, coe_signGL, coe_signGL, signMat, signMat, diagonal_map (map_zero _)]
      congr 1
      funext i
      split_ifs <;> simp
    rw [hTK] at hTΩ
    refine ⟨hΩH hTΩ, ?_⟩
    rw [heq]
    exact ⟨⟨signGL K {x, y}, hΩH hTΩ⟩, mem_subgroupOf.2 hTΩ, rfl⟩
  obtain ⟨hXH, hX⟩ := hsign i j hi₀ hj₀ hij
  obtain ⟨hYH, hY⟩ := hsign i k hi₀ hk₀ hik
  obtain ⟨hZH, hZ⟩ := hsign i l hi₀ hl₀ hil
  exact hd'.false_of_e8 hX hY hZ
    (e8Triple_sign h2 hXH hYH hZH (e8Sets (by omega) hij hik hil hjk hjl hkl))

end CFSG.ComponentClassification.GSThmB.X10Orth
