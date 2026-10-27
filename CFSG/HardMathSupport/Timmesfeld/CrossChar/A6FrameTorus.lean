module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6FrameCore
public import CFSG.RankThree.PartOne.KE.SLnFamily
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)
open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable {τ : Tag}

variable {nd : Fin 6 → Fin τ.rank} (hD : A6ChainData τ nd) (hF : A6ChainFrames τ nd)
  {L : Type} [Field L]

section Diagonal

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

@[expose] def hEntries7 (t : Fin 6) (s : Lˣ) (i : Fin 7) : L :=
  if i = t.castSucc then (s : L) else if i = t.succ then ((s⁻¹ : Lˣ) : L) else 1

theorem coe_blockSL2_HSL_a6 (t : Fin 6) (s : Lˣ) :
    ((blockSL2 L 6 t (HSL s) : SL(7, L)) : Matrix (Fin 7) (Fin 7) L) =
      Matrix.diagonal (hEntries7 t s) := by
  rw [blockSL2, coe_blockSL]
  ext a b
  fin_cases t <;> fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, HSL, hEntries7]

theorem a6Frame_blockSL2_HSL (t : Fin 6) (s : Lˣ) :
    a6Frame hD hF L (blockSL2 L 6 t (HSL s)) = torusElt τ L (nd t) s := by
  rw [← MonoidHom.comp_apply, a6Frame_comp_blockSL2, simpleRootSL2_HSL]

theorem exists_diag_eq_prod_a6 (A : SL(7, L))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 7) (Fin 7) L) i j = 0) :
    ∃ s : Fin 6 → Lˣ, A = blockSL2 L 6 0 (HSL (s 0)) * blockSL2 L 6 1 (HSL (s 1)) *
      blockSL2 L 6 2 (HSL (s 2)) * blockSL2 L 6 3 (HSL (s 3)) * blockSL2 L 6 4 (HSL (s 4)) *
      blockSL2 L 6 5 (HSL (s 5)) := by
  have hdiag : (A : Matrix (Fin 7) (Fin 7) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 7) (Fin 7) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, (A : Matrix (Fin 7) (Fin 7) L) i i = 1 := by
    have h := A.2
    rwa [hdiag, Matrix.det_diagonal] at h
  have hne : ∀ i, (A : Matrix (Fin 7) (Fin 7) L) i i ≠ 0 := by
    intro i h0
    have : ∏ j, (A : Matrix (Fin 7) (Fin 7) L) j j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at this
    exact one_ne_zero this
  set u : Fin 7 → Lˣ := fun i => Units.mk0 _ (hne i) with hu
  refine ⟨![u 0, u 0 * u 1, u 0 * u 1 * u 2, u 0 * u 1 * u 2 * u 3,
    u 0 * u 1 * u 2 * u 3 * u 4, u 0 * u 1 * u 2 * u 3 * u 4 * u 5], ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_HSL_a6, Matrix.diagonal_mul_diagonal]
  rw [hdiag]
  congr 1
  funext i
  have h6 : (A : Matrix (Fin 7) (Fin 7) L) 6 6 =
      ((u 0 * u 1 * u 2 * u 3 * u 4 * u 5)⁻¹ : Lˣ) := by
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [Fin.prod_univ_seven] at hdet
    simp only [hu, Units.val_mul, Units.val_mk0]
    linear_combination hdet
  have n0 := hne 0
  have n1 := hne 1
  have n2 := hne 2
  have n3 := hne 3
  have n4 := hne 4
  have n5 := hne 5
  fin_cases i <;> simp [hEntries7, h6, hu] <;> field_simp

theorem a6Frame_diag_mem_torusGroup (A : SL(7, L))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 7) (Fin 7) L) i j = 0) :
    a6Frame hD hF L A ∈ torusGroup τ L := by
  obtain ⟨s, rfl⟩ := exists_diag_eq_prod_a6 A hA
  simp only [map_mul, a6Frame_blockSL2_HSL]
  have hmem : ∀ (t : Fin 6) (s : Lˣ), torusElt τ L (nd t) s ∈ torusGroup τ L :=
    fun t s => Subgroup.subset_closure ⟨(nd t, s), rfl⟩
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (hmem _ _) (hmem _ _)) (hmem _ _))
    (hmem _ _)) (hmem _ _)) (hmem _ _)

end Diagonal

section Injective

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)

private theorem eq_prod_of_scalar_a6 {u : Lˣ} (hu : u ^ 7 = 1) {A : SL(7, L)}
    (hA : (A : Matrix (Fin 7) (Fin 7) L) = Matrix.scalar (Fin 7) (u : L)) :
    A = blockSL2 L 6 0 (HSL (u ^ 1)) * blockSL2 L 6 1 (HSL (u ^ 2)) *
        blockSL2 L 6 2 (HSL (u ^ 3)) * blockSL2 L 6 3 (HSL (u ^ 4)) *
        blockSL2 L 6 4 (HSL (u ^ 5)) * blockSL2 L 6 5 (HSL (u ^ 6)) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL2_HSL_a6,
    Matrix.diagonal_mul_diagonal]
  rw [hA, Matrix.scalar_apply]
  congr 1
  funext i
  have hu7 : (u : L) ^ 7 = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hu0 : (u : L) ≠ 0 := u.ne_zero
  fin_cases i <;> simp [hEntries7] <;> field_simp
  linear_combination hu7

theorem a6Frame_injective (j₀ : Fin τ.rank)
    (hj₀ : ∀ t : Fin 6, τ.cartan (nd t) j₀ = if t = 2 then -1 else 0) :
    Function.Injective (a6Frame hD hF L) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hc : A ∈ Subgroup.center SL(7, L) := ker_a6Frame_le_center hD hF hA
  obtain ⟨r, hr7, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [Fintype.card_fin] at hr7
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr7
  set u : Lˣ := Units.mk0 r hr0 with hudef
  have hu7 : u ^ 7 = 1 := Units.ext (by simp [hudef, hr7])
  have hA' : (A : Matrix (Fin 7) (Fin 7) L) = Matrix.scalar (Fin 7) (u : L) := by
    rw [← hrA]
    rfl
  rw [eq_prod_of_scalar_a6 hu7 hA'] at hA
  simp only [map_mul, a6Frame_blockSL2_HSL, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul] at hA
  set a : Fin τ.rank → Lˣ := (fun j => (u ^ 1) ^ τ.cartan (nd 0) j) *
    (fun j => (u ^ 2) ^ τ.cartan (nd 1) j) * (fun j => (u ^ 3) ^ τ.cartan (nd 2) j) *
    (fun j => (u ^ 4) ^ τ.cartan (nd 3) j) * (fun j => (u ^ 5) ^ τ.cartan (nd 4) j) *
    (fun j => (u ^ 6) ^ τ.cartan (nd 5) j) with ha
  have haj : a j₀ = (u ^ 3)⁻¹ := by
    simp only [ha, Pi.mul_apply, hj₀]
    simp
  have hconj := (root_diagonal_conjugation τ L a).1 j₀ 1
  rw [hA, one_mul, inv_one, mul_one, haj, mul_one, ← pinnedX_single, ← pinnedX_single] at hconj
  have h3 : ((u ^ 3)⁻¹ : Lˣ) = 1 := Units.ext (pinnedX_injective τ L _ hconj).symm
  have h3' : u ^ 3 = 1 := inv_eq_one.1 h3
  have hu1 : u = 1 := by
    have : u = u ^ 7 * ((u ^ 3) ^ 2)⁻¹ := by group
    rw [this, hu7, h3']
    simp
  apply Subtype.ext
  rw [hA', hu1]
  simp

end Injective

@[expose] def a6Roots (nd : Fin 6 → Fin τ.rank) : Set (Fin τ.rank → ℤ) :=
  {r | ∃ a b : Fin 7, a ≠ b ∧ r = chainRoot nd a b}

theorem a6Frame_range : (a6Frame hD hF L).range = rootSpan τ L (a6Roots nd) := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation
      (n := 7) (K := L), MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, t, rfl⟩, rfl⟩
    obtain ⟨ε, hε⟩ := a6Frame_transv hD hF (L := L) i j hij
    rw [hε]
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ a6Roots nd) => rootSubgroup τ L γ)
      (chainRoot nd i j) ⟨i, j, hij, rfl⟩ le_rfl (Subgroup.subset_closure ⟨_, rfl⟩)
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b, hab, rfl⟩ := hγ
    obtain ⟨ε, hε⟩ := a6Frame_transv hD hF (L := L) a b hab
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    refine ⟨Matrix.SpecialLinearGroup.transvection hab (((ε⁻¹ : Lˣ) : L) * c), ?_⟩
    rw [hε]
    congr 1
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

variable (L) in
@[expose] noncomputable def rhoA6 (v : WeylGroup τ) : SL(7, L) →* ModGL τ L :=
  (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom.comp (a6Frame hD hF L)

@[expose] def sigmaA6 (nd : Fin 6 → Fin τ.rank) (v : WeylGroup τ) (a b : Fin 7) :
    Fin τ.rank → ℤ :=
  v • chainRoot nd a b

@[expose] def a6SigmaRoots (nd : Fin 6 → Fin τ.rank) (v : WeylGroup τ) :
    Set (Fin τ.rank → ℤ) :=
  {r | ∃ a b : Fin 7, a ≠ b ∧ r = sigmaA6 nd v a b}

theorem rhoA6_apply (v : WeylGroup τ) (X : SL(7, L)) :
    rhoA6 hD hF L v X = canonicalRep (coxeterSystem τ) L v * a6Frame hD hF L X *
      (canonicalRep (coxeterSystem τ) L v)⁻¹ := by
  simp [rhoA6, MulAut.conj_apply]

theorem rhoA6_injective (v : WeylGroup τ) (h : Function.Injective (a6Frame hD hF L)) :
    Function.Injective (rhoA6 hD hF L v) :=
  (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).injective.comp h

include hD in
theorem isRoot_sigmaA6 (v : WeylGroup τ) {a b : Fin 7} (hab : a ≠ b) :
    IsRoot τ (sigmaA6 nd v a b) :=
  IsRoot.smul (hD.isRoot a b hab) v

theorem sigmaA6_neg (v : WeylGroup τ) (a b : Fin 7) :
    sigmaA6 nd v b a = -sigmaA6 nd v a b := by
  rw [sigmaA6, sigmaA6, CFSG.RankThree.E6.chainRoot_swap, smul_neg]

include hD in
theorem sigmaA6_add (v : WeylGroup τ) (a b c : Fin 7) :
    sigmaA6 nd v a b + sigmaA6 nd v b c = sigmaA6 nd v a c := by
  rw [sigmaA6, sigmaA6, sigmaA6, ← smul_add, hD.add]

theorem rhoA6_transvection (v : WeylGroup τ) (a b : Fin 7) (hab : a ≠ b) :
    ∃ ε : Lˣ, ∀ t : L, rhoA6 hD hF L v (Matrix.SpecialLinearGroup.transvection hab t) =
      pinnedX τ L (sigmaA6 nd v a b) ((ε : L) * t) := by
  obtain ⟨ε₀, h₀⟩ := a6Frame_transv hD hF (L := L) a b hab
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v)
    (hD.isRoot a b hab)
  have hπ : weylQuotientHom τ L ⟨canonicalRep (coxeterSystem τ) L v,
      canonicalRep_mem_monomialSubgroup L v⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  refine ⟨μ * ε₀, fun t => ?_⟩
  rw [rhoA6_apply, h₀, hμ, hπ, Units.val_mul, mul_assoc]
  rfl

theorem rhoA6_range (v : WeylGroup τ) :
    (rhoA6 hD hF L v).range = rootSpan τ L (a6SigmaRoots nd v) := by
  rw [rhoA6, MonoidHom.range_comp, a6Frame_range,
    map_conj_rootSpan v (fun γ hγ => by obtain ⟨a, b, hab, rfl⟩ := hγ; exact hD.isRoot a b hab)]
  congr 1
  ext r
  constructor
  · rintro ⟨γ, ⟨a, b, hab, rfl⟩, rfl⟩
    exact ⟨a, b, hab, rfl⟩
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨chainRoot nd a b, ⟨a, b, hab, rfl⟩, rfl⟩

theorem rhoA6_torus (v : WeylGroup τ) (b : Fin τ.rank → Lˣ) :
    ∃ d : Fin 7 → Lˣ, ∀ A : SL(7, L), rootDiagUnit τ b * rhoA6 hD hF L v A *
      (rootDiagUnit τ b)⁻¹ = rhoA6 hD hF L v (conjDiagn d A) := by
  set d : Fin 7 → Lˣ := fun i => rootChar b (sigmaA6 nd v i 0) with hd
  refine ⟨d, fun A => ?_⟩
  have h : (MulAut.conj (rootDiagUnit τ b)).toMonoidHom.comp (rhoA6 hD hF L v) =
      (rhoA6 hD hF L v).comp (conjDiagnHom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 7) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := rhoA6_transvection hD hF (L := L) v i j hij
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiagnHom_apply]
    rw [hε, conjDiagn_transvection, hε, rootDiagUnit_conj_pinnedX b (isRoot_sigmaA6 hD v hij)]
    congr 1
    have hsub : sigmaA6 nd v i j = sigmaA6 nd v i 0 - sigmaA6 nd v j 0 := by
      rw [← sigmaA6_add hD v i 0 j, sigmaA6_neg v j 0]
      abel
    rw [hsub, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun h A

theorem rhoA6_diagonal (v : WeylGroup τ) (A : SL(7, L))
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 7) (Fin 7) L) i j = 0) :
    rhoA6 hD hF L v A ∈ torusGroup τ L := by
  rw [rhoA6_apply]
  exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1
    (a6Frame_diag_mem_torusGroup hD hF A hA)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
