module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSFourU
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.RankThree.PartOne.KE
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section Frame

variable {τ : Tag} {L : Type} [Field L] {ν : ℕ}
  {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem frame_ker_le_center (hν : 3 ≤ ν) (hψ : IsSLFrame ψ σ) :
    ψ.ker ≤ Subgroup.center SL(ν, L) := by
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
    rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  intro κ hκ
  exact mem_center_SL_of_commute hν ψ hker fun X => by
    rw [MonoidHom.mem_ker.1 hκ, one_mul, mul_one]

theorem center_le_diagSL : Subgroup.center SL(ν, L) ≤ diagSL ν L := by
  intro A hA i j hij
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [← hr]
  simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem conjDiagn_of_mem_diagSL (d : Fin ν → Lˣ) {δ : SL(ν, L)} (hδ : δ ∈ diagSL ν L) :
    conjDiagn d δ = δ := by
  obtain ⟨x, hx, rfl⟩ := exists_units_of_mem_diagSL hδ
  apply Subtype.ext
  rw [coe_conjDiagn, coe_diagSLOf]
  change Matrix.diagonal (fun k => (d k : L)) * Matrix.diagonal (fun k => (x k : L)) *
    Matrix.diagonal (fun k => (((d k)⁻¹ : Lˣ) : L)) = _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  simp only [Units.val_inv_eq_inv_val]
  have h0 : (d k : L) ≠ 0 := Units.ne_zero _
  field_simp

theorem frame_diag_mem_torusGroup [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) (hν : 0 < ν) {ψ : SL(ν, L) →* ModGL Tag.E6 L}
    {σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ) {δ : SL(ν, L)}
    (hδ : δ ∈ diagSL ν L) : ψ δ ∈ torusGroup Tag.E6 L := by
  classical
  haveI : NeZero ((3 : ℕ) : L) := ⟨h3⟩
  obtain ⟨ω₀, hω₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ω₀ := hω₀.isUnit (by norm_num)
  set ω : Lˣ := hu.unit with hωdef
  have hωprim : IsPrimitiveRoot ω 3 :=
    IsPrimitiveRoot.coe_units_iff.1 (by rw [hωdef, IsUnit.unit_spec]; exact hω₀)
  have hω : orderOf ω = 3 := hωprim.eq_orderOf.symm
  have hcomm : ∀ x : Fin Tag.E6.rank → ZMod 3, Commute (dV ω x) (ψ δ) := fun x => by
    have h := hψ.torus ⟨0, hν⟩ (torV ω x) δ
    rw [conjDiagn_of_mem_diagSL _ hδ] at h
    change rootDiagUnit Tag.E6 (torV ω x) * ψ δ = ψ δ * rootDiagUnit Tag.E6 (torV ω x)
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  exact mem_torusGroup_of_commute_dV hω (hψ.range_le_adjointGroup ⟨δ, rfl⟩) hcomm

theorem exists_unit_pow_ne_one [Infinite L] {n : ℕ} (hn : 0 < n) : ∃ s : Lˣ, s ^ n ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (insert (0 : L) (Polynomial.nthRoots n (1 : L)).toFinset)
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
  have h1 : c ^ n = 1 := by simpa using congrArg (fun u : Lˣ => (u : L)) h
  exact Finset.mem_insert_of_mem (by simpa [Polynomial.mem_nthRoots hn] using h1)

@[expose] def twoDiag (i j : Fin ν) (s : Lˣ) : Fin ν → Lˣ :=
  fun k => if k = i then s else if k = j then s⁻¹ else 1

theorem prod_twoDiag {i j : Fin ν} (hij : i ≠ j) (s : Lˣ) : ∏ k, twoDiag i j s k = 1 := by
  classical
  rw [Finset.prod_eq_mul i j hij]
  · simp [twoDiag, hij.symm]
  · intro k _ hk
    simp [twoDiag, hk.1, hk.2]
  · intro h
    exact absurd (Finset.mem_univ i) h
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem frame_hc2 [Infinite L] (hker : ψ.ker ≤ Subgroup.center SL(ν, L)) {y : SL(ν, L)}
    (hy : ∀ δ ∈ diagSL ν L, ψ y * ψ δ = ψ δ * ψ y) : y ∈ diagSL ν L := by
  classical
  intro i j hij
  by_contra hyij
  obtain ⟨s, hs⟩ := exists_unit_pow_ne_one (L := L) (n := 2 * ν) (by omega)
  set δ : SL(ν, L) := diagSLOf (twoDiag i j s) (prod_twoDiag hij s) with hδdef
  have hδ : δ ∈ diagSL ν L := diagSLOf_mem _ _
  have hκ : y * δ * y⁻¹ * δ⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hy δ hδ]
    group
  obtain ⟨r, hr, hrκ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hker hκ)
  rw [Fintype.card_fin] at hr
  have hyδ : y * δ = (y * δ * y⁻¹ * δ⁻¹) * δ * y := by group
  have h1 := congrArg (fun A : SL(ν, L) => (A : Matrix (Fin ν) (Fin ν) L) i j) hyδ
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← hrκ] at h1
  rw [hδdef, coe_diagSLOf, Matrix.mul_diagonal, Matrix.mul_assoc, Matrix.scalar_apply] at h1
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul] at h1
  have hj : twoDiag i j s j = s⁻¹ := by simp [twoDiag, hij.symm]
  have hi : twoDiag i j s i = s := by simp [twoDiag]
  rw [hj, hi] at h1
  have h2 : ((s⁻¹ : Lˣ) : L) = r * (s : L) := by
    have h3 : (y : Matrix (Fin ν) (Fin ν) L) i j * ((s⁻¹ : Lˣ) : L) =
        (y : Matrix (Fin ν) (Fin ν) L) i j * (r * (s : L)) := by
      rw [h1]; ring
    exact mul_left_cancel₀ hyij h3
  have h0 : (s : L) ≠ 0 := Units.ne_zero _
  rw [Units.val_inv_eq_inv_val] at h2
  have h4 : r = ((s : L) ^ 2)⁻¹ := by
    field_simp at h2 ⊢
    linear_combination -h2
  apply hs
  apply Units.ext
  rw [h4, inv_pow, ← pow_mul] at hr
  have h5 : ((s : L) ^ (2 * ν))⁻¹ = 1 := hr
  rw [inv_eq_one] at h5
  simpa using h5

end Frame

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
