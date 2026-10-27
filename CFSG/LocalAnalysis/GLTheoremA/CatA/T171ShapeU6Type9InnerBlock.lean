module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9InnerBasic
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Shape

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.StandardType CFSG.StandardType.TableBUD
open CFSG.StandardType.TableBUE CFSG.StandardType.Line63.H5 CFSG.SectionRank.OddCover

variable {K : Type} [Field K] {n d : ℕ}

theorem isComponentOf_map_blockSU_of_fiber [Finite K] (h : UnitaryFieldData 2 n K)
    {τ : Fin d → Kˣ}
    (hD : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {v : Kˣ} {S : Finset (Fin d)} (hS : ∀ i, i ∈ S ↔ τ i = v)
    (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ n) ≠ (3, 2)) :
    IsComponentOf ((blockSU (n := n) S).map (LargeEvenProjMk (unitarySU 2 n K d)))
      (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩)) := by
  classical
  set π := LargeEvenProjMk (unitarySU 2 n K d) with hπ
  set C := ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩) with hC
  have hτS : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j := fun i hi j hj => by
    rw [(hS i).mp hi, (hS j).mp hj]
  have hNC : (blockSU (n := n) S).map π ≤ (cenSU (n := n) (diagHom d τ)).map π :=
    Subgroup.map_mono (blockSU_le_cenSU hτS)
  have hCC : (cenSU (n := n) (diagHom d τ)).map π ≤ C := by
    rintro _ ⟨s, hs, rfl⟩
    exact mk_mem_ggFix_of_mem_cenSU hD hs
  have hN : (((blockSU (n := n) S).map π).subgroupOf
      ((cenSU (n := n) (diagHom d τ)).map π)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨s, hs, hsg⟩ := g.2
    refine ⟨s * t * s⁻¹, conj_mem_blockSU_of_commute hS (mem_cenSU.mp hs) ht, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hsg, htx]
  have hC' : ((cenSU (n := n) (diagHom d τ)).map π).subgroupOf C |>.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨s, hsg⟩ := QuotientGroup.mk_surjective (g : LargeEvenProj (unitarySU 2 n K d))
    have hgC : (g : LargeEvenProj (unitarySU 2 n K d)) ∈ C := g.2
    rw [← hsg] at hgC
    obtain ⟨c, hs⟩ := exists_conj_eq_scalar_mul hD hgC
    have hπs : π s = (g : LargeEvenProj (unitarySU 2 n K d)) := hsg
    refine ⟨s * t * s⁻¹, conj_mem_cenSU hs ht, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hπs, htx]
  refine ⟨hNC.trans hCC, ?_, ?_⟩
  · exact IsSubnormal.step hNC hN (IsSubnormal.step hCC hC' (IsSubnormal.refl C))
  · exact SURepair.isQuasisimple_map_of_isQuasisimple ker_projMk_le_center
      (isQuasisimple_blockSU S h h.card_eq_sq hS3 hSq)

theorem layer_eq_map_blockSU_of_fiber [Finite K] (h : UnitaryFieldData 2 n K)
    {τ : Fin d → Kˣ}
    (hD : diagHom d τ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {v : Kˣ} {S : Finset (Fin d)} (hS : ∀ i, i ∈ S ↔ τ i = v)
    (hS3 : 3 ≤ S.card) (hSq : (S.card, 2 ^ n) ≠ (3, 2))
    (hcomp : IsComponentOf
      (LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩)))
      (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩))) :
    LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩)) =
      (blockSU (n := n) S).map (LargeEvenProjMk (unitarySU 2 n K d)) := by
  have h1 := isComponentOf_map_blockSU_of_fiber h hD hS hS3 hSq
  have hle : (blockSU (n := n) S).map (LargeEvenProjMk (unitarySU 2 n K d)) ≤
      LargeEvenLayer (ggFix (TableB.projConj (unitarySU 2 n K d) ⟨diagHom d τ, hD⟩)) :=
    le_sSup h1
  exact (eq_of_isComponentOf_of_isQuasisimple (h1.of_le_of_le hle hcomp.1) hcomp.2.2).symm

theorem fiber_card_eq_of_mul [DecidableEq K] {τ : Fin d → Kˣ} {c : Kˣ} {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ i, τ (σ i) = c * τ i) (u : Kˣ) :
    (fiber τ u).card = (fiber τ (c * u)).card := by
  classical
  have h := card_filter_shift σ (fun _ => True) τ c (fun _ => Iff.rfl) hσ u
  simpa [fiber] using h

theorem eq_one_of_conj_diag_eq_scalar [DecidableEq K] {τ : Fin 6 → Kˣ} {N : GL (Fin 6) K}
    {c : Kˣ}
    (hND : (N : Matrix (Fin 6) (Fin 6) K) * (diagHom 6 τ : Matrix (Fin 6) (Fin 6) K) =
      (c : K) • ((diagHom 6 τ : Matrix (Fin 6) (Fin 6) K) * (N : Matrix (Fin 6) (Fin 6) K)))
    (hdet : (N : Matrix (Fin 6) (Fin 6) K).det ≠ 0) (hc3 : c ^ 3 = 1)
    {v : Kˣ} {S : Finset (Fin 6)} (hS : ∀ i, i ∈ S ↔ τ i = v) (hS4 : 4 ≤ S.card) :
    c = 1 := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_ne_zero_of_det hdet
  have hentry : ∀ i j, (N : Matrix (Fin 6) (Fin 6) K) i j ≠ 0 → τ j = c * τ i := by
    intro i j hij
    have h1 : ((N : Matrix (Fin 6) (Fin 6) K) *
        (diagHom 6 τ : Matrix (Fin 6) (Fin 6) K)) i j =
        ((c : K) • ((diagHom 6 τ : Matrix (Fin 6) (Fin 6) K) *
          (N : Matrix (Fin 6) (Fin 6) K))) i j := by
      rw [hND]
    rw [coe_diagHom, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_mul] at h1
    refine Units.ext ?_
    have h2 : (N : Matrix (Fin 6) (Fin 6) K) i j * (τ j : K) =
        (N : Matrix (Fin 6) (Fin 6) K) i j * ((c : K) * (τ i : K)) := by
      rw [h1]
      ring
    exact mul_left_cancel₀ hij h2
  have hτσ : ∀ i, τ (σ i) = c⁻¹ * τ i := by
    intro i
    have h1 : τ i = c * τ (σ i) := hentry (σ i) i (hσ i)
    refine Units.ext ?_
    have h2 : (τ i : K) = (c : K) * (τ (σ i) : K) := by
      rw [← Units.val_mul]
      exact congrArg (fun u : Kˣ => (u : K)) h1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [h2, ← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
  have hfiber : ∀ u : Kˣ, (fiber τ u).card = (fiber τ (c⁻¹ * u)).card :=
    fun u => fiber_card_eq_of_mul hτσ u
  by_contra hc1
  have hc2 : c ^ 2 ≠ 1 := by
    intro h2
    have h1 : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have h3 : orderOf c ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hc3
    have h4 : orderOf c ∣ 1 := by
      have := Nat.dvd_gcd h1 h3
      simpa using this
    exact hc1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4))
  have hne12 : v ≠ c⁻¹ * v := by
    intro h'
    have h3 : v * v⁻¹ = (c⁻¹ * v) * v⁻¹ := congrArg (fun w => w * v⁻¹) h'
    rw [mul_inv_cancel, mul_inv_cancel_right] at h3
    exact hc1 (inv_eq_one.mp h3.symm)
  have hne13 : v ≠ c⁻¹ * (c⁻¹ * v) := by
    intro h'
    have h3 : c⁻¹ * c⁻¹ = 1 := by
      have h4 : v * v⁻¹ = (c⁻¹ * (c⁻¹ * v)) * v⁻¹ := congrArg (fun w => w * v⁻¹) h'
      rw [mul_inv_cancel, mul_assoc, mul_inv_cancel_right] at h4
      exact h4.symm
    have h6 : (c ^ 2)⁻¹ = 1 := by
      rw [← inv_pow, sq]
      exact h3
    exact hc2 (inv_eq_one.mp h6)
  have hne23 : c⁻¹ * v ≠ c⁻¹ * (c⁻¹ * v) := by
    intro h'
    exact hne12 (mul_left_cancel h')
  have hd12 : Disjoint (fiber τ v) (fiber τ (c⁻¹ * v)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact hne12 ((Finset.mem_filter.mp hi1).2.symm.trans (Finset.mem_filter.mp hi2).2)
  have hd13 : Disjoint (fiber τ v) (fiber τ (c⁻¹ * (c⁻¹ * v))) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact hne13 ((Finset.mem_filter.mp hi1).2.symm.trans (Finset.mem_filter.mp hi2).2)
  have hd23 : Disjoint (fiber τ (c⁻¹ * v)) (fiber τ (c⁻¹ * (c⁻¹ * v))) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact hne23 ((Finset.mem_filter.mp hi1).2.symm.trans (Finset.mem_filter.mp hi2).2)
  have hcard : (fiber τ v ∪ fiber τ (c⁻¹ * v) ∪ fiber τ (c⁻¹ * (c⁻¹ * v))).card =
      (fiber τ v).card + (fiber τ (c⁻¹ * v)).card + (fiber τ (c⁻¹ * (c⁻¹ * v))).card := by
    rw [Finset.card_union_eq_card_add_card.mpr
        (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
      Finset.card_union_eq_card_add_card.mpr hd12]
  have hS_eq : fiber τ v = S := by
    ext i
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hS i).symm
  have hcard4 : 4 ≤ (fiber τ v).card := by rw [hS_eq]; exact hS4
  have hle : (fiber τ v ∪ fiber τ (c⁻¹ * v) ∪ fiber τ (c⁻¹ * (c⁻¹ * v))).card ≤ 6 := by
    calc _ ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 6 := by simp
  have h1 : (fiber τ v).card = (fiber τ (c⁻¹ * v)).card := hfiber v
  have h2 : (fiber τ (c⁻¹ * v)).card = (fiber τ (c⁻¹ * (c⁻¹ * v))).card := hfiber (c⁻¹ * v)
  omega

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
