module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.InvolutionMovedBlocks

theorem two_mul_card_le_finrank_range {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : ι → Submodule K V} (hW : iSupIndep W) (τ : V →ₗ[K] V) (σ : ι → ι)
    (hτ : ∀ i, ∀ v ∈ W i, τ v ∈ W (σ i)) (M : Finset ι) (hM : ∀ i ∈ M, σ i ∉ M) (f : ι → Fin 2 → V)
    (hf : ∀ i ∈ M, LinearIndependent K (f i)) (hfW : ∀ i ∈ M, ∀ j, f i j ∈ W i) :
    2 * M.card ≤ Module.finrank K (LinearMap.range (τ - 1)) := by
  classical
  have hspan : ∀ i : ↥M, Submodule.span K (Set.range (f i)) ≤ W i := fun i =>
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hfW i.1 i.2 j)
  have hli : LinearIndependent K (fun ij : (Σ _ : ↥M, Fin 2) => f ij.1 ij.2) := by
    refine linearIndependent_iUnion_finite (f := fun (i : ↥M) => f i) (fun i => hf i.1 i.2)
      fun i t _ hit => ?_
    have hi : (i : ι) ∉ Subtype.val '' t := by
      rintro ⟨k, hk, hki⟩
      exact hit (Subtype.ext hki ▸ hk)
    refine (hW.disjoint_biSup hi).mono (hspan i) (iSup₂_le fun k hk => (hspan k).trans ?_)
    exact le_iSup₂_of_le (f := fun j (_ : j ∈ Subtype.val '' t) => W j) (k : ι) (Set.mem_image_of_mem _ hk)
      le_rfl
  have hsub : ∀ ij : (Σ _ : ↥M, Fin 2), f ij.1 ij.2 ∈ ⨆ i ∈ (M : Set ι), W i := fun ij =>
    (le_iSup₂_of_le (f := fun j (_ : j ∈ (M : Set ι)) => W j) (ij.1 : ι) (Finset.mem_coe.mpr ij.1.2) le_rfl)
      (hfW ij.1.1 ij.1.2 ij.2)
  have hdisjM : Disjoint (M : Set ι) (σ '' (M : Set ι)) := by
    rw [Set.disjoint_left]
    rintro i hi ⟨j, hj, rfl⟩
    exact hM j hj hi
  have hker : Disjoint (⨆ i ∈ (M : Set ι), W i) (LinearMap.ker (τ - 1)) := by
    rw [Submodule.disjoint_def]
    intro v hv hvk
    have hτv : τ v = v := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hvk
      exact hvk
    have hle : (⨆ i ∈ (M : Set ι), W i) ≤ (⨆ i ∈ σ '' (M : Set ι), W i).comap τ :=
      iSup₂_le fun i hi w hw => (le_iSup₂_of_le (f := fun j (_ : j ∈ σ '' (M : Set ι)) => W j) (σ i)
        (Set.mem_image_of_mem σ hi) le_rfl) (hτ i w hw)
    have h1 : τ v ∈ ⨆ i ∈ σ '' (M : Set ι), W i := hle hv
    rw [hτv] at h1
    exact Submodule.disjoint_def.mp (hW.disjoint_biSup_biSup' hdisjM M.finite_toSet) v hv h1
  have hli2 : LinearIndependent K (fun ij : (Σ _ : ↥M, Fin 2) => (τ - 1) (f ij.1 ij.2)) :=
    hli.map (hker.mono_left (Submodule.span_le.mpr (Set.range_subset_iff.mpr hsub)))
  have hli3 : LinearIndependent K (fun ij : (Σ _ : ↥M, Fin 2) =>
      (⟨(τ - 1) (f ij.1 ij.2), LinearMap.mem_range_self _ _⟩ : ↥(LinearMap.range (τ - 1)))) :=
    LinearIndependent.of_comp (LinearMap.range (τ - 1)).subtype hli2
  have hcard := hli3.fintype_card_le_finrank
  rw [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_coe, Fintype.card_fin,
    smul_eq_mul] at hcard
  omega

theorem exists_half_moved {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i) :
    ∃ M : Finset ι, (∀ i ∈ M, σ i ≠ i) ∧ (∀ i ∈ M, σ i ∉ M) ∧
      (Finset.univ.filter fun i => σ i ≠ i).card ≤ 2 * M.card := by
  let e : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ)
  have he : Function.Injective e := fun a b h => (Fintype.equivFin ι).injective (Fin.ext h)
  refine ⟨Finset.univ.filter fun i => σ i ≠ i ∧ e i < e (σ i), fun i hi => (Finset.mem_filter.mp hi).2.1,
    fun i hi hσi => ?_, ?_⟩
  · have h1 := (Finset.mem_filter.mp hi).2.2
    have h2 := (Finset.mem_filter.mp hσi).2.2
    rw [hσ] at h2
    omega
  · set M₁ := Finset.univ.filter fun i => σ i ≠ i ∧ e i < e (σ i) with hM₁
    set M₂ := Finset.univ.filter fun i => σ i ≠ i ∧ e (σ i) < e i with hM₂
    have hsplit : (Finset.univ.filter fun i => σ i ≠ i) ⊆ M₁ ∪ M₂ := by
      intro i hi
      have hne := (Finset.mem_filter.mp hi).2
      have hne' : e i ≠ e (σ i) := fun h => hne (he h).symm
      rcases lt_or_gt_of_ne hne' with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, h⟩)
    have h21 : M₂.card ≤ M₁.card := by
      refine Finset.card_le_card_of_injOn σ (fun i hi => ?_) (fun a _ b _ hab => ?_)
      · obtain ⟨-, hne, hlt⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hi)
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => ?_, ?_⟩)
        · rw [hσ] at h
          exact hne h.symm
        · rw [hσ]
          exact hlt
      · have h := congrArg σ hab
        rwa [hσ, hσ] at h
    calc (Finset.univ.filter fun i => σ i ≠ i).card ≤ (M₁ ∪ M₂).card := Finset.card_le_card hsplit
      _ ≤ M₁.card + M₂.card := Finset.card_union_le _ _
      _ ≤ 2 * M₁.card := by omega

theorem card_moved_le_finrank_range {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] {W : ι → Submodule K V} (hW : iSupIndep W)
    (τ : V →ₗ[K] V) (σ : ι → ι) (hσ : ∀ i, σ (σ i) = i) (hτ : ∀ i, ∀ v ∈ W i, τ v ∈ W (σ i))
    (f : ι → Fin 2 → V) (hf : ∀ i, σ i ≠ i → LinearIndependent K (f i))
    (hfW : ∀ i, σ i ≠ i → ∀ j, f i j ∈ W i) :
    (Finset.univ.filter fun i => σ i ≠ i).card ≤ Module.finrank K (LinearMap.range (τ - 1)) := by
  obtain ⟨M, hMm, hM, hcard⟩ := exists_half_moved σ hσ
  exact hcard.trans (two_mul_card_le_finrank_range hW τ σ hτ M hM f (fun i hi => hf i (hMm i hi))
    fun i hi => hfW i (hMm i hi))

theorem two_mul_card_fixed_le {α : Type*} [Fintype α] [DecidableEq α] {A : Subgroup (Equiv.Perm α)}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (htrans : ∀ x y : α, ∃ a ∈ A, a x = y)
    {σ : Equiv.Perm α} (hσA : ∀ a ∈ A, σ * a * σ⁻¹ ∈ A) (hσ : σ ≠ 1) :
    2 * (Finset.univ.filter fun x => σ x = x).card ≤ Fintype.card α := by
  classical
  by_cases hfix : ∃ x₀, σ x₀ = x₀
  swap
  · push Not at hfix
    have h0 : (Finset.univ.filter fun x => σ x = x) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun x _ => hfix x
    rw [h0, Finset.card_empty]
    omega
  obtain ⟨x₀, hx₀⟩ := hfix
  have hinvself : ∀ (g : Equiv.Perm α) (x : α), g⁻¹ (g x) = x := fun g x => Equiv.Perm.inv_eq_iff_eq.mpr rfl
  have hreg : ∀ a ∈ A, a x₀ = x₀ → a = 1 := by
    intro a ha hax
    ext y
    obtain ⟨b, hb, rfl⟩ := htrans x₀ y
    show a (b x₀) = b x₀
    have h1 : a (b x₀) = (a * b) x₀ := rfl
    rw [h1, hAab a ha b hb, Equiv.Perm.mul_apply, hax]
  set C : Subgroup (Equiv.Perm α) := A ⊓ Subgroup.centralizer {σ} with hC
  have hmemC : ∀ a, a ∈ C ↔ a ∈ A ∧ a * σ = σ * a := fun a => by
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have h1 : (Finset.univ.filter fun x => σ x = x).card ≤ Nat.card C := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_surjective (fun a : C => (⟨a.1 x₀, ?_⟩ : {x // σ x = x})) ?_
    · have hca := ((hmemC a.1).mp a.2).2
      have h2 : σ (a.1 x₀) = (σ * a.1) x₀ := rfl
      rw [h2, ← hca, Equiv.Perm.mul_apply, hx₀]
    · rintro ⟨y, hy⟩
      obtain ⟨b, hb, rfl⟩ := htrans x₀ y
      have hc : b⁻¹ * (σ * b * σ⁻¹) ∈ A := A.mul_mem (A.inv_mem hb) (hσA b hb)
      have hσinv : σ⁻¹ x₀ = x₀ := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hx₀.symm
      have hcx : (b⁻¹ * (σ * b * σ⁻¹)) x₀ = x₀ := by
        simp only [Equiv.Perm.mul_apply]
        rw [hσinv, hy, hinvself]
      have hc1 := hreg _ hc hcx
      have hcomm : b * σ = σ * b := by
        have h3 : σ * b * σ⁻¹ = b := by
          have h4 := congrArg (b * ·) hc1
          simpa [mul_assoc] using h4
        calc b * σ = σ * b * σ⁻¹ * σ := by rw [h3]
          _ = σ * b := by group
      exact ⟨⟨b, (hmemC b).mpr ⟨hb, hcomm⟩⟩, rfl⟩
  have hCA : C ≠ A := by
    intro h
    apply hσ
    ext y
    obtain ⟨a, ha, rfl⟩ := htrans x₀ y
    have haC : a ∈ C := h ▸ ha
    have hca := ((hmemC a).mp haC).2
    show σ (a x₀) = a x₀
    have h2 : σ (a x₀) = (σ * a) x₀ := rfl
    rw [h2, ← hca, Equiv.Perm.mul_apply, hx₀]
  have h2 : 2 * Nat.card C ≤ Nat.card A := by
    have hle : C ≤ A := inf_le_left
    obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hle
    have hpos : 0 < Nat.card C := Nat.card_pos
    have hm1 : m ≠ 1 := by
      rintro rfl
      exact hCA (Subgroup.eq_of_le_of_card_ge hle (by rw [hm, mul_one]))
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact (Nat.card_pos (α := A)).ne' hm
    rw [hm]
    have hm2 : 2 ≤ m := by omega
    nlinarith
  have h3 : Nat.card A ≤ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective (fun a : A => a.1 x₀) fun a b hab => ?_
    have hc : (b : Equiv.Perm α)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem b.2) a.2
    have hcx : ((b : Equiv.Perm α)⁻¹ * a) x₀ = x₀ := by
      rw [Equiv.Perm.mul_apply]
      have hab' : (a : Equiv.Perm α) x₀ = (b : Equiv.Perm α) x₀ := hab
      rw [hab', hinvself]
    exact Subtype.ext (inv_mul_eq_one.mp (hreg _ hc hcx)).symm
  omega

theorem two_mul_succ_lt_two_pow {e : ℕ} (he : 4 ≤ e) : 2 * (e + 1) < 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    omega

theorem two_mul_succ_lt {e N : ℕ} (he : 2 < e) (h2 : 2 ^ e ≤ N) (h4 : Odd e → 4 ^ e ≤ N) :
    2 * (e + 1) < N := by
  rcases Nat.lt_or_ge e 4 with h | h
  · have he3 : e = 3 := by omega
    subst he3
    have := h4 ⟨1, rfl⟩
    norm_num at this
    omega
  · exact lt_of_lt_of_le (two_mul_succ_lt_two_pow h) h2

end CFSG.LocalAnalysis.RankThreeUC.Section5.InvolutionMovedBlocks
