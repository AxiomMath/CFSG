module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Concl
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  exists_coe_add_of_isCompl)
open scoped DirectSum CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (A : Subgroup (V ≃ₗ[F] V)) [Fintype A]
variable {p : ℕ}

abbrev InvariantBilin (B : LinearMap.BilinForm F V) : Prop :=
  ∀ a : ↥A, ∀ u v : V, B ((a : V ≃ₗ[F] V) u) ((a : V ≃ₗ[F] V) v) = B u v

theorem orthogonal_blockSpace_eq_ker (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {B : LinearMap.BilinForm F V} (hB : InvariantBilin A B)
    (hBn : B.Nondegenerate) (D : Hyperplane A p) :
    B.orthogonal (blockSpace A D.1) = LinearMap.ker (projBlock A hp hpF hA D) := by
  have hle : LinearMap.ker (projBlock A hp hpF hA D) ≤ B.orthogonal (blockSpace A D.1) := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    exact blockSpace_ker_orthogonal A hp hpF hA B hB D hu hv
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal hBn]
  have hdim := finrank_ker_projBlock_add_finrank_blockSpace A hp hpF hA D
  omega

theorem blockSpace_nondegenerate (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    {B : LinearMap.BilinForm F V} (halt : B.IsAlt) (hB : InvariantBilin A B)
    (hBn : B.Nondegenerate) (D : Hyperplane A p) :
    (LinearMap.BilinForm.restrict B (blockSpace A D.1)).Nondegenerate := by
  have hker : LinearMap.ker (projBlock A hp hpF hA D) = B.orthogonal (blockSpace A D.1) :=
    (orthogonal_blockSpace_eq_ker A hp hpF hA hB hBn D).symm
  have hdisj : Disjoint (blockSpace A D.1) (B.orthogonal (blockSpace A D.1)) := by
    rw [← hker]
    exact (isCompl_blockSpace_ker A hp hpF hA D).disjoint
  exact LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal B halt.isRefl hdisj

theorem finrank_fixedByEnd_blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : Hyperplane A p) :
    Module.finrank F ↥(fixedByEnd (blockEnd A hp hpF hA t ht D)) =
      Module.finrank F V - Module.finrank F ↥(blockSpace A D.1) := by
  have hker : fixedByEnd (blockEnd A hp hpF hA t ht D) =
      LinearMap.ker (projBlock A hp hpF hA D) := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rw [mem_fixedByEnd] at hv
      obtain ⟨u, r, -, rfl⟩ :=
        exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
      have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
        rw [LinearMap.mem_ker]; exact r.2
      rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
        blockEnd_apply_of_ker A hp hpF hA t ht D hr] at hv
      have h2 : (t D : V ≃ₗ[F] V) (u : V) = (u : V) := add_right_cancel hv
      have h3 : (u : V) = 0 := eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) u.2 h2
      rw [LinearMap.mem_ker, h3]
      simp
    · intro v hv
      rw [mem_fixedByEnd]
      exact blockEnd_apply_of_ker A hp hpF hA t ht D (by rw [LinearMap.mem_ker]; exact hv)
  have hdim := finrank_ker_projBlock_add_finrank_blockSpace A hp hpF hA D
  rw [hker]
  omega

private theorem exists_three_of_three_le_card {α : Type*} [Finite α] (h : 3 ≤ Nat.card α) :
    ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  haveI := Fintype.ofFinite α
  have h3 : Fintype.card (Fin 3) ≤ Fintype.card α := by simpa using h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le h3
  refine ⟨f 0, f 1, f 2, ?_, ?_, ?_⟩ <;>
    (intro hc; have := f.injective hc; revert this; decide)

theorem exists_three_ne_bot_blockSpace (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    [Finite (V ≃ₗ[F] V)] {k : ℕ} (hk : Nat.card ↥A = p ^ k)
    {H : Subgroup (V ≃ₗ[F] V)} (hAH : A ≤ H) (hHH : CFSG.Open.pRank p H ≤ k)
    (htH : ∀ D, blockEnd A hp hpF hA t ht D ∈ H) (hk3 : 3 ≤ k) :
    ∃ D₁ D₂ D₃ : Hyperplane A p, D₁ ≠ D₂ ∧ D₁ ≠ D₃ ∧ D₂ ≠ D₃ ∧
      blockSpace A D₁.1 ≠ ⊥ ∧ blockSpace A D₂.1 ≠ ⊥ ∧ blockSpace A D₃.1 ≠ ⊥ := by
  have hcard := card_le_card_ne_bot_blockSpace A hp hpF hA t ht hk hAH hHH htH
  obtain ⟨D₁, D₂, D₃, h₁₂, h₁₃, h₂₃⟩ :=
    exists_three_of_three_le_card (le_trans hk3 hcard)
  exact ⟨D₁.1, D₂.1, D₃.1, fun h => h₁₂ (Subtype.ext h), fun h => h₁₃ (Subtype.ext h),
    fun h => h₂₃ (Subtype.ext h), D₁.2, D₂.2, D₃.2⟩

def pointwiseStab (H : Subgroup (V ≃ₗ[F] V)) (U : Submodule F V) : Subgroup H where
  carrier := {g | ∀ u ∈ U, (g : V ≃ₗ[F] V) u = u}
  one_mem' := by intro u _; rfl
  mul_mem' := by
    intro g h hg hh u hu
    change (((g : ↥H) : V ≃ₗ[F] V) * ((h : ↥H) : V ≃ₗ[F] V)) u = u
    rw [LinearEquiv.mul_apply, hh u hu, hg u hu]
  inv_mem' := by
    intro g hg u hu
    have h1 : ((g : ↥H) : V ≃ₗ[F] V) (((g⁻¹ : ↥H) : V ≃ₗ[F] V) u) =
        ((g : ↥H) : V ≃ₗ[F] V) u := by
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
      simpa using (hg u hu).symm
    exact ((g : ↥H) : V ≃ₗ[F] V).injective h1

@[simp] theorem mem_pointwiseStab {H : Subgroup (V ≃ₗ[F] V)} {U : Submodule F V}
    {g : ↥H} : g ∈ pointwiseStab H U ↔ ∀ u ∈ U, (g : V ≃ₗ[F] V) u = u := Iff.rfl

theorem pointwiseStab_mono {H : Subgroup (V ≃ₗ[F] V)} {U₁ U₂ : Submodule F V} (h : U₁ ≤ U₂) :
    pointwiseStab H U₂ ≤ pointwiseStab H U₁ :=
  fun _ hg _ hu => hg _ (h hu)

theorem conj_pointwiseStab_mem {U : Submodule F V} {A₀ : Subgroup (V ≃ₗ[F] V)}
    (hAU : ∀ a ∈ A₀, ∀ u ∈ U, a u ∈ U) {a : V ≃ₗ[F] V} (ha : a ∈ A₀)
    {g : V ≃ₗ[F] V} (hg : ∀ u ∈ U, g u = u) :
    ∀ u ∈ U, (a * g * a⁻¹) u = u := by
  intro u hu
  have hU : a⁻¹ u ∈ U := hAU a⁻¹ (Subgroup.inv_mem (H := A₀) ha) u hu
  simp only [LinearEquiv.mul_apply, hg _ hU]
  simp

theorem le_normalizer_pointwiseStab {H : Subgroup (V ≃ₗ[F] V)} {U : Submodule F V}
    {A₀ : Subgroup (V ≃ₗ[F] V)} (hAH : A₀ ≤ H) (hAU : ∀ a ∈ A₀, ∀ u ∈ U, a u ∈ U) :
    (⊤ : Subgroup ↥A₀).map (Subgroup.inclusion hAH) ≤
      Subgroup.normalizer (pointwiseStab H U : Set ↥H) := by
  intro a ha
  obtain ⟨a₀, -, rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact conj_pointwiseStab_mem hAU a₀.2 hg
  · intro hg u hu
    have hU : (a₀ : V ≃ₗ[F] V) u ∈ U := hAU _ a₀.2 u hu
    have h4 : ((a₀ : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) * ((a₀ : V ≃ₗ[F] V))⁻¹)
        ((a₀ : V ≃ₗ[F] V) u) = (a₀ : V ≃ₗ[F] V) u := by
      have h := hg _ hU
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using h
    have h5 : (a₀ : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) u) = (a₀ : V ≃ₗ[F] V) u := by
      simpa using h4
    exact (a₀ : V ≃ₗ[F] V).injective h5

theorem pointwiseStab_le_centralizer_blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) {B : LinearMap.BilinForm F V} (hBn : B.Nondegenerate)
    (hAinv : InvariantBilin A B) {H : Subgroup (V ≃ₗ[F] V)}
    (hbH : ∀ g ∈ H, ∀ u v : V, B ((g : V ≃ₗ[F] V) u) ((g : V ≃ₗ[F] V) v) = B u v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p)
    (htH : blockEnd A hp hpF hA t ht D ∈ H) :
    pointwiseStab H (blockSpace A D.1) ≤
      Subgroup.centralizer ({(⟨blockEnd A hp hpF hA t ht D, htH⟩ : ↥H)} : Set ↥H) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  refine LinearEquiv.ext fun v => ?_
  simp only [LinearEquiv.mul_apply]
  obtain ⟨u, r, -, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
  have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    rw [LinearMap.mem_ker]; exact r.2
  have hgr : ((g : ↥H) : V ≃ₗ[F] V) (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    have horth : ((g : ↥H) : V ≃ₗ[F] V) (r : V) ∈ B.orthogonal (blockSpace A D.1) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro u' hu'
      have h1 : ((g : ↥H) : V ≃ₗ[F] V) u' = u' := hg u' hu'
      calc B u' (((g : ↥H) : V ≃ₗ[F] V) (r : V))
          = B (((g : ↥H) : V ≃ₗ[F] V) u') (((g : ↥H) : V ≃ₗ[F] V) (r : V)) := by rw [h1]
        _ = B u' (r : V) := hbH _ g.2 u' (r : V)
        _ = 0 := blockSpace_ker_orthogonal A hp hpF hA B hAinv D hu' hr
    rwa [orthogonal_blockSpace_eq_ker A hp hpF hA hAinv hBn D] at horth
  have hsum : ((g : ↥H) : V ≃ₗ[F] V) ((u : V) + (r : V)) =
      (u : V) + ((g : ↥H) : V ≃ₗ[F] V) (r : V) := by
    rw [map_add, hg (u : V) u.2]
  have hmem : ((t D : ↥A) : V ≃ₗ[F] V) (u : V) ∈ blockSpace A D.1 :=
    blockSpace_invariant A hp hpF hA (a := (t D)) u.2
  have LHS : (blockEnd A hp hpF hA t ht D) (((g : ↥H) : V ≃ₗ[F] V) ((u : V) + (r : V))) =
      ((t D : ↥A) : V ≃ₗ[F] V) (u : V) + ((g : ↥H) : V ≃ₗ[F] V) (r : V) := by
    rw [hsum, map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
      blockEnd_apply_of_ker A hp hpF hA t ht D hgr]
  have RHS : ((g : ↥H) : V ≃ₗ[F] V)
      ((blockEnd A hp hpF hA t ht D) ((u : V) + (r : V))) =
      ((t D : ↥A) : V ≃ₗ[F] V) (u : V) + ((g : ↥H) : V ≃ₗ[F] V) (r : V) := by
    rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
      blockEnd_apply_of_ker A hp hpF hA t ht D hr, map_add, hg _ hmem]
  rw [LHS, RHS]

theorem blockEnd_mem_pointwiseStab (hp : p.Prime) (hpF : (p : F) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {H : Subgroup (V ≃ₗ[F] V)} (htH : ∀ D, blockEnd A hp hpF hA t ht D ∈ H)
    {D E : Hyperplane A p} (hDE : E ≠ D) :
    (⟨blockEnd A hp hpF hA t ht E, htH E⟩ : ↥H) ∈ pointwiseStab H (blockSpace A D.1) :=
  fun _ hv => blockEnd_apply_of_mem_block A hp hpF hA t ht (D := E) (E := D) (Ne.symm hDE) hv

theorem orderOf_blockEnd (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D : Hyperplane A p}
    (hD : blockSpace A D.1 ≠ ⊥) : orderOf (blockEnd A hp hpF hA t ht D) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime (blockEnd_pow A hp hpF hA t ht D)
    (fun h => hD (eq_one_of_blockEnd_eq_one A hp hpF hA t ht h))

theorem dvd_card_pointwiseStab (hp : p.Prime) (hpF : (p : F) ≠ 0) (hA : IsElemAbelian p A)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {H : Subgroup (V ≃ₗ[F] V)} (htH : ∀ D, blockEnd A hp hpF hA t ht D ∈ H)
    {D E : Hyperplane A p} (hDE : E ≠ D) (hE : blockSpace A E.1 ≠ ⊥) :
    p ∣ Nat.card (pointwiseStab H (blockSpace A D.1)) := by
  have hmem := blockEnd_mem_pointwiseStab A hp hpF hA t ht htH hDE
  have hx : orderOf (⟨⟨blockEnd A hp hpF hA t ht E, htH E⟩, hmem⟩ :
      ↥(pointwiseStab H (blockSpace A D.1))) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, orderOf_blockEnd A hp hpF hA t ht hE]
  have hdvd : orderOf (⟨⟨blockEnd A hp hpF hA t ht E, htH E⟩, hmem⟩ :
      ↥(pointwiseStab H (blockSpace A D.1))) ∣
      Nat.card (pointwiseStab H (blockSpace A D.1)) := orderOf_dvd_natCard _
  rwa [hx] at hdvd

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
