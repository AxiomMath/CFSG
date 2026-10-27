module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwDMinus
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwDFixed
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbTwDAbs

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.AGLEmbedding.ToralCensus
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

set_option linter.unusedSectionVars false

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

abbrev OmegaOf (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) :=
  ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆

theorem three_ne_zero_of_charTwo : (3 : K) ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro h
  have : (1 : K) = 0 := by linear_combination h - h2
  exact one_ne_zero this

theorem oddOrderIsometry_of_mem (hB : (polarBilin Q).Nondegenerate) {g : ↥(OmegaOf Q)}
    (hg3 : g ^ 3 = 1) : OddOrderIsometry Q 3 (g : V ≃ₗ[K] V) :=
  ⟨Subgroup.commutator_le_self _ g.2, by
    rw [← Subgroup.coe_pow, hg3, Subgroup.coe_one], by
    have : ((3 : ℕ) : K) = 3 := by norm_num
    rw [this]; exact three_ne_zero_of_charTwo,
    fun v hv => hB.1 v fun w => by rw [polarBilin_apply_apply]; exact hv w⟩

theorem commutator_subgroupOf_self {G : Type*} [Group G] {V D : Subgroup G} (hVD : V ≤ D)
    (hV : ⁅V, V⁆ = V) : ⁅V.subgroupOf D, V.subgroupOf D⁆ = V.subgroupOf D := by
  apply Subgroup.map_injective D.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVD, hV]

theorem exists_perfect_of_perfectThreeIn {g : ↥(OmegaOf Q)}
    (hP : PerfectThreeIn (isometryCentralizer Q (g : V ≃ₗ[K] V))) :
    ∃ V₀ : Subgroup ↥(OmegaOf Q), V₀ ≤ Subgroup.centralizer ({g} : Set ↥(OmegaOf Q)) ∧
      ⁅V₀, V₀⁆ = V₀ ∧ V₀ ≠ ⊥ := by
  obtain ⟨V₁, hV₁C, hV₁, z, hz, hz3, hz1⟩ := hP
  have hV₁O : V₁ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun y hy =>
    (mem_isometryCentralizer.mp (hV₁C hy)).1 |> fun _ => (Subgroup.mem_inf.mp (hV₁C hy)).1
  have hVD : V₁ ≤ OmegaOf Q := by
    rw [← hV₁]
    exact Subgroup.commutator_mono hV₁O hV₁O
  refine ⟨V₁.subgroupOf (OmegaOf Q), ?_, commutator_subgroupOf_self hVD hV₁, ?_⟩
  · intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    have := (mem_isometryCentralizer.mp (hV₁C hy)).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    exact this v
  · intro hbot
    have : (⟨z, hVD hz⟩ : ↥(OmegaOf Q)) ∈ V₁.subgroupOf (OmegaOf Q) := hz
    rw [hbot, Subgroup.mem_bot] at this
    exact hz1 (congrArg Subtype.val this)

theorem exists_perfect_of_fixes (hK : Nat.card K = 2) (hB : (polarBilin Q).Nondegenerate)
    [Fintype V] {n : ℕ} (hdim : finrank K V = 2 * n) (hn : n = 4 ∨ n = 5)
    (hS : ∑ v : V, chi (Q v) = -(2 : ℤ) ^ n) {g : ↥(OmegaOf Q)} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    {W : Submodule K V} (hWQ : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = n - 2)
    (hfix : ∀ w ∈ W, (g : V ≃ₗ[K] V) w = w) :
    ∃ V₀ : Subgroup ↥(OmegaOf Q), V₀ ≤ Subgroup.centralizer ({g} : Set ↥(OmegaOf Q)) ∧
      ⁅V₀, V₀⁆ = V₀ ∧ V₀ ≠ ⊥ := by
  have hx := oddOrderIsometry_of_mem hB hg3
  have hle := two_mul_finrank_le_fixed hx hWQ hfix
  refine exists_perfect_of_perfectThreeIn (perfectThreeIn_isometryCentralizer_minus hK hx hdim hn
    hS (fun h1 => hg1 (Subtype.ext h1)) ?_)
  omega

theorem exists_perfect_of_stable (hK : Nat.card K = 2) (hB : (polarBilin Q).Nondegenerate)
    [Fintype V] {n : ℕ} (hdim : finrank K V = 2 * n) (hn : n = 4 ∨ n = 5)
    (hS : ∑ v : V, chi (Q v) = -(2 : ℤ) ^ n) {g : ↥(OmegaOf Q)} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    {W : Submodule K V} (hWQ : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = n - 1)
    (hWx : ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W)
    (hN : ∀ u : V, (∀ w ∈ W, polar Q u w = 0) → (g : V ≃ₗ[K] V) u - u ∈ W) :
    ∃ V₀ : Subgroup ↥(OmegaOf Q), V₀ ≤ Subgroup.centralizer ({g} : Set ↥(OmegaOf Q)) ∧
      ⁅V₀, V₀⁆ = V₀ ∧ V₀ ≠ ⊥ := by
  have hx := oddOrderIsometry_of_mem hB hg3
  have hmod := finrank_fixed_mod_four hK hx hdim hWQ hWx hWdim (by omega) hN
  refine exists_perfect_of_perfectThreeIn (perfectThreeIn_isometryCentralizer_minus hK hx hdim hn
    hS (fun h1 => hg1 (Subtype.ext h1)) ?_)
  omega

theorem trivial_on_perp_of_perfect (hK : Nat.card K = 2) (hB : (polarBilin Q).Nondegenerate)
    {n : ℕ} (hdim : finrank K V = 2 * n) (hn : 1 ≤ n) {W : Submodule K V}
    (hWQ : ∀ w ∈ W, Q w = 0) (hWdim : finrank K W = n - 1) (U : Subgroup ↥(OmegaOf Q))
    (hU : ⁅U, U⁆ = U) (hst : ∀ g ∈ U, ∀ w ∈ W, (g : V ≃ₗ[K] V) w ∈ W) :
    ∀ g ∈ U, ∀ u : V, (∀ w ∈ W, polar Q u w = 0) → (g : V ≃ₗ[K] V) u - u ∈ W := by
  classical
  let N : Submodule K V := LinearMap.BilinForm.orthogonal (polarBilin Q) W
  have hNmem : ∀ u, u ∈ N ↔ ∀ w ∈ W, polar Q u w = 0 := fun u => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    refine forall₂_congr fun w hw => ?_
    rw [polarBilin_apply_apply, QuadraticMap.polar_comm]
  have hNdim : finrank K N = 2 * n - (n - 1) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, hdim, hWdim]
  have hWpol : ∀ w ∈ W, ∀ w' ∈ W, polar Q w w' = 0 := fun w hw w' hw' => by
    have hvu : Q (w + w') = 0 := hWQ _ (W.add_mem hw hw')
    simp only [QuadraticMap.polar, hvu, hWQ w hw, hWQ w' hw']
    simp
  have hWN : W ≤ N := fun w hw => (hNmem w).mpr fun w' hw' => hWpol w hw w' hw'
  let U' : Subgroup (V ≃ₗ[K] V) := U.map (OmegaOf Q).subtype
  have hU' : ⁅U', U'⁆ = U' := by
    rw [← Subgroup.map_commutator, hU]
  have hW' : ∀ g ∈ U', ∀ w ∈ W, g w ∈ W := by
    rintro _ ⟨g, hg, rfl⟩ w hw
    exact hst g hg w hw
  have hN' : ∀ g ∈ U', ∀ u ∈ N, g u ∈ N := by
    intro g hg u hu
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      obtain ⟨g', -, rfl⟩ := hg
      exact Subgroup.commutator_le_self _ g'.2
    refine (hNmem _).mpr fun w hw => ?_
    have h1 := CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hgO u (g⁻¹ w)
    have h2 : g (g⁻¹ w) = w := by simp
    rw [h2] at h1
    rw [h1]
    exact (hNmem u).mp hu _ (hW' g⁻¹ (U'.inv_mem hg) w hw)
  have key := trivial_on_quotient_of_perfect hK U' hU' hWN (by rw [hNdim, hWdim]; omega) hW' hN'
  intro g hg u hu
  exact key _ ⟨g, hg, rfl⟩ u ((hNmem u).mpr hu)

end Group

end CFSG.HardMathSupport.Curtis.UnitaryLevi
