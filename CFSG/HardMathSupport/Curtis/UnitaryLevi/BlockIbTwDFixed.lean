module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.CharSum
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

section Fixed

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem two_mul_finrank_le_fixed (hx : OddOrderIsometry Q 3 x) {W : Submodule K V}
    (hWQ : ∀ w ∈ W, Q w = 0) (hWx : ∀ w ∈ W, x w = w) :
    2 * finrank K W ≤ finrank K (fixedSpace x) := by
  classical
  set V₁ := fixedSpace x with hV₁
  have hWle : W ≤ V₁ := fun w hw => mem_fixedSpace.mpr (hWx w hw)
  let Q₁ : QuadraticForm K V₁ := Q.comp V₁.subtype
  have hB₁ : (polarBilin Q₁).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  let W' : Submodule K V₁ := W.comap V₁.subtype
  have hW'dim : finrank K W' = finrank K W := (Submodule.comapSubtypeEquivOfLe hWle).finrank_eq
  have hpol : ∀ v ∈ W', ∀ u ∈ W', polar Q₁ v u = 0 := fun v hv u hu => by
    have hvu : Q ((v : V) + u) = 0 := hWQ _ (W.add_mem hv hu)
    have hv0 : Q (v : V) = 0 := hWQ _ hv
    have hu0 : Q (u : V) = 0 := hWQ _ hu
    change Q ((v : V) + (u : V)) - Q (v : V) - Q (u : V) = 0
    rw [hvu, hv0, hu0]
    simp
  have hle : W' ≤ LinearMap.BilinForm.orthogonal (polarBilin Q₁) W' := fun v hv =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => by
      rw [polarBilin_apply_apply]
      exact hpol u hu v hv
  have := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hB₁, hW'dim] at this
  omega

end Fixed

section Parity

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem pow_two_mod_three (a : ℕ) : 2 ^ a % 3 = if a % 2 = 0 then 1 else 2 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

theorem finrank_mod_two_eq_fixed (hK : Nat.card K = 2) {x : V ≃ₗ[K] V} (h3 : x ^ 3 = 1)
    {U : Submodule K V} (hU : ∀ u ∈ U, x u ∈ U) :
    finrank K U % 2 = finrank K ↥(U ⊓ fixedSpace x) % 2 := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Fintype V := Fintype.ofFinite V
  have hg : ∀ v, x (x (x v)) = v := fun v => by
    have := congrArg (fun y : V ≃ₗ[K] V => y v) h3
    simpa [pow_succ] using this
  have hP : ∀ a, (x a ∈ U) ↔ (a ∈ U) := fun a => by
    refine ⟨fun h => ?_, hU a⟩
    have := hU _ (hU _ h)
    rwa [hg] at this
  have h := CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.card_filter_modEq_three
    (fun v => x v) hg (fun v => v ∈ U) hP
  have e1 : (Finset.univ.filter fun v => v ∈ U).card = 2 ^ finrank K U := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := K),
      hK]
  have e2 : (Finset.univ.filter fun v => v ∈ U ∧ x v = v).card =
      2 ^ finrank K ↥(U ⊓ fixedSpace x) := by
    have : (Finset.univ.filter fun v => v ∈ U ∧ x v = v) =
        Finset.univ.filter fun v => v ∈ U ⊓ fixedSpace x := by
      ext v
      simp [mem_fixedSpace]
    rw [this, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := K), hK]
  rw [e1, e2] at h
  have h' := h
  unfold Nat.ModEq at h'
  rw [pow_two_mod_three, pow_two_mod_three] at h'
  split_ifs at h' <;> omega

end Parity

section Quotient

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem finrank_fixed_mod_four (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x) {r : ℕ}
    (hdim : finrank K V = 2 * r) {W : Submodule K V} (hWQ : ∀ w ∈ W, Q w = 0)
    (hWx : ∀ w ∈ W, x w ∈ W) (hWdim : finrank K W = r - 1) (hr : 1 ≤ r)
    (hN : ∀ u : V, (∀ w ∈ W, polar Q u w = 0) → x u - u ∈ W) :
    finrank K (fixedSpace x) % 4 = (2 * r) % 4 := by
  classical
  have hB : (polarBilin Q).Nondegenerate :=
    ⟨fun v hv => hx.regular v fun w => by simpa [polarBilin_apply_apply] using hv w,
     fun v hv => hx.regular v fun w => by
      rw [QuadraticMap.polar_comm]; simpa [polarBilin_apply_apply] using hv w⟩
  have hx3 : ∀ v, x (x (x v)) = v := fun v => by
    have := congrArg (fun y : V ≃ₗ[K] V => y v) hx.pow_eq_one
    simpa [pow_succ] using this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hadd : ∀ v : V, v + v = 0 := fun v => by rw [← two_smul K v, h2, zero_smul]
  have hpx : ∀ v u, polar Q (x v) (x u) = polar Q v u := fun v u =>
    CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hx.mem v u
  have hxW : ∀ w ∈ W, x (x w) ∈ W := fun w hw => hWx _ (hWx _ hw)
  set V₁ := fixedSpace x with hV₁
  let N : Submodule K V := LinearMap.BilinForm.orthogonal (polarBilin Q) W
  have hNmem : ∀ u, u ∈ N ↔ ∀ w ∈ W, polar Q u w = 0 := fun u => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    refine forall₂_congr fun w hw => ?_
    rw [polarBilin_apply_apply, QuadraticMap.polar_comm]
  have hNdim : finrank K N = 2 * r - (r - 1) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, hdim, hWdim]
  have hWpol : ∀ w ∈ W, ∀ w' ∈ W, polar Q w w' = 0 := fun w hw w' hw' => by
    have hvu : Q (w + w') = 0 := hWQ _ (W.add_mem hw hw')
    simp only [QuadraticMap.polar, hvu, hWQ w hw, hWQ w' hw']
    simp
  have hWN : W ≤ N := fun w hw => (hNmem w).mpr fun w' hw' => hWpol w hw w' hw'
  have hNx : ∀ u ∈ N, x u ∈ N := fun u hu => (hNmem _).mpr fun w hw => by
    have := hpx u (x (x w))
    rw [hx3] at this
    rw [this]
    exact (hNmem u).mp hu _ (hxW w hw)
  have he1 : ∀ v, x (v + x v + x (x v)) = v + x v + x (x v) := fun v => by
    rw [map_add, map_add, hx3]; abel
  have he1N : ∀ u ∈ N, u + x u + x (x u) ∈ N := fun u hu =>
    N.add_mem (N.add_mem hu (hNx _ hu)) (hNx _ (hNx _ hu))
  have hneg : ∀ v : V, -v = v := fun v => by rw [neg_eq_iff_add_eq_zero]; exact hadd v
  have hNle : N ≤ (N ⊓ V₁) ⊔ W := by
    intro u hu
    have hwu : x (x u) - x u ∈ W := hN (x u) ((hNmem _).mp (hNx u hu))
    have hu' : (u + x u + x (x u)) + (x (x u) - x u) = u := by
      have : (u + x u + x (x u)) + (x (x u) - x u) = u + (x (x u) + x (x u)) := by abel
      rw [this, hadd, add_zero]
    exact Submodule.mem_sup.mpr ⟨u + x u + x (x u), ⟨he1N u hu, mem_fixedSpace.mpr (he1 u)⟩,
      x (x u) - x u, hwu, hu'⟩
  have hsup : (N ⊓ V₁) ⊔ W = N := le_antisymm (sup_le inf_le_left hWN) hNle
  have hinf : (N ⊓ V₁) ⊓ W = W ⊓ V₁ := by
    ext u
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hWN h1, h2⟩, h1⟩
  have hdimsum := Submodule.finrank_sup_add_finrank_inf_eq (N ⊓ V₁) W
  rw [hsup, hinf, hNdim, hWdim] at hdimsum
  have hA : ∀ u ∈ V₁, u ∈ N ↔ ∀ w₁ ∈ W ⊓ V₁, polar Q u w₁ = 0 := by
    intro u hu
    have hux : x u = u := mem_fixedSpace.mp hu
    constructor
    · exact fun h w₁ hw₁ => (hNmem u).mp h w₁ hw₁.1
    · intro h
      refine (hNmem u).mpr fun w hw => ?_
      have hw1 : polar Q u (x w) = polar Q u w := by
        have := hpx u w
        rwa [hux] at this
      have hw2 : polar Q u (x (x w)) = polar Q u w := by
        have := hpx u (x w)
        rwa [hux, hw1] at this
      have hmemW : w + x w + x (x w) ∈ W ⊓ V₁ :=
        ⟨W.add_mem (W.add_mem hw (hWx _ hw)) (hxW _ hw), mem_fixedSpace.mpr (he1 w)⟩
      have := h _ hmemW
      rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, hw1, hw2] at this
      have hp : polar Q u w + polar Q u w = 0 := CharTwo.add_self_eq_zero _
      rw [hp, zero_add] at this
      exact this
  let Q₁ : QuadraticForm K V₁ := Q.comp V₁.subtype
  have hB₁ : (polarBilin Q₁).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  let W₁' : Submodule K V₁ := (W ⊓ V₁).comap V₁.subtype
  have hW₁'dim : finrank K W₁' = finrank K ↥(W ⊓ V₁) :=
    (Submodule.comapSubtypeEquivOfLe (inf_le_right : W ⊓ V₁ ≤ V₁)).finrank_eq
  let O' : Submodule K V₁ := LinearMap.BilinForm.orthogonal (polarBilin Q₁) W₁'
  have hO'dim : finrank K O' = finrank K V₁ - finrank K W₁' :=
    LinearMap.BilinForm.finrank_orthogonal hB₁ W₁'
  have hmap : O'.map V₁.subtype = N ⊓ V₁ := by
    ext u
    simp only [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨u', hu', rfl⟩
      have hu'1 : (u' : V) ∈ V₁ := u'.2
      refine ⟨?_, hu'1⟩
      refine (hA _ hu'1).mpr fun w₁ hw₁ => ?_
      have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hu') ⟨w₁, hw₁.2⟩ hw₁
      rw [polarBilin_apply_apply] at h1
      rw [QuadraticMap.polar_comm]
      exact h1
    · rintro ⟨hu, hu1⟩
      refine ⟨⟨u, hu1⟩, ?_, rfl⟩
      refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w' hw' => ?_
      rw [polarBilin_apply_apply]
      have := (hNmem u).mp hu w' hw'.1
      rw [QuadraticMap.polar_comm]
      exact this
  have hdim1 : finrank K ↥(N ⊓ V₁) = finrank K V₁ - finrank K ↥(W ⊓ V₁) := by
    rw [← hmap, Submodule.finrank_map_subtype_eq, hO'dim, hW₁'dim]
  have hpar : finrank K W % 2 = finrank K ↥(W ⊓ V₁) % 2 :=
    finrank_mod_two_eq_fixed hK hx.pow_eq_one hWx
  have hle1 : finrank K ↥(W ⊓ V₁) ≤ finrank K V₁ := Submodule.finrank_mono inf_le_right
  omega

end Quotient

end CFSG.HardMathSupport.Curtis.UnitaryLevi
