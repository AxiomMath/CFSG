module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign
public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTwin

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem commutes_La_of_scalar (F : OFrame Q) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {ε : K} (hε : ε * ε = 1)
    (hg : ∀ w ∈ F.span, g w = ε • w) (A : SL(2, K)) : g * F.La A = F.La A * g := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ F.span ⊔ F.perp by rw [F.isCompl_span_perp.sup_eq_top]; trivial)
  have hgb : g b ∈ F.perp := by
    rw [Frame.mem_perp_iff_forall_incl]
    intro X
    have e1 : g (ε • F.incl X) = F.incl X := by
      rw [map_smul, hg _ ⟨X, rfl⟩, smul_smul, hε, one_smul]
    have h1 := polar_map_of_mem hgO b (ε • F.incl X)
    rw [e1] at h1
    rw [h1, polar_smul_right_eq, (Frame.mem_perp_iff_forall_incl F).mp hb X, mul_zero]
  have hAa : F.La A a ∈ F.span := by
    obtain ⟨X, rfl⟩ := ha
    rw [Frame.La_apply_incl]
    exact ⟨_, rfl⟩
  simp only [LinearEquiv.mul_apply, map_add]
  rw [Frame.La_apply_of_coords_eq_zero F A ((Frame.mem_perp_iff F).mp hb),
    Frame.La_apply_of_coords_eq_zero F A ((Frame.mem_perp_iff F).mp hgb), hg _ hAa, hg _ ha,
    map_smul]

theorem orth_of_commutes_chain3 (hodd : Odd (Nat.card K)) {s : ℕ} (hs : 2 ≤ s)
    {pr : ℕ → HypPair Q} (horth : ∀ a b, a < s + 1 → b < s + 1 → a ≠ b → (pr a).Orth (pr b))
    {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}
    (hL : ∀ a ≤ s, IsFundamental Q (L a) (i a))
    (nL : ∀ a ≤ s, negSpace (i a) = hypPlane (pr a) ⊔ hypPlane (pr (a + 1)))
    {S : Subgroup (V ≃ₗ[K] V)} {s' : V ≃ₗ[K] V} (hS : IsFundamental Q S s')
    (hc : ∀ a < s, Commutes S (L a)) :
    ∀ a < s, ∀ x ∈ negSpace s', ∀ y ∈ negSpace (i a), polar Q x y = 0 := by
  intro a ha
  by_cases h : a + 1 < s
  · exact (orth_of_commutes_two hodd (pr := fun k => pr (a + k))
      (fun p q hp hq hpq => horth (a + p) (a + q) (by omega) (by omega) (by omega))
      (hL a (by omega)) (hL (a + 1) (by omega)) hS (nL a (by omega)) (nL (a + 1) (by omega))
      (hc a ha) (hc (a + 1) h)).1
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    exact (orth_of_commutes_two hodd (pr := fun k => pr (a' + k))
      (fun p q hp hq hpq => horth (a' + p) (a' + q) (by omega) (by omega) (by omega))
      (hL a' (by omega)) (hL (a' + 1) (by omega)) hS (nL a' (by omega)) (nL (a' + 1) (by omega))
      (hc a' (by omega)) (hc (a' + 1) ha)).2

theorem orth_of_commutes_nonscalar3 (hodd : Odd (Nat.card K)) {L S : Subgroup (V ≃ₗ[K] V)}
    {i s' : V ≃ₗ[K] V} (hL : IsFundamental Q L i) (hS : IsFundamental Q S s')
    (hc : Commutes S L) {g₀ : V ≃ₗ[K] V}
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg₀2 : g₀ * g₀ = 1)
    (fS : ∀ l ∈ S, g₀ * l = l * g₀)
    (hns : ¬ ∃ ε : K, ε * ε = 1 ∧ ∀ x ∈ negSpace i, g₀ x = ε • x) :
    ∀ x ∈ negSpace s', ∀ y ∈ negSpace i, polar Q x y = 0 := by
  rcases orth_or_twin hodd hS hL hc with h | h
  · exact h
  · exfalso
    obtain ⟨ε, hε, e⟩ := sign_of_commute (IsFundamental.two_ne_zero_of_odd hodd) hS hg₀O hg₀2 fS
    apply hns
    refine ⟨ε, by rcases hε with rfl | rfl <;> norm_num, fun x hx => e x ?_⟩
    rw [← h]
    exact hx

end Model

end CFSG.ClassicalInvolution.Q3.Q3TWY
