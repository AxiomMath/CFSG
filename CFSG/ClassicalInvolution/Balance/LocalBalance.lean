module

public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Fixed
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Moved
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Normalizes

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG CFSG.Open CFSG.LocalCores CFSG.ClassicalInvolution.Balance.LocalBalance

variable {X : Type*} [Group X] [Finite X]

theorem deltaCore_eq_bot_of_locallyTwoBalanced (hO : CFSG.pPrimeCore 2 X = ⊥) {F : Subgroup X}
    (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hloc : ∀ L : Subgroup X, IsComponent L → F ≤ Subgroup.normalizer (L : Set X) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
      IsLocallyTwoBalanced (L ⧸ Subgroup.center L)) :
    deltaCore F = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f₀, hf₀F, hf₀1⟩ : ∃ f ∈ F, f ≠ 1 := by
    have : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hF4]; norm_num)
    obtain ⟨⟨f, hf⟩, hne⟩ := exists_ne (1 : F)
    exact ⟨f, hf, fun h => hne (Subtype.ext h)⟩
  have hDodd : Odd (Nat.card (deltaCore F)) := odd_card_deltaCore hf₀F hf₀1
  have hDF : ∀ f ∈ F, f ≠ 1 → deltaCore F ≤ CFSG.Assembly.Dichotomy.involutionOddCore f :=
    fun f hf hf1 => deltaCore_le_involutionOddCore hf hf1
  have hord : ∀ f ∈ F, f ≠ 1 → orderOf f = 2 := fun f hf hf1 =>
    orderOf_eq_prime (by rw [sq]; exact hF2 f hf) hf1
  have hQ : deltaCore F ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := commute_pCore_of_mem_involutionOddCore (hord f₀ hf₀F hf₀1)
      (deltaCore_le_involutionOddCore hf₀F hf₀1 hd) q hq
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hL : ∀ L : Subgroup X, IsComponent L → deltaCore F ≤ Subgroup.centralizer (L : Set X) := by
    intro L hL
    have key : ∀ d ∈ deltaCore F, ∀ x ∈ L, d * x = x * d := by
      by_cases hcen : ∃ f ∈ F, f ≠ 1 ∧ ∀ x ∈ L, f * x = x * f
      ·
        obtain ⟨f, hfF, hf1, hfL⟩ := hcen
        have hLC : L ≤ Subgroup.centralizer ({f} : Set X) := fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hfL x hx).symm
        intro d hd
        exact commute_of_isComponent_centralizer (hDF f hfF hf1 hd) hLC
          (component_overgroup hL hLC)
      · by_cases hmov : ∃ f ∈ F, conjSub f L ≠ L
        · obtain ⟨f, hfF, hfne⟩ := hmov
          have hf1 : f ≠ 1 := fun h => hfne (by rw [h, conjSub_one])
          intro d hd
          exact commute_of_moved hL (hF2 f hfF) hfne (hDF f hfF hf1 hd)
        · push Not at hcen hmov
          have hDn : ∀ d ∈ deltaCore F, conjSub d L = L := fun d hd =>
            conjSub_eq_of_mem_involutionOddCore hL (hF2 f₀ hf₀F) (hmov f₀ hf₀F)
              (hDF f₀ hf₀F hf₀1 hd)
          have hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f := by
            intro f hf hf1 h
            obtain ⟨x, hx, hxne⟩ := hcen f hf hf1
            exact hxne (h x hx)
          intro d hd
          have hFn : F ≤ Subgroup.normalizer (L : Set X) := fun f hf =>
            mem_normalizer_of_conjSub_eq (hmov f hf)
          exact commute_of_faithful hL (hloc L hL hFn hfaith) hF4 hF2 hmov hfaith hDn hDF d hd
    intro d hd x hx
    exact (key d hd x hx).symm
  exact eq_bot_of_centralizes_pCore_of_centralizes_components hO hDodd hQ hL

theorem deltaCore_eq_bot_of_locallyTwoBalanced_of_isComponentOf
    (hO : CFSG.pPrimeCore 2 X = ⊥) {F : Subgroup X} (hF4 : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1)
    (hloc : ∀ L : Subgroup X, IsComponentOf L ⊤ → F ≤ Subgroup.normalizer (L : Set X) →
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) →
      IsLocallyTwoBalanced (L ⧸ Subgroup.center L)) :
    deltaCore F = ⊥ :=
  deltaCore_eq_bot_of_locallyTwoBalanced hO hF4 hF2 fun L hL =>
    hloc L ((CFSG.isComponent_iff_open L).mp hL)

theorem map_deltaCore_le_of_surjective {Z : Type*} [Group Z] (φ : X →* Z)
    (hφ : Function.Surjective φ)
    {F : Subgroup X} (hF2 : ∀ f ∈ F, f * f = 1) :
    (deltaCore F).map φ ≤ deltaCore (F.map φ) := by
  refine le_deltaCore fun g hg hg1 => ?_
  obtain ⟨f, hfF, rfl⟩ := hg
  have hf1 : f ≠ 1 := fun h => hg1 (by rw [h, map_one])
  exact (Subgroup.map_mono (deltaCore_le_involutionOddCore hfF hf1)).trans
    (map_involutionOddCore_le φ hφ (isPGroup_zpowers_of_mul_self_eq_one (hF2 f hfF)))

omit [Finite X] in
theorem oddCoreCentralizer_eq_oddCoreIn (B : Subgroup X) :
    oddCoreCentralizer B = oddCoreIn (Subgroup.centralizer (B : Set X)) := rfl

end CFSG.ClassicalInvolution.Balance
