module

public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaConst
public import CFSG.ClassicalInvolution.Balance.Prop311

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.SignalizerFunctorTheorem CFSG.Assembly.Dichotomy CFSG.ComponentClassification
open scoped commutatorElement

section Constancy

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem alphaCore_le_alphaCore (h : RankThreeBalance A) {F F' : Subgroup G} (hFA : F ≤ A)
    (hF4 : Nat.card F = 4) (hF'A : F' ≤ A) (hF'4 : Nat.card F' = 4) :
    alphaCore F' ≤ alphaCore F := by
  obtain ⟨d', hd'F', hd'1⟩ := exists_ne_one_of_card_eq_two_pow (n := 2) (by norm_num) hF'4
  have hD'odd : Odd (Nat.card (deltaCore F')) := odd_card_deltaCore hd'F' hd'1
  have hU'W : uCore F' ≤ deltaStarCompletion A := uCore_le_completion hF'A
  have hD'W : deltaCore F' ≤ deltaStarCompletion A := (deltaCore_le_uCore hd'F' hd'1).trans hU'W
  have hK1 : ∀ {w g : G}, w ∈ deltaStarCompletion A → g ∈ A → ⁅w, g⁆ ∈ alphaCore F :=
    fun hw hg => commutator_mem_alphaCore_of_mem_completion h hFA hF4 hw hg
  have hcomm : ⁅uCore F', F'⁆ ≤ alphaCore F := by
    rw [Subgroup.commutator_le]
    intro u hu f hf
    exact hK1 (hU'W hu) (hF'A hf)
  have hdelta : deltaCore F' ≤ alphaCore F := by
    obtain ⟨y, hyA, hyF'⟩ : ∃ y ∈ A, y ∉ F' := by
      by_contra hcon
      have hAF' : A ≤ F' := fun x hx => by
        by_contra hx'
        exact hcon ⟨x, hx, hx'⟩
      have := Subgroup.card_le_of_le hAF'
      rw [h.card, hF'4] at this
      omega
    have hy2 : y * y = 1 := h.mul_self hyA
    have hcardF' : Nat.card A = 2 * Nat.card F' := by rw [h.card, hF'4]
    have hcyc : IsPGroup 2 (Subgroup.zpowers y) := isPGroup_zpowers_of_mul_self_eq_one hy2
    have hnormD : Subgroup.zpowers y ≤ Subgroup.normalizer (deltaCore F' : Set G) :=
      (Subgroup.zpowers_le.mpr hyA).trans (normalizer_deltaCore h.elem.1 hF'A)
    have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2
      Nat.prime_two (Subgroup.zpowers y) (deltaCore F') hcyc hnormD
      (Nat.coprime_two_left.mpr hD'odd)
    refine le_of_eq_of_le hfac.symm (sup_le ?_ ?_)
    · rw [Subgroup.commutator_le]
      intro x hx g hg
      exact hK1 (hD'W hx) ((Subgroup.zpowers_le.mpr hyA) hg)
    · rintro x ⟨hxD, hxy⟩
      have hxy' : y * x = x * y :=
        Subgroup.mem_centralizer_iff.mp hxy y (Subgroup.mem_zpowers y)
      have hxF' : ∀ f ∈ F', f * x = x * f := fun f hf =>
        Subgroup.mem_centralizer_iff.mp (deltaCore_le_centralizer F' hxD) f hf
      refine deltaCore_le_alphaCore (mem_deltaCore_iff.mpr fun f hf hf1 => ?_)
      have hfA : f ∈ A := hFA hf
      by_cases hfF' : f ∈ F'
      · exact deltaCore_le_involutionOddCore hfF' hf1 hxD
      · rcases mem_or_inv_mul_mem hF'A hcardF' hyA hyF' hfA with h1 | h1
        · exact absurd h1 hfF'
        · have hxg : (y⁻¹ * f) * x = x * (y⁻¹ * f) := hxF' _ h1
          have hxf : x ∈ Subgroup.centralizer ({f} : Set G) := by
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hf_eq : f = y * (y⁻¹ * f) := by group
            calc x * f = x * (y * (y⁻¹ * f)) := by rw [← hf_eq]
              _ = (x * y) * (y⁻¹ * f) := by group
              _ = (y * x) * (y⁻¹ * f) := by rw [hxy']
              _ = y * (x * (y⁻¹ * f)) := by group
              _ = y * ((y⁻¹ * f) * x) := by rw [hxg]
              _ = (y * (y⁻¹ * f)) * x := by group
              _ = f * x := by rw [← hf_eq]
          exact h.two F' ⟨hF'A, by rw [hF'4]; norm_num⟩ f hfA hf1 ⟨hxD, hxf⟩
  have hS' : ⁅uCore F', F'⁆ ⊔ deltaCore F' ≤ alphaCore F := sup_le hcomm hdelta
  refine normalClosureIn_le fun g hg => ?_
  rintro _ ⟨y, hy, rfl⟩
  exact conj_mem_alphaCore_of_mem_completion h hFA hF4 (hU'W hg) (hS' hy)

theorem alphaCore_eq_alphaCore (h : RankThreeBalance A) {F F' : Subgroup G} (hFA : F ≤ A)
    (hF4 : Nat.card F = 4) (hF'A : F' ≤ A) (hF'4 : Nat.card F' = 4) :
    alphaCore F = alphaCore F' :=
  le_antisymm (alphaCore_le_alphaCore h hF'A hF'4 hFA hF4)
    (alphaCore_le_alphaCore h hFA hF4 hF'A hF'4)

theorem deltaCore_eq_bot_of_rankThreeBalance (h : RankThreeBalance A)
    (hO : componentClassificationOddCore G = ⊥)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤) :
    ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ := by
  obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two A h.elem (by rw [h.card]; norm_num)
  have hcard : ∀ F ∈ signalizerFunctorEk 2 2 A, Nat.card F = 4 := fun F hF => by
    rw [hF.2]; norm_num
  have hconst : ∀ F ∈ signalizerFunctorEk 2 2 A, alphaCore F = alphaCore F₀ := fun F hF =>
    alphaCore_eq_alphaCore h hF.1 (hcard F hF) hF₀.1 (hcard F₀ hF₀)
  have hnormle : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) ≤
      Subgroup.normalizer (alphaCore F₀ : Set G) := by
    refine iSup₂_le fun F hF => ?_
    intro c hc
    have hcF : ∀ f ∈ F, c * f = f * c := fun f hf =>
      (Subgroup.mem_centralizer_iff.mp hc f hf).symm
    have hcF' : ∀ f ∈ F, c⁻¹ * f = f * c⁻¹ := fun f hf => by
      have := hcF f hf
      calc c⁻¹ * f = c⁻¹ * (f * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * f) * c⁻¹ := by rw [this]
        _ = f * c⁻¹ := by group
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · rw [← hconst F hF] at hy ⊢
      exact conj_mem_alphaCore hcF hy
    · rw [← hconst F hF] at hy ⊢
      have := conj_mem_alphaCore hcF' hy
      simpa [mul_assoc] using this
  have hN : (alphaCore F₀).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (alphaCore F₀ : Set G) :=
      hnormle (hgen ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  obtain ⟨d, hdF₀, hd1⟩ := exists_ne_one_of_card_eq_two_pow (n := 2) (by norm_num)
    (hF₀.2 : Nat.card F₀ = 2 ^ 2)
  obtain ⟨hodd, -⟩ := deltaStar_isCompletion h.elem (by rw [h.card]) h.weak
  have hαW : alphaCore F₀ ≤ deltaStarCompletion A :=
    (alphaCore_le_uCore (comm_of_mem_subgroup h hF₀.1) hdF₀ hd1).trans
      (uCore_le_completion hF₀.1)
  have hαodd : Odd (Nat.card (alphaCore F₀)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le hαW)
  have hαbot : alphaCore F₀ = ⊥ := by
    have hle := OddCore.maximal G (alphaCore F₀) hN hαodd
    rw [hO] at hle
    exact le_bot_iff.mp hle
  intro F hF
  have := deltaCore_le_alphaCore (F := F)
  rw [hconst F hF, hαbot] at this
  exact le_bot_iff.mp this

theorem centralizedDelta_of_rankThreeBalance (h : RankThreeBalance A)
    (hO : componentClassificationOddCore G = ⊥)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤) :
    ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F ≤ Subgroup.centralizer (A : Set G) := by
  intro F hF
  rw [deltaCore_eq_bot_of_rankThreeBalance h hO hgen F hF]
  exact bot_le

end Constancy

end CFSG.ClassicalInvolution.Balance.Bootstrap
