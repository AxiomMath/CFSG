module

public import CFSG.ClassicalInvolution.Q3.Q3T7E9Main
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Comp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.ModelFacts (Gen3)
open scoped commutatorElement MatrixGroups

section NoTwins

variable {X Y : Type} [Group X] [Group Y]

theorem map_conjSub_eq_self_of_noTwins (φ : X →* Y) (hφ : Function.Injective φ)
    {F₁ : Subgroup X} {z₁ t₁ : X} (hz₁ : IsUniqueInvolution F₁ z₁)
    (hzt : φ z₁ * φ t₁ = φ t₁ * φ z₁)
    (hnt : ∀ g : X, IsUniqueInvolution (conjSub g F₁) z₁ → conjSub g F₁ = F₁) :
    conjSub (φ t₁) (F₁.map φ) = F₁.map φ := by
  have h1 : t₁ * z₁ * t₁⁻¹ = z₁ := by
    apply hφ
    rw [map_mul, map_mul, map_inv, ← hzt]
    group
  have h2 : IsUniqueInvolution (conjSub t₁ F₁) z₁ := by
    have := hz₁.conj t₁
    rwa [h1] at this
  rw [← map_conjSub_eq φ t₁ F₁, hnt t₁ h2]

end NoTwins

section Comp

variable {Y : Type} [Group Y]


theorem e189_bar_comp {Λ : Set (Subgroup Y)} (hΛc : ConjInvariant Λ) (c : Q3.CompData)
    (hcv : CompValid 3 1 c) (φ : c.G →* Y) (hker : φ.ker ≤ Subgroup.center c.G)
    {K : Subgroup Y} {F₁ : Subgroup c.G} (hF₁ : F₁ ∈ c.fund) (hKF : K = F₁.map φ)
    (hKΛ : K ∈ Λ) {z t : Y} (hz : IsUniqueInvolution K z) (q : c.G)
    (hq : t = φ q * z * (φ q)⁻¹) (hzt : z * t = t * z) (hne : conjSub t K ≠ K)
    (hcomm : Commutes K (conjSub t K))
    (hnb : ∀ L ∈ Λ, ((L = K ∨ Commutes L K) ↔ (L = conjSub t K ∨ Commutes L (conjSub t K)))) :
    (∃ K'' ∈ twinSet Λ K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ K ∧ IsSylow2In R₂ K'' ∧
        Commutes R₁ R₂ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧ u * u = 1 ∧ x * u * x⁻¹ = z * t) ∨
    (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
        ∀ w ∈ conjSub x K ⊔ M', w * (z * t) = (z * t) * w) := by
  subst hKF
  rcases hcv with ⟨t', k, e, hfund, hadm, he, hc⟩ | ⟨-, hc | hc⟩
  ·
    subst hc
    have he1 : e = 1 := by
      rcases he with he | ⟨-, he⟩
      · exact he
      · omega
    subst he1
    have hne2 : ¬ (t' = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by norm_num)
    have hinj : ∀ x ∈ F₁, φ x = 1 → x = 1 :=
      injOn_of_ker_le_center hker fun r hr hcen =>
        ModelFacts.fundNoncentral_generic 3 t' k 1 hfund hadm hne2 F₁ hF₁ r hr hcen
    obtain ⟨z₁, hz₁F, hφz₁⟩ : ∃ z₁ ∈ F₁, φ z₁ = z := by
      have := hz.mem
      obtain ⟨z₁, h1, h2⟩ := this
      exact ⟨z₁, h1, h2⟩
    have hz₁ : IsUniqueInvolution F₁ z₁ := by
      refine ⟨hz₁F, fun h1 => hz.ne_one (by rw [← hφz₁, h1, map_one]), ?_, ?_⟩
      · exact hinj _ (F₁.mul_mem hz₁F hz₁F) (by rw [map_mul, hφz₁, hz.sq])
      · intro y hy hy2
        have hφy : φ y ∈ F₁.map φ := Subgroup.mem_map_of_mem φ hy
        rcases hz.unique (φ y) hφy (by rw [← map_mul, hy2, map_one]) with h | h
        · left
          exact hinj y hy h
        · right
          have : φ (y⁻¹ * z₁) = 1 := by rw [map_mul, map_inv, h, hφz₁, inv_mul_cancel]
          have := hinj _ (F₁.mul_mem (F₁.inv_mem hy) hz₁F) this
          exact inv_mul_eq_one.mp this
    have hφt : φ (q * z₁ * q⁻¹) = t := by
      rw [map_mul, map_mul, map_inv, hφz₁, ← hq]
    have hzt₁ : φ z₁ * φ (q * z₁ * q⁻¹) = φ (q * z₁ * q⁻¹) * φ z₁ := by
      rw [hφz₁, hφt]
      exact hzt
    by_cases hG2D4 : t' = .G2 ∨ t' = .trialityD4
    ·
      exfalso
      apply hne
      have hinjφ : Function.Injective φ :=
        RouteD.G2D4.injective_of_ker_le_center (by norm_num) hG2D4 k le_rfl φ hker
      have hnt : ∀ g : (modelUniv t' k 3 1 Fact.out).K, IsUniqueInvolution (conjSub g F₁) z₁ →
          conjSub g F₁ = F₁ := by
        rcases hG2D4 with rfl | rfl
        · obtain rfl : k = 0 := hadm.2.2.1
          exact fun g hg => G2D4Models.noTwins_g2 (by norm_num) le_rfl F₁ hF₁ z₁ hz₁ g hg
        · obtain rfl : k = 0 := hadm.2.2
          exact fun g hg => G2D4Models.noTwinsFund_td4 (by norm_num) hadm F₁ hF₁ z₁ hz₁ g hg
      have := map_conjSub_eq_self_of_noTwins φ hinjφ hz₁ hzt₁ hnt
      rwa [hφt] at this
    ·
      have hG2 : t' ≠ .G2 := fun h => hG2D4 (Or.inl h)
      have hD4 : t' ≠ .trialityD4 := fun h => hG2D4 (Or.inr h)
      have hmodel : E189ModelAt 3 1 t' k := e189ModelAt_three_all t' k hfund hadm
      have hfin : Finite (modelUniv t' k 3 1 Fact.out).K :=
        ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three hfund hadm
      have hk3 : ∀ x ∈ φ.ker, x ^ 3 = 1 → x = 1 := fun x hx hx3 =>
        CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t' k 3 1 Nat.prime_three
          (by norm_num) (ih8_isFundTag_mf hfund) hadm x (hker hx) hx3
      have hgen : Gen3 F₁ := gen3_of_mem_fundamentalSubgroups_three hfund hadm hG2 hD4 hF₁
      have key := e189_component_three 1 t' k hmodel hΛc φ hker hk3 hF₁ hinj hgen hKΛ hz₁ q hzt₁
        (by rw [hφz₁, hφt]; exact e189_mul_ne_one hz hne)
        (by rw [hφt]; exact hne) (by rw [hφt]; exact hcomm) (by rw [hφt]; exact hnb)
      rw [hφz₁, hφt] at key
      exact key
  ·
    subst hc
    exfalso
    apply hne
    have hF₁top : F₁ = ⊤ := hF₁
    subst hF₁top
    have hzr : z ∈ φ.range := by simpa [Subgroup.map_top] using hz.mem
    have htr : t ∈ φ.range := by
      rw [hq]
      exact φ.range.mul_mem (φ.range.mul_mem ⟨q, rfl⟩ hzr) (φ.range.inv_mem ⟨q, rfl⟩)
    exact conjSub_eq_self_of_mem (by simpa [Subgroup.map_top] using htr)
  ·
    subst hc
    exfalso
    apply hne
    have hinjφ : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans (Q3.center_m11_eq_bot Q3.m11Facts).le
    obtain ⟨z₀, h0⟩ := hF₁
    have hz0sq : z₀ * z₀ = 1 := by
      have := pow_orderOf_eq_one z₀
      rwa [h0.orderOf_eq_two, pow_two] at this
    have hφz₀ : φ z₀ = z := by
      have hmem : φ z₀ ∈ F₁.map φ := Subgroup.mem_map_of_mem φ h0.mem
      rcases hz.unique (φ z₀) hmem (by rw [← map_mul, hz0sq, map_one]) with h | h
      · exact absurd (hinjφ (by rw [h, map_one])) h0.ne_one
      · exact h
    have hφt : φ (q * z₀ * q⁻¹) = t := by
      rw [map_mul, map_mul, map_inv, hφz₀, ← hq]
    have h1 : q * z₀ * q⁻¹ * z₀ * (q * z₀ * q⁻¹)⁻¹ = z₀ := by
      apply hinjφ
      rw [map_mul, map_mul, map_inv, hφt, hφz₀, ← hzt]
      group
    have h2 : Q3.IsClassicalMember3 (conjSub (q * z₀ * q⁻¹) F₁) z₀ := by
      have := h0.conj (q * z₀ * q⁻¹)
      rwa [h1] at this
    have hF : conjSub (q * z₀ * q⁻¹) F₁ = F₁ :=
      classical_eq_of_mulEquiv_m11 (MulEquiv.refl _) h2 h0
    rw [← hφt, ← map_conjSub_eq φ (q * z₀ * q⁻¹) F₁, hF]

end Comp

end CFSG.ClassicalInvolution.Q3.Q3T7E9
