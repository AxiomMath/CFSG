module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyClassical
public import CFSG.ClassicalInvolution.RouteD.TypeCThreeBridgeQuot

public section

namespace CFSG.ClassicalInvolution.RouteD.LieBridge

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.ModelFacts (StandardPairDichotomyTypes longestFundamental
  fundamentalSubgroups_subset_longest fundamentalSubgroups_eq_top_PSL_two
  standardPairDichotomyTypes_psl standardPairDichotomyTypes_psu)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped commutatorElement

@[expose] def FundamentalCentralizerNotSolvable (p : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → ∀ (t : StatedLieTag) (n e : ℕ), IsFundTag t → StatedLieAdmissible t n p e → 4 ≤ p ^ e →
    ¬ (t = .PSL ∧ n ≤ 3) → ¬ (t = .PSU ∧ n = 3) →
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ¬ Group.IsSolvable ↥(Subgroup.centralizer (R : Set (modelUniv t n p e Fact.out).K))

@[expose] def CentersExponentThree (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (e : ℕ), (t = .PSL ∨ t = .PSU) → StatedLieAdmissible t 3 p e →
    ∀ x ∈ Subgroup.center (modelUniv t 3 p e Fact.out).K, x ^ 3 = 1

@[expose] def UnitaryPairNoSplitNormalizer (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (e : ℕ), 5 ≤ p ^ e → ∀ {X : Type} [Group X] (W U V : Subgroup X),
    UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W U V →
    ¬ ∃ a ∈ U, orderOf a = p ^ e - 1 ∧ conjSub a V = V

section Lift

variable {K X : Type*} [Group K] [Group X]

theorem exists_involution_lift (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K)
    (h3 : ∀ x ∈ Subgroup.center K, x ^ 3 = 1) {R : Subgroup K} {u : X} (hu : u ∈ R.map ψ)
    (ho : orderOf u = 2) : ∃ c ∈ R, ψ c = u ∧ orderOf c = 2 := by
  obtain ⟨c, hcR, rfl⟩ := hu
  have hsq : ψ c * ψ c = 1 := by rw [← pow_two]; exact ho ▸ pow_orderOf_eq_one (ψ c)
  have hc2 : c * c ∈ Subgroup.center K := hker (by rw [MonoidHom.mem_ker, map_mul, hsq])
  have h6 : (c * c) ^ 3 = 1 := h3 _ hc2
  have hc3 : (c ^ 3) * (c ^ 3) = 1 := by
    rw [← pow_add, show 3 + 3 = 2 * 3 by norm_num, pow_mul, pow_two]
    exact h6
  have hψ : ψ (c ^ 3) = ψ c := by
    rw [map_pow, pow_succ, pow_two, hsq, one_mul]
  have hne : c ^ 3 ≠ 1 := by
    intro h
    have h1 : ψ c = 1 := by rw [← hψ, h, map_one]
    rw [h1, orderOf_one] at ho
    omega
  exact ⟨c ^ 3, R.pow_mem hcR 3, hψ, orderOf_eq_prime (by rwa [pow_two]) hne⟩

theorem commute_of_commute_map_of_exp_three (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K)
    (h3 : ∀ x ∈ Subgroup.center K, x ^ 3 = 1) {a b : K} (hb : b * b = 1)
    (h : Commute (ψ a) (ψ b)) : Commute a b := by
  have hκ : ⁅a, b⁆ ∈ ψ.ker := commutator_mem_ker ψ h
  have hcen : ⁅a, b⁆ ∈ Subgroup.center K := hker hκ
  have h1 : a * b * a⁻¹ = ⁅a, b⁆ * b := by
    rw [commutatorElement_def]
    group
  have hsq : ⁅a, b⁆ * ⁅a, b⁆ = 1 := sq_eq_one_of_conj_eq hb hcen h1
  have h3κ : ⁅a, b⁆ ^ 3 = 1 := h3 _ hcen
  have : ⁅a, b⁆ = 1 := by
    calc ⁅a, b⁆ = ⁅a, b⁆ ^ 3 := by rw [pow_succ, pow_two, hsq, one_mul]
      _ = 1 := h3κ
  exact commutatorElement_eq_one_iff_commute.mp this

end Lift

section Component

variable {p f : ℕ} [Fact p.Prime]

theorem four_le_pow_exp (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27) {t : StatedLieTag}
    {e : ℕ} (hexp : e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) : 4 ≤ p ^ e := by
  rcases hexp with rfl | ⟨-, h3e⟩
  · omega
  · by_contra hlt
    have hp3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    have he : e ≠ 0 := by
      rintro rfl
      simp at h3e
      subst h3e
      simp at hq
    have h1 : p ≤ p ^ e := Nat.le_self_pow he p
    have hpe : p ^ e = 3 := by omega
    apply h27
    rw [← h3e, pow_mul', hpe]
    norm_num

theorem component_dichotomy (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (hOrth : FundamentalCentralizerNotSolvable p) (hK3 : CentersExponentThree p)
    (hU3 : UnitaryPairNoSplitNormalizer p) {t : StatedLieTag} {n e : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hexp : e = f ∨ (t = .trialityD4 ∧ 3 * e = f))
    {X : Type} [Group X] (ψ : (modelUniv t n p e Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K)
    {R₀ R₁ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hR₁ : R₁ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {u₀ u₁ : X} (hu₀ : u₀ ∈ R₀.map ψ) (hu₁ : u₁ ∈ R₁.map ψ) (ho₀ : orderOf u₀ = 2)
    (ho₁ : orderOf u₁ = 2) (hc : u₀ * u₁ = u₁ * u₀) (hne : R₀.map ψ ≠ R₁.map ψ)
    (hnc : ¬ Commutes (R₀.map ψ) (R₁.map ψ))
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer ((R₀.map ψ : Subgroup X) : Set X)))
    (hγ : ∃ a ∈ R₀.map ψ, orderOf a = p ^ f - 1 ∧ conjSub a (R₁.map ψ) = R₁.map ψ) :
    e = f ∧
      ∃ W : Subgroup X, LinearBlockStandardPair (GaloisField p f) W (R₀.map ψ) (R₁.map ψ) := by
  classical
  have hef : t = .PSL ∨ t = .PSU → e = f := by
    intro ht
    rcases hexp with h | ⟨h, -⟩
    · exact h
    · rcases ht with ht | ht <;> rw [ht] at h <;> exact absurd h (by decide)
  by_cases hPSL : t = .PSL ∧ n = 3
  · obtain ⟨rfl, rfl⟩ := hPSL
    obtain rfl := hef (Or.inl rfl)
    have h3 := hK3 .PSL _ (Or.inl rfl) hadm
    obtain ⟨c₀, hc₀R, hc₀u, hc₀o⟩ := exists_involution_lift ψ hker h3 hu₀ ho₀
    obtain ⟨c₁, hc₁R, hc₁u, hc₁o⟩ := exists_involution_lift ψ hker h3 hu₁ ho₁
    have hc₁sq : c₁ * c₁ = 1 := by rw [← pow_two]; exact hc₁o ▸ pow_orderOf_eq_one c₁
    have hcomm : c₀ * c₁ = c₁ * c₀ :=
      (commute_of_commute_map_of_exp_three ψ hker h3 hc₁sq (by
        rw [hc₀u, hc₁u]; exact hc)).eq
    rcases (standardPairDichotomyTypes_psl hadm).map_of_commute hp2 hq ψ hker
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₀)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁) hc₀R hc₁R hc₀o hc₁o
      hcomm with h | h | ⟨-, W, hW⟩ | ⟨hF, -⟩
    · exact absurd h hne
    · exact absurd h hnc
    · exact ⟨rfl, W, hW⟩
    · exact hF.elim
  by_cases hPSU : t = .PSU ∧ n = 3
  · obtain ⟨rfl, rfl⟩ := hPSU
    obtain rfl := hef (Or.inr rfl)
    have h3 := hK3 .PSU _ (Or.inr rfl) hadm
    obtain ⟨c₀, hc₀R, hc₀u, hc₀o⟩ := exists_involution_lift ψ hker h3 hu₀ ho₀
    obtain ⟨c₁, hc₁R, hc₁u, hc₁o⟩ := exists_involution_lift ψ hker h3 hu₁ ho₁
    have hc₁sq : c₁ * c₁ = 1 := by rw [← pow_two]; exact hc₁o ▸ pow_orderOf_eq_one c₁
    have hcomm : c₀ * c₁ = c₁ * c₀ :=
      (commute_of_commute_map_of_exp_three ψ hker h3 hc₁sq (by
        rw [hc₀u, hc₁u]; exact hc)).eq
    rcases (standardPairDichotomyTypes_psu hadm).map_of_commute hp2 hq ψ hker
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₀)
      (fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR₁) hc₀R hc₁R hc₀o hc₁o
      hcomm with h | h | ⟨hF, -⟩ | ⟨-, W, hW⟩
    · exact absurd h hne
    · exact absurd h hnc
    · exact hF.elim
    · exact (hU3 _ hq W _ _ hW hγ).elim
  exfalso
  by_cases hA2 : t = .PSL ∧ n = 2
  · obtain ⟨rfl, rfl⟩ := hA2
    have h0 := fundamentalSubgroups_eq_top_PSL_two p e Fact.out hadm
    exact hne (by rw [h0 R₀ hR₀, h0 R₁ hR₁])
  · have h1 : ¬ (t = .PSL ∧ n ≤ 3) := by
      rintro ⟨rfl, hn⟩
      have hn2 : 2 ≤ n := hadm.2.2.1
      have : n = 2 ∨ n = 3 := by omega
      rcases this with rfl | rfl
      · exact hA2 ⟨rfl, rfl⟩
      · exact hPSL ⟨rfl, rfl⟩
    exact hOrth hp2 t n e hfund hadm (four_le_pow_exp hp2 hq h27 hexp) h1 hPSU R₀ hR₀
      (isSolvable_centralizer_of_ker_le_center ψ hker R₀ hsolv)

end Component

end CFSG.ClassicalInvolution.RouteD.LieBridge
