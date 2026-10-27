module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOdd
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityArith

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG.HardMathSupport.Lang.E6Descent CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.GH74.GLS.Stage2.OddAut
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (d4_outer_three_normal_form d4MonoNF d4_toral_conj
  d4Minus_outer_three_nf d4OuterThreeA2Toral_card D4MinusToral D4MinusElliptic
  d4_fieldActor_pow_three)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def EllQ1Lower : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 1 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom →
      (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom →
      normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1 →
        27 ∣ Nat.card (fixedSubgroup (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ))

@[expose] def MinusToralLower : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      D4MinusToral p f hp K σ s →
      normSeq (fieldActor (t := TwistTag.D4) σ σ) s 3 = 1 →
        27 ∣ Nat.card (fixedSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ))

@[expose] def MinusEllLower : Prop :=
  ∀ (p f : ℕ) (hp : p.Prime), p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
    ∀ n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      D4MinusElliptic p f hp K σ n →
      normSeq (fieldActor (t := TwistTag.D4) σ σ) n 3 = 1 →
        27 ∣ Nat.card (fixedSubgroup (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ))

theorem twentySeven_dvd_cocycle_q1 (h1 : EllQ1Lower) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    27 ∣ Nat.card (fixedSubgroup (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ)) := by
  obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
  rw [card_fixedSubgroup_of_conj_eq y hyn]
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨y', s, -, -, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
    rw [card_fixedSubgroup_of_conj_eq y' hconj]
    by_cases hd1 : d = 1
    · have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      rw [hs1, map_one, one_mul, card_fixedSubgroup_delta0 hp hf hK σ hσ]
      exact twentySeven_dvd_ordG2 _
    · have hcard := d4OuterThreeA2Toral_card hp hp2 hf hq hK hσ hd hd3 hd1 hsd
      rw [← card_fixSub_eq_card_fixedSubgroup, hcard]
      exact twentySeven_dvd_ordPGL3 hq
  · exact h1 p f hp hp2 hp3 hf hq K hK σ hσ n hn hnT hN

theorem twentySeven_dvd_q2 (h2 : MinusToralLower) (h3 : MinusEllLower) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα3 : α ^ 3 = 1)
    (hαord : orderOf α = 3)
    (hαout : α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  rcases d4Minus_outer_three_nf hp hp2 hp3 hf hq K hK σ hσ α hαord hαout with
    ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ | ⟨y, n, hn, hyn⟩
  · have h27 : 27 ∣ Nat.card (fixedSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [card_fixedSubgroup_delta0 hp hf hK σ hσ]
      exact twentySeven_dvd_ordG2 _
    rcases hy with hy | hy
    · rw [card_fixedSubgroup_of_conj_eq y hy]
      exact h27
    · rw [card_fixedSubgroup_of_conj_eq_inv y hy]
      exact h27
  · have hc := pow_three_of_conj_eq y hα3 hys
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hc
    rcases hys with hys | hys
    · rw [card_fixedSubgroup_of_conj_eq y hys]
      exact h2 p f hp hp2 hp3 hf hq K hK σ hσ s hs hN
    · rw [card_fixedSubgroup_of_conj_eq_inv y hys]
      exact h2 p f hp hp2 hp3 hf hq K hK σ hσ s hs hN
  · have hc := pow_three_of_conj_eq y hα3 hyn
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hc
    rcases hyn with hyn | hyn
    · rw [card_fixedSubgroup_of_conj_eq y hyn]
      exact h3 p f hp hp2 hp3 hf hq K hK σ hσ n hn hN
    · rw [card_fixedSubgroup_of_conj_eq_inv y hyn]
      exact h3 p f hp hp2 hp3 hf hq K hK σ hσ n hn hN

theorem twentySeven_dvd_fixedSubgroup_odd (h1 : EllQ1Lower) (h2 : MinusToralLower)
    (h3 : MinusEllLower) {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hα1 : α ≠ 1 := fun h => hαin ⟨1, by rw [h]; exact map_one _⟩
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hq3 : ¬ 3 ∣ p ^ f := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq : (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by omega
  rcases hq with hq | hq
  · obtain ⟨g, hg, hφ | hφ⟩ := d4_outer_three_normal_form hp hp2 hf K hK σ hσ α hαord hαin
    · rw [hφ]
      exact twentySeven_dvd_cocycle_q1 h1 hp hp2 hp3 hf hq hK σ hσ g hg
    · have := twentySeven_dvd_cocycle_q1 h1 hp hp2 hp3 hf hq hK σ hσ g hg
      rwa [← hφ, oddFixedSubgroup_inv] at this
  · exact twentySeven_dvd_q2 h2 h3 hp hp2 hp3 hf hq hK σ hσ α hα3 hαord hαin

end CFSG.HardMathSupport.Lang.E27Lie
