module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Cover4ALin
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open Subgroup Module CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

theorem odd_order_conj_ne {H : Type*} [Group H] {ρ w s : H} (hρ5 : ρ ^ 5 = 1)
    (hρw : ρ * w = w * ρ) (hw2 : w * w = 1) (hw1 : w ≠ 1) : ρ * s * ρ⁻¹ ≠ w * s := by
  intro h
  have hk : ∀ k : ℕ, ρ ^ k * s * (ρ ^ k)⁻¹ = w ^ k * s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : ρ * w ^ k * ρ⁻¹ = w ^ k := by
        have h1 : ρ * w ^ k = w ^ k * ρ := (Commute.pow_right (show Commute ρ w from hρw) k).eq
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
      calc ρ ^ (k + 1) * s * (ρ ^ (k + 1))⁻¹ = ρ * (ρ ^ k * s * (ρ ^ k)⁻¹) * ρ⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = ρ * (w ^ k * s) * ρ⁻¹ := by rw [ih]
        _ = (ρ * w ^ k * ρ⁻¹) * (ρ * s * ρ⁻¹) := by group
        _ = w ^ k * (w * s) := by rw [hc, h]
        _ = w ^ (k + 1) * s := by rw [pow_succ, mul_assoc]
  have h5 := hk 5
  have hw5 : w ^ 5 = w := by
    have h2 : w ^ 5 = (w * w) * (w * w) * w := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h2, hw2, one_mul, one_mul]
  rw [hρ5, hw5] at h5
  simp only [one_mul, inv_one, mul_one] at h5
  exact hw1 (mul_eq_right.1 h5.symm)

theorem cover_group {H : Type} [Group H] {Q : Subgroup H} [hQn : Q.Normal]
    (hQ : IsPlusExtraspecial 4 Q) {ρ w a d t : H} (hρ5 : ρ ^ 5 = 1)
    (hw : w ∈ centerOf Q) (hw1 : w ≠ 1) (hρw : ρ * w = w * ρ)
    (haQ : a ∈ Q) (ha : a ∉ centerOf Q) (hρa : ρ * a = a * ρ)
    (hdQ : d ∈ Q) (hdρ : ρ * d ≠ d * ρ) (htQ : t ∈ Q)
    (hft : ρ * t = t * ρ → t ∈ centerOf Q) :
    ∃ i : ℕ, i < 5 ∧ ρ ^ i * d * (ρ ^ i)⁻¹ * t = t * (ρ ^ i * d * (ρ ^ i)⁻¹) := by
  classical
  haveI : Finite Q := hQ.finite
  have hE : IsExtraspecialPGroup 2 Q := hQ.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE
  have hwQ : w ∈ Q := (Subgroup.mem_inf.1 hw).1
  let qw : Q := ⟨w, hwQ⟩
  have hqw : qw ∈ Subgroup.center Q := (mem_centerOf_iff qw).1 hw
  have hqw1 : qw ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have hw2 : w * w = 1 := by
    have h1 : qw * qw = 1 := by rw [← pow_two]; exact sq_eq_one_of_mem_center hE hqw
    simpa using congrArg Subtype.val h1
  have hfixed : ∀ x : Q, conjEndo hQn ρ (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of x) → ρ * (x : H) = (x : H) * ρ := by
    intro x hx
    rw [conjEndo_apply] at hx
    have hz : conjAut hQn ρ x * x⁻¹ ∈ Subgroup.center Q := by
      rw [← ofMul_of_eq_zero_iff hE, ofMul_of_mul, map_inv, ofMul_inv, hx, ← sub_eq_add_neg,
        sub_self]
    by_cases h1 : conjAut hQn ρ x * x⁻¹ = 1
    · have h2 := congrArg Subtype.val (mul_inv_eq_one.1 h1)
      rw [conjAut_apply] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2
    · have heq := eq_of_mem_center hE hz hqw h1 hqw1
      have h3 : conjAut hQn ρ x = qw * x := by
        calc conjAut hQn ρ x = conjAut hQn ρ x * x⁻¹ * x := by group
          _ = qw * x := by rw [heq]
      have h4 := congrArg Subtype.val h3
      rw [conjAut_apply] at h4
      exact absurd h4 (odd_order_conj_ne hρ5 hρw hw2 hw1)
  let β := (extraspecialQuadForm hE).polarBilin
  have hβ0 : ∀ x y : Q, β (Additive.ofMul (Abelianization.of x))
      (Additive.ofMul (Abelianization.of y)) = 0 ↔ x * y = y * x := fun x y => by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact polar_extraspecialQuadForm_eq_zero_iff hE x y
  have hσ5 : conjEndo hQn ρ ^ 5 = 1 := by
    rw [← map_pow, hρ5, map_one]
  have hσ_apply : ∀ (i : ℕ) (x : Q), (conjEndo hQn ρ ^ i) (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of (conjAut hQn (ρ ^ i) x)) := by
    intro i x
    rw [← map_pow]
    exact conjEndo_apply hQn (ρ ^ i) x
  have hβσ : ∀ u v, β (conjEndo hQn ρ u) (conjEndo hQn ρ v) = β u v := by
    intro u v
    obtain ⟨x, rfl⟩ := exists_ofMul_of u
    obtain ⟨y, rfl⟩ := exists_ofMul_of v
    rw [conjEndo_apply, conjEndo_apply]
    have hz : ∀ p q : ZMod 2, (p = 0 ↔ q = 0) → p = q := by decide
    refine hz _ _ ?_
    rw [hβ0, hβ0, ← map_mul, ← map_mul, (conjAut hQn ρ).injective.eq_iff]
  have hdim : finrank (ZMod 2) (Additive (Abelianization Q)) ≤ 8 := by
    have := hQ.finrank_quotient
    omega
  let qa : Q := ⟨a, haQ⟩
  let qd : Q := ⟨d, hdQ⟩
  let qt : Q := ⟨t, htQ⟩
  have hv₀ : Additive.ofMul (Abelianization.of qa) ≠ 0 := by
    intro h
    rw [ofMul_of_eq_zero_iff hE] at h
    exact ha ((mem_centerOf_iff qa).2 h)
  have hσv₀ : conjEndo hQn ρ (Additive.ofMul (Abelianization.of qa)) =
      Additive.ofMul (Abelianization.of qa) := by
    rw [conjEndo_apply]
    congr 3
    apply Subtype.ext
    rw [conjAut_apply]
    exact mul_inv_eq_iff_eq_mul.2 hρa
  by_contra hcon
  push Not at hcon
  have hd' : conjEndo hQn ρ (Additive.ofMul (Abelianization.of qd)) ≠
      Additive.ofMul (Abelianization.of qd) := fun h => hdρ (hfixed qd h)
  have ht' : ∀ i : ℕ, β ((conjEndo hQn ρ ^ i) (Additive.ofMul (Abelianization.of qd)))
      (Additive.ofMul (Abelianization.of qt)) = 1 := by
    intro i
    have hi : conjEndo hQn ρ ^ i = conjEndo hQn ρ ^ (i % 5) := by
      conv_lhs => rw [← Nat.div_add_mod i 5, pow_add, pow_mul, hσ5, one_pow, one_mul]
    rw [hi, hσ_apply]
    have hne : ¬ (conjAut hQn (ρ ^ (i % 5)) qd * qt = qt * conjAut hQn (ρ ^ (i % 5)) qd) := by
      intro hc
      have hc' := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, conjAut_apply] at hc'
      exact hcon (i % 5) (Nat.mod_lt _ (by norm_num)) hc'
    rcases zmod2_cases (β (Additive.ofMul (Abelianization.of (conjAut hQn (ρ ^ (i % 5)) qd)))
        (Additive.ofMul (Abelianization.of qt))) with h0 | h1
    · exact absurd ((hβ0 _ _).1 h0) hne
    · exact h1
  have hnd : ∀ w : Additive (Abelianization Q), (∀ v, β v w = 0) → w = 0 :=
    (extraspecialQuadForm_nondegenerate hE).2
  have key := cover_lin β hnd (conjEndo hQn ρ) hσ5 hβσ hdim hv₀ hσv₀ hd' ht'
  have hρt : ρ * t = t * ρ := hfixed qt key
  have htc : qt ∈ Subgroup.center Q := (mem_centerOf_iff qt).1 (hft hρt)
  have hdt : qd * qt = qt * qd := Subgroup.mem_center_iff.1 htc qd
  have hdt' := congrArg Subtype.val hdt
  simp only [Subgroup.coe_mul] at hdt'
  apply hcon 0 (by norm_num)
  simpa using hdt'

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
