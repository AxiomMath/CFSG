module

public import CFSG.GH74.Generic.BProg.B3.KG531Defs
public import CFSG.GH74.Generic.S1.KL5Ord
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

namespace KG531Crit

theorem card_mul_dvd_of_commute_disjoint {S : Type} [Group S] {A B C : Subgroup S} (hA : A ≤ C)
    (hB : B ≤ C) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥) :
    Nat.card ↥A * Nat.card ↥B ∣ Nat.card ↥C := by
  let μ : ↥A × ↥B →* S := A.subtype.noncommCoprod B.subtype (fun a b => hcomm a a.2 b b.2)
  have hμ : ∀ x : ↥A × ↥B, μ x = (x.1 : S) * (x.2 : S) := fun x => rfl
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : S) * (b : S) = 1 := hab
    have ha : (a : S) = (b : S)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have hmem : (a : S) ∈ A ⊓ B := ⟨a.2, by rw [ha]; exact B.inv_mem b.2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hb1 : (b : S) = 1 := by
      rw [hmem, one_mul] at hab'
      exact hab'
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb1)
  have hrange : μ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [hμ]
    exact C.mul_mem (hA x.1.2) (hB x.2.2)
  have hc : Nat.card ↥μ.range = Nat.card ↥A * Nat.card ↥B := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hc]
  exact Subgroup.card_dvd_of_le hrange

theorem card_psl_two {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : StatedClassicalModel X .PSL 2 p f) :
    Nat.card X = p ^ f * (p ^ (2 * f) - 1) / 2 := by
  have hq := CFSG.GH74.Generic.S1.kl5_odd_pow (f := f) hp hp2
  have hm := CFSG.GH74.Generic.S1.kl5_card_mul_gcd_psl (n := 2) le_rfl hX
  have hq1 : 2 ∣ p ^ f - 1 := by omega
  rw [show 2 * (2 - 1) / 2 = 1 from rfl, show Finset.Icc 2 2 = ({2} : Finset ℕ) by decide,
    Finset.prod_singleton, pow_one, Nat.gcd_eq_left hq1, ← pow_mul, mul_comm f 2] at hm
  omega

theorem card_sl_two {X : Type} [Group X] {p f : ℕ}
    (hX : HasSL2Model X (fun q => q = p ^ f)) :
    Nat.card X = p ^ f * (p ^ (2 * f) - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hX
  rw [Nat.card_congr (e.toEquiv.trans (specialLinearGroupEquivStatedSL 2 F).symm.toEquiv),
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF, ← pow_mul, mul_comm f 2]

theorem sq_dvd_expr {q : ℕ} (hq : q % 2 = 1) :
    q ^ 2 ∣ (q * (q ^ 2 - 1) / 2) * (q * (q ^ 2 - 1)) := by
  obtain ⟨m, hm⟩ := CFSG.GH74.Generic.S1.kl5_eight_dvd_sq_sub_one hq
  rw [hm, show q * (8 * m) = 2 * (q * (4 * m)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact ⟨32 * m ^ 2, by ring⟩

theorem thirty_two_dvd_expr {q : ℕ} (hq : q % 2 = 1) :
    32 ∣ (q * (q ^ 2 - 1) / 2) * (q * (q ^ 2 - 1)) := by
  obtain ⟨m, hm⟩ := CFSG.GH74.Generic.S1.kl5_eight_dvd_sq_sub_one hq
  rw [hm, show q * (8 * m) = 2 * (q * (4 * m)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact ⟨q ^ 2 * m ^ 2, by ring⟩

end KG531Crit

section Criteria

variable {S : Type} [Group S] [Finite S] {t : S} {B₁ B₂ : Subgroup S} {p f : ℕ}

omit [Finite S] in
theorem KG531Cfg.t_not_mem₁ (h : KG531Cfg t B₁ B₂ p f) : t ∉ B₁ := by
  intro ht
  have hle : B₁ ≤ centralizer ({t} : Set S) := h.comp₁.1
  have hcent : (⟨t, ht⟩ : ↥B₁) ∈ center ↥B₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
  rw [h.center₁, Subgroup.mem_bot] at hcent
  have h1 : t = 1 := congrArg Subtype.val hcent
  have h2 := h.t_ord
  rw [h1, orderOf_one] at h2
  omega

omit [Finite S] in
theorem KG531Cfg.false_of_star (h : KG531Cfg t B₁ B₂ p f)
    (hstar : ∀ B : Subgroup S, IsCompIn (centralizer ({t} : Set S)) B → t ∈ B) : False :=
  h.t_not_mem₁ (hstar B₁ h.comp₁)

omit [Finite S] in
theorem KG531Cfg.false_of_perfect (h : KG531Cfg t B₁ B₂ p f)
    (hperf : ∀ P : Subgroup S, P ≤ centralizer ({t} : Set S) → Group.IsPerfect ↥P → t ∉ P) :
    False := by
  have hle : B₂ ≤ centralizer ({t} : Set S) := h.comp₂.1
  have hP : Group.IsPerfect ↥(B₂.subgroupOf (centralizer ({t} : Set S))) := h.comp₂.2.1.1
  have hP' : Group.IsPerfect ↥B₂ := by
    have := hP
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).surjective
  exact hperf B₂ hle hP' h.t_mem

omit [Finite S] in
theorem KG531Cfg.card_dvd (h : KG531Cfg t B₁ B₂ p f) :
    (p ^ f * (p ^ (2 * f) - 1) / 2) * (p ^ f * (p ^ (2 * f) - 1)) ∣
      Nat.card ↥(centralizer ({t} : Set S)) := by
  have hz : Nat.card ↥(center ↥B₁) = 1 := by
    rw [h.center₁]
    exact Subgroup.card_bot
  have hc : Nat.card ↥B₁ = Nat.card (↥B₁ ⧸ center ↥B₁) * Nat.card ↥(center ↥B₁) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hz, mul_one, KG531Crit.card_psl_two h.prime h.odd h.model₁] at hc
  have h2 : Nat.card ↥B₂ = p ^ f * (p ^ (2 * f) - 1) := KG531Crit.card_sl_two h.model₂
  have hdvd := KG531Crit.card_mul_dvd_of_commute_disjoint h.comp₁.1 h.comp₂.1 h.comm h.disj
  rwa [hc, h2] at hdvd

theorem not_dvd_of_card {N : ℕ} (h9 : ¬ 259200 ∣ N) (h27 : ¬ 3 ^ 6 ∣ N)
    (hr : ∀ r : ℕ, r.Prime → 5 ≤ r → r ^ 2 ∣ N →
      ¬ r ^ 4 ∣ N ∧ ¬ (r * (r ^ 2 - 1) / 2) * (r * (r ^ 2 - 1)) ∣ N)
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    ¬ (p ^ f * (p ^ (2 * f) - 1) / 2) * (p ^ f * (p ^ (2 * f) - 1)) ∣ N := by
  intro hd
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  have hq := CFSG.GH74.Generic.S1.kl5_odd_pow (f := f) hp hp2
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have hsq : p ^ (2 * f) ∣ N := by
    rw [hpow]
    refine (KG531Crit.sq_dvd_expr hq).trans ?_
    rw [hpow] at hd
    exact hd
  by_cases hp3 : p = 3
  · subst hp3
    have hf2 : 2 ≤ f := by
      by_contra hlt
      have : f = 1 := by omega
      subst this
      simp at h5
    rcases Nat.eq_or_lt_of_le hf2 with h2 | h2
    · subst h2
      have e : (3 ^ 2 * (3 ^ (2 * 2) - 1) / 2) * (3 ^ 2 * (3 ^ (2 * 2) - 1)) = 259200 := by
        norm_num
      rw [e] at hd
      exact h9 hd
    · exact h27 ((pow_dvd_pow 3 (by omega : 6 ≤ 2 * f)).trans hsq)
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
      · exact absurd h hp2
      · exact absurd h hp3
      · subst h
        norm_num at hp
      · exact h
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hf) with h1 | h1
    · subst h1
      have hsq' : p ^ 2 ∣ N := by simpa using hsq
      have hd' : (p * (p ^ 2 - 1) / 2) * (p * (p ^ 2 - 1)) ∣ N := by simpa using hd
      exact (hr p hp hp5 hsq').2 hd'
    · have h2N : p ^ 2 ∣ N := (pow_dvd_pow p (by omega : 2 ≤ 2 * f)).trans hsq
      have h4N : p ^ 4 ∣ N := (pow_dvd_pow p (by omega : 4 ≤ 2 * f)).trans hsq
      exact (hr p hp hp5 h2N).1 h4N

end Criteria

end CFSG.GH74.Generic.BProg.B3
