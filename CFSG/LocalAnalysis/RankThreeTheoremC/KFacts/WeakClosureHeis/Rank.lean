module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Shape
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open Subgroup

theorem le_pRank_of_injective_heis {p : ℕ} (hp : 1 < p) {X : Type*} [Group X] [Finite X]
    {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) {k : ℕ}
    (hA : Nat.card A = p ^ k) (f : A →* X) (hf : Function.Injective f) {H : Subgroup X}
    (hH : f.range ≤ H) : k ≤ CFSG.Open.pRank p H := by
  have hbdd : BddAbove {k | ∃ E : Subgroup X, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ k} := by
    refine ⟨Nat.card X, fun m hm => ?_⟩
    obtain ⟨E', -, -, hE'⟩ := hm
    have h1 : p ^ m ≤ Nat.card X := hE' ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self hp).le.trans h1
  refine le_csSup hbdd ⟨f.range, hH, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow, map_one]
  · rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem three_le_pRank_heis {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X] {Q Q₀ Q₁ : Subgroup X}
    (h : HeisShape p Q Q₀ Q₁) : 3 ≤ CFSG.Open.pRank p Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ₀p : IsPGroup p Q₀ := IsPGroup.to_le h.pgrp h.left_le
  have hQ₀nt : Nontrivial Q₀ := (Subgroup.nontrivial_iff_ne_bot Q₀).2 h.ne_bot
  obtain ⟨n, hn, hcard⟩ := (hQ₀p.nontrivial_iff_card).1 hQ₀nt
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q₀) p
    (hcard ▸ dvd_pow_self p hn.ne')
  have hxo : orderOf (x : X) = p := by rw [Subgroup.orderOf_coe]; exact hx
  set E₁ : Subgroup X := Subgroup.zpowers (x : X) with hE₁
  have hE₁Q₀ : E₁ ≤ Q₀ := (Subgroup.zpowers_le).2 x.2
  have hE₁card : Nat.card E₁ = p := by rw [hE₁, Nat.card_zpowers, hxo]
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Q₁) p (n := 2)
    (by rw [h.card]; exact pow_dvd_pow p (by norm_num))
  set V : Subgroup X := K.map Q₁.subtype with hV
  have hVQ₁ : V ≤ Q₁ := Subgroup.map_subtype_le K
  have hVcard : Nat.card V = p ^ 2 := by
    rw [hV, Subgroup.card_map_of_injective Q₁.subtype_injective, hK]
  haveI : IsMulCommutative V := IsPGroup.isMulCommutative_of_card_eq_prime_sq hVcard
  have hcomm : ∀ a : E₁, ∀ b : V, Commute (a : X) (b : X) := fun a b =>
    h.comm a (hE₁Q₀ a.2) b (hVQ₁ b.2)
  let f : E₁ × V →* X := MonoidHom.noncommCoprod E₁.subtype V.subtype hcomm
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : X) * b = 1 := hab
    have ha : (a : X) ∈ Q₀ ⊓ Q₁ := Subgroup.mem_inf.2 ⟨hE₁Q₀ a.2, by
      rw [eq_inv_of_mul_eq_one_left hab']
      exact Q₁.inv_mem (hVQ₁ b.2)⟩
    rw [h.disj, Subgroup.mem_bot] at ha
    have hb : (b : X) = 1 := by rw [ha, one_mul] at hab'; exact hab'
    rw [Prod.mk_eq_one]
    exact ⟨Subtype.ext ha, Subtype.ext hb⟩
  have hc₁ : IsMulCommutative E₁ := by
    rw [hE₁]; infer_instance
  have hpow₁ : ∀ a : E₁, a ^ p = 1 := by
    rintro ⟨a, ha⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    apply Subtype.ext
    change ((x : X) ^ k) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo, pow_orderOf_eq_one,
      one_zpow]
  have hpow₂ : ∀ b : V, b ^ p = 1 := by
    rintro ⟨b, hb⟩
    exact Subtype.ext (h.exp b (hVQ₁ hb))
  refine le_pRank_of_injective_heis hp.one_lt (A := E₁ × V) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm' a c) (mul_comm' b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (hpow₁ a) (hpow₂ b)
  · rw [Nat.card_prod, hE₁card, hVcard, ← pow_succ']
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact h.mul_mem (hE₁Q₀ a.2) (hVQ₁ b.2)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
