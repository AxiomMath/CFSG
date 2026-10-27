module

public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Stab

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Irreducible' (Y : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ W : Submodule (ZMod 2) V, Y ≤ stab W → W = ⊥ ∨ W = ⊤

theorem exists_fixed_ne_zero [Finite V] [Nontrivial V] (N : Subgroup (V ≃ₗ[ZMod 2] V))
    (hp : IsPGroup 2 N) : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ N, a v = v := by
  have h := hp.card_modEq_card_fixedPoints V
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hcard : Nat.card V = 2 ^ finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hpos : 0 < finrank (ZMod 2) V := Module.finrank_pos
  have h2 : 2 ∣ Nat.card V := by
    rw [hcard]; exact dvd_pow_self 2 hpos.ne'
  have h3 : 2 ∣ Nat.card (MulAction.fixedPoints N V) :=
    (Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 h2)))
  have hne : (0 : V) ∈ MulAction.fixedPoints N V := fun a => by
    show (a : V ≃ₗ[ZMod 2] V) 0 = 0
    simp
  have hpos' : 0 < Nat.card (MulAction.fixedPoints N V) :=
    Nat.card_pos_iff.2 ⟨⟨⟨0, hne⟩⟩, inferInstance⟩
  have h4 : 2 ≤ Nat.card (MulAction.fixedPoints N V) := Nat.le_of_dvd hpos' h3
  have : Nontrivial (MulAction.fixedPoints N V) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := exists_pair_ne (MulAction.fixedPoints N V)
  have key : ∀ z : V, z ∈ MulAction.fixedPoints N V → ∀ a ∈ N, a z = z :=
    fun z hz a ha => hz ⟨a, ha⟩
  by_cases h0 : x = 0
  · refine ⟨y, fun hy0 => hxy ?_, key y hy⟩
    apply Subtype.ext
    simp [h0, hy0]
  · exact ⟨x, h0, key x hx⟩

@[expose] def fixSub (N : Subgroup (V ≃ₗ[ZMod 2] V)) : Submodule (ZMod 2) V where
  carrier := {v | ∀ a ∈ N, a v = v}
  add_mem' := fun {u v} hu hv a ha => by simp [hu a ha, hv a ha]
  zero_mem' := fun a _ => by simp
  smul_mem' := fun c v hv a ha => by simp [hv a ha]

theorem eq_bot_of_irreducible [Finite V] [Nontrivial V] {Y : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hY : Irreducible' Y) (N : Subgroup (V ≃ₗ[ZMod 2] V))
    (hnorm : ∀ g ∈ Y, ∀ a ∈ N, g * a * g⁻¹ ∈ N) (hN : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero N hN
  have key : ∀ g ∈ Y, ∀ u, u ∈ fixSub N → g u ∈ fixSub N := by
    intro g hg u hu a ha
    have h1 : (g⁻¹ * a * g) ∈ N := by
      have := hnorm g⁻¹ (Y.inv_mem hg) a ha
      simpa using this
    have h2 : (g⁻¹ * a * g) u = u := hu _ h1
    calc a (g u) = g (g⁻¹ (a (g u))) := by simp
      _ = g ((g⁻¹ * a * g) u) := rfl
      _ = g u := by rw [h2]
  have hinv : Y ≤ stab (fixSub N) := by
    intro g hg w
    refine ⟨fun hgw => ?_, key g hg w⟩
    have := key g⁻¹ (Y.inv_mem hg) _ hgw
    simpa using this
  rcases hY _ hinv with h | h
  · exact absurd (h ▸ (show v ∈ fixSub N from hv)) (by simpa using hv0)
  · rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    apply LinearEquiv.ext
    intro u
    have : u ∈ fixSub N := h ▸ Submodule.mem_top
    exact this a ha

@[expose] def torsionSub (A : Subgroup (V ≃ₗ[ZMod 2] V)) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (s : ℕ) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {a | a ∈ A ∧ a ^ s = 1}
  one_mem' := ⟨A.one_mem, one_pow s⟩
  mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by
    rw [(Commute.mul_pow (hA a ha.1 b hb.1)), ha.2, hb.2, one_mul]⟩
  inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩

theorem exists_normal_prime_of_irreducible [Finite V] [Nontrivial V]
    {Y : Subgroup (V ≃ₗ[ZMod 2] V)} (hY : Irreducible' Y) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrY : r ∣ Nat.card Y) (hrY2 : ¬ r ^ 2 ∣ Nat.card Y)
    (hpf : ∀ q, q.Prime → q ∣ Nat.card Y → q = 2 ∨ q = r) :
    ∃ P : Subgroup (V ≃ₗ[ZMod 2] V), P ≤ Y ∧ Nat.card P = r ∧
      ∀ g ∈ Y, ∀ a ∈ P, g * a * g⁻¹ ∈ P := by
  have : Fact r.Prime := ⟨hr⟩
  have hsolv : Group.IsSolvable Y := by
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have hsub : (Nat.card Y).primeFactors ⊆ {2, r} := by
      intro q hq
      rw [Nat.mem_primeFactors] at hq
      rcases hpf q hq.1 hq.2.1 with h | h <;> simp [h]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  have hYbot : Y ≠ ⊥ := by
    intro h
    have : Nat.card Y = 1 := by rw [h]; exact Subgroup.card_bot
    rw [this] at hrY
    exact hr.one_lt.ne' (Nat.dvd_one.1 hrY)
  obtain ⟨A, hAY, hAbot, hAcomm, hAnorm⟩ :=
    CFSG.LinearGroups.exists_abelian_normalized_of_isSolvable Y hYbot
  have hAcard : Nat.card A ≠ 1 := fun h => hAbot (Subgroup.card_eq_one.1 h)
  obtain ⟨s, hs, hsA⟩ := Nat.exists_prime_and_dvd hAcard
  have : Fact s.Prime := ⟨hs⟩
  have hsY : s ∣ Nat.card Y := hsA.trans (Subgroup.card_dvd_of_le hAY)
  obtain ⟨a0, ha0⟩ := exists_prime_orderOf_dvd_card' (G := A) s hsA
  set N := torsionSub A hAcomm s with hN
  have hNnorm : ∀ g ∈ Y, ∀ a ∈ N, g * a * g⁻¹ ∈ N := by
    intro g hg a ha
    refine ⟨hAnorm g hg a ha.1, ?_⟩
    rw [conj_pow, ha.2]; group
  have ha0N : (a0 : V ≃ₗ[ZMod 2] V) ∈ N := by
    refine ⟨a0.2, ?_⟩
    have := pow_orderOf_eq_one a0
    rw [ha0] at this
    exact congrArg Subtype.val this
  have ha01 : (a0 : V ≃ₗ[ZMod 2] V) ≠ 1 := by
    intro h
    have h1 : a0 = 1 := Subtype.ext h
    rw [h1, orderOf_one] at ha0
    exact hs.one_lt.ne ha0
  rcases hpf s hs hsY with h2 | hsr
  · subst h2
    have hN2 : IsPGroup 2 N := fun a => ⟨1, Subtype.ext (by simpa using a.2.2)⟩
    have := eq_bot_of_irreducible hY N hNnorm hN2
    rw [this] at ha0N
    exact (ha01 (Subgroup.mem_bot.1 ha0N)).elim
  · subst hsr
    have hNY : N ≤ Y := fun a ha => hAY ha.1
    have hpg : IsPGroup s N := fun a => ⟨1, Subtype.ext (by simpa using a.2.2)⟩
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hdvd : Nat.card N ∣ Nat.card Y := Subgroup.card_dvd_of_le hNY
    have hk1 : k = 1 := by
      have hk0 : k ≠ 0 := by
        rintro rfl
        have : N = ⊥ := Subgroup.card_eq_one.1 (by simpa using hk)
        rw [this] at ha0N
        exact ha01 (Subgroup.mem_bot.1 ha0N)
      by_contra hk1
      have h2 : s ^ 2 ∣ s ^ k := pow_dvd_pow s (by omega)
      rw [← hk] at h2
      exact hrY2 (h2.trans hdvd)
    exact ⟨N, hNY, by rw [hk, hk1, pow_one], hNnorm⟩

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
