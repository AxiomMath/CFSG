module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePermOrb
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePermCount

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open MulAction

theorem pmb_mul_card_le_of_fixed {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    [DecidableEq X] {r : ℕ} [NeZero r] {x₀ : X} (hx₀ : ∀ g : G, g • x₀ = x₀) :
    r * Nat.card {u : X → ZMod r //
        ∑ x, u x = 0 ∧ ∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} ≤
      Nat.card {u : X → ZMod r // ∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} := by
  let δ : X → ZMod r := fun x => if x = x₀ then 1 else 0
  have hδ : ∀ (g : G) x, δ (g⁻¹ • x) = δ x := by
    intro g x
    have hiff : g⁻¹ • x = x₀ ↔ x = x₀ := by rw [inv_smul_eq_iff, hx₀ g]
    simp only [δ, hiff]
  have hδsum : ∑ x, δ x = 1 := by simp [δ]
  have hsum : ∀ (a : ZMod r) (u : X → ZMod r), ∑ x, (u + a • δ) x = ∑ x, u x + a := by
    intro a u
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hδsum, mul_one]
  let Φ : ZMod r × {u : X → ZMod r //
        ∑ x, u x = 0 ∧ ∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} →
      {u : X → ZMod r // ∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} :=
    fun p => ⟨p.2.1 + p.1 • δ, fun g => by
      obtain ⟨c, hc⟩ := p.2.2.2 g
      refine ⟨c, fun x => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hδ g x, ← hc x]
      ring⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨a, u⟩ ⟨a', u'⟩ h
    have h1 : u.1 + a • δ = u'.1 + a' • δ := congrArg Subtype.val h
    have ha : a = a' := by
      have h2 := congrArg (fun v : X → ZMod r => ∑ x, v x) h1
      simp only [hsum, u.2.1, u'.2.1, zero_add] at h2
      exact h2
    subst ha
    rw [add_left_inj] at h1
    rw [Subtype.ext h1]
  calc r * Nat.card {u : X → ZMod r //
        ∑ x, u x = 0 ∧ ∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c}
      = Nat.card (ZMod r × {u : X → ZMod r //
        ∑ x, u x = 0 ∧ ∀ g : G, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c}) := by
        rw [Nat.card_prod, Nat.card_zmod]
    _ ≤ _ := Nat.card_le_card_of_injective Φ hΦ

theorem perm_module_bound {r m : ℕ} [Fact r.Prime] (hr : r ≠ 2) (hm : 4 ≤ m)
    (B : Subgroup (Equiv.Perm (Fin m))) (hBp : ∀ b ∈ B, b ^ r = 1)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    Nat.card B * Nat.card {u : Fin m → ZMod r //
      ∑ i, u i = 0 ∧ ∀ b ∈ B, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c} ≤ r ^ (m - 1) := by
  classical
  have hp : r.Prime := Fact.out
  have hS : Nat.card {u : Fin m → ZMod r //
      ∑ i, u i = 0 ∧ ∀ b ∈ B, ∃ c : ZMod r, ∀ i, u (b⁻¹ i) - u i = c} =
      Nat.card {u : Fin m → ZMod r //
        ∑ i, u i = 0 ∧ ∀ g : B, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun u =>
      and_congr_right fun _ => ⟨fun h g => h g g.2, fun h b hb => h ⟨b, hb⟩⟩)
  rw [hS]
  have hSU : Nat.card {u : Fin m → ZMod r //
        ∑ i, u i = 0 ∧ ∀ g : B, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} ≤
      Nat.card {u : Fin m → ZMod r // ∀ g : B, ∃ c : ZMod r, ∀ x, u (g⁻¹ • x) - u x = c} :=
    Nat.card_le_card_of_injective (fun u => ⟨u.1, u.2.2⟩) fun u v h =>
      Subtype.ext (congrArg Subtype.val h :)
  have hG : IsPGroup r B := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hBp g g.2)⟩
  have hc : ∀ g h : B, g * h = h * g := fun g h => Subtype.ext (hBc g g.2 h h.2)
  set n : orbitRel.Quotient B (Fin m) → ℕ := fun ω => Nat.card (orbit B ω.out) with hn
  have hsum : ∑ ω, n ω = m := by
    rw [hn, pmb_sum_card_orbit, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hprod : Nat.card B ≤ ∏ ω, n ω := pmb_card_le_prod_card_orbit hc
  have ht : r ^ Nat.card (orbitRel.Quotient B (Fin m)) * ∏ ω, n ω = ∏ ω, (r * n ω) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hfinish : ∀ y, r * y ≤ r ^ m → y ≤ r ^ (m - 1) := by
    intro y hy
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ m), pow_succ'] at hy
    exact Nat.le_of_mul_le_mul_left hy hp.pos
  apply hfinish
  by_cases hfix : ∃ x₀ : Fin m, ∀ g : B, g • x₀ = x₀
  · obtain ⟨x₀, hx₀⟩ := hfix
    have h1 := pmb_mul_card_le_of_fixed (r := r) hx₀
    have h2 := pmb_card_affine_le (r := r) hG x₀
    have h3 : Nat.card (orbit B x₀) = 1 :=
      Nat.card_eq_fintype_card.trans (mem_fixedPoints_iff_card_orbit_eq_one.mp hx₀)
    rw [h3, mul_one] at h2
    calc r * (Nat.card B * _) = Nat.card B * (r * _) := by ring
      _ ≤ (∏ ω, n ω) * r ^ Nat.card (orbitRel.Quotient B (Fin m)) :=
        Nat.mul_le_mul hprod (h1.trans h2)
      _ = ∏ ω, (r * n ω) := by rw [mul_comm, ht]
      _ ≤ r ^ (∑ ω, n ω) := pmb_prod_mul_le_pow hp.one_lt.ne' n
      _ = r ^ m := by rw [hsum]
  push Not at hfix
  have hn1 : ∀ ω, n ω ≠ 1 ∧ ∃ ℓ, n ω = r ^ ℓ := by
    refine fun ω => ⟨fun h => ?_, hG.card_orbit ω.out⟩
    obtain ⟨g, hg⟩ := hfix ω.out
    have hfp : ω.out ∈ fixedPoints B (Fin m) :=
      mem_fixedPoints_iff_card_orbit_eq_one.mpr (Nat.card_eq_fintype_card.symm.trans h)
    exact hg (hfp g)
  let ω₀ : orbitRel.Quotient B (Fin m) := Quotient.mk'' ⟨0, by omega⟩
  have h2 := pmb_card_affine_le (r := r) hG ω₀.out
  calc r * (Nat.card B * _)
      ≤ r * ((∏ ω, n ω) * (r ^ Nat.card (orbitRel.Quotient B (Fin m)) * n ω₀)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hprod (hSU.trans h2))
    _ = r * n ω₀ * ∏ ω, (r * n ω) := by rw [← ht]; ring
    _ ≤ r ^ (∑ ω, n ω) := pmb_mul_prod_mul_le_pow hr n hn1 (by rw [hsum]; exact hm) ω₀
    _ = r ^ m := by rw [hsum]

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
