module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private lemma neg_eq_self (v : V) : -v = v := by
  rw [← neg_one_smul (ZMod 2) v, show (-1 : ZMod 2) = 1 by decide, one_smul]

private lemma add_self_eq_zero (v : V) : v + v = 0 := by
  have h : (2 : ZMod 2) • v = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  simpa [two_smul] using h

private lemma pow_mod_five (n : ℕ) : a₀ ^ (n % 5) = a₀ ^ n := by
  have h : a₀ ^ (n % orderOf a₀) = a₀ ^ n := pow_mod_orderOf a₀ n
  rwa [orderOf_a₀] at h

private lemma pow_val_add (a b : ZMod 5) :
    a₀ ^ ((a + b).val) = a₀ ^ a.val * a₀ ^ b.val := by
  rw [ZMod.val_add, pow_mod_five, pow_add]

private lemma zmod5_val_one : (1 : ZMod 5).val = 1 := by
  haveI : Fact (1 < 5) := ⟨by norm_num⟩
  exact ZMod.val_one 5

private noncomputable def v₀ (d : A5 × A5 → V) : V :=
  ∑ p : ZMod 5 × ZMod 5, d (a₀ ^ p.1.val, a₀ ^ p.2.val)

private lemma sigma_d_apply (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (d : A5 × A5 → V)
    (hd : ∀ g h : A5 × A5, d (g * h) = d g + σ g (d h)) (p₀ p : ZMod 5 × ZMod 5) :
    σ (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) (d (a₀ ^ p.1.val, a₀ ^ p.2.val)) =
      d (a₀ ^ (p₀.1 + p.1).val, a₀ ^ (p₀.2 + p.2).val) +
        d (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) := by
  have hsub :
      σ (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) (d (a₀ ^ p.1.val, a₀ ^ p.2.val)) =
        d ((a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) * (a₀ ^ p.1.val, a₀ ^ p.2.val)) -
          d (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact (hd (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) (a₀ ^ p.1.val, a₀ ^ p.2.val)).symm
  rw [hsub, sub_eq_add_neg, neg_eq_self]
  have hs : (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) * (a₀ ^ p.1.val, a₀ ^ p.2.val) =
      (a₀ ^ (p₀.1 + p.1).val, a₀ ^ (p₀.2 + p.2).val) := by
    simp only [Prod.mk_mul_mk, Prod.mk.injEq]
    exact ⟨(pow_val_add p₀.1 p.1).symm, (pow_val_add p₀.2 p.2).symm⟩
  rw [hs]

private lemma sigma_v₀ (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (d : A5 × A5 → V)
    (hd : ∀ g h : A5 × A5, d (g * h) = d g + σ g (d h)) (p₀ : ZMod 5 × ZMod 5) :
    σ (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) (v₀ d) =
      v₀ d + d (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) := by
  unfold v₀
  rw [map_sum]
  simp_rw [sigma_d_apply σ d hd p₀]
  rw [Finset.sum_add_distrib]
  congr 1
  · have hshift :
        (∑ p : ZMod 5 × ZMod 5,
            d (a₀ ^ (p₀.1 + p.1).val, a₀ ^ (p₀.2 + p.2).val)) =
          ∑ p : ZMod 5 × ZMod 5, d (a₀ ^ p.1.val, a₀ ^ p.2.val) := by
      simpa only [Equiv.coe_addLeft, Prod.fst_add, Prod.snd_add] using
        (Equiv.sum_comp (Equiv.addLeft p₀)
          (fun p : ZMod 5 × ZMod 5 => d (a₀ ^ p.1.val, a₀ ^ p.2.val)))
    exact hshift
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card]
    show (5 * 5 : ℕ) • d (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val) =
      d (a₀ ^ p₀.1.val, a₀ ^ p₀.2.val)
    rw [show (5 * 5 : ℕ) = 25 by norm_num]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 25,
        show ((25 : ℕ) : ZMod 2) = 1 by decide, one_smul]

private noncomputable def d' (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (d : A5 × A5 → V) :
    A5 × A5 → V :=
  fun g => d g + (σ g (v₀ d) + v₀ d)

private lemma crossed_add {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {d e : A5 × A5 → V}
    (hd : ∀ g h : A5 × A5, d (g * h) = d g + σ g (d h))
    (he : ∀ g h : A5 × A5, e (g * h) = e g + σ g (e h)) :
    ∀ g h : A5 × A5, (d + e) (g * h) = (d + e) g + σ g ((d + e) h) := by
  intro g h
  simp only [Pi.add_apply, hd g h, he g h, map_add]
  abel

private lemma d'_crossed (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (d : A5 × A5 → V)
    (hd : ∀ g h : A5 × A5, d (g * h) = d g + σ g (d h)) :
    ∀ g h : A5 × A5, d' σ d (g * h) = d' σ d g + σ g (d' σ d h) := by
  let e : A5 × A5 → V := fun g => σ g (v₀ d) - v₀ d
  have he : ∀ g h : A5 × A5, e (g * h) = e g + σ g (e h) := by
    intro g h
    change σ (g * h) (v₀ d) - v₀ d =
      (σ g (v₀ d) - v₀ d) + σ g (σ h (v₀ d) - v₀ d)
    rw [map_mul, LinearEquiv.mul_apply, map_sub]
    abel
  have hd' : d' σ d = d + e := by
    funext g
    show d g + (σ g (v₀ d) + v₀ d) = d g + (σ g (v₀ d) - v₀ d)
    rw [sub_eq_add_neg, neg_eq_self]
  intro g h
  rw [hd']
  exact crossed_add hd he g h

private lemma d'_eq_zero_on_S (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (d : A5 × A5 → V)
    (hd : ∀ g h : A5 × A5, d (g * h) = d g + σ g (d h)) (p : ZMod 5 × ZMod 5) :
    d' σ d (a₀ ^ p.1.val, a₀ ^ p.2.val) = 0 := by
  unfold d'
  rw [sigma_v₀ σ d hd p]
  have h : d (a₀ ^ p.1.val, a₀ ^ p.2.val) +
        ((v₀ d + d (a₀ ^ p.1.val, a₀ ^ p.2.val)) + v₀ d) =
      (d (a₀ ^ p.1.val, a₀ ^ p.2.val) + d (a₀ ^ p.1.val, a₀ ^ p.2.val)) +
        (v₀ d + v₀ d) := by abel
  rw [h, add_self_eq_zero, add_self_eq_zero, zero_add]

private lemma d'_fst (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (d : A5 × A5 → V)
    (hd : ∀ g h : A5 × A5, d (g * h) = d g + σ g (d h))
    (hβ : ∀ u : V, σ (1, a₀) u = u → u = 0) (y : A5) :
    d' σ d (y, 1) = 0 := by
  have hb : d' σ d (1, a₀) = 0 := by
    simpa [zmod5_val_one] using d'_eq_zero_on_S σ d hd (0, 1)
  have hc := d'_crossed σ d hd
  have h1 : d' σ d ((y, 1) * (1, a₀)) = d' σ d (y, 1) := by
    rw [hc (y, 1) (1, a₀), hb, map_zero, add_zero]
  have h2 : d' σ d ((1, a₀) * (y, 1)) = σ (1, a₀) (d' σ d (y, 1)) := by
    rw [hc (1, a₀) (y, 1), hb, zero_add]
  have hcomm : (y, 1) * (1, a₀) = (1, a₀) * (y, 1) := by ext <;> simp
  have hfix : σ (1, a₀) (d' σ d (y, 1)) = d' σ d (y, 1) := by
    rw [← h2, ← hcomm, h1]
  exact hβ _ hfix

private lemma d'_snd (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (d : A5 × A5 → V)
    (hd : ∀ g h : A5 × A5, d (g * h) = d g + σ g (d h))
    (hα : ∀ u : V, σ (a₀, 1) u = u → u = 0) (z : A5) :
    d' σ d (1, z) = 0 := by
  have ha : d' σ d (a₀, 1) = 0 := by
    simpa [zmod5_val_one] using d'_eq_zero_on_S σ d hd (1, 0)
  have hc := d'_crossed σ d hd
  have h1 : d' σ d ((1, z) * (a₀, 1)) = d' σ d (1, z) := by
    rw [hc (1, z) (a₀, 1), ha, map_zero, add_zero]
  have h2 : d' σ d ((a₀, 1) * (1, z)) = σ (a₀, 1) (d' σ d (1, z)) := by
    rw [hc (a₀, 1) (1, z), ha, zero_add]
  have hcomm : (1, z) * (a₀, 1) = (a₀, 1) * (1, z) := by ext <;> simp
  have hfix : σ (a₀, 1) (d' σ d (1, z)) = d' σ d (1, z) := by
    rw [← h2, ← hcomm, h1]
  exact hα _ hfix

theorem exists_coboundary_of_fixedFree (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (hα : ∀ u : V, σ (a₀, 1) u = u → u = 0) (hβ : ∀ u : V, σ (1, a₀) u = u → u = 0)
    (d : A5 × A5 → V) (hd : ∀ g h : A5 × A5, d (g * h) = d g + σ g (d h)) :
    ∃ v : V, ∀ g : A5 × A5, d g = σ g v + v := by
  refine ⟨v₀ d, ?_⟩
  intro g
  rcases g with ⟨y, z⟩
  have h0 : d' σ d (y, z) = 0 := by
    have hc := d'_crossed σ d hd
    have hmul : (y, 1) * (1, z) = (y, z) := by ext <;> simp
    rw [← hmul, hc (y, 1) (1, z), d'_fst σ d hd hβ y, d'_snd σ d hd hα z,
      map_zero, add_zero]
  have h0' : d (y, z) + (σ (y, z) (v₀ d) + v₀ d) = 0 := by
    unfold d' at h0
    exact h0
  have hneg : d (y, z) = - (σ (y, z) (v₀ d) + v₀ d) :=
    eq_neg_of_add_eq_zero_left h0'
  rw [hneg, neg_eq_self]

end CFSG.EvenSporadicStandard.HNRecog.Fpf
