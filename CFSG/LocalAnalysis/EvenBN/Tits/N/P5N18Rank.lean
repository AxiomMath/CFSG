module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lin

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup

section Rank

variable {W : Type*} [Group W]

theorem card_le_fixSub_mul_commImg_sq [Finite W] (hc : ∀ a b : W, a * b = b * a)
    (h2 : ∀ w : W, w * w = 1) {x d : MulAut W} (hd : d * d = 1) (hx5 : x ^ 5 = 1)
    (hdx : d * x * d⁻¹ = x⁻¹) :
    Nat.card W ≤ Nat.card (fixSub x) * Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg d) ^ 2 := by
  letI : CommGroup W := { ‹Group W› with mul_comm := hc }
  have hx4 : x⁻¹ = x ^ 4 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx5)
  have e1 : d * x = x ^ 4 * d := by rw [← hx4]; exact mul_inv_eq_iff_eq_mul.1 hdx
  have e2 : d * (x * x) = x ^ 3 * d := by
    calc d * (x * x) = (d * x) * x := by rw [mul_assoc]
      _ = x ^ 4 * d * x := by rw [e1]
      _ = x ^ 4 * (d * x) := by rw [mul_assoc]
      _ = x ^ 4 * (x ^ 4 * d) := by rw [e1]
      _ = x ^ 8 * d := by rw [← mul_assoc, ← pow_add]
      _ = x ^ 3 * d := by
        have : x ^ 8 = x ^ 3 := by rw [show 8 = 5 + 3 from rfl, pow_add, hx5, one_mul]
        rw [this]
  have hsub : (fixSub d : Set W) ⊆ Set.range
      (fun p : fixSub x × (twistHom hc d).range => ((p.1 : W) * (p.2 : W))) := by
    intro c hcd
    have hcd' : d c = c := hcd
    have hp : ∀ n : ℕ, (x ^ (n + 1)) c = x ((x ^ n) c) := fun n => by rw [pow_succ']; rfl
    have p1 : (x ^ 1) c = x c := by rw [hp 0, pow_zero]; rfl
    have p2 : (x ^ 2) c = x (x c) := by rw [hp 1, p1]
    have p3 : (x ^ 3) c = x (x (x c)) := by rw [hp 2, p2]
    have p4 : (x ^ 4) c = x (x (x (x c))) := by rw [hp 3, p3]
    have p5 : x (x (x (x (x c)))) = c := by rw [← p4, ← hp 4, hx5]; rfl
    have h1 : d (x c) = x (x (x (x c))) := by
      have := congrArg (fun φ : MulAut W => φ c) e1
      simp only [MulAut.mul_apply, hcd'] at this
      rw [this, p4]
    have h2' : d (x (x c)) = x (x (x c)) := by
      have := congrArg (fun φ : MulAut W => φ c) e2
      simp only [MulAut.mul_apply, hcd'] at this
      rw [this, p3]
    have hn : x (c * x c * x (x c) * x (x (x c)) * x (x (x (x c)))) =
        c * x c * x (x c) * x (x (x c)) * x (x (x (x c))) := by
      simp only [map_mul, p5]
      simp only [mul_assoc, mul_comm, mul_left_comm]
    have hw : twistHom hc d (x c * x (x c)) = x c * x (x c) * (x (x (x (x c))) * x (x (x c))) := by
      rw [twistHom_apply, map_mul, h1, h2']
    refine ⟨(⟨c * x c * x (x c) * x (x (x c)) * x (x (x (x c))), hn⟩, ⟨twistHom hc d (x c * x (x c)),
      ⟨_, rfl⟩⟩), ?_⟩
    show c * x c * x (x c) * x (x (x c)) * x (x (x (x c))) * twistHom hc d (x c * x (x c)) = c
    rw [hw]
    have hcc : c * c = 1 := h2 c
    have hsq : (x c * x (x c) * x (x (x (x c))) * x (x (x c))) *
        (x c * x (x c) * x (x (x (x c))) * x (x (x c))) = 1 := by
      have := h2 (x c * x (x c) * x (x (x (x c))) * x (x (x c)))
      exact this
    calc c * x c * x (x c) * x (x (x c)) * x (x (x (x c))) *
        (x c * x (x c) * (x (x (x (x c))) * x (x (x c)))) =
        c * ((x c * x (x c) * x (x (x (x c))) * x (x (x c))) *
          (x c * x (x c) * x (x (x (x c))) * x (x (x c)))) := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = c := by rw [hsq, mul_one]
  have hcard1 : Nat.card (fixSub d) ≤ Nat.card (fixSub x) * Nat.card (twistHom hc d).range := by
    have hle : Nat.card (fixSub d) ≤ Nat.card (Set.range
        (fun p : fixSub x × (twistHom hc d).range => ((p.1 : W) * (p.2 : W)))) :=
      Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    have hle2 := Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective
      (f := fun p : fixSub x × (twistHom hc d).range => ((p.1 : W) * (p.2 : W))))
    rw [Nat.card_prod] at hle2
    exact hle.trans hle2
  have hcard := card_fixSub_mul_card_commImg hc h2 d
  rw [commImg_eq_range_twistHom hc h2 d] at hcard ⊢
  calc Nat.card W = Nat.card (fixSub d) * Nat.card (twistHom hc d).range := hcard.symm
    _ ≤ Nat.card (fixSub x) * Nat.card (twistHom hc d).range * Nat.card (twistHom hc d).range :=
        Nat.mul_le_mul_right _ hcard1
    _ = Nat.card (fixSub x) * Nat.card (twistHom hc d).range ^ 2 := by ring

theorem sixteen_le_card_commImg [Finite W] (hc : ∀ a b : W, a * b = b * a) (h2 : ∀ w : W, w * w = 1)
    {x d : MulAut W} (hd : d * d = 1) (hx5 : x ^ 5 = 1) (hdx : d * x * d⁻¹ = x⁻¹)
    (hW : Nat.card W = 2 ^ 10) (hfix : Nat.card (fixSub x) ≤ 4) :
    16 ≤ Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg d) := by
  have h := card_le_fixSub_mul_commImg_sq hc h2 hd hx5 hdx
  rw [hW] at h
  by_contra hlt
  push Not at hlt
  have h15 : Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg d) ≤ 15 := by omega
  have : Nat.card (fixSub x) * Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg d) ^ 2 ≤ 4 * 15 ^ 2 :=
    Nat.mul_le_mul hfix (Nat.pow_le_pow_left h15 2)
  norm_num at h this
  omega

theorem card_fixSub_conj (g x : MulAut W) : Nat.card (fixSub (g * x * g⁻¹)) = Nat.card (fixSub x) := by
  refine Nat.card_congr (g⁻¹.toEquiv.subtypeEquiv fun w => ?_)
  show (g * x * g⁻¹) w = w ↔ x (g⁻¹ w) = g⁻¹ w
  simp only [MulAut.mul_apply]
  constructor
  · intro h
    have := congrArg (fun a => g⁻¹ a) h
    simpa using this
  · intro h
    rw [h]
    simp

theorem commImg_conj (g y : MulAut W) :
    CFSG.LocalAnalysis.EvenBN.Tits.N.commImg (g * y * g⁻¹) =
      (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg y).map g.toMonoidHom := by
  unfold CFSG.LocalAnalysis.EvenBN.Tits.N.commImg
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨g⁻¹ w * (y (g⁻¹ w))⁻¹, ⟨g⁻¹ w, rfl⟩, ?_⟩
    simp
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨g w, ?_⟩
    simp

theorem card_commImg_conj (g y : MulAut W) :
    Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg (g * y * g⁻¹)) =
      Nat.card (CFSG.LocalAnalysis.EvenBN.Tits.N.commImg y) := by
  rw [commImg_conj]
  exact Subgroup.card_map_of_injective g.injective

end Rank

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
