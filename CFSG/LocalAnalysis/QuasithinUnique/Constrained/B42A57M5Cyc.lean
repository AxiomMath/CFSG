module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Orb
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5Vec
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.QuasithinUnique.B42A57

open Multiplicative

section Bp

variable {S : Type} [CommGroup S]

@[expose] def bp (t : S) (z : ZMod 2) : S := if z = 0 then 1 else t

theorem zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide

theorem bp_add {t : S} (ht : t * t = 1) (z z' : ZMod 2) : bp t (z + z') = bp t z * bp t z' := by
  rcases zmod2_cases z with rfl | rfl <;> rcases zmod2_cases z' with rfl | rfl <;>
    simp [bp, ht, show (1 : ZMod 2) + 1 = 0 from rfl]

theorem bp_mul (t t' : S) (z : ZMod 2) : bp (t * t') z = bp t z * bp t' z := by
  rcases zmod2_cases z with rfl | rfl <;> simp [bp]

theorem bp_map (g : MulAut S) (t : S) (z : ZMod 2) : g (bp t z) = bp (g t) z := by
  rcases zmod2_cases z with rfl | rfl <;> simp [bp]

@[expose] def phiMap (b0 b1 b2 b3 : S) (c : V4) : S :=
  bp b0 (c 0) * bp b1 (c 1) * bp b2 (c 2) * bp b3 (c 3)

theorem phiMap_add {b0 b1 b2 b3 : S} (h0 : b0 * b0 = 1) (h1 : b1 * b1 = 1) (h2 : b2 * b2 = 1)
    (h3 : b3 * b3 = 1) (c c' : V4) :
    phiMap b0 b1 b2 b3 (c + c') = phiMap b0 b1 b2 b3 c * phiMap b0 b1 b2 b3 c' := by
  simp only [phiMap, Pi.add_apply, bp_add h0, bp_add h1, bp_add h2, bp_add h3]
  ac_rfl

theorem phiMap_zero (b0 b1 b2 b3 : S) : phiMap b0 b1 b2 b3 0 = 1 := by
  simp [phiMap, bp]

theorem lin_wC_zero (c : V4) : lin wC c 0 = c 3 := by simp [lin, wC]

theorem lin_wC_one (c : V4) : lin wC c 1 = c 0 + c 3 := by simp [lin, wC]

theorem lin_wC_two (c : V4) : lin wC c 2 = c 1 + c 3 := by simp [lin, wC]

theorem lin_wC_three (c : V4) : lin wC c 3 = c 2 + c 3 := by simp [lin, wC]

theorem span_e0 : ∀ c : V4, c ≠ 0 → ∃ k0 k1 k2 k3 : Bool,
    (![1, 0, 0, 0] : V4) = (if k0 then c else 0) + (if k1 then lin wC c else 0) +
      (if k2 then lin wC (lin wC c) else 0) + (if k3 then lin wC (lin wC (lin wC c)) else 0) := by
  decide +kernel

end Bp

variable {S : Type} [CommGroup S]

theorem exists_cyclic_coords [Finite S] (hS : ∀ s : S, s * s = 1) (hcard : Nat.card S = 16)
    (x : MulAut S) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) :
    ∃ θ : S ≃* Multiplicative V4, ∀ s : S, θ (x s) = ofAdd (lin wC (toAdd (θ s))) := by
  have hfix : ∀ s, x s = s → s = 1 := fun s hs => by
    have h : s ∈ fixSub x := hs
    rw [fixed_eq_bot_of_card_sixteen hS hcard x hx5 hx1] at h
    exact h
  obtain ⟨s, hs1⟩ : ∃ s : S, s ≠ 1 := by
    have : 1 < Nat.card S := by rw [hcard]; norm_num
    have := Finite.one_lt_card_iff_nontrivial.1 this
    exact exists_ne (1 : S)
  have hx5' : ∀ t : S, x (x (x (x (x t)))) = t := fun t => by
    have : x * x * x * x * x = 1 := by simpa [pow_succ] using hx5
    simpa [MulAut.mul_apply] using congrArg (fun f : MulAut S => f t) this
  obtain ⟨b1, hxs⟩ : ∃ b1, x s = b1 := ⟨_, rfl⟩
  obtain ⟨b2, hxb1⟩ : ∃ b2, x b1 = b2 := ⟨_, rfl⟩
  obtain ⟨b3, hxb2⟩ : ∃ b3, x b2 = b3 := ⟨_, rfl⟩
  obtain ⟨b4, hxb3⟩ : ∃ b4, x b3 = b4 := ⟨_, rfl⟩
  have hxb4 : x b4 = s := by rw [← hxb3, ← hxb2, ← hxb1, ← hxs]; exact hx5' s
  have hnorm : s * b1 * b2 * b3 * b4 = 1 := by
    apply hfix
    rw [map_mul, map_mul, map_mul, map_mul, hxs, hxb1, hxb2, hxb3, hxb4]
    ac_rfl
  have hb4' : b4 = s * b1 * b2 * b3 := by
    have h1 : (s * b1 * b2 * b3) * b4 = 1 := hnorm
    have h2 : (s * b1 * b2 * b3) * (s * b1 * b2 * b3) = 1 := hS _
    exact mul_left_cancel (h1.trans h2.symm)
  have hs2 : s * s = 1 := hS s
  have hb12 : b1 * b1 = 1 := hS b1
  have hb22 : b2 * b2 = 1 := hS b2
  have hb32 : b3 * b3 = 1 := hS b3
  let φ : Multiplicative V4 →* S :=
    { toFun := fun c => phiMap s b1 b2 b3 (toAdd c)
      map_one' := phiMap_zero s b1 b2 b3
      map_mul' := fun c c' => phiMap_add hs2 hb12 hb22 hb32 (toAdd c) (toAdd c') }
  have hφ : ∀ c : V4, φ (ofAdd c) = phiMap s b1 b2 b3 c := fun c => rfl
  have hcompat : ∀ c : V4, x (phiMap s b1 b2 b3 c) = phiMap s b1 b2 b3 (lin wC c) := by
    intro c
    simp only [phiMap, map_mul, bp_map, hxs, hxb1, hxb2, hxb3, lin_wC_zero, lin_wC_one,
      lin_wC_two, lin_wC_three, bp_add hb12, bp_add hb22, bp_add hb32]
    rw [hb4', bp_mul, bp_mul, bp_mul]
    ac_rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    by_contra hne
    have hc0 : toAdd c ≠ 0 := fun h => hne (by rw [← ofAdd_toAdd c, h]; rfl)
    obtain ⟨k0, k1, k2, k3, hk⟩ := span_e0 (toAdd c) hc0
    have hψ1 : phiMap s b1 b2 b3 (toAdd c) = 1 := hc
    have hψ2 : phiMap s b1 b2 b3 (lin wC (toAdd c)) = 1 := by
      rw [← hcompat, hψ1, map_one]
    have hψ3 : phiMap s b1 b2 b3 (lin wC (lin wC (toAdd c))) = 1 := by
      rw [← hcompat, hψ2, map_one]
    have hψ4 : phiMap s b1 b2 b3 (lin wC (lin wC (lin wC (toAdd c)))) = 1 := by
      rw [← hcompat, hψ3, map_one]
    have hif : ∀ (k : Bool) (v : V4), phiMap s b1 b2 b3 v = 1 →
        phiMap s b1 b2 b3 (if k then v else 0) = 1 := by
      intro k v hv
      cases k <;> simp [hv, phiMap_zero]
    have h1 : phiMap s b1 b2 b3 (![1, 0, 0, 0] : V4) = 1 := by
      rw [hk, phiMap_add hs2 hb12 hb22 hb32, phiMap_add hs2 hb12 hb22 hb32,
        phiMap_add hs2 hb12 hb22 hb32, hif _ _ hψ1, hif _ _ hψ2, hif _ _ hψ3, hif _ _ hψ4]
      simp
    have h2 : phiMap s b1 b2 b3 (![1, 0, 0, 0] : V4) = s := by
      simp [phiMap, bp]
    exact hs1 (h2.symm.trans h1)
  have hcardV : Nat.card (Multiplicative V4) = 16 := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := V4))]
    simp [Nat.card_eq_fintype_card]
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hcardV])
  refine ⟨(MulEquiv.ofBijective φ hbij).symm, fun s' => ?_⟩
  obtain ⟨c, rfl⟩ := hbij.2 s'
  have e1 : ∀ c' : Multiplicative V4, (MulEquiv.ofBijective φ hbij).symm (φ c') = c' :=
    fun c' => (MulEquiv.ofBijective φ hbij).symm_apply_apply c'
  have e2 : x (φ c) = φ (ofAdd (lin wC (toAdd c))) := hcompat (toAdd c)
  rw [e2, e1, e1]

theorem exists_cols (θ : S ≃* Multiplicative V4) (g : MulAut S) :
    ∃ w : Fin 4 → V4, ∀ s : S, θ (g s) = ofAdd (lin w (toAdd (θ s))) := by
  let f : V4 →+ V4 := AddMonoidHom.mk' (fun u => toAdd (θ (g (θ.symm (ofAdd u))))) (by
    intro u v
    simp [ofAdd_add, map_mul, toAdd_mul])
  let fl : V4 →ₗ[ZMod 2] V4 :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c u => by
        rcases zmod2_cases c with rfl | rfl <;> simp }
  let M : Matrix (Fin 4) (Fin 4) (ZMod 2) := LinearMap.toMatrix' fl
  refine ⟨fun j i => M i j, fun s => ?_⟩
  have h1 : fl (toAdd (θ s)) = M.mulVec (toAdd (θ s)) := by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have h2 : f (toAdd (θ s)) = toAdd (θ (g s)) := by
    show toAdd (θ (g (θ.symm (ofAdd (toAdd (θ s)))))) = _
    simp
  have h3 : fl (toAdd (θ s)) = f (toAdd (θ s)) := rfl
  have h4 : toAdd (θ (g s)) = lin (fun j i => M i j) (toAdd (θ s)) := by
    rw [← h2, ← h3, h1]
    funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, lin]
    ring
  rw [← h4]
  rfl

end CFSG.QuasithinUnique.B42A57
