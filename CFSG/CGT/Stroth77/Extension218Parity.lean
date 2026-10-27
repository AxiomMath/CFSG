module

public import CFSG.CGT.Stroth77.Extension218Bits
public import CFSG.CGT.Stroth77.Extension218Images
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.Stroth77

namespace Ext218

open Matrix

variable {s : ℕ} {i F G : ℤ}

local macro "simp_t221" : tactic =>
  `(tactic| simp only [Type221.action, SigmaFourAction.ofMatEq, Type221.k, Type221.uvM,
    Type221.tM, Type221.uvA, Type221.ρM, Type221.uM, uMat, ofCols_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul])

@[expose] noncomputable def par221 (s : ℕ) : Torus (Type221.k s) →+ ZMod 2 × ZMod 2 × ZMod 2 :=
  ((ZMod.castHom (dvd_pow_self 2 (by simp [Type221.k])) (ZMod 2)).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun j => ZMod (2 ^ Type221.k s j)) 0)).prod
    (((ZMod.castHom (dvd_pow_self 2 (by simp [Type221.k])) (ZMod 2)).toAddMonoidHom.comp
        (Pi.evalAddMonoidHom (fun j => ZMod (2 ^ Type221.k s j)) 1)).prod
      ((ZMod.castHom (dvd_pow_self 2 (by simp [Type221.k])) (ZMod 2)).toAddMonoidHom.comp
        (Pi.evalAddMonoidHom (fun j => ZMod (2 ^ Type221.k s j)) 2)))

theorem par221_gens (A B C : ℤ) :
    par221 s (A • gen (Type221.k s) 0 + B • gen (Type221.k s) 1 + C • gen (Type221.k s) 2) =
      ((A : ZMod 2), (B : ZMod 2), (C : ZMod 2)) := by
  simp [par221, gen, Pi.single_apply]

theorem add_self_eq_zero_t221 : ∀ p : ZMod 2 × ZMod 2 × ZMod 2, p + p = 0 := by
  decide

theorem par221_two_smul (x : Torus (Type221.k s)) : par221 s ((2 : ℤ) • x) = 0 := by
  rw [two_zsmul, map_add]
  exact add_self_eq_zero_t221 _

theorem par221_bv (x y z : ℕ) : par221 s (bv221 s x y z) = 0 := by
  rw [bv221_eq_gens, par221_gens]
  push_cast
  reduce_mod_char
  simp

theorem exists_two_smul_of_par221_eq_zero {v : Torus (Type221.k s)} (h : par221 s v = 0) :
    ∃ t : Torus (Type221.k s), v = (2 : ℤ) • t := by
  obtain ⟨a, b, c, rfl⟩ := torus_eq_zsmul_gens (Type221.k s) v
  rw [par221_gens] at h
  simp only [Prod.mk_eq_zero] at h
  obtain ⟨ha, hb, hc⟩ := h
  obtain ⟨a', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mp ha
  obtain ⟨b', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mp hb
  obtain ⟨c', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c 2).mp hc
  refine ⟨a' • gen (Type221.k s) 0 + b' • gen (Type221.k s) 1 + c' • gen (Type221.k s) 2, ?_⟩
  rw [zsmul_gens]
  push_cast
  rfl

@[expose] def rhoBar221 (p : ZMod 2 × ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (p.1 + p.2.2, p.2.2, p.2.1 + p.2.2)

@[expose] def uvBar221 (p : ZMod 2 × ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 × ZMod 2 :=
  (p.1 + p.2.1 + p.2.2, p.2.1, p.2.2)

theorem phiR_apply_gens_t221 (h : Type221.Data s i F G) (a b c : ℤ) :
    (Type221.action h).φρ
        (a • gen (Type221.k s) 0 + b • gen (Type221.k s) 1 + c • gen (Type221.k s) 2) =
      (a - c) • gen (Type221.k s) 0 + (-c) • gen (Type221.k s) 1 +
        (b - c) • gen (Type221.k s) 2 := by
  refine matAct_gens_eq _ _ 0 0 0 (t0 := 0) (t1 := 0) (t2 := 0) ?_ ?_ ?_ <;>
  · simp_t221
    ring

theorem par221_phiR (h : Type221.Data s i F G) (x : Torus (Type221.k s)) :
    par221 s ((Type221.action h).φρ x) = rhoBar221 (par221 s x) := by
  obtain ⟨a, b, c, rfl⟩ := torus_eq_zsmul_gens (Type221.k s) x
  rw [phiR_apply_gens_t221 h, par221_gens, par221_gens]
  simp only [rhoBar221]
  push_cast
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem par221_phiUV (h : Type221.Data s i F G) (x : Torus (Type221.k s)) :
    par221 s ((Type221.action h).φuv x) = uvBar221 (par221 s x) := by
  obtain ⟨a, b, c, rfl⟩ := torus_eq_zsmul_gens (Type221.k s) x
  have h0 : (Type221.action h).φuv (gen (Type221.k s) 0) =
      (-8 * G - 19 : ℤ) • gen (Type221.k s) 0 + (4 : ℤ) • gen (Type221.k s) 1 +
        (-4 : ℤ) • gen (Type221.k s) 2 := by
    conv_lhs => rw [gen_zero_eq218]
    exact phiUV_gen0_t221 h
  rw [par221_gens, map_add (Type221.action h).φuv, map_add (Type221.action h).φuv,
    map_zsmul (Type221.action h).φuv, map_zsmul (Type221.action h).φuv,
    map_zsmul (Type221.action h).φuv, h0, phiUV_gen1_t221 h, phiUV_gen2_t221 h, zsmul_gens,
    zsmul_gens, zsmul_gens, gens_add, gens_add, par221_gens]
  simp only [uvBar221]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
  · push_cast
    ring_nf
    reduce_mod_char

@[expose] def invariantPlane221 (p q : ZMod 2 × ZMod 2 × ZMod 2) : Bool :=
  p ≠ 0 && q ≠ 0 && p ≠ q &&
    (rhoBar221 p = 0 || rhoBar221 p = p || rhoBar221 p = q || rhoBar221 p = p + q) &&
    (rhoBar221 q = 0 || rhoBar221 q = p || rhoBar221 q = q || rhoBar221 q = p + q) &&
    (uvBar221 p = 0 || uvBar221 p = p || uvBar221 p = q || uvBar221 p = p + q) &&
    (uvBar221 q = 0 || uvBar221 q = p || uvBar221 q = q || uvBar221 q = p + q)

theorem invariantPlane221_eq_false : ∀ p q, invariantPlane221 p q = false := by
  decide

theorem no_invariant_plane_t221 (p q : ZMod 2 × ZMod 2 × ZMod 2) (hp : p ≠ 0) (hq : q ≠ 0)
    (hpq : p ≠ q)
    (h1 : rhoBar221 p = 0 ∨ rhoBar221 p = p ∨ rhoBar221 p = q ∨ rhoBar221 p = p + q)
    (h2 : rhoBar221 q = 0 ∨ rhoBar221 q = p ∨ rhoBar221 q = q ∨ rhoBar221 q = p + q)
    (h3 : uvBar221 p = 0 ∨ uvBar221 p = p ∨ uvBar221 p = q ∨ uvBar221 p = p + q)
    (h4 : uvBar221 q = 0 ∨ uvBar221 q = p ∨ uvBar221 q = q ∨ uvBar221 q = p + q) : False := by
  have h : invariantPlane221 p q = true := by
    simp only [invariantPlane221, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      or_assoc, and_assoc]
    exact ⟨hp, hq, hpq, h1, h2, h3, h4⟩
  rw [invariantPlane221_eq_false] at h
  exact Bool.false_ne_true h

end Ext218

end CFSG.CGT.Stroth77
