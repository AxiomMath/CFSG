module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3ASound
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop

@[expose] def d8Code : DihedralGroup 4 → ℕ
  | .r i => i.val
  | .sr i => 4 + i.val

theorem d8Code_lt : ∀ a, d8Code a < 8 := by decide

theorem d8Code_surj : ∀ t : Fin 8, ∃ a, d8Code a = t.val := by decide

theorem d8M_code : ∀ a b : DihedralGroup 4, d8M (d8Code a) (d8Code b) = d8Code (a * b) := by
  decide

variable {G : Type} [Group G] {elt : ℕ → G} {P C V Q : ℕ}

theorem d8I_lt (r s k : ℕ) : d8I P r s k < 128 := by
  unfold d8I
  cases Nat.blt k 4
  · exact atR_lt _ _
  · exact powE_lt (P := P) r k

theorem d8K_spec {r s Dm : ℕ} (h : d8K P r s Dm = true) :
    (∀ u < 8, ∀ v < 8, d8I P r s (d8M u v) = mulE P (d8I P r s u) (d8I P r s v)) ∧
      Nat.rec (motive := fun _ => Nat) 0
        (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (d8I P r s k))) 8 = Dm ∧ pop Dm = 8 := by
  unfold d8K at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun u hu v hv => ?_, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  have := allBelow_spec h1 (by decide) (8 * u + v) (by omega)
  have e1 : Nat.shiftRight (8 * u + v) 3 = u := by
    change (8 * u + v) >>> 3 = u
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (8 * u + v) 7 = v := by
    change (8 * u + v) &&& (2 ^ 3 - 1) = v
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  dsimp only at this
  rw [e1, e2] at this
  exact Nat.eq_of_beq_eq_true this

theorem d8K_sound (hR : RealT elt P C V Q) {r s Dm : ℕ} (hr : r < 128)
    (h : d8K P r s Dm = true) :
    ∃ φ : DihedralGroup 4 →* G, Function.Injective φ ∧ Set.range φ = mset elt Dm := by
  classical
  obtain ⟨hmul, himg, hpop⟩ := d8K_spec h
  let φ : DihedralGroup 4 →* G :=
    { toFun := fun a => elt (d8I P r s (d8Code a))
      map_one' := by
        change elt (d8I P r s 0) = 1
        have e : d8I P r s 0 = 0 := rfl
        rw [e, hR.one]
      map_mul' := fun a b => by
        change elt (d8I P r s (d8Code (a * b))) = elt (d8I P r s (d8Code a)) *
          elt (d8I P r s (d8Code b))
        rw [← d8M_code, hmul _ (d8Code_lt a) _ (d8Code_lt b),
          mulE_elt hR (d8I_lt _ _ _) (d8I_lt _ _ _)] }
  have hrange : Set.range φ = mset elt Dm := by
    rw [← himg]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨d8I P r s (d8Code a), d8I_lt _ _ _, ?_, rfl⟩
      rw [hasB_eq]
      refine (recLor_bit (fun k => Nat.shiftLeft 1 (d8I P r s k)) _ 8).2 ⟨d8Code a, d8Code_lt a, ?_⟩
      change (1 <<< d8I P r s (d8Code a)).testBit _ = true
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
    · rintro ⟨k, -, hk, rfl⟩
      rw [hasB_eq] at hk
      obtain ⟨t, ht, hb⟩ := (recLor_bit (fun k => Nat.shiftLeft 1 (d8I P r s k)) _ 8).1 hk
      change (1 <<< d8I P r s t).testBit k = true at hb
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hb
      obtain ⟨a, ha⟩ := d8Code_surj ⟨t, ht⟩
      refine ⟨a, ?_⟩
      change elt (d8I P r s (d8Code a)) = _
      rw [ha]
      change elt (d8I P r s t) = _
      rw [hb]
  refine ⟨φ, ?_, hrange⟩
  have hcard : (Set.range φ).ncard = 8 := by
    rw [hrange, pop_sound hR.inj (repM_mset hR.inj Dm), hpop]
  have hfin : (Finset.univ.image φ).card = (Finset.univ : Finset (DihedralGroup 4)).card := by
    rw [Finset.card_univ, DihedralGroup.card, ← Set.ncard_coe_finset, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, hcard]
  intro a b hab
  exact (Finset.card_image_iff.1 hfin) (Finset.mem_coe.2 (Finset.mem_univ a))
    (Finset.mem_coe.2 (Finset.mem_univ b)) hab

end CFSG.KC.G2Three.Sec1T3
