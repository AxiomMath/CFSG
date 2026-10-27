module

public import CFSG.CGT.Stroth77.L4Sylow.Model
public import CFSG.Open.StatedAPI
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open Equiv Matrix CFSG.Open CFSG.GH74.GLS.Stage1.Thm3.Sec8

variable {K : Type} [Field K] {n : ℕ}

structure L4Data (K : Type) [Field K] (n : ℕ) where
  ζ : Kˣ
  orderOf_ζ : orderOf ζ = 2 ^ n

namespace L4Data

variable (D : L4Data K n)

@[expose] def chi : Multiplicative (ZMod (2 ^ n)) →* Kˣ where
  toFun z := D.ζ ^ (Multiplicative.toAdd z).val
  map_one' := by simp
  map_mul' a b := by
    haveI : NeZero (2 ^ n) := ⟨by positivity⟩
    have key : ∀ k : ℕ, D.ζ ^ (k % 2 ^ n) = D.ζ ^ k := fun k => by
      rw [← D.orderOf_ζ, pow_mod_orderOf]
    simp only [toAdd_mul]
    rw [ZMod.val_add, key, pow_add]

theorem chi_apply (z : Multiplicative (ZMod (2 ^ n))) :
    D.chi z = D.ζ ^ (Multiplicative.toAdd z).val := rfl

@[expose] def chiVec : Multiplicative (Fin 4 → ZMod (2 ^ n)) →* (Fin 4 → Kˣ) where
  toFun d i := D.chi (Multiplicative.ofAdd (Multiplicative.toAdd d i))
  map_one' := by
    funext i
    exact D.chi.map_one
  map_mul' d e := by
    funext i
    exact D.chi.map_mul _ _

theorem chiVec_apply (d : Multiplicative (Fin 4 → ZMod (2 ^ n))) (i : Fin 4) :
    D.chiVec d i = D.ζ ^ (Multiplicative.toAdd d i).val := rfl

@[expose] def embed : L4Hat n →* GL (Fin 4) K :=
  SemidirectProduct.lift (TauCeti.diagGL.comp D.chiVec)
    ((TauCeti.permutationGL (k := K)).comp Fin81.R0.subtype) fun π => by
      refine MonoidHom.ext fun d => ?_
      show TauCeti.diagGL (D.chiVec (actL4 n π d)) =
        TauCeti.permutationGL (k := K) (π : Perm (Fin 4)) * TauCeti.diagGL (D.chiVec d) *
          (TauCeti.permutationGL (k := K) (π : Perm (Fin 4)))⁻¹
      rw [TauCeti.permutationGL_mul_diagGL_mul_inv]
      rfl

theorem embed_apply (a : L4Hat n) :
    D.embed a = TauCeti.diagGL (D.chiVec a.left) *
      TauCeti.permutationGL (k := K) (a.right : Perm (Fin 4)) := rfl

theorem coe_embed (a : L4Hat n) :
    ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal (fun i => (D.ζ : K) ^ (Multiplicative.toAdd a.left i).val) *
        ((a.right : Perm (Fin 4))⁻¹).permMatrix K := by
  rw [embed_apply, Units.val_mul, TauCeti.diagGL_coe, TauCeti.permutationGL_coe]
  simp only [chiVec_apply, Units.val_pow_eq_pow_val]

theorem embed_apply_apply (a : L4Hat n) (i j : Fin 4) :
    ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
      if i = (a.right : Perm (Fin 4)) j then
        (D.ζ : K) ^ (Multiplicative.toAdd a.left i).val else 0 := by
  rw [embed_apply, TauCeti.coe_mul_permutationGL_apply, TauCeti.diagGL_coe, diagonal_apply,
    chiVec_apply, Units.val_pow_eq_pow_val]

theorem embed_injective : Function.Injective D.embed := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hent : ∀ i j, ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
      if i = j then 1 else 0 := fun i j => by rw [ha, Units.val_one, one_apply]
  have hπ : ∀ j, (a.right : Perm (Fin 4)) j = j := by
    intro j
    have h := hent ((a.right : Perm (Fin 4)) j) j
    rw [embed_apply_apply, if_pos rfl] at h
    by_contra hne
    rw [if_neg hne] at h
    exact pow_ne_zero _ (Units.ne_zero D.ζ) h
  have hr : a.right = 1 := Subtype.ext (Equiv.ext hπ)
  have hd : ∀ i, Multiplicative.toAdd a.left i = 0 := by
    intro i
    have h := hent i i
    rw [embed_apply_apply, if_pos (hπ i).symm, if_pos rfl] at h
    have h1 : D.ζ ^ (Multiplicative.toAdd a.left i).val = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_ζ] at h1
    haveI : NeZero (2 ^ n) := ⟨by positivity⟩
    have hlt := ZMod.val_lt (Multiplicative.toAdd a.left i)
    have h0 : (Multiplicative.toAdd a.left i).val = 0 := Nat.eq_zero_of_dvd_of_lt h1 hlt
    exact (ZMod.val_eq_zero _).mp h0
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    exact hd i
  · exact hr

theorem zeta_pow_two_pow_pred (hn : 1 ≤ n) : (D.ζ : K) ^ (2 ^ (n - 1)) = -1 := by
  have h2 : ((D.ζ : K) ^ (2 ^ (n - 1))) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, ← Units.val_pow_eq_pow_val, ← D.orderOf_ζ,
      pow_orderOf_eq_one, Units.val_one]
  rcases sq_eq_one_iff.mp h2 with h | h
  · exfalso
    have h1 : D.ζ ^ (2 ^ (n - 1)) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h,
      Units.val_one])
    rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_ζ] at h1
    have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd (Nat.le_of_dvd (by positivity) h1) (not_le.mpr hlt)
  · exact h

theorem chi_signZ (hn : 1 ≤ n) (u : ℤˣ) : ((D.chi (signZ n u) : Kˣ) : K) = ((u : ℤ) : K) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [signZ_one, map_one, Units.val_one, Units.val_one, Int.cast_one]
  · haveI : NeZero (2 ^ n) := ⟨by positivity⟩
    have hval : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)).val = 2 ^ (n - 1) :=
      ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [signZ_neg_one, chi_apply, toAdd_ofAdd, hval, Units.val_pow_eq_pow_val,
      zeta_pow_two_pow_pred D hn]
    simp

theorem det_embed (hn : 1 ≤ n) (a : L4Hat n) :
    ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det =
      (D.ζ : K) ^ (Multiplicative.toAdd (detL4 n a)).val := by
  have hchi : ∀ z, (D.ζ : K) ^ (Multiplicative.toAdd z).val = ((D.chi z : Kˣ) : K) := fun z => by
    rw [chi_apply, Units.val_pow_eq_pow_val]
  rw [hchi, coe_embed, det_mul, det_diagonal, det_permutation, Perm.sign_inv]
  have hdet : detL4 n a = sumL4 n a.left * signZ n (Perm.sign (a.right : Perm (Fin 4))) := rfl
  rw [hdet, map_mul, Units.val_mul, chi_signZ D hn]
  congr 1
  have hsum : sumL4 n a.left = ∏ i, Multiplicative.ofAdd (Multiplicative.toAdd a.left i) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    rfl
  rw [hsum, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [chi_apply, toAdd_ofAdd, Units.val_pow_eq_pow_val]

theorem embed_mem_statedSL (hn : 1 ≤ n) {a : L4Hat n} (ha : a ∈ L4P n) :
    D.embed a ∈ StatedSL 4 K := by
  rw [StatedAPI.mem_statedSL_iff, det_embed D hn, mem_L4P.mp ha, toAdd_one, ZMod.val_zero,
    pow_zero]

@[expose] def toSL (hn : 1 ≤ n) : L4P n →* StatedSL 4 K :=
  (D.embed.comp (L4P n).subtype).codRestrict (StatedSL 4 K) fun a => D.embed_mem_statedSL hn a.2

theorem coe_toSL (hn : 1 ≤ n) (a : L4P n) :
    ((D.toSL hn a : StatedSL 4 K) : GL (Fin 4) K) = D.embed a := rfl

theorem toSL_injective (hn : 1 ≤ n) : Function.Injective (D.toSL hn) := by
  intro a b h
  apply Subtype.ext
  apply D.embed_injective
  rw [← coe_toSL D hn, ← coe_toSL D hn, h]

end L4Data

theorem exists_l4Data_of_dvd [Finite K] (h : 2 ^ n ∣ Nat.card K - 1) : Nonempty (L4Data K n) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hg
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : orderOf g = 0 := by rw [hg, hk, mul_zero]
    exact (orderOf_pos g).ne' h1
  refine ⟨⟨g ^ k, ?_⟩⟩
  rw [orderOf_pow_of_dvd hk0 (by rw [hg, hk]; exact Dvd.intro_left _ rfl), hg, hk,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]

end CFSG.CGT.Stroth77.L4Sylow
