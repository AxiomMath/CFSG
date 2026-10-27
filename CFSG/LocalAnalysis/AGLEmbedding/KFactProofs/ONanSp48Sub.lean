module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Grp
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import Certificates.Data.ONanSp48Local

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped Matrix

theorem validB_of_check {A : Array ℕ} (h : validB A = true) : Valid A := validB_iff.1 h

@[expose] noncomputable def spOf (A : Array ℕ)
    (h : (decode A)ᵀ * gram GF8 2 * decode A = gram GF8 2) : Sp8 :=
  ofSymplecticMat (decode A) h

theorem sympl_t1 : (decode t1c.m)ᵀ * gram GF8 2 * decode t1c.m = gram GF8 2 := by
  decide +kernel

theorem sympl_t2 : (decode t2c.m)ᵀ * gram GF8 2 * decode t2c.m = gram GF8 2 := by
  decide +kernel

theorem sympl_w : (decode wc.m)ᵀ * gram GF8 2 * decode wc.m = gram GF8 2 := by
  decide +kernel

theorem sympl_s : (decode sc.m)ᵀ * gram GF8 2 * decode sc.m = gram GF8 2 := by
  decide +kernel

@[expose] noncomputable def gt1 : Hh := SemidirectProduct.inl (spOf t1c.m sympl_t1)
@[expose] noncomputable def gt2 : Hh := SemidirectProduct.inl (spOf t2c.m sympl_t2)
@[expose] noncomputable def gw : Hh := SemidirectProduct.inl (spOf wc.m sympl_w)
@[expose] noncomputable def gs : Hh := SemidirectProduct.inl (spOf sc.m sympl_s)
@[expose] noncomputable def gf : Hh := SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 3))

theorem repP_inl {p : Pc} {k : Sp8} (hv : Valid p.m) (hm : decode p.m = matOf k)
    (hj : p.j = 0) : RepP p (SemidirectProduct.inl k) :=
  ⟨hv, hm, by simp [hj]⟩

theorem repP_gt1 (h : gensValid = true) : RepP t1c gt1 := by
  simp only [gensValid, Bool.and_eq_true] at h
  exact repP_inl (validB_of_check h.1.1.1) rfl rfl

theorem repP_gt2 (h : gensValid = true) : RepP t2c gt2 := by
  simp only [gensValid, Bool.and_eq_true] at h
  exact repP_inl (validB_of_check h.1.1.2) rfl rfl

theorem repP_gw (h : gensValid = true) : RepP wc gw := by
  simp only [gensValid, Bool.and_eq_true] at h
  exact repP_inl (validB_of_check h.1.2) rfl rfl

theorem repP_gs (h : gensValid = true) : RepP sc gs := by
  simp only [gensValid, Bool.and_eq_true] at h
  exact repP_inl (validB_of_check h.2) rfl rfl

theorem repP_gf : RepP fc gf := by
  refine ⟨valid_idCode, ?_, ?_⟩
  · rw [show fc.m = idCode from rfl, decode_idCode]
    rfl
  · show (1 : ℕ) = (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 3))).val
    simp [ZMod.val_one]

@[expose] def codeSubgroup (L : List Pc) (h1 : oneP ∈ L) (hmul : ∀ p ∈ L, ∀ q ∈ L, mulP p q ∈ L)
    (hinv : ∀ p ∈ L, ∃ n, powP p (n + 1) = oneP ∧ powP p n ∈ L) : Subgroup Hh where
  carrier := {x | ∃ p ∈ L, RepP p x}
  mul_mem' := by
    rintro x y ⟨p, hp, hx⟩ ⟨q, hq, hy⟩
    exact ⟨mulP p q, hmul p hp q hq, hx.mul hy⟩
  one_mem' := ⟨oneP, h1, RepP.one⟩
  inv_mem' := by
    rintro x ⟨p, hp, hx⟩
    obtain ⟨n, hn1, hn2⟩ := hinv p hp
    have h1 : x ^ (n + 1) = 1 := by
      have := hx.pow (n + 1)
      rw [hn1] at this
      exact this.eq RepP.one
    refine ⟨powP p n, hn2, ?_⟩
    have : x⁻¹ = x ^ n := inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
    rw [this]
    exact hx.pow n

end CFSG.AGLEmbedding.KFactProofs.Sp48
