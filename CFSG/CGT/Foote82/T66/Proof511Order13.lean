module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.CGT.Foote82.Proof511

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero' (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem neg_eq_self' (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero']

theorem sub_mem_of_mem_closure {W : Submodule (ZMod 2) V} {S : Set (GLV V)}
    (hS : ∀ s ∈ S, ∀ v : V, s v - v ∈ W) {h : GLV V} (hh : h ∈ Subgroup.closure S) (v : V) :
    h v - v ∈ W := by
  induction hh using Subgroup.closure_induction generalizing v with
  | mem s hs => exact hS s hs v
  | one => simp
  | mul g k _ _ hg hk =>
    have e : (g * k) v - v = (g (k v) - k v) + (k v - v) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [e]
    exact W.add_mem (hg (k v)) (hk v)
  | inv g _ hg =>
    have e1 : g (g⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have e : g⁻¹ v - v = -(g (g⁻¹ v) - g⁻¹ v) := by
      rw [e1]
      abel
    rw [e]
    exact W.neg_mem (hg (g⁻¹ v))

variable [Finite V]

theorem false_of_thirteen_dvd_orderOf {W : Submodule (ZMod 2) V}
    (hW : Module.finrank (ZMod 2) W ≤ 11) {H : Subgroup (GLV V)}
    (hHW : ∀ h ∈ H, ∀ v : V, h v - v ∈ W) {y : GLV V} (hy : y ∈ H) (h13 : 13 ∣ orderOf y) :
    False := by
  classical
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Finite (GLV V) := Finite.of_injective (fun g : GLV V => (g : V → V))
    DFunLike.coe_injective
  letI : Fintype ↥W := Fintype.ofFinite ↥W
  have hfin : orderOf y ≠ 0 := (isOfFinOrder_of_finite y).orderOf_pos.ne'
  set x := y ^ (orderOf y / 13) with hxdef
  have hx13 : orderOf x = 13 := orderOf_pow_orderOf_div hfin h13
  have hxH : x ∈ H := H.pow_mem hy _
  have hxW : ∀ v : V, x v - v ∈ W := hHW x hxH
  have hxW' : ∀ w ∈ W, x w ∈ W := fun w hw => by
    have := W.add_mem hw (hxW w)
    rwa [add_sub_cancel] at this
  let f : Function.End ↥W := fun w => ⟨x w, hxW' w w.2⟩
  have hfpow : ∀ n : ℕ, ∀ w : ↥W, ((f ^ n) w : V) = (x ^ n) (w : V) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', pow_succ', LinearEquiv.mul_apply, ← ih]
      rfl
  have hf13 : f ^ 13 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    rw [pow_one, hfpow, ← hx13, pow_orderOf_eq_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥W) (p := 13) (n := 1) hf13
  let F : AddSubgroup ↥W :=
    { carrier := Function.fixedPoints f
      add_mem' := fun {a b} ha hb => by
        apply Subtype.ext
        have ha' : x (a : V) = a := congrArg Subtype.val ha
        have hb' : x (b : V) = b := congrArg Subtype.val hb
        show x ((a : V) + b) = (a : V) + b
        rw [map_add, ha', hb']
      zero_mem' := by
        apply Subtype.ext
        show x (0 : V) = 0
        exact map_zero x
      neg_mem' := fun {a} ha => by
        apply Subtype.ext
        have ha' : x (a : V) = a := congrArg Subtype.val ha
        show x (-(a : V)) = -(a : V)
        rw [map_neg, ha'] }
  have hcardW : Fintype.card ↥W = 2 ^ Module.finrank (ZMod 2) ↥W :=
    (FiniteField.pow_finrank_eq_card 2 ↥W).symm
  have hcardF : Fintype.card ↥(Function.fixedPoints f) = Nat.card ↥F := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  have hdvd : Nat.card ↥F ∣ 2 ^ Module.finrank (ZMod 2) ↥W := by
    rw [← hcardW, ← Nat.card_eq_fintype_card]
    exact F.card_addSubgroup_dvd_card
  obtain ⟨e, he, hFe⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hcardW, hcardF, hFe] at hmod
  have hde : e = Module.finrank (ZMod 2) ↥W := by
    have key : ∀ d ≤ 11, ∀ e ≤ d, 2 ^ d % 13 = 2 ^ e % 13 → e = d := by decide
    exact key _ hW e he (by simpa [Nat.ModEq] using hmod)
  have hall : ∀ w : ↥W, f w = w := by
    have hcard : Nat.card ↥F = Nat.card ↥W := by
      rw [hFe, hde, Nat.card_eq_fintype_card, hcardW]
    have htop : F = ⊤ := AddSubgroup.eq_top_of_card_eq F hcard
    intro w
    have : w ∈ F := htop ▸ AddSubgroup.mem_top w
    exact this
  have hx2 : x ^ 2 = 1 := by
    ext v
    have hw := congrArg Subtype.val (hall ⟨x v - v, hxW v⟩)
    change x (x v - v) = x v - v at hw
    rw [map_sub] at hw
    rw [pow_two, LinearEquiv.mul_apply]
    show x (x v) = v
    have : x (x v) = (x v - v) + x v := by rw [← hw, sub_add_cancel]
    rw [this, sub_add_eq_add_sub, add_self_eq_zero', zero_sub, neg_eq_self']
  have := orderOf_dvd_of_pow_eq_one hx2
  rw [hx13] at this
  norm_num at this

theorem false_of_three_conj {c h₂ h₃ : GLV V}
    (hdim : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers c) ⊤) = 2)
    (h13 : 13 ∣ orderOf (c * (h₂ * c * h₂⁻¹) * (h₃ * c * h₃⁻¹))) : False := by
  set U := commSpace (Subgroup.zpowers c) ⊤ with hU
  set W : Submodule (ZMod 2) V :=
    U ⊔ U.map (h₂ : V →ₗ[ZMod 2] V) ⊔ U.map (h₃ : V →ₗ[ZMod 2] V) with hWdef
  have hcU : ∀ v : V, c v - v ∈ U := fun v =>
    Submodule.subset_span ⟨c, Subgroup.mem_zpowers c, v, Submodule.mem_top, rfl⟩
  have hconj : ∀ h : GLV V, ∀ v : V, (h * c * h⁻¹) v - v ∈ U.map (h : V →ₗ[ZMod 2] V) := by
    intro h v
    refine ⟨c (h⁻¹ v) - h⁻¹ v, hcU _, ?_⟩
    show h (c (h⁻¹ v) - h⁻¹ v) = (h * c * h⁻¹) v - v
    have e1 : h (h⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1]
  have hS : ∀ s ∈ ({c, h₂ * c * h₂⁻¹, h₃ * c * h₃⁻¹} : Set (GLV V)), ∀ v : V, s v - v ∈ W := by
    rintro s hs v
    rcases hs with rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (hcU v))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right (hconj h₂ v))
    · exact Submodule.mem_sup_right (hconj h₃ v)
  have hWdim : Module.finrank (ZMod 2) ↥W ≤ 11 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ U.map (h₂ : V →ₗ[ZMod 2] V))
      (U.map (h₃ : V →ₗ[ZMod 2] V))
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq U (U.map (h₂ : V →ₗ[ZMod 2] V))
    have e₂ : Module.finrank (ZMod 2) ↥(U.map (h₂ : V →ₗ[ZMod 2] V)) = 2 := by
      rw [LinearEquiv.finrank_map_eq, hdim]
    have e₃ : Module.finrank (ZMod 2) ↥(U.map (h₃ : V →ₗ[ZMod 2] V)) = 2 := by
      rw [LinearEquiv.finrank_map_eq, hdim]
    rw [hWdef]
    omega
  set H := Subgroup.closure ({c, h₂ * c * h₂⁻¹, h₃ * c * h₃⁻¹} : Set (GLV V))
  have hmem : c * (h₂ * c * h₂⁻¹) * (h₃ * c * h₃⁻¹) ∈ H :=
    H.mul_mem (H.mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  exact false_of_thirteen_dvd_orderOf hWdim (fun h hh v => sub_mem_of_mem_closure hS hh v)
    hmem h13

end CFSG.CGT.Foote82.Proof511
