module

public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LargeExtraspecial.S8ThreeF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] noncomputable def commSub (X : Subgroup S.O) (τ : S.O) : Subgroup S.O :=
  closure {c | ∃ x ∈ X, c = x * τ * x⁻¹ * τ⁻¹}

theorem comm_mem_commSub {X : Subgroup S.O} {τ x : S.O} (hx : x ∈ X) :
    x * τ * x⁻¹ * τ⁻¹ ∈ commSub S X τ :=
  subset_closure ⟨x, hx, rfl⟩

theorem mem_fixSub_closure {s : Set S.O} {v : S.Qt} :
    v ∈ fixSub S (closure s) ↔ ∀ x ∈ s, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  constructor
  · intro h x hx
    exact (mem_fixSub S).mp h x (subset_closure hx)
  · intro h
    refine (mem_fixSub S).mpr fun x hx => ?_
    induction hx using closure_induction with
    | mem x hx => exact h x hx
    | one => rfl
    | mul x y _ _ hx hy => rw [coe_mul_apply, hy, hx]
    | inv x _ hx =>
      conv_lhs => rw [← hx]
      exact inv_apply_apply_O x v

theorem commSub_le_Lbar {X : Subgroup S.O} (hX : X ≤ S.Lbar g) {τ : S.O}
    (hτ : τ ∈ normalizer (S.Lbar g : Set S.O)) : commSub S X τ ≤ S.Lbar g := by
  rw [commSub, closure_le]
  rintro _ ⟨x, hx, rfl⟩
  have h1 : τ * x⁻¹ * τ⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hτ _).mp (inv_mem (hX hx))
  rw [show x * τ * x⁻¹ * τ⁻¹ = x * (τ * x⁻¹ * τ⁻¹) by group]
  exact mul_mem (hX hx) h1

theorem commSub_mono {X Y : Subgroup S.O} (hXY : X ≤ Y) (τ : S.O) :
    commSub S X τ ≤ commSub S Y τ :=
  closure_mono fun _ ⟨x, hx, e⟩ => ⟨x, hXY hx, e⟩

theorem comm_apply_sub_eq (H : Hyp4 S g) {l τ : S.O} (hl : l ∈ S.Lbar g)
    (hτa : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (hττ : τ * τ = 1) {p : S.Qt} (hp : p ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hτp : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    ((l * τ * l⁻¹ * τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p =
      (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) -
        ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) := by
  have haQ := H.conj_mem
  set a := S.cl (g * S.z * g⁻¹) with ha
  have hll : l⁻¹ = l := inv_eq_of_mul_eq_one_right (mul_self_of_mem_Lbar S haQ hl)
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hla : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := by
    have hmem : a ∈ fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]
      exact Submodule.mem_span_singleton_self _
    exact (mem_fixSub S).mp hmem l hl
  have hττp : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p) = p := by
    rw [← coe_mul_apply, hττ]
    rfl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (Lbar_apply_sub_mem_span' haQ hτp hl)
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (Lbar_apply_sub_mem_span' haQ hp hl)
  have hc' : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p) =
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p + c • a := by rw [hc]; abel
  have hd' : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p + d • a := by rw [hd]; abel
  have e1 : ((l * τ * l⁻¹ * τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p + d • a + c • a := by
    rw [hll, hτi, coe_mul_apply, coe_mul_apply, coe_mul_apply, hc', map_add, hττp, map_smul,
      hτa, map_add, hd', map_smul, hla]
  have e2 : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) =
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p + c • a - (p + d • a) := by
    rw [map_sub, hc', hd']
  rw [e1, e2]
  have hneg : -(d • a) = d • a := by rw [neg_eq_iff_add_eq_zero, add_self_zmod2]
  rw [show (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p + c • a - (p + d • a) -
      ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) = c • a + -(d • a) by abel, hneg]
  abel

theorem mem_fixSub_commSub_iff (H : Hyp4 S g) {X : Subgroup S.O} (hX : X ≤ S.Lbar g) {τ : S.O}
    (hτa : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (hττ : τ * τ = 1)
    (hτP : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g),
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g))
    {p : S.Qt} (hp : p ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    p ∈ fixSub S (commSub S X τ) ↔ (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ fixSub S X := by
  rw [commSub, mem_fixSub_closure, mem_fixSub]
  constructor
  · intro h x hx
    have h2 := comm_apply_sub_eq H (hX hx) hτa hττ hp (hτP p hp)
    rw [h _ ⟨x, hx, rfl⟩, sub_self] at h2
    exact sub_eq_zero.mp h2.symm
  · rintro h _ ⟨x, hx, rfl⟩
    have h2 := comm_apply_sub_eq H (hX hx) hτa hττ hp (hτP p hp)
    rw [h x hx, sub_self] at h2
    exact sub_eq_zero.mp h2

theorem finrank_clSub_inf_fixSpace (H : Hyp4 S g) (C : Cons311 S g) {τ : S.O}
    (hτP : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g),
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) +
        finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      S.width + finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓
        commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ∧
    finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≤
      2 * finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓
        commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  set P := S.clSub (S.QG ⊓ S.Qa g) with hPdef
  set T := commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hT
  have hP : finrank (ZMod 2) P = S.width := by
    have := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
    rw [← hPdef] at this
    omega
  have hQt := S.finrank_Qt_eq_two_mul_width
  have hPP : P ≤ S2.perp S.q P := fun u hu =>
    (S2.mem_perp).mpr fun v hv => polar_eq_zero_of_mem_clSub H.conj_ne hv hu
  have e1 := finrank_perp S.q_nondegenerate P
  have hPperp : S2.perp S.q P = P :=
    (Submodule.eq_of_le_of_finrank_eq hPP (by omega)).symm
  have hfix : fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = S2.perp S.q T :=
    fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate τ.2
  have e2 : P ⊓ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = S2.perp S.q (P ⊔ T) := by
    rw [hfix, perp_sup, hPperp]
  have e3 := finrank_perp S.q_nondegenerate (P ⊔ T)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq P T
  refine ⟨by rw [e2]; omega, ?_⟩
  have hle : P.map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤ P ⊓ T := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨sub_mem (hτP p hp) hp, sub_mem_commSpace _ p⟩
  have e5 := finrank_map_add_finrank_inf_ker ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) P
  have e6 : P ⊓ LinearMap.ker ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) =
      P ⊓ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := rfl
  rw [e6] at e5
  have i1 := Submodule.finrank_mono hle
  rw [e2] at e5
  omega

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem clSub_inf_fixSub_commSub_Lbar (H : Hyp4 S g) (ht : t ∈ S.Lbar g) {τ : S.O}
    (hτM : τ ∈ S.Mbar) (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hττ : τ * τ = 1) (hVτ : Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (commSub S (S.Lbar g) τ) =
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have haQ := H.conj_mem
  have hτa := hτV _ (cl_a_mem_Vt ht)
  have hτP : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g),
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g) := fun p hp =>
    apply_mem_clSub_of_apply_cl_eq haQ H.conj_ne hτM hτa hp
  ext p
  rw [Submodule.mem_inf, Submodule.mem_inf]
  refine and_congr_right fun hp => ?_
  rw [mem_fixSub_commSub_iff H le_rfl hτa hττ hτP hp, H.fixSub_eq, mem_fixSpace]
  constructor
  · intro h
    have hspan : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ Vt S g t :=
      (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt ht)
    have h1 : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈
        Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hspan h, sub_mem_commSpace _ p⟩
    rw [hVτ, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  · intro h
    rw [h, sub_self]
    exact zero_mem _

theorem clSub_inf_fixSub_commSub_Abar (D : Std H C ht ht1 hVQ) {τ : S.O} (hτM : τ ∈ S.Mbar)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hττ : τ * τ = 1)
    (hVτ : Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (commSub S (S.Lbar g ⊓ Nbar S g t) τ) =
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have haQ := H.conj_mem
  have hτa := hτV _ (cl_a_mem_Vt ht)
  have hτP : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g),
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g) := fun p hp =>
    apply_mem_clSub_of_apply_cl_eq haQ H.conj_ne hτM hτa hp
  have hA := clSub_inf_fixSub_Abar H C ht ht1 hVQ D.hA
  ext p
  rw [Submodule.mem_inf, Submodule.mem_inf]
  refine and_congr_right fun hp => ?_
  rw [mem_fixSub_commSub_iff H inf_le_left hτa hττ hτP hp, mem_fixSpace]
  constructor
  · intro h
    have h0 : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈
        S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (S.Lbar g ⊓ Nbar S g t) :=
      ⟨sub_mem (hτP p hp) hp, h⟩
    rw [hA] at h0
    have h1 : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈
        Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨h0.2, sub_mem_commSpace _ p⟩
    rw [hVτ, Submodule.mem_bot, sub_eq_zero] at h1
    exact h1
  · intro h
    rw [h, sub_self]
    exact zero_mem _

theorem commSub_Abar_eq_of_inf_eq_bot (D : Std H C ht ht1 hVQ) {τ : S.O} (hτM : τ ∈ S.Mbar)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hττ : τ * τ = 1)
    (hVτ : Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    commSub S (S.Lbar g ⊓ Nbar S g t) τ = commSub S (S.Lbar g) τ := by
  have hτN := mem_normalizer_Lbar_of_fix H ht hτM hτV
  have h1 := card_mul_two_pow_finrank_fix H C (commSub_le_Lbar (le_refl (S.Lbar g)) hτN)
  have h2 := card_mul_two_pow_finrank_fix H C (commSub_le_Lbar
    (inf_le_left : S.Lbar g ⊓ Nbar S g t ≤ S.Lbar g) hτN)
  rw [clSub_inf_fixSub_commSub_Lbar H ht hτM hτV hττ hVτ] at h1
  rw [clSub_inf_fixSub_commSub_Abar D hτM hτV hττ hVτ] at h2
  refine Subgroup.eq_of_le_of_card_ge (commSub_mono inf_le_left τ) ?_
  have hpos : 0 < 2 ^ finrank (ZMod 2) ↥(S.clSub (S.QG ⊓ S.Qa g) ⊓
      fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by positivity
  exact (Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)).le

theorem eq_two_pow_sub_of_mul_eq {c f n : ℕ} (h : c * 2 ^ f = 2 ^ n) (hf : f ≤ n) :
    c = 2 ^ (n - f) := by
  have hpos : 0 < 2 ^ f := by positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h, ← pow_add, Nat.sub_add_cancel hf]

theorem card_commSub_Lbar_le_of_inf_eq_bot (H : Hyp4 S g) (C : Cons311 S g)
    (ht : t ∈ S.Lbar g) {τ : S.O} (hτM : τ ∈ S.Mbar)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hττ : τ * τ = 1)
    (hVτ : Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) {m : ℕ}
    (hm : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2 * m) :
    Nat.card (commSub S (S.Lbar g) τ) ≤ 2 ^ m := by
  have haQ := H.conj_mem
  have hτa := hτV _ (cl_a_mem_Vt ht)
  have hτP : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g),
      (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g) := fun p hp =>
    apply_mem_clSub_of_apply_cl_eq haQ H.conj_ne hτM hτa hp
  have hτN := mem_normalizer_Lbar_of_fix H ht hτM hτV
  have h1 := card_mul_two_pow_finrank_fix H C (commSub_le_Lbar (le_refl (S.Lbar g)) hτN)
  rw [clSub_inf_fixSub_commSub_Lbar H ht hτM hτV hττ hVτ] at h1
  obtain ⟨e1, e2⟩ := finrank_clSub_inf_fixSpace H C hτP
  have hP : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = S.width := by
    have := S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne C.card_QG_inf_Qa
    omega
  have i1 := Submodule.finrank_mono (inf_le_left : S.clSub (S.QG ⊓ S.Qa g) ⊓
    fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ S.clSub (S.QG ⊓ S.Qa g))
  rw [hP] at i1
  rw [eq_two_pow_sub_of_mul_eq h1 i1]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_commSub_le_of_four (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm4 : D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t) :
    commSub S (S.Lbar g ⊓ Nbar S g t) τ = commSub S (S.Lbar g) τ ∧
      Nat.card (commSub S (S.Lbar g) τ) ≤ 2 ^ 4 := by
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hττ : τ * τ = 1 := by
    rw [hxτ]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim]; omega
  have hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
    fun k hk => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hk
  have hnf : ¬ ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := fun hfl =>
    hτN (mem_Nbar_of_flag hCE hNo hΩ D (by omega) hfus hsub hxM hxτ hτt hτV hfl)
  have hVτ := (finrank_inf_of_four hCE hNo hΩ D hm4 hxM hxτ hτt hτV hnf).2
  have hdimτ : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2 * 4 := by
    rw [hxτ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1, D.hdim, hm4]
  exact ⟨commSub_Abar_eq_of_inf_eq_bot D hτM hτV hττ hVτ,
    card_commSub_Lbar_le_of_inf_eq_bot H C ht hτM hτV hττ hVτ hdimτ⟩

end CFSG.LargeExtraspecial.S8
