module

public import CFSG.LocalAnalysis.GH72.Vocabulary
public import CFSG.CGT.Foote81L6.TStruct.DihSub
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH72

open Subgroup DihedralGroup
open CFSG.CGT.Foote81L6 (zc zc_mul_self zc_ne_one zc_comm mem_sup_iff_of_le_normalizer
  le_normalizer_of_comm card_sup_of_le_normalizer)
open CFSG.CGT.Foote81L6.TStruct (IsFourIn ElemBound ElemBound.sup elemBound_of_dihedral
  isElemAbelian_two_iff mul_self_of_mem_sup eq_and_eq_of_mul_eq_mul eq_sup_inf_of_card
  isFourIn_liftSub_dihFour symm_zc_eq symm_zc_mem_four mem_liftSub zc_mem_dihFour
  sr_mem_dihFour r_eq_of_mul_self)

variable {G : Type*} [Group G]

theorem isDih_of_isDihNonab {D : Subgroup G} (h : IsDihNonab D) : IsDih D := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨a, by omega, e⟩

theorem isKleinFour_of_isFourIn {D V : Subgroup G} (hV : IsFourIn D V) : IsKleinFour V := by
  obtain ⟨-, hV2, hV4⟩ := hV
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  haveI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.1 (by rw [hV4]; norm_num)
  refine ⟨hV4, (Monoid.exponent_eq_prime_iff Nat.prime_two).2 fun g hg => ?_⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (hV2 g g.2)) hg

namespace IsDih

variable {D : Subgroup G}

theorem finite (hD : IsDih D) : Finite D := by
  obtain ⟨a, -, ⟨e⟩⟩ := hD
  haveI : NeZero (2 ^ a) := ⟨by positivity⟩
  exact Finite.of_equiv _ e.symm.toEquiv

theorem elemBound (hD : IsDih D) : ElemBound D 4 := by
  obtain ⟨a, -, ⟨e⟩⟩ := hD
  haveI : NeZero (2 ^ a) := ⟨by positivity⟩
  exact elemBound_of_dihedral e

theorem exists_four (hD : IsDih D) : ∃ V, IsFourIn D V := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  exact ⟨_, isFourIn_liftSub_dihFour e ha 0⟩

theorem exists_four_mem (hD : IsDih D) {t : G} (htD : t ∈ D) (ht2 : t * t = 1) :
    ∃ V, IsFourIn D V ∧ t ∈ V := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  have hu2 : e ⟨t, htD⟩ * e ⟨t, htD⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    exact congrArg e (Subtype.ext ht2)
  cases h : e ⟨t, htD⟩ with
  | r j =>
    refine ⟨_, isFourIn_liftSub_dihFour e ha 0, (mem_liftSub e).2 ⟨htD, ?_⟩⟩
    rw [h] at hu2 ⊢
    rcases r_eq_of_mul_self ha hu2 with h1 | h1
    · rw [h1]
      exact one_mem _
    · rw [h1]
      exact zc_mem_dihFour 0
  | sr i =>
    refine ⟨_, isFourIn_liftSub_dihFour e ha i, (mem_liftSub e).2 ⟨htD, ?_⟩⟩
    rw [h]
    exact sr_mem_dihFour i

theorem mem_four_of_central (hD : IsDih D) {V : Subgroup G} (hV : IsFourIn D V) {z : G}
    (hzD : z ∈ D) (hzc : ∀ y ∈ D, y * z = z * y) : z ∈ V := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  rcases Nat.lt_or_ge a 2 with h | h
  · obtain rfl : a = 1 := by omega
    haveI : Finite D := Finite.of_equiv _ e.symm.toEquiv
    have hcard : Nat.card D = 4 := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      norm_num
    rw [eq_of_le_of_card_ge hV.1 (by rw [hcard, hV.2.2])]
    exact hzD
  · by_cases hz1 : z = 1
    · rw [hz1]
      exact one_mem V
    · rw [← symm_zc_eq e h hzD hz1 hzc]
      exact symm_zc_mem_four e ha hV

end IsDih

theorem exists_central_involution (D : Subgroup G) (hD : IsDih D) :
    ∃ z, z ∈ D ∧ orderOf z = 2 ∧ D ≤ C z := by
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  refine ⟨(e.symm (zc a) : G), (e.symm (zc a)).2, ?_, fun d hd => ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact zc_mul_self ha) (zc_ne_one ha)
  · rw [mem_centralizer_singleton_iff]
    have h := congrArg e.symm (zc_comm ha (e ⟨d, hd⟩))
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    exact congrArg Subtype.val h

theorem exists_sup_eq_of_mulEquiv_prod {H₁ H₂ : Type*} [Group H₁] [Group H₂] (S : Subgroup G)
    (e : S ≃* H₁ × H₂) :
    ∃ T₁ T₂ : Subgroup G, T₁ ⊔ T₂ = S ∧ T₁ ⊓ T₂ = ⊥ ∧ T₂ ≤ centralizer (T₁ : Set G) ∧
      Nonempty (T₁ ≃* H₁) ∧ Nonempty (T₂ ≃* H₂) := by
  set f₁ : H₁ →* G := S.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl H₁ H₂)) with hf₁
  set f₂ : H₂ →* G := S.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr H₁ H₂)) with hf₂
  have i₁ : Function.Injective f₁ :=
    S.subtype_injective.comp (e.symm.injective.comp fun a b h => congrArg Prod.fst h)
  have i₂ : Function.Injective f₂ :=
    S.subtype_injective.comp (e.symm.injective.comp fun a b h => congrArg Prod.snd h)
  have hmul : ∀ (h₁ : H₁) (h₂ : H₂), f₁ h₁ * f₂ h₂ = ((e.symm (h₁, h₂) : S) : G) := by
    intro h₁ h₂
    simp only [hf₁, hf₂, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hmul' : ∀ (h₁ : H₁) (h₂ : H₂), f₂ h₂ * f₁ h₁ = ((e.symm (h₁, h₂) : S) : G) := by
    intro h₁ h₂
    simp only [hf₁, hf₂, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  refine ⟨f₁.range, f₂.range, le_antisymm ?_ ?_, ?_, ?_, ⟨(MonoidHom.ofInjective i₁).symm⟩,
    ⟨(MonoidHom.ofInjective i₂).symm⟩⟩
  · refine sup_le ?_ ?_ <;> rintro _ ⟨h, rfl⟩ <;> exact (e.symm _).2
  · intro x hx
    have key := hmul (e ⟨x, hx⟩).1 (e ⟨x, hx⟩).2
    rw [Prod.mk.eta, MulEquiv.symm_apply_apply] at key
    have key' : f₁ (e ⟨x, hx⟩).1 * f₂ (e ⟨x, hx⟩).2 = x := key
    rw [← key']
    exact mul_mem (mem_sup_left ⟨_, rfl⟩) (mem_sup_right ⟨_, rfl⟩)
  · rw [eq_bot_iff]
    rintro x ⟨⟨h₁, rfl⟩, ⟨h₂, hh⟩⟩
    have h12 : MonoidHom.inr H₁ H₂ h₂ = MonoidHom.inl H₁ H₂ h₁ :=
      e.symm.injective (S.subtype_injective hh)
    have h1 : h₁ = 1 := (congrArg Prod.fst h12).symm
    rw [mem_bot, h1, map_one]
  · rintro _ ⟨h₂, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨h₁, rfl⟩
    rw [hmul, hmul']

theorem exists_ddDecomp (S : Subgroup G) (hS : IsDDShape S) : ∃ S₁ S₂ : Subgroup G,
    DDDecomp S S₁ S₂ := by
  obtain ⟨a, b, ha, hb, hab, ⟨e⟩⟩ := hS
  obtain ⟨T₁, T₂, hsup, hinf, hcomm, ⟨e₁⟩, ⟨e₂⟩⟩ := exists_sup_eq_of_mulEquiv_prod S e
  rcases Nat.lt_or_ge b 2 with hb2 | hb2
  · exact ⟨T₂, T₁, ⟨by rw [sup_comm, hsup], by rw [inf_comm, hinf], le_centralizer_iff.1 hcomm,
      ⟨b, hb, ⟨e₂⟩⟩, ⟨a, by omega, ⟨e₁⟩⟩⟩⟩
  · exact ⟨T₁, T₂, ⟨hsup, hinf, hcomm, ⟨a, ha, ⟨e₁⟩⟩, ⟨b, hb2, ⟨e₂⟩⟩⟩⟩

namespace DDDecomp

variable {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂)
include hd

theorem comm {x y : G} (hx : x ∈ S₁) (hy : y ∈ S₂) : x * y = y * x :=
  mem_centralizer_iff.1 (hd.commute hy) x hx

theorem le_left : S₁ ≤ S := hd.sup_eq ▸ le_sup_left

theorem le_right : S₂ ≤ S := hd.sup_eq ▸ le_sup_right

theorem isDih₂ : IsDih S₂ := isDih_of_isDihNonab hd.dih₂

theorem mem_iff {g : G} : g ∈ S ↔ ∃ x ∈ S₁, ∃ y ∈ S₂, g = x * y := by
  rw [← hd.sup_eq]
  exact mem_sup_iff_of_le_normalizer (le_normalizer_of_comm fun x hx y hy => hd.comm hx hy)

theorem eq_and_eq {x x' y y' : G} (hx : x ∈ S₁) (hx' : x' ∈ S₁) (hy : y ∈ S₂) (hy' : y' ∈ S₂)
    (h : x * y = x' * y') : x = x' ∧ y = y' :=
  eq_and_eq_of_mul_eq_mul hd.inf_eq hx hx' hy hy' h

theorem mul_self_iff {x y : G} (hx : x ∈ S₁) (hy : y ∈ S₂) :
    x * y * (x * y) = 1 ↔ x * x = 1 ∧ y * y = 1 := by
  have h : x * y * (x * y) = (x * x) * (y * y) := by
    rw [mul_assoc, ← mul_assoc y, ← hd.comm hx hy, mul_assoc, mul_assoc]
  rw [h]
  constructor
  · intro h1
    exact hd.eq_and_eq (mul_mem hx hx) (one_mem _) (mul_mem hy hy) (one_mem _)
      (h1.trans (mul_one 1).symm)
  · rintro ⟨h1, h2⟩
    rw [h1, h2, one_mul]

theorem central_components {x y : G} (hx : x ∈ S₁) (hy : y ∈ S₂) (hc : S ≤ C (x * y)) :
    (∀ s ∈ S₁, s * x = x * s) ∧ ∀ s ∈ S₂, s * y = y * s := by
  constructor
  · intro s hs
    have h1 : s * (x * y) = x * y * s := mem_centralizer_singleton_iff.1 (hc (hd.le_left hs))
    have h2 : y * s = s * y := (hd.comm hs hy).symm
    refine mul_right_cancel (b := y) ?_
    calc s * x * y = s * (x * y) := mul_assoc _ _ _
      _ = x * y * s := h1
      _ = x * (y * s) := mul_assoc _ _ _
      _ = x * s * y := by rw [h2, mul_assoc]
  · intro s hs
    have h1 : s * (x * y) = x * y * s := mem_centralizer_singleton_iff.1 (hc (hd.le_right hs))
    have h2 : s * x = x * s := (hd.comm hx hs).symm
    refine mul_left_cancel (a := x) ?_
    calc x * (s * y) = x * s * y := (mul_assoc _ _ _).symm
      _ = s * x * y := by rw [h2]
      _ = s * (x * y) := mul_assoc _ _ _
      _ = x * y * s := h1
      _ = x * (y * s) := mul_assoc _ _ _

theorem elemBound : ElemBound S 16 := by
  rw [← hd.sup_eq]
  exact ElemBound.sup (k₁ := 4) (k₂ := 4) (fun x hx y hy => hd.comm hx hy) hd.inf_eq
    hd.dih₁.elemBound hd.isDih₂.elemBound

theorem card_le_sixteen {E : Subgroup G} (hE : E ≤ S) (hE2 : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 16 :=
  hd.elemBound E hE (isElemAbelian_two_iff.1 hE2)

theorem isE16_sup {V₁ V₂ : Subgroup G} (h₁ : IsFourIn S₁ V₁) (h₂ : IsFourIn S₂ V₂) :
    IsE16 (V₁ ⊔ V₂) := by
  have hc : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x := fun x hx y hy => hd.comm (h₁.1 hx) (h₂.1 hy)
  refine ⟨isElemAbelian_two_iff.2 fun g hg => mul_self_of_mem_sup h₁.2.1 h₂.2.1 hc hg, ?_⟩
  rw [card_sup_of_le_normalizer (le_normalizer_of_comm hc)
    (eq_bot_iff.2 ((inf_le_inf h₁.1 h₂.1).trans hd.inf_eq.le)), h₁.2.2, h₂.2.2]

theorem e16_split {A : Subgroup G} (hAS : A ≤ S) (hA : IsE16 A) :
    A = (A ⊓ S₁) ⊔ (A ⊓ S₂) ∧ IsFourIn S₁ (A ⊓ S₁) ∧ IsFourIn S₂ (A ⊓ S₂) := by
  have hA2 : ∀ x ∈ A, x * x = 1 := isElemAbelian_two_iff.1 hA.1
  haveI := hd.dih₁.finite
  haveI := hd.isDih₂.finite
  obtain ⟨hsplit, h₁, h₂⟩ := eq_sup_inf_of_card (k₁ := 4) (k₂ := 4)
    (fun x hx y hy => hd.comm hx hy) hd.inf_eq hd.dih₁.elemBound hd.isDih₂.elemBound
    (hd.sup_eq ▸ hAS) hA2 (by rw [hA.2])
  exact ⟨hsplit, ⟨inf_le_right, fun x hx => hA2 x hx.1, h₁⟩,
    ⟨inf_le_right, fun x hx => hA2 x hx.1, h₂⟩⟩

theorem center_le {A : Subgroup G} (hAS : A ≤ S) (hA : IsE16 A) {z : G} (hzS : z ∈ S)
    (hzc : S ≤ C z) : z ∈ A := by
  obtain ⟨-, hV₁, hV₂⟩ := hd.e16_split hAS hA
  obtain ⟨x, hx, y, hy, rfl⟩ := hd.mem_iff.1 hzS
  obtain ⟨hxc, hyc⟩ := hd.central_components hx hy hzc
  exact mul_mem (hd.dih₁.mem_four_of_central hV₁ hx hxc).1
    (hd.isDih₂.mem_four_of_central hV₂ hy hyc).1

end DDDecomp

theorem exists_e16 {S S₁ S₂ : Subgroup G} (hd : DDDecomp S S₁ S₂) : ∃ A ≤ S, IsE16 A := by
  obtain ⟨V₁, h₁⟩ := hd.dih₁.exists_four
  obtain ⟨V₂, h₂⟩ := hd.isDih₂.exists_four
  exact ⟨V₁ ⊔ V₂, sup_le (h₁.1.trans hd.le_left) (h₂.1.trans hd.le_right), hd.isE16_sup h₁ h₂⟩

theorem dd_e16_split (S S₁ S₂ : Subgroup G) (hd : DDDecomp S S₁ S₂) (A : Subgroup G)
    (hAS : A ≤ S) (hA : IsE16 A) :
    (A ⊓ S₁) ⊔ (A ⊓ S₂) = A ∧ IsKleinFour ↥(A ⊓ S₁) ∧ IsKleinFour ↥(A ⊓ S₂) ∧
      ∀ z ∈ S, S ≤ C z → orderOf z = 2 → z ∈ A := by
  obtain ⟨hsplit, h₁, h₂⟩ := hd.e16_split hAS hA
  exact ⟨hsplit.symm, isKleinFour_of_isFourIn h₁, isKleinFour_of_isFourIn h₂,
    fun z hzS hzc _ => hd.center_le hAS hA hzS hzc⟩

end CFSG.GH72
