module

public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21b
public import CFSG.GH74.GLS.Bg.TwoGroups.Free2

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup

theorem mem_sup_zpowers_of_involutions {A : Type*} [Group A] {s t : A} (hs : s * s = 1)
    (ht : t * t = 1) (hst : s * t = t * s) (a : A) :
    a ∈ zpowers s ⊔ zpowers t ↔ a = 1 ∨ a = s ∨ a = t ∨ a = s * t := by
  constructor
  · intro ha
    obtain ⟨u, hu, v, hv, huv⟩ := mem_sup_of_commute' (Q₁ := zpowers s) (Q₂ := zpowers t)
      (by
        intro a ha b hb
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((Commute.zpow_zpow (show Commute s t from hst) i j).eq)) ha
    rcases zpowers_of_sq_eq_one s hs u hu with rfl | rfl <;>
      rcases zpowers_of_sq_eq_one t ht v hv with rfl | rfl <;> simp [← huv]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

namespace A44

theorem dd_isInv : dd.IsInv := by decide +kernel
theorem dd_isA0 : dd.IsA0 := by decide +kernel
theorem C4_char : ∀ x ∈ ord3list, ∀ a : M4, a.IsInv →
    ((M4.mul a x = M4.mul x a ∧ a.IsA0) ↔ a ∈ C4list) := by decide +kernel

theorem C4_sq : ∀ a ∈ C4list, M4.mul a a = M4.one := by decide +kernel

theorem dd_fix : ∀ v : ZMod 4 × ZMod 4, dd.act v = v ↔ v + v = 0 := by decide +kernel

theorem ddi_fix : ∀ v : ZMod 4 × ZMod 4, (M4.mul dd iota).act v = v ↔ v + v = 0 := by
  decide +kernel

theorem card_C4 : Fintype.card {x : G96 // x.1 ∈ C4list} = 4 := by decide +kernel

theorem iota_dd_comm : M4.mul iota dd = M4.mul dd iota := by decide +kernel

end A44

open A44

theorem phiB_iota {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : (phiB e (iotaB B)).1 = iota := by
  have h : ∀ w : ZMod 4 × ZMod 4, (phiB e (iotaB B)).1.act w = -w := by
    intro w
    obtain ⟨b, rfl⟩ := vec_surjective e w
    have hι : iotaB B b = b⁻¹ := rfl
    rw [← vec_phi, hι, vec_inv]
  apply M4.ext_act
  · rw [h]; decide
  · rw [h]; decide

@[expose] noncomputable def dB {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : MulAut B :=
  (phiB e).symm (G96.mk dd dd_isInv)

theorem phiB_dB {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : (phiB e (dB e)).1 = dd := by
  unfold dB; rw [MulEquiv.apply_symm_apply]; rfl

theorem dB_mem_A0 {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : dB e ∈ A0 B := by
  rw [mem_A0_iff e, M4.isA0_iff, phiB_dB]; exact dd_isA0

theorem iotaB_mul_self {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : iotaB B * iotaB B = 1 := by
  apply (phiB e).injective
  apply Subtype.ext
  rw [map_mul, map_one, G96.val_mul, G96.val_one, phiB_iota]
  exact C4_sq iota (by simp [C4list])

theorem dB_mul_self {B : Type} [CommGroup B] (e : B ≃* Z4Z4) : dB e * dB e = 1 := by
  apply (phiB e).injective
  apply Subtype.ext
  rw [map_mul, map_one, G96.val_mul, G96.val_one, phiB_dB]
  exact C4_sq dd (by simp [C4list])

theorem iotaB_comm_dB {B : Type} [CommGroup B] (e : B ≃* Z4Z4) :
    iotaB B * dB e = dB e * iotaB B := by
  apply (phiB e).injective
  apply Subtype.ext
  rw [map_mul, map_mul, G96.val_mul, G96.val_mul, phiB_iota, phiB_dB]
  exact iota_dd_comm

theorem mem_iota_dB {B : Type} [CommGroup B] (e : B ≃* Z4Z4) (a : MulAut B) :
    a ∈ zpowers (iotaB B) ⊔ zpowers (dB e) ↔ (phiB e a).1 ∈ C4list := by
  rw [mem_sup_zpowers_of_involutions (iotaB_mul_self e) (dB_mul_self e) (iotaB_comm_dB e)]
  have e1 : (phiB e (1 : MulAut B)).1 = M4.one := by rw [map_one]; rfl
  have e2 : (phiB e (iotaB B * dB e)).1 = M4.mul iota dd := by
    rw [map_mul, G96.val_mul, phiB_iota, phiB_dB]
  simp only [C4list, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl e1
    · exact Or.inr (Or.inl (phiB_iota e))
    · exact Or.inr (Or.inr (Or.inl (phiB_dB e)))
    · exact Or.inr (Or.inr (Or.inr e2))
  · rintro (h | h | h | h)
    · left; exact (phiB e).injective (Subtype.ext (h.trans e1.symm))
    · right; left; exact (phiB e).injective (Subtype.ext (h.trans (phiB_iota e).symm))
    · right; right; left; exact (phiB e).injective (Subtype.ext (h.trans (phiB_dB e).symm))
    · right; right; right; exact (phiB e).injective (Subtype.ext (h.trans e2.symm))

theorem ord3_of_orderOf {B : Type} [CommGroup B] (e : B ≃* Z4Z4) {x : MulAut B}
    (hx : orderOf x = 3) : (phiB e x).1 ∈ ord3list := by
  have h3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hne : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  apply (ord3_iff _ (phiB e x).2).mp
  refine ⟨cube_eq_one_iff.mp (by rw [← map_pow, h3, map_one]), ?_⟩
  intro h
  apply hne
  apply (phiB e).injective
  apply Subtype.ext
  rw [map_one, G96.val_one]
  exact h

theorem cent_A0_eq {B : Type} [CommGroup B] (e : B ≃* Z4Z4) {x : MulAut B} (hx : orderOf x = 3) :
    centralizer ({x} : Set (MulAut B)) ⊓ A0 B = zpowers (iotaB B) ⊔ zpowers (dB e) := by
  have hA0 : ∀ φ : MulAut B, φ ∈ A0 B ↔ (phiB e φ).1.IsA0 := fun φ => by
    rw [mem_A0_iff e, M4.isA0_iff]
  have hxl := ord3_of_orderOf e hx
  ext a
  rw [mem_iota_dB, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, hA0]
  rw [← C4_char _ hxl _ (phiB e a).2]
  constructor
  · rintro ⟨hc, h0⟩
    refine ⟨?_, h0⟩
    have := hc x (Set.mem_singleton x)
    have h1 := congrArg (fun t => (phiB e t).1) this
    simp only [map_mul, G96.val_mul] at h1
    exact h1.symm
  · rintro ⟨hc, h0⟩
    refine ⟨?_, h0⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply (phiB e).injective
    apply Subtype.ext
    rw [map_mul, map_mul, G96.val_mul, G96.val_mul]
    exact hc.symm

theorem iv2_2_1_d : IV2_2_1_d := by
  intro B _ ⟨e⟩ x hx
  refine ⟨dB e, dB_mem_A0 e, ?_, ?_, ?_, ?_, ?_⟩
  · exact cent_A0_eq e hx
  · rw [Nat.card_congr ((phiB e).toEquiv.subtypeEquiv (q := fun x : G96 => x.1 ∈ C4list)
      (fun a => mem_iota_dB e a)), Nat.card_eq_fintype_card]
    exact card_C4
  · intro a ha
    rw [mem_iota_dB] at ha
    apply (phiB e).injective
    apply Subtype.ext
    rw [map_mul, map_one, G96.val_mul, G96.val_one]
    exact C4_sq _ ha
  · ext b
    rw [mem_CB_iff, phiB_dB, dd_fix, mem_ZB_iff]
  · ext b
    have : (phiB e (dB e * iotaB B)).1 = M4.mul dd iota := by
      rw [map_mul, G96.val_mul, phiB_iota, phiB_dB]
    rw [mem_CB_iff, this, ddi_fix, mem_ZB_iff]

end CFSG.GH74.GLS.Bg.TwoGroups
