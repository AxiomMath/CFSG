module

public import CFSG.LargeExtraspecial.S5OneC
public import CFSG.LargeExtraspecial.S5Gen3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification

universe u

variable {G : Type u} [Group G] [Finite G]

structure PairData (S : Setting G) (g : G) where
  X₁ : Subgroup S.O
  X₂ : Subgroup S.O
  t : S.O
  τ : S.O
  comp₁ : IsComponentOf X₁ S.Mbar
  comp₂ : IsComponentOf X₂ S.Mbar
  norm₁ : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X₁ : Set S.O)
  norm₂ : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X₂ : Set S.O)
  ne : X₁ ≠ X₂
  t_mem_Lbar : t ∈ S.Lbar g
  t_mem : t ∈ X₁
  t_ne_one : t ≠ 1
  τ_mem_Lbar : τ ∈ S.Lbar g
  τ_mem : τ ∈ X₂
  τ_ne_one : τ ≠ 1

namespace PairData

variable {S : Setting G} {g : G} (P : PairData S g)

@[expose] def swap : PairData S g where
  X₁ := P.X₂
  X₂ := P.X₁
  t := P.τ
  τ := P.t
  comp₁ := P.comp₂
  comp₂ := P.comp₁
  norm₁ := P.norm₂
  norm₂ := P.norm₁
  ne := P.ne.symm
  t_mem_Lbar := P.τ_mem_Lbar
  t_mem := P.τ_mem
  t_ne_one := P.τ_ne_one
  τ_mem_Lbar := P.t_mem_Lbar
  τ_mem := P.t_mem
  τ_ne_one := P.t_ne_one

theorem comm {x y : S.O} (hx : x ∈ P.X₁) (hy : y ∈ P.X₂) : x * y = y * x :=
  mul_comm_of_isComponentOf_ne P.comp₁ P.comp₂ P.ne hx hy

@[expose] def A₁ : CompAt S g where
  X := P.X₂
  t := P.t
  isComponentOf := P.comp₂
  norm := P.norm₂
  mem_Lbar := P.t_mem_Lbar
  ne_one := P.t_ne_one
  comm := fun _ hx => (P.comm P.t_mem hx).symm

@[expose] def A₂ : CompAt S g := P.swap.A₁

theorem Lbar_inf_inf_eq_bot (H : Hyp4 S g) :
    (S.Lbar g ⊓ P.X₁) ⊓ (S.Lbar g ⊓ P.X₂) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  have hx1 : x ∈ S.Lbar g ⊓ P.X₁ := (Subgroup.mem_inf.mp hx).1
  have hx2 : x ∈ S.Lbar g ⊓ P.X₂ := (Subgroup.mem_inf.mp hx).2
  have hxx : x ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact S4.mul_self_of_mem_Lbar S H.conj_mem hx1.1
  exact eq_one_of_mem_center_of_pow S P.comp₁.2.1 hx1.2
    (fun y hy => (P.comm hy hx2.2).symm) hxx

theorem card_Lbar_inf_le_two (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (Q : Hyp45Q H C) (hVQ : ¬ V S g P.τ ≤ S.Qa g) :
    Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O) ≤ 2 :=
  card_le_two_of_subset fun _ hx => P.A₂.eq_one_or_eq hIrr H hNo C Q hVQ hx.1
    fun _ hy => (P.comm hy hx.2).symm

theorem false_of_not_le (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    (hVQ : ¬ V S g P.τ ≤ S.Qa g) : False := by
  have h2 := P.card_Lbar_inf_le_two hIrr H hNo C Q hVQ
  have hK : Nat.card (LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ : Subgroup _) ≤
      Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O) :=
    P.A₁.card_LmodN_inf_le hCE hIrr H hNo C Q hn
  by_cases hVt : V S g P.t ≤ S.Qa g
  · have h4 : 4 ≤ Nat.card (LmodN S g P.t) := P.A₁.four_le_card_LmodN hIrr H hNo C Q hVt
    have hKR : imgR H.conj_mem P.t P.X₂ = RmodN S g P.t :=
      ((P.A₁.hyp45q hIrr H hNo C Q).2 hVt).1
    have hle : LmodN S g P.t ≤ LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ :=
      le_inf le_rfl (by rw [hKR]; exact LmodN_le_RmodN P.t_mem_Lbar)
    have : Finite (Vt S g P.t ≃ₗ[ZMod 2] Vt S g P.t) := finite_linearEquiv_of_finite
    have := card_le_of_le hle
    omega
  · have h8 : 8 ≤ Nat.card (LmodN S g P.t) := P.A₁.eight_le_card_LmodN hIrr H hNo C Q hn hVt
    have hrel : (LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂).relIndex (LmodN S g P.t) ≤ 2 :=
      (P.A₁.hyp45q hIrr H hNo C Q).1.2
    have := card_le_two_mul_of_relIndex_le_two inf_le_left hrel
    omega

theorem Lbar_inf_Nbar_inf_eq_bot (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (Q : Hyp45Q H C) :
    (S.Lbar g ⊓ Nbar S g P.t) ⊓ (S.Lbar g ⊓ Nbar S g P.τ) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  by_contra hy1
  have hyt : y ∈ S.Lbar g ⊓ Nbar S g P.t := (Subgroup.mem_inf.mp hy).1
  have hyτ : y ∈ S.Lbar g ⊓ Nbar S g P.τ := (Subgroup.mem_inf.mp hy).2
  have hyL : y ∈ S.Lbar g := hyt.1
  have hc₂ : ∀ x ∈ P.X₂, x * y = y * x := fun x hx =>
    (P.A₁.commute_of_mem_Nbar hIrr H C hyL hyt.2 hx).symm
  have hc₁ : ∀ x ∈ P.X₁, x * y = y * x := fun x hx =>
    (P.A₂.commute_of_mem_Nbar hIrr H C hyL hyτ.2 hx).symm
  let B₁ : CompAt S g := ⟨P.X₁, y, P.comp₁, P.norm₁, hyL, hy1, hc₁⟩
  let B₂ : CompAt S g := ⟨P.X₂, y, P.comp₂, P.norm₂, hyL, hy1, hc₂⟩
  have hq₁ : CFSG.Open.IsQuasisimple (imgR H.conj_mem y P.X₁) := B₁.isQuasisimple_img hIrr H C
  have heq : imgR H.conj_mem y P.X₁ = imgR H.conj_mem y P.X₂ :=
    Q.unique hNo hyL hy1 (B₁.Rbar_ne hIrr H) (B₁.isSubnormal_img hIrr H) hq₁
      (B₂.isSubnormal_img hIrr H) (B₂.isQuasisimple_img hIrr H C)
  apply not_isSolvable_of_isQuasisimple hq₁
  refine Group.isSolvable_of_comm fun e₁ e₂ => Subtype.ext ?_
  obtain ⟨y₁, hy₁, he₁⟩ := mem_imgR.mp e₁.2
  have he₂ : (e₂ : Vt S g y ≃ₗ[ZMod 2] Vt S g y) ∈ imgR H.conj_mem y P.X₂ := heq ▸ e₂.2
  obtain ⟨y₂, hy₂, he₂'⟩ := mem_imgR.mp he₂
  change (e₁ : Vt S g y ≃ₗ[ZMod 2] Vt S g y) * e₂ = e₂ * e₁
  rw [← he₁, ← he₂', ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (P.comm hy₁ hy₂)

theorem card_Lbar_le (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    (hVt : V S g P.t ≤ S.Qa g) :
    Nat.card (S.Lbar g) ≤ Nat.card (S.Lbar g ⊓ Nbar S g P.t : Subgroup S.O) *
      Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O) := by
  have hK : Nat.card (LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ : Subgroup _) ≤
      Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O) :=
    P.A₁.card_LmodN_inf_le hCE hIrr H hNo C Q hn
  have hKR : imgR H.conj_mem P.t P.X₂ = RmodN S g P.t :=
    ((P.A₁.hyp45q hIrr H hNo C Q).2 hVt).1
  have hle : LmodN S g P.t ≤ LmodN S g P.t ⊓ imgR H.conj_mem P.t P.X₂ :=
    le_inf le_rfl (by rw [hKR]; exact LmodN_le_RmodN P.t_mem_Lbar)
  have : Finite (Vt S g P.t ≃ₗ[ZMod 2] Vt S g P.t) := finite_linearEquiv_of_finite
  rw [card_Lbar_eq H.conj_mem P.t_mem_Lbar]
  exact Nat.mul_le_mul_left _ ((card_le_of_le hle).trans hK)

theorem exists_mul (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) {s : S.O} (hs : s ∈ S.Lbar g) :
    ∃ s₁ ∈ S.Lbar g ⊓ P.X₁, ∃ s₂ ∈ S.Lbar g ⊓ P.X₂, s = s₁ * s₂ := by
  have h1 := P.card_Lbar_le hCE hIrr H hNo C Q hn hVt
  have h2 : Nat.card (S.Lbar g) ≤ Nat.card (S.Lbar g ⊓ Nbar S g P.τ : Subgroup S.O) *
      Nat.card (S.Lbar g ⊓ P.X₁ : Subgroup S.O) :=
    P.swap.card_Lbar_le hCE hIrr H hNo C Q hn hVτ
  have h3 := card_mul_card_le_of_inf_eq_bot inf_le_left inf_le_left
    (P.Lbar_inf_Nbar_inf_eq_bot hIrr H hNo C Q)
  have h4 := card_mul_card_le_of_inf_eq_bot inf_le_left inf_le_left (P.Lbar_inf_inf_eq_bot H)
  have hpos : 0 < Nat.card (S.Lbar g) := Nat.card_pos
  set L := Nat.card (S.Lbar g)
  set a := Nat.card (S.Lbar g ⊓ Nbar S g P.t : Subgroup S.O)
  set b := Nat.card (S.Lbar g ⊓ Nbar S g P.τ : Subgroup S.O)
  set c := Nat.card (S.Lbar g ⊓ P.X₁ : Subgroup S.O)
  set d := Nat.card (S.Lbar g ⊓ P.X₂ : Subgroup S.O)
  have h5 : L * L ≤ L * (c * d) := by
    calc L * L ≤ (a * d) * (b * c) := Nat.mul_le_mul h1 h2
      _ = (a * b) * (c * d) := by ring
      _ ≤ L * (c * d) := Nat.mul_le_mul_right _ h3
  exact exists_mul_of_card_le inf_le_left inf_le_left (P.Lbar_inf_inf_eq_bot H)
    (Nat.le_of_mul_le_mul_left h5 hpos) hs

end PairData

end CFSG.LargeExtraspecial.S5
