module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs5

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem cc3_conj {G : Type*} [Group G] (a b s c : G) (hc : c * s = s * c) :
    cc3 (c * a * c⁻¹) s (c * b * c⁻¹) = cc3 a s b := by
  unfold cc3
  have hc' : c⁻¹ * s = s * c⁻¹ := by
    calc c⁻¹ * s = c⁻¹ * (s * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * s) * c⁻¹ := by rw [hc]
      _ = s * c⁻¹ := by group
  refine Nat.card_congr
    { toFun := fun d => ⟨c⁻¹ * d.1 * c, ?_, ?_, ?_⟩
      invFun := fun d => ⟨c * d.1 * c⁻¹, ?_, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 := d.2.1
    calc c⁻¹ * d.1 * c * a = c⁻¹ * (d.1 * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * d.1) * c := by rw [h1]
      _ = a * (c⁻¹ * d.1 * c) := by group
  · have h1 := d.2.2.1
    calc c⁻¹ * d.1 * c * s = c⁻¹ * d.1 * (c * s) := by group
      _ = c⁻¹ * d.1 * (s * c) := by rw [hc]
      _ = c⁻¹ * (d.1 * s) * c := by group
      _ = c⁻¹ * (s * d.1) * c := by rw [h1]
      _ = (c⁻¹ * s) * d.1 * c := by group
      _ = (s * c⁻¹) * d.1 * c := by rw [hc']
      _ = s * (c⁻¹ * d.1 * c) := by group
  · have h1 := d.2.2.2
    calc c⁻¹ * d.1 * c * b = c⁻¹ * (d.1 * (c * b * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * b * c⁻¹) * d.1) * c := by rw [h1]
      _ = b * (c⁻¹ * d.1 * c) := by group
  · have h1 := d.2.1
    calc c * d.1 * c⁻¹ * (c * a * c⁻¹) = c * (d.1 * a) * c⁻¹ := by group
      _ = c * (a * d.1) * c⁻¹ := by rw [h1]
      _ = (c * a * c⁻¹) * (c * d.1 * c⁻¹) := by group
  · have h1 := d.2.2.1
    calc c * d.1 * c⁻¹ * s = c * d.1 * (c⁻¹ * s) := by group
      _ = c * d.1 * (s * c⁻¹) := by rw [hc']
      _ = c * (d.1 * s) * c⁻¹ := by group
      _ = c * (s * d.1) * c⁻¹ := by rw [h1]
      _ = (c * s) * d.1 * c⁻¹ := by group
      _ = (s * c) * d.1 * c⁻¹ := by rw [hc]
      _ = s * (c * d.1 * c⁻¹) := by group
  · have h1 := d.2.2.2
    calc c * d.1 * c⁻¹ * (c * b * c⁻¹) = c * (d.1 * b) * c⁻¹ := by group
      _ = c * (b * d.1) * c⁻¹ := by rw [h1]
      _ = (c * b * c⁻¹) * (c * d.1 * c⁻¹) := by group
  · intro d; ext; simp [mul_assoc]
  · intro d; ext; simp [mul_assoc]

namespace Ctx

variable {G : Type} [Group G] [Finite G] {C : Ctx G}

omit [Finite G] in
theorem cc3_x_s_s (hF : FFacts) : cc3 C.x C.s C.s = 288 := by
  have := cc3_eq_ccard (a := C.x) (u := C.s) (v := C.s) C.ι C.hs C.hs
  rw [this, C.hsF]
  exact hF.card_f0

omit [Finite G] in
theorem x_mem_gamma : C.x ∈ centralizer ({C.s} : Set G) :=
  mem_centralizer_singleton_iff.2 C.s_comm_x.symm

omit [Finite G] in
theorem card_cent_gamma (a : G) (ha : a * C.s = C.s * a) :
    Nat.card ↥(centralizer ({(⟨a, mem_centralizer_singleton_iff.2 ha⟩ :
      ↥(centralizer ({C.s} : Set G)))} : Set ↥(centralizer ({C.s} : Set G)))) =
      cc3 a C.s C.s := by
  unfold cc3
  refine Nat.card_congr
    { toFun := fun c => ⟨c.1.1, congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2),
        mem_centralizer_singleton_iff.1 c.1.2, mem_centralizer_singleton_iff.1 c.1.2⟩
      invFun := fun d => ⟨⟨d.1, mem_centralizer_singleton_iff.2 d.2.2.1⟩,
        mem_centralizer_singleton_iff.2 (Subtype.ext d.2.1)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro c; rfl
  · intro d; rfl

@[expose] def Acl (C : Ctx G) : Set G := {a | a * C.s = C.s * a ∧ orderOf a = 2 ∧ IsConj C.x a}

@[expose] def Bcl (C : Ctx G) : Set G := {b | b * C.s = C.s * b ∧ orderOf b = 2 ∧ ¬ IsConj C.x b}

theorem mem_Acl_iff (hF : FFacts) (hH : HFacts) (Y : C.Y1) (a : G) :
    (∃ c ∈ centralizer ({C.s} : Set G), c * C.x * c⁻¹ = a) ↔ a ∈ C.Acl := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * C.s = C.s * c := mem_centralizer_singleton_iff.1 hc
    have hinv : c⁻¹ * C.s = C.s * c⁻¹ := by
      calc c⁻¹ * C.s = c⁻¹ * (C.s * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * C.s) * c⁻¹ := by rw [hc']
        _ = C.s * c⁻¹ := by group
    refine ⟨?_, ?_, isConj_iff.2 ⟨c, rfl⟩⟩
    · calc c * C.x * c⁻¹ * C.s = c * C.x * (c⁻¹ * C.s) := by group
        _ = c * C.x * (C.s * c⁻¹) := by rw [hinv]
        _ = c * (C.x * C.s) * c⁻¹ := by group
        _ = c * (C.s * C.x) * c⁻¹ := by rw [C.s_comm_x.symm]
        _ = (c * C.s) * C.x * c⁻¹ := by group
        _ = (C.s * c) * C.x * c⁻¹ := by rw [hc']
        _ = C.s * (c * C.x * c⁻¹) := by group
    · rw [show c * C.x * c⁻¹ = MulAut.conj c C.x from rfl, MulEquiv.orderOf_eq]
      exact C.hx
  · rintro ⟨has, ha2, hax⟩
    obtain ⟨c, hc, hcx⟩ := exists_conj_X hF hH Y ha2 has hax
    exact ⟨c, mem_centralizer_singleton_iff.2 hc, hcx⟩

theorem mem_Bcl_iff (hF : FFacts) (hH : HFacts) (Y : C.Y1) (b : G) :
    (∃ c ∈ centralizer ({C.s} : Set G), c * Y.y1 * c⁻¹ = b) ↔ b ∈ C.Bcl := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * C.s = C.s * c := mem_centralizer_singleton_iff.1 hc
    have hinv : c⁻¹ * C.s = C.s * c⁻¹ := by
      calc c⁻¹ * C.s = c⁻¹ * (C.s * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * C.s) * c⁻¹ := by rw [hc']
        _ = C.s * c⁻¹ := by group
    refine ⟨?_, ?_, ?_⟩
    · calc c * Y.y1 * c⁻¹ * C.s = c * Y.y1 * (c⁻¹ * C.s) := by group
        _ = c * Y.y1 * (C.s * c⁻¹) := by rw [hinv]
        _ = c * (Y.y1 * C.s) * c⁻¹ := by group
        _ = c * (C.s * Y.y1) * c⁻¹ := by rw [Y.y1_comm_s]
        _ = (c * C.s) * Y.y1 * c⁻¹ := by group
        _ = (C.s * c) * Y.y1 * c⁻¹ := by rw [hc']
        _ = C.s * (c * Y.y1 * c⁻¹) := by group
    · rw [show c * Y.y1 * c⁻¹ = MulAut.conj c Y.y1 from rfl, MulEquiv.orderOf_eq]
      exact Y.orderOf_y1
    · intro hx
      exact Y.not_isConj_x (hx.trans (isConj_iff.2 ⟨c, rfl⟩).symm)
  · rintro ⟨hbs, hb2, hbx⟩
    obtain ⟨c, hc, hcy⟩ := exists_conj_Y hF hH Y hb2 hbs hbx
    exact ⟨c, mem_centralizer_singleton_iff.2 hc, hcy⟩

omit [Finite G] in
theorem conj_comm_s (c a : G) (hc : c * C.s = C.s * c) (ha : a * C.s = C.s * a) :
    (c * a * c⁻¹) * C.s = C.s * (c * a * c⁻¹) := by
  have hinv : c⁻¹ * C.s = C.s * c⁻¹ := by
    calc c⁻¹ * C.s = c⁻¹ * (C.s * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * C.s) * c⁻¹ := by rw [hc]
      _ = C.s * c⁻¹ := by group
  calc c * a * c⁻¹ * C.s = c * a * (c⁻¹ * C.s) := by group
    _ = c * a * (C.s * c⁻¹) := by rw [hinv]
    _ = c * (a * C.s) * c⁻¹ := by group
    _ = c * (C.s * a) * c⁻¹ := by rw [ha]
    _ = (c * C.s) * a * c⁻¹ := by group
    _ = (C.s * c) * a * c⁻¹ := by rw [hc]
    _ = C.s * (c * a * c⁻¹) := by group

omit [Finite G] in
theorem card_class_mul (a : G) (ha : a * C.s = C.s * a) :
    Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * a * c⁻¹ = g} * cc3 a C.s C.s =
      Nat.card ↥(centralizer ({C.s} : Set G)) := by
  have h := CFSG.ShultStronglyClosedTI.InvolutionCounting.card_centralizer_mul_card_conjugatesOf
    (⟨a, mem_centralizer_singleton_iff.2 ha⟩ : ↥(centralizer ({C.s} : Set G)))
  rw [card_cent_gamma a ha] at h
  have e : Nat.card ↥(conjugatesOf (⟨a, mem_centralizer_singleton_iff.2 ha⟩ :
      ↥(centralizer ({C.s} : Set G)))) =
      Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * a * c⁻¹ = g} := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.1, ?_⟩
        invFun := fun g => ⟨⟨g.1, ?_⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨c, hc⟩ := isConj_iff.1 g.2
      exact ⟨c.1, c.2, congrArg Subtype.val hc⟩
    · obtain ⟨c, hc, hcg⟩ := g.2
      rw [← hcg]
      exact mem_centralizer_singleton_iff.2 (conj_comm_s c a (mem_centralizer_singleton_iff.1 hc) ha)
    · obtain ⟨c, hc, hcg⟩ := g.2
      exact isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hcg⟩
    · intro g; rfl
    · intro g; rfl
  rw [e] at h
  rw [← h]
  ring

omit [Finite G] in
theorem card_Acl_mul (hF : FFacts) :
    Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * C.x * c⁻¹ = g} * 288 =
      Nat.card ↥(centralizer ({C.s} : Set G)) := by
  have := card_class_mul (C := C) C.x C.s_comm_x.symm
  rwa [cc3_x_s_s hF] at this

theorem card_Bcl_mul (hH : HFacts) (Y : C.Y1) :
    Nat.card {g : G // ∃ c ∈ centralizer ({C.s} : Set G), c * Y.y1 * c⁻¹ = g} * 576 =
      Nat.card ↥(centralizer ({C.s} : Set G)) := by
  have := card_class_mul (C := C) Y.y1 Y.y1_comm_s
  rwa [(Y.tau_cases hH).2] at this

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
