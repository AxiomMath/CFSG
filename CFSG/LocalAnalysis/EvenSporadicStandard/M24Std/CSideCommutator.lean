module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideBasic

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

variable (h : Setup L A C z)
include h

theorem comm_mem_A {c : G} (hc : c ∈ C) : z * c * z⁻¹ * c⁻¹ ∈ A := h.hC.comm_z c hc

theorem comm_mul {x y : G} (hx : x ∈ C) (hy : y ∈ C) :
    z * (x * y) * z⁻¹ * (x * y)⁻¹ = (z * x * z⁻¹ * x⁻¹) * (z * y * z⁻¹ * y⁻¹) := by
  have ha' : z * y * z⁻¹ * y⁻¹ ∈ C := h.hC.A_le (comm_mem_A h hy)
  have hcomm : x⁻¹ * (z * y * z⁻¹ * y⁻¹) = (z * y * z⁻¹ * y⁻¹) * x⁻¹ :=
    h.hC.comm _ (inv_mem hx) _ ha'
  calc z * (x * y) * z⁻¹ * (x * y)⁻¹
      = (z * x * z⁻¹) * ((z * y * z⁻¹ * y⁻¹) * x⁻¹) := by group
    _ = (z * x * z⁻¹) * (x⁻¹ * (z * y * z⁻¹ * y⁻¹)) := by rw [hcomm]
    _ = (z * x * z⁻¹ * x⁻¹) * (z * y * z⁻¹ * y⁻¹) := by group

@[expose] noncomputable def commHom : C →* A where
  toFun c := ⟨z * c * z⁻¹ * c⁻¹, comm_mem_A h c.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' c c' := Subtype.ext (comm_mul h c.2 c'.2)

theorem commHom_eq_one_iff {x : G} (hx : x ∈ C) : commHom h ⟨x, hx⟩ = 1 ↔ x ∈ A := by
  constructor
  · intro hc
    have h1 : z * x * z⁻¹ * x⁻¹ = 1 := congrArg Subtype.val hc
    apply mem_A_of_comm h hx
    calc x * z = (z * x * z⁻¹ * x⁻¹) * (x * z) := by rw [h1, one_mul]
      _ = z * x := by group
  · intro hc
    apply Subtype.ext
    have hcz : x * z = z * x :=
      mem_centralizer_iff.1 (h.hs.z_central (mem_zpowers z)) x (h.hAL hc)
    show z * x * z⁻¹ * x⁻¹ = 1
    calc z * x * z⁻¹ * x⁻¹ = (x * z) * z⁻¹ * x⁻¹ := by rw [← hcz]
      _ = 1 := by group

end CSide

@[expose] def fixSub {G : Type} [Group G] (H : Subgroup G) (t : G) : Subgroup H where
  carrier := {c | t * c * t⁻¹ = c}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have ha' : t * (a : G) * t⁻¹ = a := ha
    have hb' : t * (b : G) * t⁻¹ = b := hb
    show t * ((a : G) * b) * t⁻¹ = (a : G) * b
    calc t * ((a : G) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      _ = (a : G) * b := by rw [ha', hb']
  inv_mem' {a} ha := by
    have ha' : t * (a : G) * t⁻¹ = a := ha
    show t * (a : G)⁻¹ * t⁻¹ = (a : G)⁻¹
    calc t * (a : G)⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
      _ = (a : G)⁻¹ := by rw [ha']

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

variable (h : Setup L A C z)
include h

theorem card_fixSub_le {t : G} (ht : t ∈ egNL L A) :
    Nat.card (fixSub C t) ≤ Nat.card (fixSub A t) ^ 2 := by
  have htz : t * z = z * t :=
    mem_centralizer_iff.1 (h.hs.z_central (mem_zpowers z)) t (Subgroup.mem_inf.1 ht).2
  have hfix : ∀ x : fixSub C t,
      t * (z * (x : G) * z⁻¹ * (x : G)⁻¹) * t⁻¹ = z * (x : G) * z⁻¹ * (x : G)⁻¹ := by
    intro x
    have hx : t * ((x : C) : G) * t⁻¹ = (x : C) := x.2
    have hc1 : Commute t z := htz
    have hc2 : Commute t ((x : C) : G) := by
      have : t * ((x : C) : G) = (x : C) * t := by
        rw [mul_inv_eq_iff_eq_mul] at hx
        exact hx
      exact this
    have hc : Commute t (z * ((x : C) : G) * z⁻¹ * ((x : C) : G)⁻¹) :=
      (((hc1.mul_right hc2).mul_right hc1.inv_right).mul_right hc2.inv_right)
    rw [hc.eq, mul_inv_cancel_right]
  let φ : fixSub C t →* fixSub A t :=
    { toFun := fun x => ⟨commHom h x.1, hfix x⟩
      map_one' := Subtype.ext (map_one (commHom h))
      map_mul' := fun x y => Subtype.ext (map_mul (commHom h) x.1 y.1) }
  have hker : Nat.card φ.ker ≤ Nat.card (fixSub A t) := by
    have hmem : ∀ s : φ.ker, ((s.1.1 : C) : G) ∈ A := fun s => by
      have hs : φ s.1 = 1 := s.2
      have h1 : commHom h s.1.1 = 1 := congrArg (fun y : fixSub A t => (y : A)) hs
      exact (commHom_eq_one_iff h s.1.1.2).1 h1
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨((s.1.1 : C) : G), hmem s⟩, s.1.2⟩ : fixSub A t)) ?_
    intro s s' hss
    have : ((s.1.1 : C) : G) = ((s'.1.1 : C) : G) :=
      congrArg (fun y : fixSub A t => ((y : A) : G)) hss
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  have hrange : Nat.card φ.range ≤ Nat.card (fixSub A t) := Subgroup.card_le_card_group _
  calc Nat.card (fixSub C t) = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card (fixSub A t) * Nat.card (fixSub A t) := Nat.mul_le_mul hker hrange
    _ = Nat.card (fixSub A t) ^ 2 := (sq _).symm

end CSide

end CFSG.EvenSporadicStandard.M24Std
