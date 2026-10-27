module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideCommutator

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

variable (h : Setup L A C z)
include h

theorem card_fixSub_zmul_le {t : G} (ht : t ∈ egNL L A) :
    Nat.card (fixSub C (z * t)) ≤ Nat.card (fixSub A t) ^ 2 := by
  have htz : t * z = z * t := Quad.nl_comm_z h.hs ht
  have hzz : z * z = 1 := Quad.z_mul_self h.hs
  have hzi : z⁻¹ = z := Quad.z_inv h.hs
  have hfix : ∀ x : fixSub C (z * t),
      t * (z * (x : G) * z⁻¹ * (x : G)⁻¹) * t⁻¹ = z * (x : G) * z⁻¹ * (x : G)⁻¹ := by
    intro x
    have hx : (z * t) * ((x : C) : G) * (z * t)⁻¹ = (x : C) := x.2
    have h1 : z * (t * ((x : C) : G) * t⁻¹) * z⁻¹ = (x : C) := by
      calc z * (t * ((x : C) : G) * t⁻¹) * z⁻¹ = (z * t) * ((x : C) : G) * (z * t)⁻¹ := by group
        _ = (x : C) := hx
    have hx'' : t * ((x : C) : G) * t⁻¹ = z⁻¹ * (x : G) * z := by
      calc t * ((x : C) : G) * t⁻¹ = z⁻¹ * (z * (t * ((x : C) : G) * t⁻¹) * z⁻¹) * z := by group
        _ = z⁻¹ * (x : G) * z := by rw [h1]
    have hδ : (z * (x : G) * z⁻¹ * (x : G)⁻¹) * (z * (x : G) * z⁻¹ * (x : G)⁻¹) = 1 := by
      have hA : z * (x : G) * z⁻¹ * (x : G)⁻¹ ∈ A := comm_mem_A h (x : C).2
      exact h.hCe _ (h.hC.A_le hA)
    have hinv : (z * (x : G) * z⁻¹ * (x : G)⁻¹)⁻¹ = z * (x : G) * z⁻¹ * (x : G)⁻¹ :=
      inv_eq_of_mul_eq_one_right hδ
    have e1 : t * z * t⁻¹ = z := by rw [htz]; group
    have e2 : t * z⁻¹ * t⁻¹ = z⁻¹ := by
      calc t * z⁻¹ * t⁻¹ = (t * z * t⁻¹)⁻¹ := by group
        _ = z⁻¹ := by rw [e1]
    have key : t * (z * (x : G) * z⁻¹ * (x : G)⁻¹) * t⁻¹ =
        (z * (x : G) * z⁻¹ * (x : G)⁻¹)⁻¹ := by
      calc t * (z * (x : G) * z⁻¹ * (x : G)⁻¹) * t⁻¹
          = (t * z * t⁻¹) * (t * (x : G) * t⁻¹) * (t * z⁻¹ * t⁻¹) * (t * (x : G) * t⁻¹)⁻¹ := by
            group
        _ = z * (z⁻¹ * (x : G) * z) * z⁻¹ * (z⁻¹ * (x : G) * z)⁻¹ := by rw [e1, e2, hx'']
        _ = (x : G) * (z⁻¹ * (x : G)⁻¹ * z) := by group
        _ = (x : G) * (z * (x : G)⁻¹ * z⁻¹) := by rw [hzi]
        _ = (z * (x : G) * z⁻¹ * (x : G)⁻¹)⁻¹ := by group
    rw [key, hinv]
  let φ : fixSub C (z * t) →* fixSub A t :=
    { toFun := fun x => ⟨commHom h x.1, hfix x⟩
      map_one' := Subtype.ext (map_one (commHom h))
      map_mul' := fun x y => Subtype.ext (map_mul (commHom h) x.1 y.1) }
  have hker : Nat.card φ.ker ≤ Nat.card (fixSub A t) := by
    have hmem : ∀ s : φ.ker, ((s.1.1 : C) : G) ∈ A := fun s => by
      have hs : φ s.1 = 1 := s.2
      have h1 : commHom h s.1.1 = 1 := congrArg (fun y : fixSub A t => (y : A)) hs
      exact (commHom_eq_one_iff h s.1.1.2).1 h1
    have hfixA : ∀ s : φ.ker, t * ((s.1.1 : C) : G) * t⁻¹ = ((s.1.1 : C) : G) := fun s => by
      have hx : (z * t) * ((s.1.1 : C) : G) * (z * t)⁻¹ = (s.1.1 : C) := s.1.2
      have hza : z * ((s.1.1 : C) : G) = ((s.1.1 : C) : G) * z :=
        (Quad.comm_z h.hs (h.hAL (hmem s))).symm ▸
          (mem_centralizer_iff.1 (h.hs.z_central (mem_zpowers z)) _ (h.hAL (hmem s))).symm
      have e : t * ((s.1.1 : C) : G) * t⁻¹ =
          z⁻¹ * ((z * t) * ((s.1.1 : C) : G) * (z * t)⁻¹) * z := by group
      rw [e, hx]
      calc z⁻¹ * ((s.1.1 : C) : G) * z = z⁻¹ * (z * ((s.1.1 : C) : G)) := by rw [hza]; group
        _ = ((s.1.1 : C) : G) := by group
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨((s.1.1 : C) : G), hmem s⟩, hfixA s⟩ : fixSub A t)) ?_
    intro s s' hss
    have : ((s.1.1 : C) : G) = ((s'.1.1 : C) : G) :=
      congrArg (fun y : fixSub A t => ((y : A) : G)) hss
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  have hrange : Nat.card φ.range ≤ Nat.card (fixSub A t) := Subgroup.card_le_card_group _
  calc Nat.card (fixSub C (z * t)) = Nat.card φ.ker * Nat.card φ.range :=
        (Subgroup.card_ker_mul_card_range φ).symm
    _ ≤ Nat.card (fixSub A t) * Nat.card (fixSub A t) := Nat.mul_le_mul hker hrange
    _ = Nat.card (fixSub A t) ^ 2 := (sq _).symm

end CSide

end CFSG.EvenSporadicStandard.M24Std
