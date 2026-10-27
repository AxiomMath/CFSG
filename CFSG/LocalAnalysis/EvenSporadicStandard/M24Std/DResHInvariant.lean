module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerD

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open Subgroup

namespace Invariant

variable {G : Type} [Group G]

theorem card_eq_one_or_card_B {L B : Subgroup G} (hb : OctadBasics L B) {W : Subgroup G}
    (hWB : W ≤ B) (hW : ∀ n ∈ egNL L B, ∀ w ∈ W, n * w * n⁻¹ ∈ W) :
    Nat.card W = 1 ∨ Nat.card W = 16 := by
  by_cases hW1 : W = ⊥
  · left
    rw [hW1]
    exact Subgroup.card_bot
  · right
    obtain ⟨⟨x, hxW⟩, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW1
    have hx1 : x ≠ 1 := fun h => hx (Subtype.ext h)
    have hBW : B ≤ W := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]
        exact one_mem W
      · obtain ⟨n, hn, hnxy⟩ := hb.trans x (hWB hxW) y hy hx1 hy1
        rw [← hnxy]
        exact hW n hn x hxW
    rw [le_antisymm hWB hBW, hb.card_B]

theorem exists_hom_comm (z : G) {D : Subgroup G} (hc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hz : ∀ d ∈ D, z * d * z⁻¹ ∈ D) :
    ∃ δ : D →* G, ∀ d : D, δ d = z * (d : G) * z⁻¹ * (d : G)⁻¹ := by
  refine ⟨MonoidHom.mk' (fun d : D => z * (d : G) * z⁻¹ * (d : G)⁻¹) fun a b => ?_, fun d => rfl⟩
  have hcom : (a : G)⁻¹ * (z * (b : G) * z⁻¹ * (b : G)⁻¹) =
      (z * (b : G) * z⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ :=
    hc _ (inv_mem a.2) _ (mul_mem (hz b b.2) (inv_mem b.2))
  show z * ((a : G) * b) * z⁻¹ * ((a : G) * b)⁻¹ =
    (z * (a : G) * z⁻¹ * (a : G)⁻¹) * (z * (b : G) * z⁻¹ * (b : G)⁻¹)
  calc z * ((a : G) * b) * z⁻¹ * ((a : G) * b)⁻¹
      = (z * (a : G) * z⁻¹) * ((z * (b : G) * z⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
    _ = (z * (a : G) * z⁻¹) * ((a : G)⁻¹ * (z * (b : G) * z⁻¹ * (b : G)⁻¹)) := by rw [← hcom]
    _ = (z * (a : G) * z⁻¹ * (a : G)⁻¹) * (z * (b : G) * z⁻¹ * (b : G)⁻¹) := by group

end Invariant

open Invariant

theorem card_invariant_mem {G : Type} [Group G] [Finite G] {L B D : Subgroup G} {z : G}
    (hs : LocalSetting G L z) (hBL : B ≤ L) (hb : OctadBasics L B) (hD : NData B z D)
    (U : Subgroup G) (hUD : U ≤ D) (hU : ∀ l ∈ egNL L B, ∀ u ∈ U, l * u * l⁻¹ ∈ U) :
    Nat.card U = 1 ∨ Nat.card U = 16 ∨ Nat.card U = 256 := by
  obtain ⟨δD, hδD⟩ := exists_hom_comm z hD.elem.1
    (fun d hd => hD.norm z (Octad.z_mem_egM hs hBL) d hd)
  let δ : U →* G := δD.comp (Subgroup.inclusion hUD)
  have hδ : ∀ u : U, δ u = z * (u : G) * z⁻¹ * (u : G)⁻¹ := fun u => hδD ⟨u, hUD u.2⟩
  have hker : δ.ker = (U ⊓ B).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hδ, mem_subgroupOf, mem_inf]
    constructor
    · intro h
      refine ⟨u.2, ?_⟩
      have h1 : z * (u : G) = u * z := by
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        exact h
      exact LayerD.mem_B_of_mem_D_of_comm hs hBL hb hD (hUD u.2) h1.symm
    · rintro ⟨-, hB⟩
      rw [Octad.z_comm hs (hBL hB)]
      group
  have hk : Nat.card δ.ker = Nat.card (U ⊓ B : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hinf_inv : ∀ n ∈ egNL L B, ∀ w ∈ U ⊓ B, n * w * n⁻¹ ∈ U ⊓ B := by
    intro n hn w hw
    obtain ⟨hwU, hwB⟩ := mem_inf.1 hw
    exact mem_inf.2 ⟨hU n hn w hwU, (mem_normalizer_iff.1 (mem_inf.1 hn).1 w).1 hwB⟩
  have hrange_le : δ.range ≤ B := by
    rintro _ ⟨u, rfl⟩
    rw [hδ]
    exact hD.comm_z u (hUD u.2)
  have hrange_inv : ∀ n ∈ egNL L B, ∀ w ∈ δ.range, n * w * n⁻¹ ∈ δ.range := by
    rintro n hn _ ⟨u, rfl⟩
    refine ⟨⟨n * u * n⁻¹, hU n hn u u.2⟩, ?_⟩
    have hzn : z * n = n * z := Octad.z_comm hs (mem_inf.1 hn).2
    have e1 : n⁻¹ * z⁻¹ = z⁻¹ * n⁻¹ := by
      have h := congrArg (fun x => x⁻¹) hzn
      simpa [mul_inv_rev] using h
    rw [hδ, hδ]
    calc z * (n * (u : G) * n⁻¹) * z⁻¹ * (n * (u : G) * n⁻¹)⁻¹
        = (z * n) * u * (n⁻¹ * z⁻¹) * n * (u : G)⁻¹ * n⁻¹ := by group
      _ = (n * z) * u * (z⁻¹ * n⁻¹) * n * (u : G)⁻¹ * n⁻¹ := by rw [hzn, e1]
      _ = n * (z * (u : G) * z⁻¹ * (u : G)⁻¹) * n⁻¹ := by group
  have hprod := Subgroup.card_ker_mul_card_range δ
  rw [hk] at hprod
  rcases card_eq_one_or_card_B hb inf_le_right hinf_inv with h1 | h1 <;>
    rcases card_eq_one_or_card_B hb hrange_le hrange_inv with h2 | h2 <;>
    rw [h1, h2] at hprod <;> omega

end CFSG.EvenSporadicStandard.M24Std.DResH
