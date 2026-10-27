module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DGen
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DFull
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.PermV

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def Bb (V H : Subgroup G) : Subgroup G := normalizer (V : Set G) ⊓ normalizer (H : Set G)

theorem Mm_eq (V H : Subgroup G) : Mm V H = centralizer (V : Set G) ⊓ Bb V H := by
  ext m
  constructor
  · intro hm; exact ⟨hm.1, centralizer_le_normalizer _ hm.1, hm.2⟩
  · intro hm; exact ⟨hm.1, hm.2.2⟩

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f)
include d

theorem cent_cover [Finite G] (hsyl : Sylow2In H (centralizer (V : Set G))) :
    ∀ b ∈ Bb V H, ∃ h ∈ H, b * x * b⁻¹ = h * x * h⁻¹ := by
  obtain ⟨n, -, hn⟩ := IsYGroup.card_pow4 d.iv4
  have hxM : x ∈ Mm V H := d.x_mem_M
  have hxB : x ∈ Bb V H := ⟨centralizer_le_normalizer _ hxM.1, hxM.2⟩
  have hfB : f ∈ Bb V H := ⟨d.hI.f_N, d.hI.f_H⟩
  have hfQ : ∀ q ∈ Bb V H, f * q * f⁻¹ ∈ Bb V H := fun q hq =>
    (Bb V H).mul_mem ((Bb V H).mul_mem hfB hq) ((Bb V H).inv_mem hfB)
  have hBle : Bb V H ≤ normalizer (V : Set G) ⊓ normalizer (H : Set G) := le_rfl
  have hBV : Bb V H ≤ normalizer (V : Set G) := fun b hb => hb.1
  have N1 := card_cls_mul (Bb V H) hxB
  have hβ6 := relIndex_dvd_six (V := V) (Q := Bb V H) d.out.V_four.2 hBV
  have N5 := relIndex_mul_card (centralizer (V : Set G) ⊓ Bb V H) (Bb V H)
  rw [inf_of_le_left inf_le_right] at N5
  have hCx : Bb V H ⊓ centralizer ({x} : Set G) ≤ Bb V H := inf_le_left
  have hk := relIndex_dvd_of_le V hCx hBV
  have N6 := relIndex_mul_card (centralizer (V : Set G) ⊓ (Bb V H ⊓ centralizer ({x} : Set G)))
    (Bb V H ⊓ centralizer ({x} : Set G))
  rw [inf_of_le_left inf_le_right] at N6
  have hCxM : centralizer (V : Set G) ⊓ (Bb V H ⊓ centralizer ({x} : Set G)) =
      Mm V H ⊓ centralizer ({x} : Set G) := by
    ext m
    constructor
    · intro hm; exact ⟨⟨hm.1, hm.2.1.2⟩, hm.2.2⟩
    · intro hm; exact ⟨hm.1.1, ⟨centralizer_le_normalizer _ hm.1.1, hm.1.2⟩, hm.2⟩
  obtain ⟨o, ho, hCx8⟩ := d.out.card_cent_M d.hI.E_le
  have hHM : H ≤ Mm V H := fun h hh => ⟨d.hI.H_le hh, le_normalizer hh⟩
  have hMC : Mm V H ≤ centralizer (V : Set G) := fun m hm => hm.1
  have hmul := relIndex_mul_relIndex H (Mm V H) (centralizer (V : Set G)) hHM hMC
  have hu : ¬ 2 ∣ H.relIndex (Mm V H) := fun hd => hsyl.2.2 (hmul ▸ Dvd.dvd.mul_right hd _)
  have N4 := relIndex_mul_card H (Mm V H)
  rw [inf_of_le_left hHM] at N4
  have hH : Nat.card H = 2 * 4 ^ n := by
    rw [InH.card_H_of d.out d.iv1 d.iv2 d.iv3 d.hI, hn]
  have hMcard : Nat.card ↥(centralizer (V : Set G) ⊓ Bb V H) = Nat.card ↥(Mm V H) := by
    rw [Mm_eq]
  have hCxcard : Nat.card ↥(centralizer (V : Set G) ⊓ (Bb V H ⊓ centralizer ({x} : Set G))) =
      8 * o := by
    rw [hCxM]; exact hCx8
  have N4' : H.relIndex (Mm V H) * (2 * 4 ^ n) =
      Nat.card ↥(centralizer (V : Set G) ⊓ Bb V H) := by
    rw [hMcard, ← hH]; exact N4
  have N6' : (centralizer (V : Set G) ⊓ (Bb V H ⊓ centralizer ({x} : Set G))).relIndex
      (Bb V H ⊓ centralizer ({x} : Set G)) * (8 * o) =
      Nat.card ↥(Bb V H ⊓ centralizer ({x} : Set G)) := by
    rw [← hCxcard]; exact N6
  obtain ⟨β', hβ'⟩ := hk
  have hk0 : 0 < (centralizer (V : Set G) ⊓ (Bb V H ⊓ centralizer ({x} : Set G))).relIndex
      (Bb V H ⊓ centralizer ({x} : Set G)) := by
    rcases Nat.eq_zero_or_pos ((centralizer (V : Set G) ⊓
      (Bb V H ⊓ centralizer ({x} : Set G))).relIndex (Bb V H ⊓ centralizer ({x} : Set G))) with h0 | h0
    · exfalso
      have hpos : 0 < Nat.card ↥(Bb V H ⊓ centralizer ({x} : Set G)) := Nat.card_pos
      rw [h0, zero_mul] at N6'
      omega
    · exact h0
  have ha0 : 0 < Nat.card (cls (Bb V H) x) := by
    have : Nonempty (cls (Bb V H) x) := ⟨⟨x, x_mem_cls⟩⟩
    exact Nat.card_pos
  have hale : Nat.card (cls (Bb V H) x) ≤ 4 ^ n := by
    have := d.card_cls_le' hBle
    rwa [hn] at this
  have hmod : Nat.card (cls (Bb V H) x) % 3 = 1 := d.card_cls_mod3' hBle hfQ
  have h4a := para_arith n _ o _ _ _ β' _ _ _ ho hu hβ6 hβ' hk0 N1 N5 N6' N4' hale hmod ha0
  have hHB : H ≤ Bb V H := fun h hh => ⟨centralizer_le_normalizer _ (d.hI.H_le hh), le_normalizer hh⟩
  have hcH := card_cls_mul H d.hI.x_mem
  rw [InH.C_H_x d.out d.hI, d.out.card_EV, hH] at hcH
  have hsub : cls H x ⊆ cls (Bb V H) x := by
    rintro y ⟨m, hm, rfl⟩
    exact ⟨m, hHB hm, rfl⟩
  have hHc : 4 * Nat.card (cls H x) = 4 ^ n := by omega
  have hle : (cls (Bb V H) x).ncard ≤ (cls H x).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  intro b hb
  have : b * x * b⁻¹ ∈ cls (Bb V H) x := ⟨b, hb, rfl⟩
  rw [← heq] at this
  obtain ⟨h, hh, hbh⟩ := this
  exact ⟨h, hh, hbh⟩

end D13

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
