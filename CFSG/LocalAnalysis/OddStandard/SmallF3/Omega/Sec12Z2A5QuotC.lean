module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128Odd
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {Y : Type} [Group Y] {τ : Y}

private theorem z2a5_odd_oddCore [Finite Y] : Odd (Nat.card (oddCore Y)) :=
  CFSG.ComponentClassification.OddCore.odd_card Y

theorem z2a5_cent_inf_oddCore [Finite Y] (h : Z2A5Hyp Y τ) :
    centralizer ({τ} : Set Y) ⊓ oddCore Y = ⊥ := by
  have hinv := (sec128_oddCore_cent τ h.1 h.2.1 h.2.2).1
  refine eq_bot_iff.mpr fun o ho => ?_
  obtain ⟨hoC, hoO⟩ := Subgroup.mem_inf.mp ho
  have hc : o * τ = τ * o := mem_centralizer_singleton_iff.1 hoC
  have h1 : τ * o * τ⁻¹ = o := by rw [← hc, mul_inv_cancel_right]
  have hsq : o * o = 1 := by
    have h2 := hinv o hoO
    rw [h1] at h2
    calc o * o = o * o⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel o
  have h2 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hodd : Odd (orderOf o) := by
    have h3 : orderOf o ∣ Nat.card (oddCore Y) := by
      rw [← orderOf_mk o hoO]
      exact orderOf_dvd_natCard _
    exact z2a5_odd_oddCore.of_dvd_nat h3
  have h4 : orderOf o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h5 | h5
    · exact h5
    · rw [h5] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.1 h4)

theorem z2a5_quot_cent [Finite Y] (h : Z2A5Hyp Y τ) :
    centralizer ({(τ : Y ⧸ oddCore Y)} : Set (Y ⧸ oddCore Y)) =
      (centralizer ({τ} : Set Y)).map (QuotientGroup.mk' (oddCore Y)) :=
  CFSG.ComponentClassification.AschbacherToolkit.centralizer_quotient_odd (oddCore Y)
    z2a5_odd_oddCore τ h.1

theorem z2a5_map_oTwoRes {Z : Type} [Group Z] (f : Y →* Z) {H : Subgroup Y}
    (hf : H ⊓ f.ker = ⊥) : (oTwoRes H).map f = oTwoRes (H.map f) := by
  have hres : Function.Injective (f.comp H.subtype) := by
    refine (injective_iff_map_eq_one _).2 fun a ha => ?_
    have hmem : (a : Y) ∈ H ⊓ f.ker := ⟨a.2, f.mem_ker.2 ha⟩
    rw [hf] at hmem
    exact Subtype.ext (Subgroup.mem_bot.1 hmem)
  have hord : ∀ x ∈ H, orderOf (f x) = orderOf x := by
    intro x hx
    have h1 := orderOf_injective (f.comp H.subtype) hres ⟨x, hx⟩
    rw [orderOf_mk] at h1
    exact h1
  unfold oTwoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨hxH, hxo⟩, rfl⟩
    exact ⟨⟨x, hxH, rfl⟩, by rw [hord x hxH]; exact hxo⟩
  · rintro ⟨⟨x, hxH, rfl⟩, hzo⟩
    exact ⟨x, ⟨hxH, by rw [← hord x hxH]; exact hzo⟩, rfl⟩

end CFSG.OddStandard.SmallF3.Omega
