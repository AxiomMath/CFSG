module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPCompA5

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Equiv Subgroup

variable {K : Type*} [Group K] {A : Subgroup K}

theorem inf_centralizer_eq_bot_of_alt5 (e : ↥A ≃* alternatingGroup (Fin 5)) :
    A ⊓ centralizer (A : Set K) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
    have htriv : ∀ z : alternatingGroup (Fin 5), (∀ y, y * z = z * y) → z = 1 := by
      decide +kernel
    have hx1 : e ⟨x, hxA⟩ = 1 :=
      htriv (e ⟨x, hxA⟩) fun y => by
        have hcomm : (e.symm y) * ⟨x, hxA⟩ = ⟨x, hxA⟩ * (e.symm y) := by
          apply Subtype.ext
          simpa using hxC (e.symm y : K) (e.symm y).2
        calc
          y * e ⟨x, hxA⟩ = e (e.symm y) * e ⟨x, hxA⟩ := by
            rw [MulEquiv.apply_symm_apply]
          _ = e ((e.symm y) * ⟨x, hxA⟩) := by rw [map_mul]
          _ = e (⟨x, hxA⟩ * (e.symm y)) := by rw [hcomm]
          _ = e ⟨x, hxA⟩ * e (e.symm y) := by rw [map_mul]
          _ = e ⟨x, hxA⟩ * y := by rw [MulEquiv.apply_symm_apply]
    have hsub : (⟨x, hxA⟩ : ↥A) = 1 := e.injective (by rw [hx1, map_one])
    simpa using congrArg Subtype.val hsub
  · exact bot_le

theorem card_inf_centralizer_single_of_alt5 (e : ↥A ≃* alternatingGroup (Fin 5)) {c : K}
    (hcA : c ∈ A) (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    Nat.card ↥(A ⊓ centralizer ({c} : Set K)) = 4 ∧
      ∀ a ∈ A ⊓ centralizer ({c} : Set K), a * a = 1 := by
  have hc2' : (⟨c, hcA⟩ : ↥A) * ⟨c, hcA⟩ = 1 := by
    apply Subtype.ext
    simpa using hc2
  have hc1' : (⟨c, hcA⟩ : ↥A) ≠ 1 := by
    intro h
    exact hc1 (by simpa using congrArg Subtype.val h)
  obtain ⟨h4, hall⟩ := card_centralizer_of_involution_alt5 e (c := ⟨c, hcA⟩) hc2' hc1'
  have hmap : (Subgroup.centralizer ({⟨c, hcA⟩} : Set ↥A)).map A.subtype =
      A ⊓ Subgroup.centralizer ({c} : Set K) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact Subgroup.mem_inf.mpr ⟨a.2, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp ha)⟩
    · intro hx
      obtain ⟨hxA, hxc⟩ := Subgroup.mem_inf.mp hx
      rw [Subgroup.mem_map]
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (by simpa using Subgroup.mem_centralizer_singleton_iff.mp hxc)
  refine ⟨?_, ?_⟩
  · calc
      Nat.card ↥(A ⊓ centralizer ({c} : Set K))
          = Nat.card ↥((Subgroup.centralizer ({⟨c, hcA⟩} : Set ↥A)).map A.subtype) := by
            rw [hmap]
      _ = Nat.card ↥(Subgroup.centralizer ({⟨c, hcA⟩} : Set ↥A)) :=
            Subgroup.card_map_of_injective A.subtype_injective
      _ = Nat.card {a : ↥A // a * ⟨c, hcA⟩ = ⟨c, hcA⟩ * a} :=
            Nat.card_congr (Equiv.subtypeEquivRight
              (fun a : ↥A => Subgroup.mem_centralizer_singleton_iff))
      _ = 4 := h4
  · intro a ha
    obtain ⟨haA, hac⟩ := Subgroup.mem_inf.mp ha
    have hcomm : (⟨a, haA⟩ : ↥A) * ⟨c, hcA⟩ = ⟨c, hcA⟩ * ⟨a, haA⟩ :=
      Subtype.ext (by simpa using Subgroup.mem_centralizer_singleton_iff.mp hac)
    have haa := hall ⟨a, haA⟩ hcomm
    simpa using congrArg Subtype.val haa

end CFSG.EvenSporadicStandard.M12Std.Rbc
