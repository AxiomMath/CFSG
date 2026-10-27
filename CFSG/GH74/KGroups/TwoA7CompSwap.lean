module

public import CFSG.GH74.KGroups.TwoA7Odd
public import CFSG.GH74.KGroups.TwoA7Small
public import CFSG.GH74.GLS.IVK.A7.Core
public import CFSG.GH74.KGroups.TwoA7Cover
public import CFSG.GH74.KGroups.TwoA7Fixed

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm Subgroup CFSG.GH74.GLS

section Swap

variable {E : Type} [Group E] [Finite E] {π : E →* A7} {z : E}

theorem exists_pComponent_swap
    (h : IsDoubleCoverA7 π z) (φ : MulAut E)
    (hσ : (h.autPerm φ).IsSwap) :
    ∃ L : Subgroup ↥(fixedSubgroup E φ), IsPComponent 2 L := by
  obtain ⟨e⟩ := CFSG.GH74.GLS.IVK.A7.centralizer_A7_swap_equiv hσ
  let e' : ↥(centA (h.autPerm φ)) ≃* Perm (Fin 5) := e
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  set ρ := rhoX h φ e' with hρ
  let zX : ↥(fixedSubgroup E φ) := ⟨z, z_mem_fixed h φ⟩
  have hzX : orderOf zX = 2 := by rw [Subgroup.orderOf_mk, orderOf_z h]
  have hker : ∀ x : ↥(fixedSubgroup E φ), ρ x = 1 → x = 1 ∨ x = zX := by
    intro x hx
    rcases (rhoX_eq_one_iff h φ e' x).1 hx with h1 | h1
    · exact Or.inl (Subtype.ext h1)
    · exact Or.inr (Subtype.ext h1)
  have hX : pPrimeCore 2 ↥(fixedSubgroup E φ) = ⊥ :=
    pPrimeCore_eq_bot_of_rho ρ hzX hker (alternatingGroup (Fin 5))
      (alternatingGroup_le_range_rhoX h φ e') hBodd_alt5 hC_alt5
  let L : Subgroup ↥(fixedSubgroup E φ) := (alternatingGroup (Fin 5)).comap ρ
  have hzL : zX ∈ L := by
    show ρ zX ∈ alternatingGroup (Fin 5)
    have : ρ zX = 1 := (rhoX_eq_one_iff h φ e' zX).2 (Or.inr rfl)
    rw [this]
    exact Subgroup.one_mem _
  let θ : ↥L →* ↥(alternatingGroup (Fin 5)) :=
    (ρ.comp L.subtype).codRestrict (alternatingGroup (Fin 5)) (fun x => x.2)
  have hθ : Function.Surjective θ := by
    intro a
    obtain ⟨x, hx⟩ := alternatingGroup_le_range_rhoX h φ e' a.2
    have hxL : x ∈ L := by
      show ρ x ∈ alternatingGroup (Fin 5)
      rw [hx]
      exact a.2
    exact ⟨⟨x, hxL⟩, Subtype.ext hx⟩
  have hnc : ∃ a b : ↥(alternatingGroup (Fin 5)), a * b ≠ b * a :=
    ⟨⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      ⟨swap 2 3 * swap 3 4, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      fun h1 => by
        have := congrArg Subtype.val h1
        revert this
        decide +kernel⟩
  have hev : ∃ s : ↥(alternatingGroup (Fin 5)), s * s = 1 ∧ s ≠ 1 :=
    ⟨⟨swap 0 1 * swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
      Subtype.ext (by decide +kernel), fun h1 => by
        have := congrArg Subtype.val h1
        revert this
        decide +kernel⟩
  have hqs : CFSG.IsQuasisimple ↥L := by
    refine isQuasisimple_of_cover hnc hev θ hθ (z := ⟨zX, hzL⟩) ?_ ?_ ?_
    · intro g
      exact Subtype.ext (Subtype.ext (h.central ((g : ↥(fixedSubgroup E φ)) : E)))
    · intro w
      constructor
      · intro hw
        have h1 : ρ (w : ↥(fixedSubgroup E φ)) = 1 := congrArg Subtype.val hw
        rcases (rhoX_eq_one_iff h φ e' _).1 h1 with h2 | h2
        · exact Or.inl (Subtype.ext (Subtype.ext h2))
        · exact Or.inr (Subtype.ext (Subtype.ext h2))
      · rintro (h2 | h2)
        · rw [h2, map_one]
        · apply Subtype.ext
          show ρ (w : ↥(fixedSubgroup E φ)) = 1
          rw [h2]
          exact (rhoX_eq_one_iff h φ e' zX).2 (Or.inr rfl)
    · intro w hw
      have h1 : ((w : ↥(fixedSubgroup E φ)) : E) * ((w : ↥(fixedSubgroup E φ)) : E) = 1 :=
        congrArg (fun t : ↥L => ((t : ↥(fixedSubgroup E φ)) : E)) hw
      rcases h.eq_one_or_eq_z_of_sq_eq_one h1 with h2 | h2
      · exact Or.inl (Subtype.ext (Subtype.ext h2))
      · exact Or.inr (Subtype.ext (Subtype.ext h2))
  exact ⟨L, isPComponent_of_normal hX hqs⟩

end Swap

end CFSG.GH74.KGroups.TwoA7
