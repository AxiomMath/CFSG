module

public import CFSG.CGT.PushingUpLit.SYMB.FiveCount

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7

section Mult

variable {H : Type*} [Group H] [Finite H]

@[expose] noncomputable def multB (x : H) : ℕ :=
  {A : Subgroup H | IsMaxElemAbelian (⊤ : Subgroup H) A ∧ x ∈ A}.ncard

theorem multB_le (σ : H ≃* H) (x : H) : multB (σ x) ≤ multB x := by
  refine Set.ncard_le_ncard_of_injOn (fun A => A.map σ.symm.toMonoidHom) ?_ ?_ (Set.toFinite _)
  · rintro A ⟨hA, hx⟩
    refine ⟨?_, ?_⟩
    · have := (isMaxElemAbelian_map_mulEquiv σ.symm (H := ⊤) (A := A)).2 hA
      rwa [C1GN.map_top_mulEquiv] at this
    · rw [Subgroup.mem_map_equiv]
      simpa using hx
  · intro A₁ _ A₂ _ h
    exact Subgroup.map_injective σ.symm.injective h

theorem multB_equiv (σ : H ≃* H) (x : H) : multB (σ x) = multB x := by
  refine le_antisymm (multB_le σ x) ?_
  have := multB_le σ.symm (σ x)
  simpa using this

@[expose] def multSub (H : Type*) [Group H] [Finite H] (θ : ℕ) : Subgroup H :=
  Subgroup.closure {x : H | θ ≤ multB x}

theorem multSub_characteristic (θ : ℕ) : (multSub H θ).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr fun σ => ?_
  rw [multSub, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.subset_closure ?_
  show θ ≤ multB (σ x)
  rw [multB_equiv]
  exact hx

end Mult

section Bridge

variable {Γ : Type} [Group Γ] [Finite Γ] {T : Subgroup Γ}

omit [Finite Γ] in
theorem le_baum_of_member {A : Subgroup Γ} (hA : IsMaxElemAbelian T A) : A ≤ baum T :=
  (B6.le_thompsonJ hA).trans (B6.thompsonJ_le_baum T)

omit [Finite Γ] in
theorem isMax_baum_of_isMax {A : Subgroup Γ} (hA : IsMaxElemAbelian T A) :
    IsMaxElemAbelian (baum T) A :=
  ⟨le_baum_of_member hA, hA.2.1, fun B' hB' hB'e => hA.2.2 B' (hB'.trans inf_le_left) hB'e⟩

theorem isMax_of_isMax_baum {A : Subgroup Γ} (hA : IsMaxElemAbelian (baum T) A) :
    IsMaxElemAbelian T A := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
  have hA₀B : A₀ ≤ baum T := le_baum_of_member hA₀
  have h1 : Nat.card ↥A₀ ≤ Nat.card ↥A := hA.2.2 A₀ hA₀B hA₀.2.1
  have hAT : A ≤ T := hA.1.trans inf_le_left
  exact isMaxElemAbelian_of_card_eq hA₀ hAT hA.2.1 (le_antisymm (hA₀.2.2 A hAT hA.2.1) h1)

theorem multB_eq_ncard {x : Γ} (hx : x ∈ baum T) :
    multB (⟨x, hx⟩ : ↥(baum T)) = (memSet T x).ncard := by
  unfold multB
  refine Set.ncard_congr (fun A' _ => A'.map (baum T).subtype) ?_ ?_ ?_
  · rintro A' ⟨hA', hxA'⟩
    exact ⟨isMax_of_isMax_baum (isMaxElemAbelian_top_iff.1 hA'), ⟨⟨x, hx⟩, hxA', rfl⟩⟩
  · intro A₁ A₂ _ _ h
    exact Subgroup.map_injective (baum T).subtype_injective h
  · rintro A ⟨hA, hxA⟩
    have hAB := le_baum_of_member hA
    refine ⟨A.subgroupOf (baum T), ⟨?_, ?_⟩, Subgroup.map_subgroupOf_eq_of_le hAB⟩
    · rw [isMaxElemAbelian_top_iff, Subgroup.map_subgroupOf_eq_of_le hAB]
      exact isMax_baum_of_isMax hA
    · exact Subgroup.mem_subgroupOf.2 hxA

end Bridge

end CFSG.CGT.PushingUpLit.SYMB
