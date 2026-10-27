module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G]

theorem c13K_charIn_iff {A B : Subgroup G} :
    CharIn A B ↔ A ≤ B ∧ ∀ φ : MulAut ↥B, ∀ a : ↥B, (a : G) ∈ A → ((φ a : ↥B) : G) ∈ A := by
  unfold CharIn
  refine and_congr_right fun hAB => ?_
  rw [Subgroup.characteristic_iff_map_le]
  constructor
  · intro h φ a ha
    have h1 : φ a ∈ (A.subgroupOf B).map φ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (h φ h1)
  · intro h φ x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_subgroupOf.mpr (h φ a (Subgroup.mem_subgroupOf.mp ha))

theorem c13K_charIn_trans {A B C : Subgroup G} (hAB : CharIn A B) (hBC : CharIn B C) :
    CharIn A C := by
  obtain ⟨hAB1, hAB2⟩ := (c13K_charIn_iff).mp hAB
  obtain ⟨hBC1, hBC2⟩ := (c13K_charIn_iff).mp hBC
  refine (c13K_charIn_iff).mpr ⟨hAB1.trans hBC1, fun φ a ha => ?_⟩
  have haB : (a : G) ∈ B := hAB1 ha
  have hpres : ∀ ψ : MulAut ↥C, ∀ b : ↥B, ((ψ ⟨(b : G), hBC1 b.2⟩ : ↥C) : G) ∈ B :=
    fun ψ b => hBC2 ψ ⟨(b : G), hBC1 b.2⟩ b.2
  let ψ : MulAut ↥B :=
    { toFun := fun b => ⟨((φ ⟨(b : G), hBC1 b.2⟩ : ↥C) : G), hpres φ b⟩
      invFun := fun b => ⟨((φ.symm ⟨(b : G), hBC1 b.2⟩ : ↥C) : G), hpres φ.symm b⟩
      left_inv := fun b => by
        apply Subtype.ext
        simp
      right_inv := fun b => by
        apply Subtype.ext
        simp
      map_mul' := fun b₁ b₂ => by
        apply Subtype.ext
        have h : (⟨((b₁ * b₂ : ↥B) : G), hBC1 (b₁ * b₂).2⟩ : ↥C) =
            ⟨(b₁ : G), hBC1 b₁.2⟩ * ⟨(b₂ : G), hBC1 b₂.2⟩ := rfl
        change ((φ ⟨((b₁ * b₂ : ↥B) : G), hBC1 (b₁ * b₂).2⟩ : ↥C) : G) = _
        rw [h, map_mul]
        rfl }
  have := hAB2 ψ ⟨(a : G), haB⟩ ha
  exact this

theorem c13K_charIn_commutator (U : Subgroup G) : CharIn (⁅U, U⁆ : Subgroup G) U := by
  refine ⟨Subgroup.commutator_le_of_le le_rfl le_rfl, ?_⟩
  have hTop : (⊤ : Subgroup ↥U).map U.subtype = U := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have heq : (⁅U, U⁆ : Subgroup G) =
      Subgroup.map U.subtype ⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆ := by
    rw [Subgroup.map_commutator, hTop]
  rw [heq]
  have : (Subgroup.map U.subtype ⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆).subgroupOf U =
      ⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆ :=
    Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  rw [this]
  infer_instance

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
