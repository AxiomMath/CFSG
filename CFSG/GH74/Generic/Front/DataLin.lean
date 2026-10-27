module

public import CFSG.GH74.Generic.Front.DataAbs
public import CFSG.GH74.Generic.Front.DataLA
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.GH74.Generic

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.GH74.Filter.ClassicalOdd
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
  CFSG.ClassicalInvolution CFSG.LinearGroups Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem hmat_lin (h2 : (2 : F) ≠ 0) (t : ↥(ModelData.lin F).K4)
    (hT : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1)
    (h1 : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ 1)
    (hm1 : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ≠ -1) :
    ∃ g : GL (Fin 4) F, g ∈ (ModelData.lin F).K4 ∧
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
        (g : Matrix (Fin 4) (Fin 4) F) * Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) := by
  have hdet : ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 :=
    (((ModelData.lin F).mem_K4 _).1 t.2).2
  obtain ⟨P, hPdet, hTP⟩ := exists_conj_diag4_det_one h2 _ hT hdet h1 hm1
  refine ⟨Matrix.GeneralLinearGroup.mk'' P (by rw [hPdet]; exact isUnit_one), ?_, hTP⟩
  exact ((ModelData.lin F).mem_K4 _).2 ⟨Subgroup.mem_top _, hPdet⟩

section OddGen

@[expose] def sl2BlkL : SL(2, F) →* ↥(ModelData.lin F).K4 :=
  ((blkL F).comp SpecialLinearGroup.toGL).codRestrict (ModelData.lin F).K4 (fun s =>
    (ModelData.lin F).blkL_mem_K4 (by
      change _ ∈ StatedSL 2 F
      rw [statedSL_eq_range_toGL]
      exact ⟨s, rfl⟩))

@[expose] def sl2BlkR : SL(2, F) →* ↥(ModelData.lin F).K4 :=
  ((blkR F).comp SpecialLinearGroup.toGL).codRestrict (ModelData.lin F).K4 (fun s =>
    (ModelData.lin F).blkR_mem_K4 (by
      change _ ∈ StatedSL 2 F
      rw [statedSL_eq_range_toGL]
      exact ⟨s, rfl⟩))

theorem orderOf_transvection_dvd {i j : Fin 2} (hij : i ≠ j) (c : F) :
    orderOf (SpecialLinearGroup.transvection hij c) ∣ Nat.card F := by
  have h1 : SpecialLinearGroup.transvection hij c =
      SpecialLinearGroup.transvectionHom (n := Fin 2) (A := F) hij (Multiplicative.ofAdd c) := by
    rw [SpecialLinearGroup.transvectionHom_apply]
    rfl
  rw [h1]
  exact (orderOf_map_dvd _ _).trans (orderOf_dvd_natCard _)

theorem odd_orderOf_map_elementary (hodd : Odd (Nat.card F)) {G : Type*} [Group G]
    (κ : SL(2, F) →* G) {e : SL(2, F)} (he : e ∈ elementarySet 2 F) : Odd (orderOf (κ e)) := by
  obtain ⟨i, j, hij, c, rfl⟩ := he
  exact Odd.of_dvd_nat hodd ((orderOf_map_dvd κ _).trans (orderOf_transvection_dvd hij c))

theorem map_mem_closure_of_elementary {G : Type*} [Group G] (κ : SL(2, F) →* G) (S : Set G)
    (hS : ∀ e ∈ elementarySet 2 F, κ e ∈ S) (s : SL(2, F)) : κ s ∈ Subgroup.closure S := by
  have hs : s ∈ Subgroup.closure (elementarySet 2 F) := by
    rw [special_linear_elementary_generation]
    trivial
  refine (Subgroup.closure_le ((Subgroup.closure S).comap κ)).2 (fun e he => ?_) hs
  exact Subgroup.subset_closure (hS e he)

theorem oddGenerated_lin_J (hodd : Odd (Nat.card F)) :
    OddGenerated ((ModelData.lin F).J2 ⊔ (ModelData.lin F).J4) := by
  set M := ModelData.lin F with hM
  set S : Set ↥M.K4 := {g | g ∈ M.J2 ⊔ M.J4 ∧ Odd (orderOf g)} with hS
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 (fun g hg => hg.1)
  · refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨a, ha, hga⟩ := ModelData.mem_J2.1 hg
      have ha' : a ∈ (SpecialLinearGroup.toGL : SL(2, F) →* GL (Fin 2) F).range := by
        rw [← statedSL_eq_range_toGL]
        exact ha
      obtain ⟨s, rfl⟩ := ha'
      have hgs : g = sl2BlkL s := Subtype.ext hga
      rw [hgs]
      refine map_mem_closure_of_elementary sl2BlkL S (fun e he => ⟨?_, ?_⟩) s
      · refine Subgroup.mem_sup_left (ModelData.mem_J2.2 ⟨SpecialLinearGroup.toGL e, ?_, rfl⟩)
        change _ ∈ StatedSL 2 F
        rw [statedSL_eq_range_toGL]
        exact ⟨e, rfl⟩
      · exact odd_orderOf_map_elementary hodd sl2BlkL he
    · intro g hg
      obtain ⟨a, ha, hga⟩ := ModelData.mem_J4.1 hg
      have ha' : a ∈ (SpecialLinearGroup.toGL : SL(2, F) →* GL (Fin 2) F).range := by
        rw [← statedSL_eq_range_toGL]
        exact ha
      obtain ⟨s, rfl⟩ := ha'
      have hgs : g = sl2BlkR s := Subtype.ext hga
      rw [hgs]
      refine map_mem_closure_of_elementary sl2BlkR S (fun e he => ⟨?_, ?_⟩) s
      · refine Subgroup.mem_sup_right (ModelData.mem_J4.2 ⟨SpecialLinearGroup.toGL e, ?_, rfl⟩)
        change _ ∈ StatedSL 2 F
        rw [statedSL_eq_range_toGL]
        exact ⟨e, rfl⟩
      · exact odd_orderOf_map_elementary hodd sl2BlkR he

end OddGen

theorem frontData0_statedSL4 {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) :
    Nonempty (FrontData0 ↥(StatedSL 4 F)) := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  obtain ⟨a, b, h⟩ := (odd_field_two_dimensional_quaternion_matrices hF2).1
  let ρ : Q8 →* GL (Fin 2) F :=
    (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).comp (quatHom h)
  have hρ : ∀ g, ρ g ∈ (ModelData.lin F).H2 := fun g => by
    change _ ∈ StatedSL 2 F
    rw [statedSL_eq_detOne, mem_detOne]
    exact (quatHom h g).2
  have hinj : Function.Injective ρ :=
    SpecialLinearGroup.toGL_injective.comp (quatHom_injective hF2 h)
  have hz : ρ (QuaternionGroup.a 2) = -1 := by
    apply Units.ext
    change ((quatHom h (QuaternionGroup.a 2) : Matrix (Fin 2) (Fin 2) F)) = _
    rw [quatHom_a_two h]
    simp
  refine frontData0_of_model (ModelData.lin F) ρ hρ hinj hz
    (hone_of_model _ (mem_center_lin_iff hF) (fun t hT h1 hm1 => hmat_lin h2 t hT h1 hm1)) ?_
  by_cases h4 : 4 ≤ Nat.card F
  · exact goodSub_J2_sup_J4 (ModelData.lin F) _ h4 (lin_sl2_equiv_H2 F)
  · have h3 : Nat.card F = 3 := by omega
    exact Or.inr ⟨oddGenerated_lin_J hodd, ⟨F, inferInstance, inferInstance, h3,
      Or.inl ⟨MulEquiv.refl _⟩⟩⟩

end CFSG.GH74.Generic
