module

public import CFSG.CharacterTheory.Wreathed.DegreeThreeModelFullCenterScalars
public import CFSG.CharacterTheory.Wreathed.OddLinearTwoAutomorphisms

public noncomputable section

namespace CFSG.Wreathed.DegreeThreeModelFullCenter

open Matrix
open CFSG.Semidihedral.OddLinearNormals

universe u v w

@[expose] def reducedTargetHom
    {B : Type u} {C : Type v} [Group B] [Group C] (phi : B →* C) :
    B →* C ⧸ CFSG.oddCore C := (QuotientGroup.mk' (CFSG.oddCore C)).comp phi

theorem reducedTargetHom_ker
    {B : Type u} {C : Type v} [Group B] [Group C] (phi : B →* C) :
    (reducedTargetHom phi).ker = (CFSG.oddCore C).comap phi := by
  rw [reducedTargetHom, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

theorem reducedTargetHom_surjective
    {B : Type u} {C : Type v} [Group B] [Group C] (phi : B →* C)
    (hphi : Function.Surjective phi) : Function.Surjective (reducedTargetHom phi) :=
  (QuotientGroup.mk'_surjective _).comp hphi

theorem reducedTargetHom_ker_eq
    {B : Type u} {C : Type v} [Group B] [Group C] (phi : B →* C)
    (U : Subgroup B) (hU : phi.ker ≤ U) (hcore : CFSG.oddCore C = U.map phi) :
    (reducedTargetHom phi).ker = U := by
  rw [reducedTargetHom_ker, hcore, Subgroup.comap_map_eq_self hU]

section MatrixReducedTarget

variable {F : Type u} {E : Type v} [Field F] [Field E]

theorem reducedTargetHom_full_center_comap [Finite F] (hF : 4 ≤ Nat.card F)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    {C : Type w} [Group C] (phi : B →* C) (hphi : Function.Surjective phi)
    (hker : phi.ker ≤ oddScalarSubgroup B)
    (hcore : CFSG.oddCore C = (oddScalarSubgroup B).map phi) :
    (Subgroup.center (C ⧸ CFSG.oddCore C)).comap (reducedTargetHom phi) =
      scalarSubgroup B := by
  exact matrix_overgroup_center_comap hF i b B hSB (reducedTargetHom phi)
    (reducedTargetHom_surjective phi hphi) (by
      rw [reducedTargetHom_ker_eq phi _ hker hcore]
      exact oddScalarSubgroup_le_scalars B)

@[expose] def reducedTargetFullCenterEquiv [Finite F] (hF : 4 ≤ Nat.card F)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    {C : Type w} [Group C] (phi : B →* C) (hphi : Function.Surjective phi)
    (hker : phi.ker ≤ oddScalarSubgroup B)
    (hcore : CFSG.oddCore C = (oddScalarSubgroup B).map phi) :
    B ⧸ scalarSubgroup B ≃*
      (C ⧸ CFSG.oddCore C) ⧸ Subgroup.center (C ⧸ CFSG.oddCore C) :=
  fullCenterQuotientEquiv (reducedTargetHom phi) (reducedTargetHom_surjective phi hphi)
    (scalarSubgroup B) (reducedTargetHom_full_center_comap hF i b B hSB phi hphi hker hcore)

theorem reducedTargetFullCenterEquiv_mk [Finite F] (hF : 4 ≤ Nat.card F)
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    {C : Type w} [Group C] (phi : B →* C) (hphi : Function.Surjective phi)
    (hker : phi.ker ≤ oddScalarSubgroup B)
    (hcore : CFSG.oddCore C = (oddScalarSubgroup B).map phi) (g : B) :
    reducedTargetFullCenterEquiv hF i b B hSB phi hphi hker hcore
      (QuotientGroup.mk' (scalarSubgroup B) g) =
        QuotientGroup.mk' (Subgroup.center (C ⧸ CFSG.oddCore C))
          (QuotientGroup.mk' (CFSG.oddCore C) (phi g)) := by
  unfold reducedTargetFullCenterEquiv
  exact fullCenterQuotientEquiv_mk _ _ _ _ g

theorem reducedTargetHom_full_center_comap_of_two_power
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    [Finite (scalarSubgroup B)] (k : ℕ) (hZ : Nat.card (scalarSubgroup B) = 2 ^ k)
    {C : Type w} [Group C] (phi : B →* C) (hphi : Function.Surjective phi)
    (hker : phi.ker ≤ oddScalarSubgroup B)
    (hcore : CFSG.oddCore C = (oddScalarSubgroup B).map phi) :
    (Subgroup.center (C ⧸ CFSG.oddCore C)).comap (reducedTargetHom phi) =
      scalarSubgroup B := by
  exact matrix_overgroup_center_comap_of_ker_bot i b B hSB (reducedTargetHom phi)
    (reducedTargetHom_surjective phi hphi) (by
      rw [reducedTargetHom_ker_eq phi _ hker hcore, oddScalarSubgroup_eq_bot_of_two_power B k hZ])

@[expose] def reducedTargetFullCenterEquivOfTwoPower
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    [Finite (scalarSubgroup B)] (k : ℕ) (hZ : Nat.card (scalarSubgroup B) = 2 ^ k)
    {C : Type w} [Group C] (phi : B →* C) (hphi : Function.Surjective phi)
    (hker : phi.ker ≤ oddScalarSubgroup B)
    (hcore : CFSG.oddCore C = (oddScalarSubgroup B).map phi) :
    B ⧸ scalarSubgroup B ≃*
      (C ⧸ CFSG.oddCore C) ⧸ Subgroup.center (C ⧸ CFSG.oddCore C) :=
  fullCenterQuotientEquiv (reducedTargetHom phi) (reducedTargetHom_surjective phi hphi)
    (scalarSubgroup B)
    (reducedTargetHom_full_center_comap_of_two_power i b B hSB k hZ phi hphi hker hcore)

theorem reducedTargetFullCenterEquivOfTwoPower_mk
    (i : F →+* E) (b : GeneralLinearGroup (Fin 2) E)
    (B : Subgroup (GeneralLinearGroup (Fin 2) E)) (hSB : conjugatedImageSL i b ≤ B)
    [Finite (scalarSubgroup B)] (k : ℕ) (hZ : Nat.card (scalarSubgroup B) = 2 ^ k)
    {C : Type w} [Group C] (phi : B →* C) (hphi : Function.Surjective phi)
    (hker : phi.ker ≤ oddScalarSubgroup B)
    (hcore : CFSG.oddCore C = (oddScalarSubgroup B).map phi) (g : B) :
    reducedTargetFullCenterEquivOfTwoPower i b B hSB k hZ phi hphi hker hcore
      (QuotientGroup.mk' (scalarSubgroup B) g) =
        QuotientGroup.mk' (Subgroup.center (C ⧸ CFSG.oddCore C))
          (QuotientGroup.mk' (CFSG.oddCore C) (phi g)) := by
  unfold reducedTargetFullCenterEquivOfTwoPower
  exact fullCenterQuotientEquiv_mk _ _ _ _ g

end MatrixReducedTarget

section MatrixScalarCompatibility

variable {E : Type v} [Field E]

theorem mem_oddScalarSubgroup_iff
    {B : Subgroup (GeneralLinearGroup (Fin 2) E)} {g : B} :
    g ∈ oddScalarSubgroup B ↔ g ∈ scalarSubgroup B ∧ Odd (orderOf g) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, ?_⟩
    change Odd (orderOf a) at ha
    change Odd (orderOf (a : B))
    exact (orderOf_injective (scalarSubgroup B).subtype Subtype.val_injective a).symm ▸ ha
  · rintro ⟨hg, ho⟩
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩, ?_, rfl⟩
    change Odd (orderOf (⟨g, hg⟩ : scalarSubgroup B))
    rw [← orderOf_injective (scalarSubgroup B).subtype Subtype.val_injective]
    exact ho

theorem oddScalarSubgroup_eq_map
    (B : Subgroup (GeneralLinearGroup (Fin 2) E))
    {A : Type*} [Group A] [IsMulCommutative A] (kappa : A →* B)
    (hkappa : Function.Injective kappa) (hZ : kappa.range = scalarSubgroup B) :
    oddScalarSubgroup B = (CyclicOddScalarQuotient.oddElements A).map kappa := by
  ext g
  rw [mem_oddScalarSubgroup_iff]
  constructor
  · rintro ⟨hg, ho⟩
    rw [← hZ] at hg
    obtain ⟨a, rfl⟩ := hg
    refine Subgroup.mem_map.mpr ⟨a, ?_, rfl⟩
    simpa only [CyclicOddScalarQuotient.mem_oddElements,
      orderOf_injective kappa hkappa] using ho
  · rintro ⟨a, ha, rfl⟩
    refine ⟨hZ ▸ (show kappa a ∈ kappa.range from ⟨a, rfl⟩), ?_⟩
    change Odd (orderOf a) at ha
    simpa only [orderOf_injective kappa hkappa] using ha

end MatrixScalarCompatibility

@[expose] def linearMatrixScalarHom (F : Type u) [Field F] :
    Fˣ →* (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)) :=
  (GeneralLinearGroup.scalar (Fin 2)).codRestrict ⊤ (fun _ => Subgroup.mem_top _)

theorem linearMatrixScalarHom_coe (F : Type u) [Field F] (a : Fˣ) :
    (linearMatrixScalarHom F a : GeneralLinearGroup (Fin 2) F) =
      GeneralLinearGroup.scalar (Fin 2) a := rfl

theorem linearMatrixScalarHom_injective (F : Type u) [Field F] :
    Function.Injective (linearMatrixScalarHom F) := by
  intro a b hab
  apply Units.ext
  have heq := congrArg
    (fun g : (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)) =>
      (g.val.val : Matrix (Fin 2) (Fin 2) F) 0 0) hab
  simpa only [linearMatrixScalarHom_coe, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq] using heq

theorem linearMatrixScalarHom_range (F : Type u) [Field F] :
    (linearMatrixScalarHom F).range =
      scalarSubgroup (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)) := by
  ext g
  change (∃ a : Fˣ, linearMatrixScalarHom F a = g) ↔
    g.val ∈ Subgroup.center (GeneralLinearGroup (Fin 2) F)
  rw [GeneralLinearGroup.center_eq_range_scalar]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem card_linearMatrixScalars (F : Type u) [Field F] :
    Nat.card (scalarSubgroup (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F))) =
      Nat.card F - 1 := by
  rw [← linearMatrixScalarHom_range,
    ← Nat.card_congr (MonoidHom.ofInjective (linearMatrixScalarHom_injective F)).toEquiv,
    Nat.card_units]

theorem card_linearMatrixGroup (F : Type u) [Field F] [Finite F] :
    Nat.card (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F)) =
      Nat.card F * (Nat.card F ^ 2 - 1) *
        Nat.card (scalarSubgroup (⊤ : Subgroup (GeneralLinearGroup (Fin 2) F))) := by
  rw [Subgroup.card_top, OddLinearTwoAutomorphisms.card_matrix_two,
    card_linearMatrixScalars]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hq2 : 1 ≤ Nat.card F ^ 2 := one_le_pow₀ hq
  zify [hq, hq2]
  ring

end CFSG.Wreathed.DegreeThreeModelFullCenter
