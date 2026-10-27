module

public import CFSG.Quasithin.Background.G2UAdjoint
public import CFSG.Blueprint.ChevalleyWeyl
public import Certificates.Certificate27212

public section

namespace CFSG.EvenSporadicStandard.G24Model

open CFSG.Fischer CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

noncomputable abbrev e₀ : ModGL .G2 F4 ≃* GL (Fin 14) F4 := glEquiv (RingEquiv.refl F4)

@[expose] noncomputable def Cmat : Subgroup (GL (Fin 14) F4) :=
  (adjointGroup .G2 F4).map e₀.toMonoidHom

@[expose] def genSet : Set (GL (Fin 14) F4) :=
  {u | ∃ j : Fin 16, (u : Matrix (Fin 14) (Fin 14) F4) = Gmat j}

theorem coe_e₀_xUnit
    (i : Fin Tag.G2.rank) (c : F4) :
    ((e₀ (xUnit .G2 F4 i c) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) = XMat F4 i c := by
  rw [coe_glEquiv]
  exact endEquiv_xOp (RingEquiv.refl F4) i c

theorem coe_e₀_yUnit
    (i : Fin Tag.G2.rank) (c : F4) :
    ((e₀ (yUnit .G2 F4 i c) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) = YMat F4 i c := by
  rw [coe_glEquiv]
  exact endEquiv_yOp (RingEquiv.refl F4) i c

theorem genOK_parts :
    (∀ (i : Fin 2) (c : F4), XMat F4 i c = Gmat (xIdx i c)) ∧
      ∀ (i : Fin 2) (c : F4), YMat F4 i c = Gmat (yIdx i c) := by
  have h := of_decide_eq_true Certificates.certificate27212
  exact ⟨fun i c => Matrix.ext fun a b => h.1 i c a b,
    fun i c => Matrix.ext fun a b => h.2 i c a b⟩

theorem coe_e₀_xUnit_eq
    (i : Fin 2) (c : F4) :
    ((e₀ (xUnit .G2 F4 i c) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) =
      Gmat (xIdx i c) :=
  (coe_e₀_xUnit i c).trans (genOK_parts.1 i c)

theorem coe_e₀_yUnit_eq
    (i : Fin 2) (c : F4) :
    ((e₀ (yUnit .G2 F4 i c) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) =
      Gmat (yIdx i c) :=
  (coe_e₀_yUnit i c).trans (genOK_parts.2 i c)

theorem exists_idx (j : Fin 16) : ∃ (i : Fin 2) (c : F4), j = xIdx i c ∨ j = yIdx i c := by
  revert j
  decide

theorem exists_gen_unit
    (j : Fin 16) :
    ∃ u ∈ Cmat, (u : Matrix (Fin 14) (Fin 14) F4) = Gmat j := by
  obtain ⟨i, c, hj | hj⟩ := exists_idx j
  · exact ⟨e₀ (xUnit .G2 F4 i c), ⟨_, xUnit_mem_adjointGroup (τ := .G2) i c, rfl⟩,
      hj ▸ coe_e₀_xUnit_eq i c⟩
  · exact ⟨e₀ (yUnit .G2 F4 i c), ⟨_, yUnit_mem_adjointGroup (τ := .G2) i c, rfl⟩,
      hj ▸ coe_e₀_yUnit_eq i c⟩

theorem Cmat_le_closure :
    Cmat ≤ Subgroup.closure genSet := by
  rw [Cmat, adjointGroup, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, ⟨i, c, hg | hg⟩, rfl⟩
  · have : g = xUnit .G2 F4 i c := Units.ext hg
    exact ⟨xIdx i c, this ▸ coe_e₀_xUnit_eq i c⟩
  · have : g = yUnit .G2 F4 i c := Units.ext hg
    exact ⟨yIdx i c, this ▸ coe_e₀_yUnit_eq i c⟩

end CFSG.EvenSporadicStandard.G24Model
