module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.GolayBasic
public import CFSG.Blueprint.NativeSporadic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Wong77.Module

open CFSG.Blueprint

@[expose] def permLin (g : Equiv.Perm (Fin 23)) : Word ≃ₗ[ZMod 2] Word :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) g⁻¹

@[simp] theorem permLin_apply (g : Equiv.Perm (Fin 23)) (v : Word) (i : Fin 23) :
    permLin g v i = v (g⁻¹ i) := rfl

@[simp] theorem permLin_one (v : Word) : permLin 1 v = v := rfl

theorem permLin_mul (g h : Equiv.Perm (Fin 23)) (v : Word) :
    permLin (g * h) v = permLin g (permLin h v) := rfl

theorem permLin_inv_permLin (g : Equiv.Perm (Fin 23)) (v : Word) :
    permLin g⁻¹ (permLin g v) = v := by
  ext i
  simp

theorem permLin_permLin_inv (g : Equiv.Perm (Fin 23)) (v : Word) :
    permLin g (permLin g⁻¹ v) = v := by
  ext i
  simp

theorem permLin_symm (g : Equiv.Perm (Fin 23)) : (permLin g).symm = permLin g⁻¹ := rfl

theorem permLin_single (g : Equiv.Perm (Fin 23)) (i : Fin 23) :
    permLin g (Pi.single i 1) = Pi.single (g i) 1 := by
  ext j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

theorem coordSum_permLin (g : Equiv.Perm (Fin 23)) (v : Word) :
    coordSum (permLin g v) = coordSum v := by
  simp only [coordSum_apply, permLin_apply]
  exact Equiv.sum_comp g⁻¹ v

@[expose] def permLinHom : Equiv.Perm (Fin 23) →* (Word ≃ₗ[ZMod 2] Word) where
  toFun := permLin
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' g h := LinearEquiv.ext fun v => permLin_mul g h v

@[expose] def permStab (C : Submodule (ZMod 2) Word) : Subgroup (Equiv.Perm (Fin 23)) where
  carrier := {g | ∀ v, permLin g v ∈ C ↔ v ∈ C}
  mul_mem' := by
    intro g h hg hh v
    rw [permLin_mul, hg, hh]
  one_mem' := fun v => Iff.rfl
  inv_mem' := by
    intro g hg v
    rw [← hg (permLin g⁻¹ v), permLin_permLin_inv]

theorem map_permLin_eq {C : Submodule (ZMod 2) Word} {g : Equiv.Perm (Fin 23)}
    (hg : g ∈ permStab C) : C.map (permLin g : Word →ₗ[ZMod 2] Word) = C := by
  ext x
  rw [Submodule.mem_map_equiv, permLin_symm]
  exact (permStab C).inv_mem hg x

@[expose] def genA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

@[expose] def genB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem M23_eq_closure : NativeSporadic.M23 = Subgroup.closure {genA, genB} := rfl

@[expose] def tabA : Fin 23 → Fin 23 :=
  ![1, 0, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 15, 14, 16, 17, 19, 18, 21, 20, 22]

@[expose] def tabB : Fin 23 → Fin 23 :=
  ![15, 8, 0, 4, 7, 21, 6, 22, 20, 9, 2, 1, 19, 17, 16, 10, 14, 5, 18, 12, 11, 13, 3]

@[expose] def tabB' : Fin 23 → Fin 23 :=
  ![2, 11, 10, 22, 3, 17, 6, 4, 1, 9, 15, 20, 19, 21, 16, 0, 14, 13, 18, 12, 8, 5, 7]

theorem genA_apply : ∀ i, genA i = tabA i := by decide

theorem genA_inv_apply : ∀ i, genA⁻¹ i = tabA i := by decide

theorem genB_apply : ∀ i, genB i = tabB i := by decide

theorem genB_inv_apply : ∀ i, genB⁻¹ i = tabB' i := by decide

private theorem tabA_check : ∀ k i, golayRow k (tabA i) =
    ∑ j, golayRow k (tabA (golayPivot j)) * golayRow j i := by
  decide

private theorem tabB_check : ∀ k i, golayRow k (tabB i) =
    ∑ j, golayRow k (tabB (golayPivot j)) * golayRow j i := by
  decide

private theorem tabB'_check : ∀ k i, golayRow k (tabB' i) =
    ∑ j, golayRow k (tabB' (golayPivot j)) * golayRow j i := by
  decide

theorem mem_permStab_golayCode (g : Equiv.Perm (Fin 23))
    (h : ∀ k, permLin g (golayRow k) ∈ golayCode)
    (h' : ∀ k, permLin g⁻¹ (golayRow k) ∈ golayCode) : g ∈ permStab golayCode := by
  have key : ∀ f : Word ≃ₗ[ZMod 2] Word, (∀ k, f (golayRow k) ∈ golayCode) →
      ∀ v ∈ golayCode, f v ∈ golayCode := by
    intro f hf v hv
    have : golayCode ≤ golayCode.comap (f : Word →ₗ[ZMod 2] Word) :=
      Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hf k)
    exact this hv
  intro v
  constructor
  · intro hv
    have := key (permLin g⁻¹) h' _ hv
    rwa [permLin_inv_permLin] at this
  · exact key (permLin g) h v

private theorem permLin_row_mem (g : Equiv.Perm (Fin 23)) (t : Fin 23 → Fin 23)
    (ht : ∀ i, g⁻¹ i = t i)
    (h : ∀ k i, golayRow k (t i) = ∑ j, golayRow k (t (golayPivot j)) * golayRow j i)
    (k : Fin 12) : permLin g (golayRow k) ∈ golayCode := by
  rw [mem_golayCode_iff]
  intro i
  simp only [permLin_apply, ht]
  exact h k i

private theorem genA_mem_permStab : genA ∈ permStab golayCode :=
  mem_permStab_golayCode genA (permLin_row_mem genA tabA genA_inv_apply tabA_check)
    (permLin_row_mem genA⁻¹ tabA (by simpa using genA_apply) tabA_check)

private theorem genB_mem_permStab : genB ∈ permStab golayCode :=
  mem_permStab_golayCode genB (permLin_row_mem genB tabB' genB_inv_apply tabB'_check)
    (permLin_row_mem genB⁻¹ tabB (by simpa using genB_apply) tabB_check)

theorem M23_le_permStab_golayCode : NativeSporadic.M23 ≤ permStab golayCode := by
  rw [M23_eq_closure, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact genA_mem_permStab
  · exact genB_mem_permStab

theorem permLin_mem_golayCode_iff {g : Equiv.Perm (Fin 23)} (hg : g ∈ NativeSporadic.M23)
    (v : Word) : permLin g v ∈ golayCode ↔ v ∈ golayCode :=
  M23_le_permStab_golayCode hg v

theorem permLin_mem_golayEven_iff {g : Equiv.Perm (Fin 23)} (hg : g ∈ NativeSporadic.M23)
    (v : Word) : permLin g v ∈ golayEven ↔ v ∈ golayEven := by
  rw [mem_golayEven_iff, mem_golayEven_iff, permLin_mem_golayCode_iff hg,
    ← coordSum_apply, ← coordSum_apply, coordSum_permLin]

theorem golayEven_mem_permStab {g : Equiv.Perm (Fin 23)} (hg : g ∈ NativeSporadic.M23) :
    g ∈ permStab golayEven := fun v => permLin_mem_golayEven_iff hg v

theorem golayCode_mem_permStab {g : Equiv.Perm (Fin 23)} (hg : g ∈ NativeSporadic.M23) :
    g ∈ permStab golayCode := M23_le_permStab_golayCode hg

@[expose] def toPermHom : NativeSporadic.Carrier .M23 →* Equiv.Perm (Fin 23) :=
  NativeSporadic.M23.subtype

@[expose] def toPerm (g : NativeSporadic.Carrier .M23) : Equiv.Perm (Fin 23) := toPermHom g

theorem toPerm_mem (g : NativeSporadic.Carrier .M23) : toPerm g ∈ NativeSporadic.M23 :=
  (show NativeSporadic.M23 from g).2

theorem toPerm_injective : Function.Injective toPerm := fun _ _ h => Subtype.ext h

@[expose] def wordRep : NativeSporadic.Carrier .M23 →* (Word ≃ₗ[ZMod 2] Word) :=
  permLinHom.comp toPermHom

theorem wordRep_apply (g : NativeSporadic.Carrier .M23) (v : Word) (i : Fin 23) :
    wordRep g v i = v ((toPerm g)⁻¹ i) := rfl

theorem wordRep_single (g : NativeSporadic.Carrier .M23) (i : Fin 23) :
    wordRep g (Pi.single i 1) = Pi.single (toPerm g i) 1 :=
  permLin_single (toPerm g) i

end CFSG.EvenSporadicStandard.Wong77.Module
