module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsModels

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

open Module Matrix CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3 traceZero)

@[expose] def proj (i : Fin 4) : Module.End (ZMod 2) V where
  toFun x := (if i = 0 then x.1 else 0, if i = 1 then x.2.1 else 0, if i = 2 then x.2.2.1 else 0,
    if i = 3 then x.2.2.2 else 0)
  map_add' x y := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> dsimp only <;> split_ifs <;> simp
  map_smul' c x := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> dsimp only <;> split_ifs <;> simp

theorem repK_tmul (k : K) (x y : V) : repK k (x ⊗ₜ y) = rho k.1 x ⊗ₜ rho k.2 y :=
  rfl

theorem repK_mem_block (k : K) (ij : Fin 4 × Fin 4) {m : T} (hm : m ∈ block ij.1 ij.2) :
    repK k m ∈ block ij.1 ij.2 :=
  mapsBlocks_repK k ij ⟨m, hm, rfl⟩

@[expose] def blockRepK (ij : Fin 4 × Fin 4) : Representation (ZMod 2) K (block ij.1 ij.2) where
  toFun k := (repK k).restrict fun _ hm => repK_mem_block k ij hm
  map_one' := LinearMap.ext fun m => Subtype.ext (by
    change repK 1 m = m
    rw [map_one, Module.End.one_apply])
  map_mul' k l := LinearMap.ext fun m => Subtype.ext (by
    change repK (k * l) m = repK k (repK l m)
    rw [map_mul, Module.End.mul_apply])

@[expose] def tensorIncl (ij : Fin 4 × Fin 4) :
    TensorProduct (ZMod 2) (labelSub ij.1) (labelSub ij.2) →ₗ[ZMod 2] T :=
  TensorProduct.mapIncl (labelSub ij.1) (labelSub ij.2)

theorem tensorIncl_injective (ij : Fin 4 × Fin 4) : Function.Injective (tensorIncl ij) :=
  TensorProduct.map_injective_of_flat_flat _ _ (Submodule.injective_subtype _)
    (Submodule.injective_subtype _)

theorem range_tensorIncl (ij : Fin 4 × Fin 4) :
    LinearMap.range (tensorIncl ij) = block ij.1 ij.2 := by
  rw [tensorIncl, TensorProduct.range_mapIncl, Submodule.map₂_eq_span_image2]
  rfl

@[expose] def blockEquiv (ij : Fin 4 × Fin 4) :
    (outer (labelRep ij.1) (labelRep ij.2)).Equiv (blockRepK ij) :=
  equivOf ((LinearEquiv.ofInjective _ (tensorIncl_injective ij)).trans
      (LinearEquiv.ofEq _ _ (range_tensorIncl ij))) fun k m => by
    apply Subtype.ext
    change tensorIncl ij (outer (labelRep ij.1) (labelRep ij.2) k m) = repK k (tensorIncl ij m)
    induction m using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add m m' h h' => rw [map_add, map_add, h, h', map_add, map_add]

end CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
