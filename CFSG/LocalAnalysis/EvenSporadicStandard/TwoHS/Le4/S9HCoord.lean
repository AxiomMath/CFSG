module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Coord

public section

namespace CFSG.EvenSporadicStandard.TwoHS

variable {G : Type*} [Group G]

@[expose] def basisElt (b : Fin 4 → G) (v : V4) : G :=
  b 0 ^ (v 0).val * b 1 ^ (v 1).val * b 2 ^ (v 2).val * b 3 ^ (v 3).val

theorem basisElt_zero {b : Fin 4 → G} : basisElt b 0 = 1 := by
  simp [basisElt]

theorem basisElt_add {b : Fin 4 → G} (hcomm : ∀ i j, b i * b j = b j * b i)
    (h4 : ∀ i, b i ^ 4 = 1) (v w : V4) :
    basisElt b (v + w) = basisElt b v * basisElt b w := by
  have key : ∀ (i : Fin 4) (x y : ZMod 4), b i ^ (x + y).val = b i ^ x.val * b i ^ y.val := by
    intro i x y
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (h4 i), pow_add]
  have hc : ∀ (i j : Fin 4) (m n : ℕ), Commute (b i ^ m) (b j ^ n) := fun i j m n =>
    (show Commute (b i) (b j) from hcomm i j).pow_pow m n
  simp only [basisElt, Pi.add_apply, key]
  simp only [mul_assoc]
  rw [(hc 3 0 _ _).left_comm, (hc 2 0 _ _).left_comm, (hc 1 0 _ _).left_comm,
    (hc 3 1 _ _).left_comm, (hc 2 1 _ _).left_comm, (hc 3 2 _ _).left_comm]

theorem basisElt_single (b : Fin 4 → G) (i : Fin 4) : basisElt b (Pi.single i 1) = b i := by
  have h1 : (1 : ZMod 4).val = 1 := rfl
  fin_cases i <;> simp [basisElt, h1]

theorem basisElt_mem_closure (b : Fin 4 → G) (v : V4) :
    basisElt b v ∈ Subgroup.closure (Set.range b) := by
  have h : ∀ (i : Fin 4) (n : ℕ), b i ^ n ∈ Subgroup.closure (Set.range b) := fun i n =>
    Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) n
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (h 0 _) (h 1 _)) (h 2 _))
    (h 3 _)

@[expose] def basisHom (b : Fin 4 → G) (hcomm : ∀ i j, b i * b j = b j * b i)
    (h4 : ∀ i, b i ^ 4 = 1) : Multiplicative V4 →* G where
  toFun v := basisElt b (Multiplicative.toAdd v)
  map_one' := basisElt_zero
  map_mul' _ _ := basisElt_add hcomm h4 _ _

theorem basisHom_injective {b : Fin 4 → G} (hcomm : ∀ i j, b i * b j = b j * b i)
    (h4 : ∀ i, b i ^ 4 = 1) (hinj : ∀ v : V4, basisElt b v = 1 → v = 0) :
    Function.Injective (basisHom b hcomm h4) :=
  (injective_iff_map_eq_one _).2 fun _ hv => toAdd_eq_zero.1 (hinj _ hv)

@[expose] noncomputable def ECoord.ofBasis (b : Fin 4 → G) (hcomm : ∀ i j, b i * b j = b j * b i)
    (h4 : ∀ i, b i ^ 4 = 1) (hinj : ∀ v : V4, basisElt b v = 1 → v = 0) : ECoord G where
  E := (basisHom b hcomm h4).range
  φ := (MonoidHom.ofInjective (basisHom_injective hcomm h4 hinj)).symm

theorem ECoord.ofBasis_elt (b : Fin 4 → G) (hcomm : ∀ i j, b i * b j = b j * b i)
    (h4 : ∀ i, b i ^ 4 = 1) (hinj : ∀ v : V4, basisElt b v = 1 → v = 0) (v : V4) :
    (ECoord.ofBasis b hcomm h4 hinj).elt v = basisElt b v := rfl

theorem ECoord.ofBasis_mem (b : Fin 4 → G) (hcomm : ∀ i j, b i * b j = b j * b i)
    (h4 : ∀ i, b i ^ 4 = 1) (hinj : ∀ v : V4, basisElt b v = 1 → v = 0) (i : Fin 4) :
    b i ∈ (ECoord.ofBasis b hcomm h4 hinj).E := by
  have := (ECoord.ofBasis b hcomm h4 hinj).elt_mem (Pi.single i 1)
  rwa [ECoord.ofBasis_elt, basisElt_single] at this

theorem ECoord.ofBasis_vec (b : Fin 4 → G) (hcomm : ∀ i j, b i * b j = b j * b i)
    (h4 : ∀ i, b i ^ 4 = 1) (hinj : ∀ v : V4, basisElt b v = 1 → v = 0) (i : Fin 4) :
    (ECoord.ofBasis b hcomm h4 hinj).vec (b i) = Pi.single i 1 := by
  have h : b i = (ECoord.ofBasis b hcomm h4 hinj).elt (Pi.single i 1) := by
    rw [ECoord.ofBasis_elt, basisElt_single]
  rw [h, (ECoord.ofBasis b hcomm h4 hinj).vec_elt]

theorem ECoord.ofBasis_E (b : Fin 4 → G) (hcomm : ∀ i j, b i * b j = b j * b i)
    (h4 : ∀ i, b i ^ 4 = 1) (hinj : ∀ v : V4, basisElt b v = 1 → v = 0) :
    (ECoord.ofBasis b hcomm h4 hinj).E = Subgroup.closure (Set.range b) := by
  refine le_antisymm (fun x hx => ?_) ((Subgroup.closure_le _).2 ?_)
  · rw [← (ECoord.ofBasis b hcomm h4 hinj).elt_vec hx, ECoord.ofBasis_elt]
    exact basisElt_mem_closure b _
  · rintro _ ⟨i, rfl⟩
    exact ECoord.ofBasis_mem b hcomm h4 hinj i

end CFSG.EvenSporadicStandard.TwoHS
