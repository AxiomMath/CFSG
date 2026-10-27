module

public import CFSG.Blueprint.ChevalleyRootGroupsTorus

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem yUnit_add
    {τ : Tag} {R : Type*} [CommRing R] (i : Fin τ.rank) (c d : R) :
    yUnit τ R i (c + d) = yUnit τ R i c * yUnit τ R i d :=
  Units.ext (yOp_mul_yOp (downTransport τ) i c d).symm

theorem yUnit_zero
    {τ : Tag} {R : Type*} [CommRing R] (i : Fin τ.rank) : yUnit τ R i 0 = 1 :=
  Units.ext (yOp_zero i)

theorem xUnit_neg
    {τ : Tag} {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R) :
    xUnit τ R i (-c) = (xUnit τ R i c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← xUnit_add, neg_add_cancel, xUnit_zero])

theorem yUnit_neg
    {τ : Tag} {R : Type*} [CommRing R] (i : Fin τ.rank) (c : R) :
    yUnit τ R i (-c) = (yUnit τ R i c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← yUnit_add, neg_add_cancel, yUnit_zero])

variable (τ : Tag) (K : Type*) [Field K]

@[expose] def simplePosSubgroup
    (i : Fin τ.rank) : Subgroup (adjointGroup τ K) where
  carrier := {g | ∃ c : K, (g : ModGL τ K) = xUnit τ K i c}
  mul_mem' := by
    rintro _ _ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [Subgroup.coe_mul, hc, hd, xUnit_add]⟩
  one_mem' := ⟨0, by rw [xUnit_zero]; rfl⟩
  inv_mem' := by
    rintro _ ⟨c, hc⟩
    exact ⟨-c, by rw [Subgroup.coe_inv, hc, xUnit_neg]⟩

@[expose] def simpleNegSubgroup
    (i : Fin τ.rank) : Subgroup (adjointGroup τ K) where
  carrier := {g | ∃ c : K, (g : ModGL τ K) = yUnit τ K i c}
  mul_mem' := by
    rintro _ _ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [Subgroup.coe_mul, hc, hd, yUnit_add]⟩
  one_mem' := ⟨0, by rw [yUnit_zero]; rfl⟩
  inv_mem' := by
    rintro _ ⟨c, hc⟩
    exact ⟨-c, by rw [Subgroup.coe_inv, hc, yUnit_neg]⟩

variable {τ K}

theorem mem_simplePosSubgroup
    {i : Fin τ.rank} {g : adjointGroup τ K} :
    g ∈ simplePosSubgroup τ K i ↔ ∃ c : K, (g : ModGL τ K) = xUnit τ K i c :=
  Iff.rfl

theorem mem_simpleNegSubgroup
    {i : Fin τ.rank} {g : adjointGroup τ K} :
    g ∈ simpleNegSubgroup τ K i ↔ ∃ c : K, (g : ModGL τ K) = yUnit τ K i c :=
  Iff.rfl

theorem sum_cartan_mul_pi_single (i j : Fin τ.rank) :
    ∑ k, τ.cartan i k * (Pi.single j 1 : Fin τ.rank → ℤ) k = τ.cartan i j := by
  simp [Pi.single_apply]

theorem simple_torus_root_conjugation
    (τ : Tag) (R : Type*) [CommRing R] (i j : Fin τ.rank)
    (t : Rˣ) (c : R) :
    torusElt τ R i t * xUnit τ R j c * (torusElt τ R i t)⁻¹ =
        xUnit τ R j (((t ^ τ.cartan i j : Rˣ) : R) * c) ∧
      torusElt τ R i t * yUnit τ R j c * (torusElt τ R i t)⁻¹ =
        yUnit τ R j (((t ^ (-τ.cartan i j) : Rˣ) : R) * c) := by
  constructor
  · rw [← pinnedX_single, ← pinnedX_single, root_torus_conjugation i (isRoot_single τ j),
      sum_cartan_mul_pi_single]
  · rw [← pinnedX_neg_single, ← pinnedX_neg_single,
      root_torus_conjugation i (isRoot_neg_single τ j)]
    congr 3
    simp [Pi.single_apply]

end CFSG.LieType.Chevalley
