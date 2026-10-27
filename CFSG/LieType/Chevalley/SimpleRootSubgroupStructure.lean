module

public import CFSG.LieType.Chevalley.SimpleRootSubgroups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable (τ : Tag) (K : Type*) [Field K]

@[expose] def simplePosHom
    (i : Fin τ.rank) : Multiplicative K →* simplePosSubgroup τ K i where
  toFun c := ⟨⟨xUnit τ K i c.toAdd, xUnit_mem_adjointGroup i _⟩, c.toAdd, rfl⟩
  map_one' := Subtype.ext (Subtype.ext (xUnit_zero i))
  map_mul' a b := Subtype.ext (Subtype.ext (xUnit_add i a.toAdd b.toAdd))

@[expose] def simpleNegHom
    (i : Fin τ.rank) : Multiplicative K →* simpleNegSubgroup τ K i where
  toFun c := ⟨⟨yUnit τ K i c.toAdd, yUnit_mem_adjointGroup i _⟩, c.toAdd, rfl⟩
  map_one' := Subtype.ext (Subtype.ext (yUnit_zero i))
  map_mul' a b := Subtype.ext (Subtype.ext (yUnit_add i a.toAdd b.toAdd))

variable {τ K}

theorem coe_simplePosHom
    (i : Fin τ.rank) (c : Multiplicative K) :
    ((simplePosHom τ K i c : adjointGroup τ K) : ModGL τ K) = xUnit τ K i c.toAdd :=
  rfl

theorem coe_simpleNegHom
    (i : Fin τ.rank) (c : Multiplicative K) :
    ((simpleNegHom τ K i c : adjointGroup τ K) : ModGL τ K) = yUnit τ K i c.toAdd :=
  rfl

theorem simplePosHom_bijective
    (i : Fin τ.rank) : Function.Bijective (simplePosHom τ K i) := by
  refine ⟨fun a b h => ?_, fun g => ?_⟩
  · have h' := congrArg (fun g : simplePosSubgroup τ K i =>
      (((g : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K))) h
    exact Multiplicative.toAdd.injective (xOp_injective i h')
  · obtain ⟨c, hc⟩ := mem_simplePosSubgroup.1 g.2
    exact ⟨Multiplicative.ofAdd c, Subtype.ext (Subtype.ext hc.symm)⟩

theorem simpleNegHom_bijective
    (i : Fin τ.rank) : Function.Bijective (simpleNegHom τ K i) := by
  refine ⟨fun a b h => ?_, fun g => ?_⟩
  · have h' := congrArg (fun g : simpleNegSubgroup τ K i =>
      (((g : adjointGroup τ K) : ModGL τ K) : Module.End K (RootModule τ K))) h
    exact Multiplicative.toAdd.injective (yOp_injective i h')
  · obtain ⟨c, hc⟩ := mem_simpleNegSubgroup.1 g.2
    exact ⟨Multiplicative.ofAdd c, Subtype.ext (Subtype.ext hc.symm)⟩

theorem iSup_simplePosSubgroup_sup_simpleNegSubgroup :
    ⨆ i, (simplePosSubgroup τ K i ⊔ simpleNegSubgroup τ K i) = ⊤ := by
  refine (Subgroup.map_injective (adjointGroup τ K).subtype_injective) (le_antisymm
    (Subgroup.map_mono le_top) ?_)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg | hg⟩
  · have hx : g = xUnit τ K i c := Units.ext hg
    subst hx
    exact ⟨⟨_, xUnit_mem_adjointGroup i c⟩, Subgroup.mem_iSup_of_mem i
      (Subgroup.mem_sup_left ⟨c, rfl⟩), rfl⟩
  · have hy : g = yUnit τ K i c := Units.ext hg
    subst hy
    exact ⟨⟨_, yUnit_mem_adjointGroup i c⟩, Subgroup.mem_iSup_of_mem i
      (Subgroup.mem_sup_right ⟨c, rfl⟩), rfl⟩

theorem orderOf_ofAdd_eq_of_charP {p : ℕ} [Fact p.Prime] [CharP K p] {c : K} (hc : c ≠ 0) :
    orderOf (Multiplicative.ofAdd c) = p := by
  rw [orderOf_ofAdd_eq_addOrderOf, addOrderOf_eq_prime_iff]
  exact ⟨by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul], hc⟩

theorem simple_root_subgroup_structure
    (τ : Tag) (K : Type*) [Field K] (i : Fin τ.rank) :
    Function.Bijective (simplePosHom τ K i) ∧ Function.Bijective (simpleNegHom τ K i) ∧
    IsMulCommutative (simplePosSubgroup τ K i) ∧ IsMulCommutative (simpleNegSubgroup τ K i) ∧
    (⨆ j, (simplePosSubgroup τ K j ⊔ simpleNegSubgroup τ K j)) = ⊤ ∧
    ∀ [Finite K] (p : ℕ) [CharP K p],
      Nat.card (simplePosSubgroup τ K i) = Nat.card K ∧
      Nat.card (simpleNegSubgroup τ K i) = Nat.card K ∧
      (∀ g : simplePosSubgroup τ K i, g ≠ 1 → orderOf g = p) ∧
      ∀ g : simpleNegSubgroup τ K i, g ≠ 1 → orderOf g = p := by
  have hP := simplePosHom_bijective (τ := τ) (K := K) i
  have hN := simpleNegHom_bijective (τ := τ) (K := K) i
  let eP := MulEquiv.ofBijective _ hP
  let eN := MulEquiv.ofBijective _ hN
  refine ⟨hP, hN, ⟨⟨fun x y => ?_⟩⟩, ⟨⟨fun x y => ?_⟩⟩,
    iSup_simplePosSubgroup_sup_simpleNegSubgroup, fun p _ => ?_⟩
  · simpa using congrArg eP (mul_comm (eP.symm x) (eP.symm y))
  · simpa using congrArg eN (mul_comm (eN.symm x) (eN.symm y))
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  refine ⟨(Nat.card_congr eP.toEquiv).symm.trans (Nat.card_congr Multiplicative.toAdd),
    (Nat.card_congr eN.toEquiv).symm.trans (Nat.card_congr Multiplicative.toAdd),
    fun g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨c, rfl⟩ := hP.2 g
    have hc : c.toAdd ≠ 0 := fun h => hg (by rw [← ofAdd_toAdd c, h, ofAdd_zero, map_one])
    rw [orderOf_injective _ hP.1, ← ofAdd_toAdd c, orderOf_ofAdd_eq_of_charP hc]
  · obtain ⟨c, rfl⟩ := hN.2 g
    have hc : c.toAdd ≠ 0 := fun h => hg (by rw [← ofAdd_toAdd c, h, ofAdd_zero, map_one])
    rw [orderOf_injective _ hN.1, ← ofAdd_toAdd c, orderOf_ofAdd_eq_of_charP hc]

end CFSG.LieType.Chevalley
