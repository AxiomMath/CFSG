module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.Open Matrix

namespace SmallOmegaFour

abbrev ι4 : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

abbrev Q4 : (ι4 → ZMod 2) → ZMod 2 := StatedQuadMinus 2 (ZMod 2) 1 1

@[expose] def vec (x y u v : ZMod 2) : ι4 → ZMod 2
  | .inl _ => x
  | .inr (.inl _) => y
  | .inr (.inr i) => ![u, v] i

@[expose] def idx : ι4 → Fin 4
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr i) => ![2, 3] i

@[expose] def mat (r : Fin 4 → Fin 4 → ZMod 2) : Matrix ι4 ι4 (ZMod 2) :=
  Matrix.of fun i j => r (idx i) (idx j)

@[expose] def sing : Fin 5 → ι4 → ZMod 2 :=
  ![vec 0 1 0 0, vec 1 1 0 1, vec 1 1 1 1, vec 1 1 1 0, vec 1 0 0 0]

@[expose] def M5 : Matrix ι4 ι4 (ZMod 2) :=
  mat ![![0, 1, 0, 0], ![1, 1, 0, 1], ![0, 0, 0, 1], ![0, 1, 1, 0]]

@[expose] def M5inv : Matrix ι4 ι4 (ZMod 2) :=
  mat ![![1, 1, 1, 0], ![1, 0, 0, 0], ![1, 0, 0, 1], ![0, 0, 1, 0]]

@[expose] def MT : Matrix ι4 ι4 (ZMod 2) :=
  mat ![![1, 1, 1, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 1]]

theorem sing_injective : Function.Injective sing := by decide +kernel

theorem sing_range (v : ι4 → ZMod 2) :
    (Q4 v = 0 ∧ v ≠ 0) ↔ ∃ i, sing i = v := by
  revert v
  decide +kernel

theorem decomp (v : ι4 → ZMod 2) :
    v = 0 ∨ (∃ i, v = sing i) ∨ ∃ i j, v = sing i + sing j := by
  revert v
  decide +kernel

theorem M5_mul_M5inv : M5 * M5inv = 1 := by decide +kernel
theorem M5inv_mul_M5 : M5inv * M5 = 1 := by decide +kernel
theorem MT_mul_MT : MT * MT = 1 := by decide +kernel

theorem M5_pres (v : ι4 → ZMod 2) : Q4 (M5 *ᵥ v) = Q4 v := by
  revert v
  decide +kernel

theorem MT_pres (v : ι4 → ZMod 2) : Q4 (MT *ᵥ v) = Q4 v := by
  revert v
  decide +kernel

theorem M5_sing : ∀ i : Fin 5, M5 *ᵥ sing i = sing (finRotate 5 i) := by decide +kernel

theorem MT_sing : ∀ i : Fin 5, MT *ᵥ sing i = sing (Equiv.swap 0 (finRotate 5 0) i) := by decide +kernel

@[expose] def O4 : Subgroup (GL ι4 (ZMod 2)) where
  carrier := {A | ∀ v, Q4 ((A : Matrix ι4 ι4 (ZMod 2)) *ᵥ v) = Q4 v}
  mul_mem' := by
    intro a b ha hb v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' := by
    intro v
    simp
  inv_mem' := by
    intro a ha v
    have h := ha (((a⁻¹ : GL ι4 (ZMod 2)) : Matrix ι4 ι4 (ZMod 2)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact h.symm

theorem statedOmega_eq : StatedOmega Q4 = ⁅O4, O4⁆ := by
  have h : Subgroup.closure
      {A : GL ι4 (ZMod 2) | ∀ v, Q4 ((A : Matrix ι4 ι4 (ZMod 2)) *ᵥ v) = Q4 v} = O4 :=
    Subgroup.closure_eq O4
  unfold StatedOmega
  rw [h]

theorem exists_perm (A : O4) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ i, (A : GL ι4 (ZMod 2)).1 *ᵥ sing i = sing (σ i) := by
  have hA := A.2
  have h : ∀ i, ∃ j, (A : GL ι4 (ZMod 2)).1 *ᵥ sing i = sing j := by
    intro i
    obtain ⟨j, hj⟩ := (sing_range ((A : GL ι4 (ZMod 2)).1 *ᵥ sing i)).1 (by
      constructor
      · rw [hA]
        exact ((sing_range _).2 ⟨i, rfl⟩).1
      · intro h0
        have := congrArg (fun w => ((A⁻¹ : GL ι4 (ZMod 2)) : Matrix ι4 ι4 (ZMod 2)) *ᵥ w) h0
        simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
          Matrix.mulVec_zero] at this
        exact ((sing_range _).2 ⟨i, rfl⟩).2 this)
    exact ⟨j, hj.symm⟩
  choose f hf using h
  have hinj : Function.Injective f := by
    intro i j hij
    apply sing_injective
    apply Matrix.mulVec_injective_of_invertible
      (A := (A : GL ι4 (ZMod 2)).1)
    rw [hf, hf, hij]
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => hf i⟩

theorem perm_unique {A : GL ι4 (ZMod 2)} {σ τ : Equiv.Perm (Fin 5)}
    (hσ : ∀ i, A.1 *ᵥ sing i = sing (σ i)) (hτ : ∀ i, A.1 *ᵥ sing i = sing (τ i)) : σ = τ := by
  exact Equiv.ext fun i => sing_injective ((hσ i).symm.trans (hτ i))

@[expose] noncomputable def toPerm (A : O4) : Equiv.Perm (Fin 5) := (exists_perm A).choose

theorem toPerm_spec (A : O4) (i : Fin 5) :
    (A : GL ι4 (ZMod 2)).1 *ᵥ sing i = sing (toPerm A i) :=
  (exists_perm A).choose_spec i

theorem toPerm_eq {A : O4} {σ : Equiv.Perm (Fin 5)}
    (h : ∀ i, (A : GL ι4 (ZMod 2)).1 *ᵥ sing i = sing (σ i)) : toPerm A = σ :=
  perm_unique (fun i => toPerm_spec A i) h

@[expose] noncomputable def toPermHom : O4 →* Equiv.Perm (Fin 5) where
  toFun := toPerm
  map_one' := by
    apply toPerm_eq
    intro i
    simp
  map_mul' := by
    intro A B
    apply toPerm_eq
    intro i
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, toPerm_spec B, toPerm_spec A]
    rfl

theorem toPermHom_injective : Function.Injective toPermHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker] at hA
  have hfix : ∀ i, (A : GL ι4 (ZMod 2)).1 *ᵥ sing i = sing i := by
    intro i
    rw [toPerm_spec]
    have : toPerm A = 1 := hA
    rw [this]
    rfl
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  rcases decomp v with h | ⟨i, h⟩ | ⟨i, j, h⟩
  · rw [h]; simp
  · rw [h, hfix]
  · rw [h, Matrix.mulVec_add, hfix, hfix]
  
@[expose] def g5 : O4 := ⟨⟨M5, M5inv, M5_mul_M5inv, M5inv_mul_M5⟩, M5_pres⟩

@[expose] def gT : O4 := ⟨⟨MT, MT, MT_mul_MT, MT_mul_MT⟩, MT_pres⟩

theorem toPermHom_g5 : toPermHom g5 = finRotate 5 := toPerm_eq M5_sing

theorem toPermHom_gT : toPermHom gT = Equiv.swap 0 (finRotate 5 0) := toPerm_eq MT_sing

theorem toPermHom_surjective : Function.Surjective toPermHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← Equiv.Perm.closure_cycle_adjacent_swap (σ := finRotate 5) (isCycle_finRotate (n := 3))
      (support_finRotate (n := 3)) 0, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact ⟨g5, toPermHom_g5⟩
  · exact ⟨gT, toPermHom_gT⟩

@[expose] noncomputable def o4MulEquivPerm : O4 ≃* Equiv.Perm (Fin 5) :=
  MulEquiv.ofBijective toPermHom ⟨toPermHom_injective, toPermHom_surjective⟩

end SmallOmegaFour

open SmallOmegaFour in
@[expose] noncomputable def statedOmega_quadMinus_two_mulEquiv_alt5 :
    ↥(StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1)) ≃* ↥(alternatingGroup (Fin 5)) := by
  have h1 : Subgroup.map O4.subtype (⁅(⊤ : Subgroup O4), (⊤ : Subgroup O4)⁆) = StatedOmega Q4 := by
    rw [statedOmega_eq, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have h2 : Subgroup.map o4MulEquivPerm.toMonoidHom (⁅(⊤ : Subgroup O4), (⊤ : Subgroup O4)⁆) = alternatingGroup (Fin 5) := by
    have htop : o4MulEquivPerm.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.2 o4MulEquivPerm.surjective
    rw [Subgroup.map_commutator, Subgroup.map_top, htop]
    exact alternatingGroup.commutator_perm_eq (by simp)
  exact ((MulEquiv.subgroupCongr h1.symm).trans
    (Subgroup.equivMapOfInjective _ O4.subtype O4.subtype_injective).symm).trans
    ((MulEquiv.subgroupMap o4MulEquivPerm _).trans (MulEquiv.subgroupCongr h2))

open SmallOmegaFour in
theorem card_alternatingGroup_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_statedOmega_quadMinus_two :
    Nat.card ↥(StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1)) = 60 := by
  rw [Nat.card_congr statedOmega_quadMinus_two_mulEquiv_alt5.toEquiv]
  exact card_alternatingGroup_five

theorem isSimpleGroup_statedOmega_quadMinus_two :
    IsSimpleGroup ↥(StatedOmega (StatedQuadMinus 2 (ZMod 2) 1 1)) :=
  statedOmega_quadMinus_two_mulEquiv_alt5.isSimpleGroup

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
