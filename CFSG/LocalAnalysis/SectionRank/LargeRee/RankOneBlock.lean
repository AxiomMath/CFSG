module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Steinberg.Adjoint.Unipotent

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint

section Strings

variable {τ : Tag}

theorem stringUp_stringDown_of_root_eq
    {k : ℕ} (hk : k < τ.rootCertificate.roots.length)
    {β : Fin τ.rank → ℤ} (hkβ : τ.rootCertificate.root k = β) (i : Fin τ.rank)
    (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1) :
    stringUp τ i β = τ.stringData.up k i ∧ stringDown τ i β = τ.stringData.down k i := by
  subst hkβ
  have hβ := RootCertificate.isRoot_root τ.rootCertificate_check k hk
  obtain ⟨-, h⟩ := isRoot_add_smul_single_iff hβ i h₁ h₂
  obtain ⟨-, h'⟩ := StringData.isRoot_root_add_iff τ.rootCertificate_check τ.stringData_check hk
    i h₁ h₂
  have e : ∀ m : ℤ, (-(stringDown τ i (τ.rootCertificate.root k) : ℤ) ≤ m ∧
      m ≤ stringUp τ i (τ.rootCertificate.root k)) ↔
        (-(τ.stringData.down k i : ℤ) ≤ m ∧ m ≤ τ.stringData.up k i) := fun m => by
    rw [← h, h']
  have a1 := (e (stringUp τ i (τ.rootCertificate.root k))).1 ⟨by omega, le_rfl⟩
  have a2 := (e (τ.stringData.up k i)).2 ⟨by omega, le_rfl⟩
  have a3 := (e (-(stringDown τ i (τ.rootCertificate.root k) : ℤ))).1 ⟨le_rfl, by omega⟩
  have a4 := (e (-(τ.stringData.down k i : ℤ))).2 ⟨le_rfl, by omega⟩
  omega

end Strings

section Ops

variable {τ : Tag} {K : Type} [Field K]

theorem rootVec_eq_single_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ K β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem xOp_rootVec_of_stringUp_eq_zero {i : Fin τ.rank} (c : K) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1)
    (hup : stringUp τ i β = 0) :
    xOp τ K i c (rootVec τ K β) = rootVec τ K β := by
  rw [rootVec_eq_single_of_isRoot hβ, xOp, Finsupp.linearCombination_single, one_smul]
  simp only [h₁, h₂, ite_false, hup, zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, mul_one, one_smul, Nat.cast_zero, zero_smul, add_zero]
  exact rootVec_eq_single_of_isRoot hβ

theorem xOp_rootVec_of_stringUp_eq_one {i : Fin τ.rank} (c : K) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1)
    (hup : stringUp τ i β = 1) (hdown : stringDown τ i β = 0) :
    xOp τ K i c (rootVec τ K β) = rootVec τ K β + c • rootVec τ K (β + Pi.single i 1) := by
  rw [rootVec_eq_single_of_isRoot hβ, xOp, Finsupp.linearCombination_single, one_smul]
  simp only [h₁, h₂, ite_false, hup, hdown, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [rootVec_eq_single_of_isRoot hβ]

theorem yOp_rootVec_of_stringDown_eq_zero {i : Fin τ.rank} (c : K) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1)
    (hdown : stringDown τ i β = 0) :
    yOp τ K i c (rootVec τ K β) = rootVec τ K β := by
  rw [rootVec_eq_single_of_isRoot hβ, yOp, Finsupp.linearCombination_single, one_smul]
  simp only [h₁, h₂, ite_false, hdown, zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, pow_zero, mul_one, one_smul, Nat.cast_zero, zero_smul, sub_zero]
  exact rootVec_eq_single_of_isRoot hβ

theorem yOp_rootVec_of_stringDown_eq_one {i : Fin τ.rank} (c : K) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1)
    (hdown : stringDown τ i β = 1) (hup : stringUp τ i β = 0) :
    yOp τ K i c (rootVec τ K β) = rootVec τ K β + c • rootVec τ K (β - Pi.single i 1) := by
  rw [rootVec_eq_single_of_isRoot hβ, yOp, Finsupp.linearCombination_single, one_smul]
  simp only [h₁, h₂, ite_false, hup, hdown, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [rootVec_eq_single_of_isRoot hβ]

end Ops

section Block

variable {τ : Tag} {K : Type} [Field K] {n : ℕ} (ℓ : Fin n → Label τ)

@[expose] noncomputable def blockMat (A : Module.End K (RootModule τ K)) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => A (Finsupp.single (ℓ j) 1) (ℓ i)

@[expose] def PresBlock (A : Module.End K (RootModule τ K)) : Prop :=
  ∀ j, A (Finsupp.single (ℓ j) 1) = ∑ i, blockMat ℓ A i j • Finsupp.single (ℓ i) 1

variable {ℓ}

theorem sum_smul_single_apply (hℓ : Function.Injective ℓ) (M : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    (∑ k, M k j • Finsupp.single (ℓ k) (1 : K) : RootModule τ K) (ℓ i) = M i j := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, Finsupp.single_apply, hℓ.eq_iff, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem presBlock_of
    (hℓ : Function.Injective ℓ) {A : Module.End K (RootModule τ K)}
    (M : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, A (Finsupp.single (ℓ j) 1) = ∑ i, M i j • Finsupp.single (ℓ i) 1) :
    PresBlock ℓ A ∧ blockMat ℓ A = M := by
  have hM : blockMat ℓ A = M := by
    ext i j
    rw [blockMat, Matrix.of_apply, h j, sum_smul_single_apply hℓ]
  refine ⟨fun j => ?_, hM⟩
  rw [hM]
  exact h j

theorem PresBlock.mul
    (hℓ : Function.Injective ℓ) {A B : Module.End K (RootModule τ K)}
    (hA : PresBlock ℓ A) (hB : PresBlock ℓ B) :
    PresBlock ℓ (A * B) ∧ blockMat ℓ (A * B) = blockMat ℓ A * blockMat ℓ B := by
  refine presBlock_of hℓ _ fun j => ?_
  rw [Module.End.mul_apply, hB j, map_sum]
  simp only [map_smul, hA _, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem presBlock_one
    (hℓ : Function.Injective ℓ) :
    PresBlock ℓ (1 : Module.End K (RootModule τ K)) ∧
      blockMat ℓ (1 : Module.End K (RootModule τ K)) = 1 :=
  presBlock_of hℓ 1 fun j => by
    rw [Module.End.one_apply, Finset.sum_eq_single j (fun i _ hij => by
      rw [Matrix.one_apply_ne hij, zero_smul]) (by simp), Matrix.one_apply_eq, one_smul]

variable (ℓ) in
@[expose] def blockStab
    (hℓ : Function.Injective ℓ) : Subgroup (adjointGroup τ K) where
  carrier := {g | PresBlock ℓ (endHom K g) ∧ PresBlock ℓ (endHom K g⁻¹)}
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [map_mul]
      exact (hg.1.mul hℓ hh.1).1
    · rw [_root_.mul_inv_rev, map_mul]
      exact (hh.2.mul hℓ hg.2).1
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [map_one]
      exact (presBlock_one hℓ).1
    · rw [inv_one, map_one]
      exact (presBlock_one hℓ).1
  inv_mem' {g} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

variable (ℓ) in
@[expose] noncomputable def blockRep
    (hℓ : Function.Injective ℓ) :
    blockStab (K := K) ℓ hℓ →* GL (Fin n) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => blockMat ℓ (endHom K (g : adjointGroup τ K))
      map_one' := by
        rw [OneMemClass.coe_one, map_one]
        exact (presBlock_one hℓ).2
      map_mul' := fun g h => by
        rw [Subgroup.coe_mul, map_mul]
        exact (g.2.1.mul hℓ h.2.1).2 }

theorem coe_blockRep
    (hℓ : Function.Injective ℓ) (g : blockStab (K := K) ℓ hℓ) :
    ((blockRep ℓ hℓ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      blockMat ℓ (endHom K (g : adjointGroup τ K)) :=
  rfl

end Block

end CFSG.SectionRank.LargeRee
