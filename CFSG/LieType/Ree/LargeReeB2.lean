module

public import CFSG.LieType.Ree.SmallReeCollectionCheck
public import CFSG.LieType.Chevalley.ProductInjectivity
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.LieType.Chevalley.RootCommutatorReduction

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

section Injective

variable {τ : Tag}

theorem baseChange_list_map_pinnedX
    {ι : Type*} {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (l : List ι) (γ : ι → Fin τ.rank → ℤ) (v : ι → R) :
    BaseChange g (((l.map fun i => pinnedX τ R (γ i) (v i)).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      (((l.map fun i => pinnedX τ S (γ i) (g (v i))).prod :
        (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) := by
  induction l with
  | nil => simpa using BaseChange.one (τ := τ) (f := g)
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul]
    exact (baseChange_pinnedX g (γ i) (v i)).mul ih

open MvPolynomial in
theorem list_ofFn_pinnedX_injective
    {m : ℕ} (α : Fin m → Fin τ.rank → ℤ)
    (hα : Function.Injective α) (hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i))
    (R : Type*) [CommRing R] :
    Function.Injective fun c : Fin m → R =>
      (List.ofFn fun i => pinnedX τ R (α i) (c i)).prod := by
  intro c c' h
  set φ : MvPolynomial (Fin m ⊕ Fin m) ℤ →+* R := eval₂Hom (Int.castRingHom R) (Sum.elim c c')
  set Q := MvPolynomial (Fin m ⊕ Fin m) ℤ ⧸ RingHom.ker φ
  set ψ : Q →+* R := RingHom.kerLift φ
  have hψ : Function.Injective ψ := RingHom.kerLift_injective φ
  set d : Fin m → Q := fun i => Ideal.Quotient.mk _ (X (Sum.inl i))
  set d' : Fin m → Q := fun i => Ideal.Quotient.mk _ (X (Sum.inr i))
  have hd : ∀ i, ψ (d i) = c i := fun i => by
    rw [RingHom.kerLift_mk, eval₂Hom_X', Sum.elim_inl]
  have hd' : ∀ i, ψ (d' i) = c' i := fun i => by
    rw [RingHom.kerLift_mk, eval₂Hom_X', Sum.elim_inr]
  have hb := baseChange_list_map_pinnedX (τ := τ) ψ (List.finRange m) α d
  have hb' := baseChange_list_map_pinnedX (τ := τ) ψ (List.finRange m) α d'
  simp only [hd, hd'] at hb hb'
  have hc : ((List.finRange m).map fun i => pinnedX τ R (α i) (c i)).prod =
      ((List.finRange m).map fun i => pinnedX τ R (α i) (c' i)).prod := by
    simpa only [List.ofFn_eq_map] using h
  rw [hc] at hb
  have hQ : (List.ofFn fun i => pinnedX τ Q (α i) (d i)).prod =
      (List.ofFn fun i => pinnedX τ Q (α i) (d' i)).prod := by
    simp only [List.ofFn_eq_map]
    exact Units.ext (BaseChange.eq_of_injective hψ hb hb')
  have hdd := (positive_root_product_injectivity τ Q α hα hpos).2 hQ
  funext i
  rw [← hd, ← hd', hdd]

end Injective

@[expose] def largeReeRoot (i : Fin 4) : Fin Tag.F4.rank → ℤ :=
  ![![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![0, 1, 2, 0]] i

@[expose] def largeReeX
    (R : Type*) [CommRing R] (i : Fin 4) (c : R) :
    (Module.End R (RootModule Tag.F4 R))ˣ :=
  pinnedX Tag.F4 R (largeReeRoot i) c

@[expose] def largeReeP
    (R : Type*) [CommRing R] (A B C D : R) :
    (Module.End R (RootModule Tag.F4 R))ˣ :=
  largeReeX R 0 A * largeReeX R 1 B * largeReeX R 2 C * largeReeX R 3 D

@[expose] def largeReeBlock : Set (Fin Tag.F4.rank) :=
  {i | i.val = 1 ∨ i.val = 2}

@[expose] def largeReePos (i : Fin 4) : ℕ :=
  ![2, 1, 8, 7] i

theorem root_largeReePos (i : Fin 4) :
    Tag.F4.rootCertificate.root (largeReePos i) = largeReeRoot i := by
  revert i
  decide

theorem largeReeRoot_injective : Function.Injective largeReeRoot := by
  intro i j
  revert i j
  decide

theorem largeReeRoot_check : ∀ i : Fin 4,
    RootOps.isRootB Tag.F4 (largeReeRoot i) = true ∧ 0 < height (largeReeRoot i) ∧
      ∀ k : Fin Tag.F4.rank, ¬ (k.val = 1 ∨ k.val = 2) → largeReeRoot i k = 0 := by
  decide

theorem largeReeBlock_check : ∀ k < Tag.F4.rootCertificate.roots.length,
    0 < height (Tag.F4.rootCertificate.root k) →
      (∀ l : Fin Tag.F4.rank, ¬ (l.val = 1 ∨ l.val = 2) → Tag.F4.rootCertificate.root k l = 0) →
        ∃ i : Fin 4, largeReeRoot i = Tag.F4.rootCertificate.root k := by
  decide

theorem mem_largeReeBlockRoots
    {α : Fin Tag.F4.rank → ℤ} :
    α ∈ parabolicPosRoots Tag.F4 largeReeBlock ↔ ∃ i, largeReeRoot i = α := by
  constructor
  · rintro ⟨⟨hα, hsupp⟩, -, hpos⟩
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq Tag.F4.rootCertificate_check hα
    exact largeReeBlock_check k hk hpos hsupp
  · rintro ⟨i, rfl⟩
    obtain ⟨hr, hpos, hsupp⟩ := largeReeRoot_check i
    have hroot := RootOps.isRootB_iff.1 hr
    exact ⟨⟨hroot, hsupp⟩, hroot, hpos⟩

theorem largeReeRoot_pos (i : Fin 4) :
    IsRoot Tag.F4 (largeReeRoot i) ∧ 0 < height (largeReeRoot i) :=
  ⟨RootOps.isRootB_iff.1 (largeReeRoot_check i).1, (largeReeRoot_check i).2.1⟩

theorem largeReeCheck_commutator
    : wordCheck Tag.F4 2
    [(0, 1, largeReePos 1, 1), (1, 0, largeReePos 0, 1), (0, 1, largeReePos 1, -1),
      (1, 0, largeReePos 0, -1)]
    [(1, 1, largeReePos 2, 1), (2, 1, largeReePos 3, 1)] = true := by
  decide +kernel

@[expose] def largeReeLeft (i j : Fin 4) : List Factor :=
  [(0, 1, largeReePos j, 1), (1, 0, largeReePos i, 1)]

@[expose] def largeReeRight (i j : Fin 4) : List Factor :=
  [(1, 0, largeReePos i, 1), (0, 1, largeReePos j, 1)]

theorem largeReeCheck_0_2 :
    wordCheck Tag.F4 2 (largeReeLeft 0 2) (largeReeRight 0 2) = true := by
  decide +kernel

theorem largeReeCheck_0_3 :
    wordCheck Tag.F4 2 (largeReeLeft 0 3) (largeReeRight 0 3) = true := by
  decide +kernel

theorem largeReeCheck_1_2 :
    wordCheck Tag.F4 2 (largeReeLeft 1 2) (largeReeRight 1 2) = true := by
  decide +kernel

theorem largeReeCheck_1_3 :
    wordCheck Tag.F4 2 (largeReeLeft 1 3) (largeReeRight 1 3) = true := by
  decide +kernel

theorem largeReeCheck_2_3 :
    wordCheck Tag.F4 2 (largeReeLeft 2 3) (largeReeRight 2 3) = true := by
  decide +kernel

@[expose] def largeReeCommPairs : List (Fin 4 × Fin 4) :=
  [(0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

theorem mem_largeReeCommPairs : ∀ i j : Fin 4, i < j → (i, j) ≠ (0, 1) →
    (i, j) ∈ largeReeCommPairs := by
  decide

theorem largeReeCheck_comm
    : ∀ p ∈ largeReeCommPairs,
    wordCheck Tag.F4 2 (largeReeLeft p.1 p.2) (largeReeRight p.1 p.2) = true := by
  simp only [largeReeCommPairs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_true]
  exact ⟨largeReeCheck_0_2, largeReeCheck_0_3, largeReeCheck_1_2, largeReeCheck_1_3,
    largeReeCheck_2_3⟩

section Relations

variable {R : Type*} [CommRing R]

theorem largeReeX_add
    (i : Fin 4) (c d : R) :
    largeReeX R i (c + d) = largeReeX R i c * largeReeX R i d :=
  pinnedX_add Tag.F4 R _ c d

theorem largeReeX_zero
    (i : Fin 4) : largeReeX R i 0 = 1 :=
  pinnedX_zero Tag.F4 R _

theorem largeReeX_inv
    (i : Fin 4) (c : R) : (largeReeX R i c)⁻¹ = largeReeX R i (-c) :=
  pinnedX_neg Tag.F4 R _ c

variable (h2 : (2 : R) = 0)
include h2

theorem largeRee_commutator
    (a b : R) :
    ⁅largeReeX R 1 b, largeReeX R 0 a⁆ = largeReeX R 2 (b * a) * largeReeX R 3 (b * a ^ 2) := by
  have hn : ((2 : ℕ) : R) = 0 := by exact_mod_cast h2
  have h := factorPinned_eq_of_wordCheck largeReeCheck_commutator R hn a b
  simp only [factorPinned_cons, factorPinned_nil, root_largeReePos, Int.cast_one, Int.cast_neg,
    one_mul, neg_mul, pow_zero, pow_one, mul_one] at h
  rw [commutatorElement_def, largeReeX_inv, largeReeX_inv]
  simp only [largeReeX, mul_assoc]
  rw [h, mul_comm b a, mul_comm b (a ^ 2)]

theorem largeRee_commute_of_mem
    {i j : Fin 4} (hij : (i, j) ∈ largeReeCommPairs) (c d : R) :
    Commute (largeReeX R i c) (largeReeX R j d) := by
  have hn : ((2 : ℕ) : R) = 0 := by exact_mod_cast h2
  have h := factorPinned_eq_of_wordCheck (largeReeCheck_comm (i, j) hij) R hn c d
  simp only [largeReeLeft, largeReeRight, factorPinned_cons, factorPinned_nil,
    root_largeReePos, Int.cast_one, one_mul, pow_zero, pow_one, mul_one] at h
  exact h.symm

theorem largeRee_swap
    (a B : R) :
    largeReeX R 1 B * largeReeX R 0 a =
      largeReeX R 2 (B * a) * largeReeX R 3 (B * a ^ 2) * (largeReeX R 0 a * largeReeX R 1 B) := by
  rw [← largeRee_commutator h2, commutatorElement_def]
  group

theorem largeRee_commute_20
    (c d : R) : Commute (largeReeX R 2 c) (largeReeX R 0 d) :=
  (largeRee_commute_of_mem h2 (by decide : ((0 : Fin 4), (2 : Fin 4)) ∈ largeReeCommPairs)
    d c).symm

theorem largeRee_commute_30
    (c d : R) : Commute (largeReeX R 3 c) (largeReeX R 0 d) :=
  (largeRee_commute_of_mem h2 (by decide : ((0 : Fin 4), (3 : Fin 4)) ∈ largeReeCommPairs)
    d c).symm

theorem largeRee_commute_21
    (c d : R) : Commute (largeReeX R 2 c) (largeReeX R 1 d) :=
  (largeRee_commute_of_mem h2 (by decide : ((1 : Fin 4), (2 : Fin 4)) ∈ largeReeCommPairs)
    d c).symm

theorem largeRee_commute_31
    (c d : R) : Commute (largeReeX R 3 c) (largeReeX R 1 d) :=
  (largeRee_commute_of_mem h2 (by decide : ((1 : Fin 4), (3 : Fin 4)) ∈ largeReeCommPairs)
    d c).symm

theorem largeRee_commute_32
    (c d : R) : Commute (largeReeX R 3 c) (largeReeX R 2 d) :=
  (largeRee_commute_of_mem h2 (by decide : ((2 : Fin 4), (3 : Fin 4)) ∈ largeReeCommPairs)
    d c).symm

theorem largeRee_swap_mul
    (a B : R) (Z : (Module.End R (RootModule Tag.F4 R))ˣ) :
    largeReeX R 1 B * (largeReeX R 0 a * Z) =
      largeReeX R 2 (B * a) * (largeReeX R 3 (B * a ^ 2) *
        (largeReeX R 0 a * (largeReeX R 1 B * Z))) := by
  rw [← mul_assoc, largeRee_swap h2]
  simp only [mul_assoc]

omit h2 in
theorem largeReeX_mul_mul
    (i : Fin 4) (p q : R) (Z : (Module.End R (RootModule Tag.F4 R))ˣ) :
    largeReeX R i p * (largeReeX R i q * Z) = largeReeX R i (p + q) * Z := by
  rw [← mul_assoc, ← largeReeX_add]

theorem largeReeP_mul
    (A B C D a b c d : R) :
    largeReeP R A B C D * largeReeP R a b c d =
      largeReeP R (A + a) (B + b) (C + c + B * a) (D + d + B * a ^ 2) := by
  have c20 := largeRee_commute_20 h2
  have c30 := largeRee_commute_30 h2
  have c21 := largeRee_commute_21 h2
  have c31 := largeRee_commute_31 h2
  have c32 := largeRee_commute_32 h2
  simp only [largeReeP, mul_assoc]
  rw [(c30 D a).left_comm, (c31 D b).left_comm, (c20 C a).left_comm, (c21 C b).left_comm,
    largeRee_swap_mul h2, (c30 _ a).left_comm, (c20 _ a).left_comm, (c31 _ B).left_comm,
    (c21 _ B).left_comm, (c31 _ b).left_comm, (c21 _ b).left_comm, (c32 _ C).left_comm,
    (c32 D c).left_comm, (c32 _ c).left_comm, largeReeX_mul_mul, largeReeX_mul_mul,
    largeReeX_mul_mul, largeReeX_mul_mul, largeReeX_mul_mul, ← largeReeX_add]
  rw [show B * a + C + c = C + c + B * a by ring,
    show B * a ^ 2 + D + d = D + d + B * a ^ 2 by ring]

theorem largeReeP_inv
    (A B C D : R) :
    (largeReeP R A B C D)⁻¹ = largeReeP R (-A) (-B) (B * A - C) (-(B * A ^ 2) - D) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [largeReeP_mul h2]
  have e : ∀ x : R, x = 0 → ∀ y : R, y = 0 → ∀ z : R, z = 0 → ∀ w : R, w = 0 →
      largeReeP R x y z w = 1 := by
    rintro _ rfl _ rfl _ rfl _ rfl
    simp only [largeReeP, largeReeX_zero, mul_one]
  exact e _ (by ring) _ (by ring) _ (by ring) _ (by ring)

end Relations

section Bijection

variable {R : Type*} [CommRing R]

theorem largeReeP_eq_ofFn
    (v : Fin 4 → R) :
    largeReeP R (v 0) (v 1) (v 2) (v 3) =
      (List.ofFn fun i => pinnedX Tag.F4 R (largeReeRoot i) (v i)).prod := by
  simp only [largeReeP, largeReeX, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, mul_assoc]
  rfl

theorem largeReeX_mem_rootSpan
    (i : Fin 4) (c : R) :
    largeReeX R i c ∈ rootSpan Tag.F4 R (parabolicPosRoots Tag.F4 largeReeBlock) :=
  (le_iSup₂_of_le (largeReeRoot i) (mem_largeReeBlockRoots.2 ⟨i, rfl⟩) le_rfl :
      rootSubgroup Tag.F4 R (largeReeRoot i) ≤ _) (Subgroup.subset_closure ⟨c, rfl⟩)

theorem largeReeP_mem_rootSpan
    (A B C D : R) :
    largeReeP R A B C D ∈ rootSpan Tag.F4 R (parabolicPosRoots Tag.F4 largeReeBlock) :=
  mul_mem (mul_mem (mul_mem (largeReeX_mem_rootSpan 0 A) (largeReeX_mem_rootSpan 1 B))
    (largeReeX_mem_rootSpan 2 C)) (largeReeX_mem_rootSpan 3 D)

theorem exists_largeReeP_eq
    (i : Fin 4) (c : R) :
    ∃ A B C D : R, largeReeP R A B C D = largeReeX R i c := by
  fin_cases i
  · exact ⟨c, 0, 0, 0, by simp [largeReeP, largeReeX_zero]⟩
  · exact ⟨0, c, 0, 0, by simp [largeReeP, largeReeX_zero]⟩
  · exact ⟨0, 0, c, 0, by simp [largeReeP, largeReeX_zero]⟩
  · exact ⟨0, 0, 0, c, by simp [largeReeP, largeReeX_zero]⟩

theorem bijOn_largeReeP
    (h2 : (2 : R) = 0) :
    Set.BijOn (fun v : Fin 4 → R => largeReeP R (v 0) (v 1) (v 2) (v 3)) Set.univ
      (rootSpan Tag.F4 R (parabolicPosRoots Tag.F4 largeReeBlock)) := by
  refine ⟨fun v _ => largeReeP_mem_rootSpan _ _ _ _, fun v _ v' _ h => ?_, fun g hg => ?_⟩
  · simp only [largeReeP_eq_ofFn] at h
    exact list_ofFn_pinnedX_injective largeReeRoot largeReeRoot_injective largeReeRoot_pos R h
  · let H : Subgroup (Module.End R (RootModule Tag.F4 R))ˣ :=
      { carrier := Set.range fun v : Fin 4 → R => largeReeP R (v 0) (v 1) (v 2) (v 3)
        one_mem' := ⟨0, by simp [largeReeP, largeReeX_zero]⟩
        mul_mem' := by
          rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
          exact ⟨![v 0 + w 0, v 1 + w 1, v 2 + w 2 + v 1 * w 0, v 3 + w 3 + v 1 * w 0 ^ 2],
            (largeReeP_mul h2 _ _ _ _ _ _ _ _).symm⟩
        inv_mem' := by
          rintro _ ⟨v, rfl⟩
          exact ⟨![-v 0, -v 1, v 1 * v 0 - v 2, -(v 1 * v 0 ^ 2) - v 3],
            (largeReeP_inv h2 _ _ _ _).symm⟩ }
    have hle : rootSpan Tag.F4 R (parabolicPosRoots Tag.F4 largeReeBlock) ≤ H := by
      refine iSup₂_le fun α hα => ?_
      obtain ⟨i, rfl⟩ := mem_largeReeBlockRoots.1 hα
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      obtain ⟨A, B, C, D, h⟩ := exists_largeReeP_eq i c
      exact ⟨![A, B, C, D], h⟩
    obtain ⟨v, hv⟩ := hle hg
    exact ⟨v, Set.mem_univ _, hv⟩

end Bijection

theorem large_Ree_B2_characteristic_two_commutators
    (R : Type*) [CommRing R] (h2 : (2 : R) = 0) :
    (∀ a b : R,
      ⁅largeReeX R 1 b, largeReeX R 0 a⁆ = largeReeX R 2 (b * a) * largeReeX R 3 (b * a ^ 2)) ∧
    (∀ i j : Fin 4, i < j → (i, j) ≠ (0, 1) →
      ∀ x ∈ rootSubgroup Tag.F4 R (largeReeRoot i), ∀ y ∈ rootSubgroup Tag.F4 R (largeReeRoot j),
        Commute x y) ∧
    (∀ A B C D a b c d : R, largeReeP R A B C D * largeReeP R a b c d =
      largeReeP R (A + a) (B + b) (C + c + B * a) (D + d + B * a ^ 2)) ∧
    Set.BijOn (fun v : Fin 4 → R => largeReeP R (v 0) (v 1) (v 2) (v 3)) Set.univ
      (rootSpan Tag.F4 R (parabolicPosRoots Tag.F4 largeReeBlock)) := by
  refine ⟨largeRee_commutator h2, fun i j hij hne x hx y hy => ?_, largeReeP_mul h2,
    bijOn_largeReeP h2⟩
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  exact largeRee_commute_of_mem h2 (mem_largeReeCommPairs i j hij hne) c d

end CFSG.LieType.Ree
