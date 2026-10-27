module

public import CFSG.LieType.SteinbergBRBlockParabolic

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix

variable {F : Type*} [Field F] {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a]
  [DecidableEq b]

variable (a) in
@[expose] def rightAut (D : SpecialLinearGroup b F) : MulAut (Multiplicative (Matrix a b F)) where
  toFun x := Multiplicative.ofAdd (Multiplicative.toAdd x * (D⁻¹).val)
  invFun x := Multiplicative.ofAdd (Multiplicative.toAdd x * D.val)
  left_inv x := by
    change Multiplicative.toAdd x * (D⁻¹).val * D.val = Multiplicative.toAdd x
    rw [Matrix.mul_assoc, inv_val_mul_val, Matrix.mul_one]
  right_inv x := by
    change Multiplicative.toAdd x * D.val * (D⁻¹).val = Multiplicative.toAdd x
    rw [Matrix.mul_assoc, val_mul_inv_val, Matrix.mul_one]
  map_mul' x y := by
    change Multiplicative.ofAdd ((Multiplicative.toAdd x + Multiplicative.toAdd y) * (D⁻¹).val) =
      Multiplicative.ofAdd (Multiplicative.toAdd x * (D⁻¹).val + Multiplicative.toAdd y * (D⁻¹).val)
    rw [Matrix.add_mul]

variable (a F) in
@[expose] def phiR : SpecialLinearGroup b F →* MulAut (Multiplicative (Matrix a b F)) where
  toFun := rightAut a
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    change Multiplicative.toAdd x * ((1 : SpecialLinearGroup b F)⁻¹).val = Multiplicative.toAdd x
    rw [inv_one]
    exact Matrix.mul_one _
  map_mul' D E := by
    refine MulEquiv.ext fun x => ?_
    change Multiplicative.toAdd x * ((D * E)⁻¹).val =
      Multiplicative.toAdd x * (E⁻¹).val * (D⁻¹).val
    have h : ((D * E)⁻¹).val = (E⁻¹).val * (D⁻¹).val :=
      congrArg Subtype.val (_root_.mul_inv_rev D E)
    rw [h, Matrix.mul_assoc]

variable (b) in
@[expose] def leftAut (A : SpecialLinearGroup a F) : MulAut (Multiplicative (Matrix a b F)) where
  toFun x := Multiplicative.ofAdd (A.val * Multiplicative.toAdd x)
  invFun x := Multiplicative.ofAdd ((A⁻¹).val * Multiplicative.toAdd x)
  left_inv x := by
    change (A⁻¹).val * (A.val * Multiplicative.toAdd x) = Multiplicative.toAdd x
    rw [← Matrix.mul_assoc, inv_val_mul_val, Matrix.one_mul]
  right_inv x := by
    change A.val * ((A⁻¹).val * Multiplicative.toAdd x) = Multiplicative.toAdd x
    rw [← Matrix.mul_assoc, val_mul_inv_val, Matrix.one_mul]
  map_mul' x y := by
    change Multiplicative.ofAdd (A.val * (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
      Multiplicative.ofAdd (A.val * Multiplicative.toAdd x + A.val * Multiplicative.toAdd y)
    rw [Matrix.mul_add]

variable (b F) in
@[expose] def phiL : SpecialLinearGroup a F →* MulAut (Multiplicative (Matrix a b F)) where
  toFun := leftAut b
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    exact Matrix.one_mul (Multiplicative.toAdd x)
  map_mul' A E := by
    refine MulEquiv.ext fun x => ?_
    exact Matrix.mul_assoc A.val E.val (Multiplicative.toAdd x)

variable (a b F) in
@[expose] noncomputable def thetaR :
    Multiplicative (Matrix a b F) ⋊[phiR F a] SpecialLinearGroup b F →*
      SpecialLinearGroup (a ⊕ b) F :=
  SemidirectProduct.lift (uniHom F a b) (levR F a) fun D => by
    refine MonoidHom.ext fun x => ?_
    change uniHom F a b (Multiplicative.ofAdd (Multiplicative.toAdd x * (D⁻¹).val)) =
      levR F a D * uniHom F a b x * (levR F a D)⁻¹
    exact (levR_conj_uni D (Multiplicative.toAdd x)).symm

variable (a b F) in
@[expose] noncomputable def thetaL :
    Multiplicative (Matrix a b F) ⋊[phiL F b] SpecialLinearGroup a F →*
      SpecialLinearGroup (a ⊕ b) F :=
  SemidirectProduct.lift (uniHom F a b) (levL F b) fun A => by
    refine MonoidHom.ext fun x => ?_
    change uniHom F a b (Multiplicative.ofAdd (A.val * Multiplicative.toAdd x)) =
      levL F b A * uniHom F a b x * (levL F b A)⁻¹
    exact (levL_conj_uni A (Multiplicative.toAdd x)).symm

theorem thetaR_val (x : Multiplicative (Matrix a b F) ⋊[phiR F a] SpecialLinearGroup b F) :
    (thetaR F a b x).val =
      fromBlocks 1 (Multiplicative.toAdd x.left * x.right.val) 0 x.right.val := by
  change (uniHom F a b x.left * levR F a x.right).val = _
  change fromBlocks 1 (Multiplicative.toAdd x.left) 0 1 * fromBlocks 1 0 0 x.right.val = _
  rw [fromBlocks_multiply]
  simp

theorem thetaL_val (x : Multiplicative (Matrix a b F) ⋊[phiL F b] SpecialLinearGroup a F) :
    (thetaL F a b x).val = fromBlocks x.right.val (Multiplicative.toAdd x.left) 0 1 := by
  change (uniHom F a b x.left * levL F b x.right).val = _
  change fromBlocks 1 (Multiplicative.toAdd x.left) 0 1 * fromBlocks x.right.val 0 0 1 = _
  rw [fromBlocks_multiply]
  simp

theorem thetaR_injective : Function.Injective (thetaR F a b) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := congrArg Subtype.val hx
  rw [thetaR_val] at h
  rw [show (1 : SpecialLinearGroup (a ⊕ b) F).val = fromBlocks 1 0 0 1 from fromBlocks_one.symm,
    fromBlocks_inj] at h
  obtain ⟨-, hX, -, hD⟩ := h
  rw [hD, Matrix.mul_one] at hX
  exact SemidirectProduct.ext hX (Subtype.ext hD)

theorem thetaL_injective : Function.Injective (thetaL F a b) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := congrArg Subtype.val hx
  rw [thetaL_val] at h
  rw [show (1 : SpecialLinearGroup (a ⊕ b) F).val = fromBlocks 1 0 0 1 from fromBlocks_one.symm,
    fromBlocks_inj] at h
  obtain ⟨hA, hX, -, -⟩ := h
  exact SemidirectProduct.ext hX (Subtype.ext hA)

variable (a b F) in
@[expose] noncomputable def parJR : Subgroup (SpecialLinearGroup (a ⊕ b) F) :=
  (thetaR F a b).range

variable (a b F) in
@[expose] noncomputable def parJL : Subgroup (SpecialLinearGroup (a ⊕ b) F) :=
  (thetaL F a b).range

theorem uniHom_mem_parJR (x : Multiplicative (Matrix a b F)) : uniHom F a b x ∈ parJR F a b :=
  ⟨SemidirectProduct.inl x, SemidirectProduct.lift_inl _ _ _ x⟩

theorem levR_mem_parJR (D : SpecialLinearGroup b F) : levR F a D ∈ parJR F a b :=
  ⟨SemidirectProduct.inr D, SemidirectProduct.lift_inr _ _ _ D⟩

theorem uniHom_mem_parJL (x : Multiplicative (Matrix a b F)) : uniHom F a b x ∈ parJL F a b :=
  ⟨SemidirectProduct.inl x, SemidirectProduct.lift_inl _ _ _ x⟩

theorem levL_mem_parJL (A : SpecialLinearGroup a F) : levL F b A ∈ parJL F a b :=
  ⟨SemidirectProduct.inr A, SemidirectProduct.lift_inr _ _ _ A⟩

theorem mem_parJR {g : SpecialLinearGroup (a ⊕ b) F} :
    g ∈ parJR F a b ↔ g ∈ parQ ∧ g.val.toBlocks₁₁ = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [mem_parQ, thetaR_val, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₁₁]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hQ, h11⟩
    have hdet := det_eq_of_mem_parQ hQ
    rw [h11, det_one, one_mul] at hdet
    let D : SpecialLinearGroup b F := ⟨g.val.toBlocks₂₂, hdet⟩
    refine ⟨⟨Multiplicative.ofAdd (g.val.toBlocks₁₂ * (D⁻¹).val), D⟩, Subtype.ext ?_⟩
    rw [thetaR_val, eq_fromBlocks_of_mem_parQ hQ, h11]
    change fromBlocks 1 (g.val.toBlocks₁₂ * (D⁻¹).val * D.val) 0 D.val = _
    rw [Matrix.mul_assoc, inv_val_mul_val, Matrix.mul_one]

theorem mem_parJL {g : SpecialLinearGroup (a ⊕ b) F} :
    g ∈ parJL F a b ↔ g ∈ parQ ∧ g.val.toBlocks₂₂ = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [mem_parQ, thetaL_val, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hQ, h22⟩
    have hdet := det_eq_of_mem_parQ hQ
    rw [h22, det_one, mul_one] at hdet
    let A : SpecialLinearGroup a F := ⟨g.val.toBlocks₁₁, hdet⟩
    refine ⟨⟨Multiplicative.ofAdd g.val.toBlocks₁₂, A⟩, Subtype.ext ?_⟩
    rw [thetaL_val, eq_fromBlocks_of_mem_parQ hQ, h22]
    rfl

theorem parJR_le_parQ : parJR F a b ≤ parQ := fun _ hg => (mem_parJR.1 hg).1

theorem parJL_le_parQ : parJL F a b ≤ parQ := fun _ hg => (mem_parJL.1 hg).1

theorem uniHom_mem_of_single {H : Subgroup (SpecialLinearGroup (a ⊕ b) F)}
    (h : ∀ (i : a) (j : b) (c : F), uniHom F a b (Multiplicative.ofAdd (single i j c)) ∈ H)
    (X : Matrix a b F) : uniHom F a b (Multiplicative.ofAdd X) ∈ H := by
  have hadd : ∀ A B : Matrix a b F, uniHom F a b (Multiplicative.ofAdd A) ∈ H →
      uniHom F a b (Multiplicative.ofAdd B) ∈ H → uniHom F a b (Multiplicative.ofAdd (A + B)) ∈ H :=
    fun A B hA hB => by
      rw [ofAdd_add, map_mul]
      exact mul_mem hA hB
  have hzero : uniHom F a b (Multiplicative.ofAdd (0 : Matrix a b F)) ∈ H := by
    rw [ofAdd_zero, map_one]
    exact one_mem H
  rw [matrix_eq_sum_single X]
  refine Finset.sum_induction _ (fun A => uniHom F a b (Multiplicative.ofAdd A) ∈ H) hadd hzero
    fun i _ => ?_
  exact Finset.sum_induction _ (fun A => uniHom F a b (Multiplicative.ofAdd A) ∈ H) hadd hzero
    fun j _ => h i j (X i j)

theorem uniHom_neg (X : Matrix a b F) :
    (uniHom F a b (Multiplicative.ofAdd X))⁻¹ = uniHom F a b (Multiplicative.ofAdd (-X)) := by
  rw [← map_inv]
  rfl

theorem commutator_le_self {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun _ hx _ hy =>
    H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)

theorem uniHom_single_mem_commutator_parJR [Nontrivial b] (i : a) (j : b) (c : F) :
    uniHom F a b (Multiplicative.ofAdd (single i j c)) ∈ ⁅parJR F a b, parJR F a b⁆ := by
  obtain ⟨k, hkj⟩ := exists_ne j
  let D : SpecialLinearGroup b F := ⟨transvection k j 1, det_transvection_of_ne k j hkj 1⟩
  have hmem := Subgroup.commutator_mem_commutator (levR_mem_parJR (a := a) D⁻¹)
    (uniHom_mem_parJR (Multiplicative.ofAdd (single i k c)))
  convert hmem using 1
  rw [commutatorElement_def, levR_conj_uni, uniHom_neg, ← map_mul]
  congr 1
  change single i j c = single i k c * ((D⁻¹)⁻¹).val + -single i k c
  rw [inv_inv]
  change single i j c = single i k c * (1 + single k j 1) + -single i k c
  rw [Matrix.mul_add, Matrix.mul_one, single_mul_single_same, mul_one]
  abel

theorem uniHom_single_mem_commutator_parJL [Nontrivial a] (i : a) (j : b) (c : F) :
    uniHom F a b (Multiplicative.ofAdd (single i j c)) ∈ ⁅parJL F a b, parJL F a b⁆ := by
  obtain ⟨k, hki⟩ := exists_ne i
  let A : SpecialLinearGroup a F := ⟨transvection i k 1, det_transvection_of_ne i k hki.symm 1⟩
  have hmem := Subgroup.commutator_mem_commutator (levL_mem_parJL (b := b) A)
    (uniHom_mem_parJL (Multiplicative.ofAdd (single k j c)))
  convert hmem using 1
  rw [commutatorElement_def, levL_conj_uni, uniHom_neg, ← map_mul]
  congr 1
  change single i j c = ((1 : Matrix a a F) + single i k 1) * single k j c + -single k j c
  rw [Matrix.add_mul, Matrix.one_mul, single_mul_single_same, one_mul]
  abel

theorem commutator_parJR [Nontrivial b] (hSL : commutator (SpecialLinearGroup b F) = ⊤) :
    ⁅parJR F a b, parJR F a b⁆ = parJR F a b := by
  refine le_antisymm (commutator_le_self _) ?_
  rintro _ ⟨⟨x, D⟩, rfl⟩
  change uniHom F a b x * levR F a D ∈ _
  refine mul_mem (uniHom_mem_of_single (uniHom_single_mem_commutator_parJR (a := a)) _) ?_
  have hD : D ∈ commutator (SpecialLinearGroup b F) := hSL ▸ Subgroup.mem_top D
  have h := Subgroup.mem_map_of_mem (levR F a) hD
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h
  have hle : (levR F a : SpecialLinearGroup b F →* _).range ≤ parJR F a b := by
    rintro _ ⟨E, rfl⟩
    exact levR_mem_parJR E
  exact Subgroup.commutator_mono hle hle h

theorem commutator_parJL [Nontrivial a] (hSL : commutator (SpecialLinearGroup a F) = ⊤) :
    ⁅parJL F a b, parJL F a b⁆ = parJL F a b := by
  refine le_antisymm (commutator_le_self _) ?_
  rintro _ ⟨⟨x, A⟩, rfl⟩
  change uniHom F a b x * levL F b A ∈ _
  refine mul_mem (uniHom_mem_of_single (uniHom_single_mem_commutator_parJL (b := b)) _) ?_
  have hA : A ∈ commutator (SpecialLinearGroup a F) := hSL ▸ Subgroup.mem_top A
  have h := Subgroup.mem_map_of_mem (levL F b) hA
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map] at h
  have hle : (levL F b : SpecialLinearGroup a F →* _).range ≤ parJL F a b := by
    rintro _ ⟨E, rfl⟩
    exact levL_mem_parJL E
  exact Subgroup.commutator_mono hle hle h

end CFSG.LieType.SteinbergBR.BlockPar
