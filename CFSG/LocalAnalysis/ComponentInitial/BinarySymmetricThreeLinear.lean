module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullCosetMiddleSubgroup
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCongruenceOrbits
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

instance moduleBinarySymMatrices (n : ℕ) : Module (ZMod 2) ↥(binarySymMatrices n) where
  smul c X := ⟨c • (X : Matrix (Fin n) (Fin n) (ZMod 2)), by
    rw [mem_binarySymMatrices, transpose_smul,
      show (X : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = X from X.2]⟩
  one_smul X := Subtype.ext (one_smul (ZMod 2) (X : Matrix (Fin n) (Fin n) (ZMod 2)))
  mul_smul a b X := Subtype.ext (mul_smul a b (X : Matrix (Fin n) (Fin n) (ZMod 2)))
  smul_zero a := Subtype.ext (smul_zero a)
  smul_add a X Y := Subtype.ext (smul_add a (X : Matrix (Fin n) (Fin n) (ZMod 2)) Y)
  add_smul a b X := Subtype.ext (add_smul a b (X : Matrix (Fin n) (Fin n) (ZMod 2)))
  zero_smul X := Subtype.ext (zero_smul (ZMod 2) (X : Matrix (Fin n) (Fin n) (ZMod 2)))

theorem coe_smul_binarySymMatrices {n : ℕ} (c : ZMod 2) (X : ↥(binarySymMatrices n)) :
    ((c • X : ↥(binarySymMatrices n)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      c • (X : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  rfl

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def symThreeDiagLin : ↥(binarySymMatrices 3) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun B := symThreeDiag (B : M₃)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem symThreeDiagLin_apply (B : 𝕍) : symThreeDiagLin B = symThreeDiag (B : M₃) :=
  rfl

@[expose] def symThreeDiagSection : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ↥(binarySymMatrices 3) where
  toFun e := ⟨diagonal e, diagonal_transpose e⟩
  map_add' e e' := Subtype.ext (diagonal_add e e').symm
  map_smul' c e := Subtype.ext (diagonal_smul c e)

theorem coe_symThreeDiagSection (e : Fin 3 → ZMod 2) :
    (symThreeDiagSection e : M₃) = diagonal e :=
  rfl

theorem symThreeDiag_diagSection (e : Fin 3 → ZMod 2) :
    symThreeDiag (symThreeDiagSection e : M₃) = e := by
  funext k
  exact diagonal_apply_eq e k

theorem symThreeDiag_add_diagSection (B : 𝕍) :
    symThreeDiag ((B + symThreeDiagSection (symThreeDiag (B : M₃)) : 𝕍) : M₃) = 0 := by
  rw [AddSubgroup.coe_add, symThreeDiag_add, symThreeDiag_diagSection]
  exact symThree_add_self_diag _
where
  symThree_add_self_diag (x : Fin 3 → ZMod 2) : x + x = 0 := by
    funext k
    exact symThree_zmod_add_self _

theorem symThreeCongr_one (B : 𝕍) : symThreeCongr 1 B = B :=
  Subtype.ext (by rw [coe_symThreeCongr, Units.val_one, Matrix.one_mul, transpose_one,
    Matrix.mul_one])

theorem symThreeCongr_mul (D D' : GL (Fin 3) (ZMod 2)) (B : 𝕍) :
    symThreeCongr (D * D') B = symThreeCongr D (symThreeCongr D' B) :=
  Subtype.ext (by
    rw [coe_symThreeCongr, coe_symThreeCongr, coe_symThreeCongr, Units.val_mul, transpose_mul]
    simp only [Matrix.mul_assoc])

theorem symThreeCongr_smul (D : GL (Fin 3) (ZMod 2)) (c : ZMod 2) (B : 𝕍) :
    symThreeCongr D (c • B) = c • symThreeCongr D B :=
  Subtype.ext (by
    rw [coe_symThreeCongr, coe_smul_binarySymMatrices, coe_smul_binarySymMatrices,
      coe_symThreeCongr, Matrix.mul_smul, Matrix.smul_mul])

@[expose] def symThreeCongrEquiv (D : GL (Fin 3) (ZMod 2)) :
    ↥(binarySymMatrices 3) ≃ₗ[ZMod 2] ↥(binarySymMatrices 3) where
  toFun := symThreeCongr D
  invFun := symThreeCongr D⁻¹
  map_add' := symThreeCongr_add D
  map_smul' := symThreeCongr_smul D
  left_inv B := by
    rw [← symThreeCongr_mul, inv_mul_cancel, symThreeCongr_one]
  right_inv B := by
    rw [← symThreeCongr_mul, mul_inv_cancel, symThreeCongr_one]

theorem symThreeCongrEquiv_apply (D : GL (Fin 3) (ZMod 2)) (B : 𝕍) :
    symThreeCongrEquiv D B = symThreeCongr D B :=
  rfl

@[expose] def symThreeCongrHom :
    GL (Fin 3) (ZMod 2) →* (↥(binarySymMatrices 3) ≃ₗ[ZMod 2] ↥(binarySymMatrices 3)) where
  toFun := symThreeCongrEquiv
  map_one' := LinearEquiv.ext symThreeCongr_one
  map_mul' D D' := LinearEquiv.ext (symThreeCongr_mul D D')

theorem symThreeCongrHom_apply (D : GL (Fin 3) (ZMod 2)) (B : 𝕍) :
    symThreeCongrHom D B = symThreeCongr D B :=
  rfl

@[expose] def symThreeCongrGroup :
    Subgroup (↥(binarySymMatrices 3) ≃ₗ[ZMod 2] ↥(binarySymMatrices 3)) :=
  symThreeCongrHom.range

theorem mem_symThreeCongrGroup {g : 𝕍 ≃ₗ[ZMod 2] 𝕍} :
    g ∈ symThreeCongrGroup ↔ ∃ D : GL (Fin 3) (ZMod 2), symThreeCongrHom D = g :=
  Iff.rfl

@[expose] def symThreeRankOne (v : Fin 3 → ZMod 2) : 𝕍 :=
  ⟨vecMulVec v v, by rw [mem_binarySymMatrices, transpose_vecMulVec]⟩

theorem symThreeCongr_rankOne (D : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    symThreeCongr D (symThreeRankOne v) =
      symThreeRankOne ((D : M₃) *ᵥ v) :=
  Subtype.ext (by
    rw [coe_symThreeCongr]
    exact BinarySymplecticSix.mul_vecMulVec_mul_transpose _ v)

theorem symThreeCongrHom_injective : Function.Injective symThreeCongrHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro D hD
  rw [MonoidHom.mem_ker] at hD
  have hv : ∀ v : Fin 3 → ZMod 2, (D : M₃) *ᵥ v = v := fun v => by
    have h := congrArg (fun g : 𝕍 ≃ₗ[ZMod 2] 𝕍 => (g (symThreeRankOne v) : M₃)) hD
    simp only [symThreeCongrHom_apply, symThreeCongr_rankOne] at h
    exact BinarySymplecticSix.vecMulVec_self_injective h
  have h1 : (D : M₃) = 1 := by
    rw [← Matrix.toLin'.injective.eq_iff]
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, hv, Matrix.toLin'_one, LinearMap.id_apply]
  exact Subgroup.mem_bot.mpr (Units.ext h1)

theorem card_glThree : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem card_symThreeCongrGroup : Nat.card symThreeCongrGroup = 168 := by
  rw [symThreeCongrGroup, ← card_glThree]
  exact Nat.card_congr (Equiv.ofInjective _ symThreeCongrHom_injective).symm

theorem symThreeDiagLin_congr (D : GL (Fin 3) (ZMod 2)) (B : 𝕍) :
    symThreeDiagLin (symThreeCongrHom D B) = (D : M₃) *ᵥ symThreeDiagLin B :=
  symThreeDiag_coe_congr D B

@[expose] def symThreeType (B : M₃) : Fin 5 :=
  if (Finset.univ.image B.mulVec).card = 1 then 0
  else if (Finset.univ.image B.mulVec).card = 2 then 1
  else if (Finset.univ.image B.mulVec).card = 4 then (if symThreeDiag B = 0 then 2 else 3)
  else 4

@[expose] def symThreeTypeCount (t : Fin 5) : ℕ :=
  ![1, 7, 7, 21, 28] t

theorem card_symThreeType : ∀ t : Fin 5,
    (Finset.univ.filter fun B : 𝕍 => symThreeType (B : M₃) = t).card = symThreeTypeCount t := by
  decide +kernel

theorem card_symThree : Nat.card 𝕍 = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem symThreeType_eq_zero_iff : ∀ B : 𝕍, symThreeType (B : M₃) = 0 ↔ B = 0 := by
  decide +kernel

theorem symThreeType_mem_zero_two_iff : ∀ B : 𝕍,
    (symThreeType (B : M₃) = 0 ∨ symThreeType (B : M₃) = 2) ↔ symThreeDiag (B : M₃) = 0 := by
  decide +kernel

theorem card_image_mulVec_three (B : M₃) :
    (Finset.univ.image B.mulVec).card = 1 ∨ (Finset.univ.image B.mulVec).card = 2 ∨
      (Finset.univ.image B.mulVec).card = 4 ∨ (Finset.univ.image B.mulVec).card = 8 := by
  rw [card_image_mulVec_eq_pow_rank, ZMod.card]
  have h := Matrix.rank_le_width B
  interval_cases B.rank <;> simp

theorem symThreeType_eq_aux {c c' : ℕ} {p p' : Prop} [Decidable p] [Decidable p']
    (hc : c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8) (hc' : c' = 1 ∨ c' = 2 ∨ c' = 4 ∨ c' = 8)
    (h : (if c = 1 then 0 else if c = 2 then 1 else if c = 4 then (if p then 2 else 3) else 4 :
        Fin 5) =
      if c' = 1 then 0 else if c' = 2 then 1 else if c' = 4 then (if p' then 2 else 3) else 4) :
    c = c' ∧ (c = 4 → (p ↔ p')) := by
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl <;>
    by_cases hp : p <;> by_cases hp' : p' <;> simp_all

theorem symThreeType_congr (D : GL (Fin 3) (ZMod 2)) (B : 𝕍) :
    symThreeType (symThreeCongr D B : M₃) = symThreeType (B : M₃) := by
  have hc : (Finset.univ.image (symThreeCongr D B : M₃).mulVec).card =
      (Finset.univ.image (B : M₃).mulVec).card := by
    rw [card_image_mulVec_eq_pow_rank, card_image_mulVec_eq_pow_rank, coe_symThreeCongr,
      BinarySymplecticSix.rank_congr_three]
  have hd : symThreeDiag (symThreeCongr D B : M₃) = 0 ↔ symThreeDiag (B : M₃) = 0 := by
    rw [symThreeDiag_coe_congr]
    constructor
    · intro h
      have h1 := congrArg (((D⁻¹ : GL (Fin 3) (ZMod 2)) : M₃) *ᵥ ·) h
      simp only [mulVec_mulVec, mulVec_zero] at h1
      rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h1
    · intro h
      rw [h, mulVec_zero]
  unfold symThreeType
  rw [hc]
  by_cases h0 : symThreeDiag (B : M₃) = 0
  · simp only [h0, hd.2 h0]
  · have h1 : ¬ symThreeDiag (symThreeCongr D B : M₃) = 0 := fun h => h0 (hd.1 h)
    simp only [h0, h1]

theorem exists_symThreeCongr_of_type_eq {B B' : 𝕍}
    (h : symThreeType (B : M₃) = symThreeType (B' : M₃)) :
    ∃ D : GL (Fin 3) (ZMod 2), symThreeCongr D B = B' := by
  obtain ⟨hcc, hp⟩ := symThreeType_eq_aux (card_image_mulVec_three _) (card_image_mulVec_three _) h
  have hr : (B : M₃).rank = (B' : M₃).rank := by
    rw [card_image_mulVec_eq_pow_rank, card_image_mulVec_eq_pow_rank] at hcc
    exact Nat.pow_right_injective (le_refl 2) (by simpa [ZMod.card] using hcc)
  have ha : (B : M₃).rank = 2 → ((∀ i, (B : M₃) i i = 0) ↔ ∀ i, (B' : M₃) i i = 0) := by
    intro h2
    have h4 : (Finset.univ.image (B : M₃).mulVec).card = 4 := by
      rw [card_image_mulVec_eq_pow_rank, h2, ZMod.card]
      rfl
    have h5 := hp h4
    constructor
    · intro hB i
      exact congrFun (h5.1 (funext hB)) i
    · intro hB i
      exact congrFun (h5.2 (funext hB)) i
  obtain ⟨D, hD⟩ := (BinarySymplecticSix.sym_congruent_iff B B').mpr ⟨hr, ha⟩
  exact ⟨D, Subtype.ext hD⟩

@[expose] def IsSymThreeCongrInvariant (W : Set 𝕍) : Prop :=
  ∀ D : GL (Fin 3) (ZMod 2), ∀ B ∈ W, symThreeCongr D B ∈ W

theorem mem_of_symThreeType_eq {W : Set 𝕍} (hW : IsSymThreeCongrInvariant W) {B B' : 𝕍}
    (h : symThreeType (B : M₃) = symThreeType (B' : M₃)) (hB : B ∈ W) : B' ∈ W := by
  obtain ⟨D, rfl⟩ := exists_symThreeCongr_of_type_eq h
  exact hW D B hB

open Classical in
noncomputable def symThreeTypesOf (W : Set 𝕍) : Finset (Fin 5) :=
  (Finset.univ.filter (· ∈ W)).image fun B : 𝕍 => symThreeType (B : M₃)

theorem mem_symThreeTypesOf {W : Set 𝕍} (hW : IsSymThreeCongrInvariant W) {B : 𝕍} :
    symThreeType (B : M₃) ∈ symThreeTypesOf W ↔ B ∈ W := by
  classical
  constructor
  · intro h
    rw [symThreeTypesOf, Finset.mem_image] at h
    obtain ⟨B', hB', h'⟩ := h
    rw [Finset.mem_filter] at hB'
    exact mem_of_symThreeType_eq hW h' hB'.2
  · intro h
    rw [symThreeTypesOf, Finset.mem_image]
    exact ⟨B, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩

theorem card_eq_sum_of_invariant {W : Set 𝕍} (hW : IsSymThreeCongrInvariant W) :
    Nat.card W = ∑ t ∈ symThreeTypesOf W, symThreeTypeCount t := by
  classical
  have hset : W = ↑(Finset.univ.filter fun B : 𝕍 =>
      symThreeType (B : M₃) ∈ symThreeTypesOf W) := by
    ext B
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, (mem_symThreeTypesOf hW).2 h⟩,
      fun h => (mem_symThreeTypesOf hW).1 h.2⟩
  have h1 : Nat.card W = (Finset.univ.filter fun B : 𝕍 =>
      symThreeType (B : M₃) ∈ symThreeTypesOf W).card := by
    conv_lhs => rw [hset]
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [h1, Finset.card_eq_sum_card_fiberwise (f := fun B : 𝕍 => symThreeType (B : M₃))
    (s := Finset.univ.filter fun B : 𝕍 => symThreeType (B : M₃) ∈ symThreeTypesOf W)
    (t := symThreeTypesOf W) (fun B hB => Finset.mem_coe.2 (Finset.mem_filter.1 hB).2)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [← card_symThreeType t, Finset.filter_filter]
  exact congrArg Finset.card (Finset.filter_congr fun B _ => ⟨fun h => h.2, fun h => ⟨h ▸ ht, h⟩⟩)

theorem symThreeTypes_of_card_dvd_sixtyFour : ∀ τ : Finset (Fin 5), 0 ∈ τ →
    (∑ t ∈ τ, symThreeTypeCount t) ∣ 64 →
      τ = {0} ∨ τ = {0, 1} ∨ τ = {0, 2} ∨ τ = Finset.univ := by
  decide

theorem symThreeTypes_of_card_dvd_twentyOne : ∀ τ : Finset (Fin 5), 0 ∉ τ → τ.Nonempty →
    (∑ t ∈ τ, symThreeTypeCount t) ∣ 21 → τ = {1} ∨ τ = {2} ∨ τ = {3} := by
  decide

theorem symThreeType_diag_units : symThreeType (symThreeRankOne ![1, 0, 0] : M₃) = 1 ∧
    symThreeType (symThreeRankOne ![0, 1, 0] : M₃) = 1 ∧
    symThreeType ((symThreeRankOne ![1, 0, 0] + symThreeRankOne ![0, 1, 0] : 𝕍) : M₃) = 3 := by
  decide +kernel

theorem invariant_addSubgroup (W : AddSubgroup 𝕍) (hW : IsSymThreeCongrInvariant (W : Set 𝕍)) :
    W = ⊥ ∨ (∀ B, B ∈ W ↔ symThreeDiag (B : M₃) = 0) ∨ W = ⊤ := by
  have hcard : Nat.card W = ∑ t ∈ symThreeTypesOf (W : Set 𝕍), symThreeTypeCount t :=
    card_eq_sum_of_invariant hW
  have hdvd : Nat.card W ∣ 64 := card_symThree ▸ AddSubgroup.card_addSubgroup_dvd_card W
  have hmem : ∀ B : 𝕍, symThreeType (B : M₃) ∈ symThreeTypesOf (W : Set 𝕍) ↔ B ∈ W :=
    fun B => mem_symThreeTypesOf hW
  have h0 : (0 : Fin 5) ∈ symThreeTypesOf (W : Set 𝕍) := by
    rw [← (symThreeType_eq_zero_iff 0).2 rfl, hmem]
    exact W.zero_mem
  rw [hcard] at hdvd
  rcases symThreeTypes_of_card_dvd_sixtyFour _ h0 hdvd with hτ | hτ | hτ | hτ
  · left
    rw [eq_bot_iff]
    intro B hB
    rw [← hmem, hτ, Finset.mem_singleton, symThreeType_eq_zero_iff] at hB
    exact AddSubgroup.mem_bot.2 hB
  · exfalso
    obtain ⟨h1, h2, h3⟩ := symThreeType_diag_units
    have hq1 : symThreeRankOne ![1, 0, 0] ∈ W := by
      rw [← hmem, h1, hτ]
      simp
    have hq2 : symThreeRankOne ![0, 1, 0] ∈ W := by
      rw [← hmem, h2, hτ]
      simp
    have hq := (hmem _).2 (W.add_mem hq1 hq2)
    rw [h3, hτ] at hq
    simp at hq
  · right
    left
    intro B
    rw [← hmem, hτ, ← symThreeType_mem_zero_two_iff]
    simp
  · right
    right
    rw [eq_top_iff]
    intro B _
    rw [← hmem, hτ]
    exact Finset.mem_univ _

theorem symThreeType_eq_one_iff : ∀ B : 𝕍, symThreeType (B : M₃) = 1 ↔
    (B ≠ 0 ∧ ∀ A : 𝕍, symThreeType (A : M₃) = 3 → symThreeType ((B + A : 𝕍) : M₃) ≠ 3) := by
  decide +kernel

theorem eq_sum_rankOne : ∀ B : 𝕍, B = (B : M₃) 0 0 • symThreeRankOne ![1, 0, 0] +
    (B : M₃) 1 1 • symThreeRankOne ![0, 1, 0] + (B : M₃) 2 2 • symThreeRankOne ![0, 0, 1] +
    (B : M₃) 0 1 • (symThreeRankOne ![1, 1, 0] + symThreeRankOne ![1, 0, 0] +
      symThreeRankOne ![0, 1, 0]) +
    (B : M₃) 0 2 • (symThreeRankOne ![1, 0, 1] + symThreeRankOne ![1, 0, 0] +
      symThreeRankOne ![0, 0, 1]) +
    (B : M₃) 1 2 • (symThreeRankOne ![0, 1, 1] + symThreeRankOne ![0, 1, 0] +
      symThreeRankOne ![0, 0, 1]) := by
  decide +kernel

theorem symThreeType_rankOne_ne_zero : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    symThreeType (symThreeRankOne v : M₃) = 1 := by
  decide +kernel

theorem eq_of_eq_on_symThreeType_one {f g : 𝕍 ≃ₗ[ZMod 2] 𝕍}
    (h : ∀ B : 𝕍, symThreeType (B : M₃) = 1 → f B = g B) : f = g := by
  have hq : ∀ v : Fin 3 → ZMod 2, v ≠ 0 → f (symThreeRankOne v) = g (symThreeRankOne v) :=
    fun v hv => h _ (symThreeType_rankOne_ne_zero v hv)
  refine LinearEquiv.ext fun B => ?_
  rw [eq_sum_rankOne B]
  simp only [map_add, map_smul]
  rw [hq _ (by decide), hq _ (by decide), hq _ (by decide), hq _ (by decide), hq _ (by decide),
    hq _ (by decide)]

end CFSG.LocalAnalysis.ComponentInitial
