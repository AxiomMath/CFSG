module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.KC.GL62

open CFSG.OddStandard.AltStdSmall4.GL62
open Matrix

@[expose] def inlLin : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun v := Fin.append v (0 : Fin 3 → ZMod 2)
  map_add' v v' := by
    rw [← append_add, add_zero]
  map_smul' c v := by
    rw [RingHom.id_apply, ← append_smul, smul_zero]

@[expose] def inrLin : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun w := Fin.append (0 : Fin 3 → ZMod 2) w
  map_add' w w' := by
    rw [← append_add, add_zero]
  map_smul' c w := by
    rw [RingHom.id_apply, ← append_smul, smul_zero]

@[expose] def blockLin (A X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  appendLin (A.mulVecLin ∘ₗ fstLin + X.mulVecLin ∘ₗ sndLin) (A.mulVecLin ∘ₗ sndLin)

@[expose] def blockMat (A X : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  LinearMap.toMatrix' (blockLin A X)

theorem blockMat_mulVec (A X : Matrix (Fin 3) (Fin 3) (ZMod 2)) (x : Fin 6 → ZMod 2) :
    blockMat A X *ᵥ x = Fin.append (A *ᵥ fst x + X *ᵥ snd x) (A *ᵥ snd x) := by
  rw [blockMat, LinearMap.toMatrix'_mulVec]
  rfl

theorem ext6 {M N : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h : ∀ v w : Fin 3 → ZMod 2, M *ᵥ Fin.append v w = N *ᵥ Fin.append v w) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← append_fst_snd x]
    exact h _ _)

theorem ext3 {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h v)

theorem blockMat_mul (A X B Y : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    blockMat A X * blockMat B Y = blockMat (A * B) (A * Y + X * B) := by
  refine ext6 fun v w => ?_
  rw [← Matrix.mulVec_mulVec]
  simp only [blockMat_mulVec]
  simp only [fst_append, snd_append, Matrix.mulVec_add, Matrix.add_mulVec, Matrix.mulVec_mulVec,
    add_assoc]

theorem blockMat_one : blockMat 1 0 = 1 :=
  ext6 fun v w => by
    rw [blockMat_mulVec, fst_append, snd_append, Matrix.one_mulVec, Matrix.one_mulVec,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

theorem blockMat_inj {A X B Y : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : blockMat A X = blockMat B Y) : A = B ∧ X = Y := by
  have h1 : ∀ v w : Fin 3 → ZMod 2, A *ᵥ v + X *ᵥ w = B *ᵥ v + Y *ᵥ w := fun v w => by
    have e : blockMat A X *ᵥ (Fin.append v w : Fin 6 → ZMod 2) =
        blockMat B Y *ᵥ (Fin.append v w : Fin 6 → ZMod 2) := by rw [h]
    rw [blockMat_mulVec, blockMat_mulVec, fst_append, snd_append] at e
    have e2 := congrArg fst e
    rwa [fst_append, fst_append] at e2
  refine ⟨ext3 fun v => ?_, ext3 fun w => ?_⟩
  · simpa only [Matrix.mulVec_zero, add_zero] using h1 v 0
  · simpa only [Matrix.mulVec_zero, zero_add] using h1 0 w

theorem coe_z0_eq : (z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = blockMat 1 1 :=
  ext6 fun v w => by
    rw [z0_mulVec, blockMat_mulVec, fst_append, snd_append, Matrix.one_mulVec, Matrix.one_mulVec]

theorem coe_dg_eq (A : GL (Fin 3) (ZMod 2)) :
    (dg A : Matrix (Fin 6) (Fin 6) (ZMod 2)) = blockMat A 0 :=
  ext6 fun v w => by
    rw [dg_mulVec, blockMat_mulVec, fst_append, snd_append, Matrix.zero_mulVec, add_zero]

@[expose] def blockGL (A : GL (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    GL (Fin 6) (ZMod 2) where
  val := blockMat A X
  inv := blockMat (A⁻¹ : GL (Fin 3) (ZMod 2)) (-((A⁻¹ : GL (Fin 3) (ZMod 2)) * X *
    (A⁻¹ : GL (Fin 3) (ZMod 2))))
  val_inv := by
    rw [blockMat_mul]
    simp only [mul_neg, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel, blockMat_one]
  inv_val := by
    rw [blockMat_mul]
    simp only [neg_mul, mul_assoc, Units.inv_mul, mul_one, add_neg_cancel, blockMat_one]

theorem coe_blockGL (A : GL (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (blockGL A X : Matrix (Fin 6) (Fin 6) (ZMod 2)) = blockMat A X := rfl

theorem blockGL_mul_z0 (A : GL (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    blockGL A X * z₀ = z₀ * blockGL A X := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_z0_eq, coe_blockGL, blockMat_mul, mul_one, one_mul]
  rw [add_comm]

theorem blockGL_inj {A B : GL (Fin 3) (ZMod 2)} {X Y : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : blockGL A X = blockGL B Y) : A = B ∧ X = Y := by
  obtain ⟨h1, h2⟩ := blockMat_inj (congrArg Units.val h)
  exact ⟨Units.ext h1, h2⟩

theorem exists_blockMat_of_comm {M : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h : M * (z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = (z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) * M) :
    ∃ A X, M = blockMat A X := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2),
      ∀ v, A *ᵥ v = fst (M *ᵥ Fin.append v (0 : Fin 3 → ZMod 2)) :=
    ⟨LinearMap.toMatrix' (fstLin ∘ₗ M.mulVecLin ∘ₗ inlLin), fun v => by
      rw [LinearMap.toMatrix'_mulVec]
      rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 3) (Fin 3) (ZMod 2),
      ∀ w, X *ᵥ w = fst (M *ᵥ Fin.append (0 : Fin 3 → ZMod 2) w) :=
    ⟨LinearMap.toMatrix' (fstLin ∘ₗ M.mulVecLin ∘ₗ inrLin), fun w => by
      rw [LinearMap.toMatrix'_mulVec]
      rfl⟩
  have hz : ∀ x, M *ᵥ ((z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x) =
      (z₀ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ (M *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  have hc : ∀ v, snd (M *ᵥ Fin.append v (0 : Fin 3 → ZMod 2)) = 0 := fun v => by
    have e := congrArg fst (hz (Fin.append v (0 : Fin 3 → ZMod 2)))
    rw [z0_mulVec, add_zero, z0_mulVec', fst_append] at e
    simpa using e
  have hd : ∀ w, snd (M *ᵥ Fin.append (0 : Fin 3 → ZMod 2) w) = A *ᵥ w := fun w => by
    have e := congrArg fst (hz (Fin.append (0 : Fin 3 → ZMod 2) w))
    rw [z0_mulVec, zero_add, z0_mulVec', fst_append,
      show Fin.append w w = Fin.append w (0 : Fin 3 → ZMod 2) + Fin.append (0 : Fin 3 → ZMod 2) w by rw [← append_add, add_zero, zero_add],
      Matrix.mulVec_add, fst_add, ← hA w, add_comm] at e
    exact ((add_left_cancel e).symm)
  refine ⟨A, X, ext6 fun v w => ?_⟩
  rw [blockMat_mulVec, fst_append, snd_append,
    show Fin.append v w = Fin.append v (0 : Fin 3 → ZMod 2) + Fin.append (0 : Fin 3 → ZMod 2) w by rw [← append_add, add_zero, zero_add],
    Matrix.mulVec_add]
  refine ext_halves ?_ ?_
  · rw [fst_add, fst_append, hA, hX]
  · rw [snd_add, snd_append, hc, zero_add, hd]

theorem centralizer_z0 {g : GL (Fin 6) (ZMod 2)} :
    g * z₀ = z₀ * g ↔ ∃ (A : GL (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 3) (ZMod 2)),
      g = blockGL A X := by
  constructor
  · intro h
    obtain ⟨A, X, hAX⟩ := exists_blockMat_of_comm (congrArg Units.val h)
    have hi : g⁻¹ * z₀ = z₀ * g⁻¹ := Commute.inv_left (h : Commute g z₀)
    obtain ⟨B, Y, hBY⟩ := exists_blockMat_of_comm (congrArg Units.val hi)
    have h1 := congrArg Units.val (mul_inv_cancel g)
    have h2 := congrArg Units.val (inv_mul_cancel g)
    rw [Units.val_mul, hAX, hBY, blockMat_mul, Units.val_one, ← blockMat_one] at h1
    rw [Units.val_mul, hAX, hBY, blockMat_mul, Units.val_one, ← blockMat_one] at h2
    refine ⟨⟨A, B, (blockMat_inj h1).1, (blockMat_inj h2).1⟩, X, Units.ext ?_⟩
    rw [coe_blockGL, hAX]
  · rintro ⟨A, X, rfl⟩
    exact blockGL_mul_z0 A X

theorem card_GL32 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_three]
  norm_num

theorem card_GL62 : Nat.card (GL (Fin 6) (ZMod 2)) = 20158709760 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_six]
  norm_num

theorem card_mat3 : Nat.card (Matrix (Fin 3) (Fin 3) (ZMod 2)) = 512 := by
  change Nat.card (Fin 3 → Fin 3 → ZMod 2) = 512
  simp [Nat.card_fun]

theorem card_centralizer_z0 :
    Nat.card (Subgroup.centralizer {z₀} : Subgroup (GL (Fin 6) (ZMod 2))) = 86016 := by
  let φ : GL (Fin 3) (ZMod 2) × Matrix (Fin 3) (Fin 3) (ZMod 2) →
      (Subgroup.centralizer {z₀} : Subgroup (GL (Fin 6) (ZMod 2))) := fun p =>
    ⟨blockGL p.1 p.2, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (blockGL_mul_z0 p.1 p.2).symm⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨A, X⟩ ⟨B, Y⟩ hp
      obtain ⟨h1, h2⟩ := blockGL_inj (congrArg Subtype.val hp)
      exact Prod.ext h1 h2
    · rintro ⟨g, hg⟩
      have hc : g * z₀ = z₀ * g :=
        (Subgroup.mem_centralizer_iff.1 hg z₀ (Set.mem_singleton z₀)).symm
      obtain ⟨A, X, rfl⟩ := centralizer_z0.1 hc
      exact ⟨(A, X), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, card_GL32, card_mat3]

theorem ncard_conj_mul (K : Subgroup (GL (Fin 6) (ZMod 2))) (y : GL (Fin 6) (ZMod 2)) :
    {d | ∃ c ∈ K, d = c * y * c⁻¹}.ncard * {c | c ∈ K ∧ c * y = y * c}.ncard = Nat.card K := by
  letI : MulAction K (GL (Fin 6) (ZMod 2)) := MulAction.compHom _ (MulAut.conj.comp K.subtype)
  have hsmul : ∀ (x : K) (g : GL (Fin 6) (ZMod 2)),
      x • g = (x : GL (Fin 6) (ZMod 2)) * g * (x : GL (Fin 6) (ZMod 2))⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit K y = {d | ∃ c ∈ K, d = c * y * c⁻¹} := by
    ext d
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hsmul x y⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hsmul _ _⟩
  have hstab : (((MulAction.stabilizer K y).map K.subtype : Subgroup (GL (Fin 6) (ZMod 2))) :
      Set (GL (Fin 6) (ZMod 2))) = {c | c ∈ K ∧ c * y = y * c} := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_map, MulAction.mem_stabilizer_iff, hsmul,
      Subgroup.coe_subtype, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, mul_inv_eq_iff_eq_mul.1 hx⟩
    · rintro ⟨hg, hc⟩
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      change g * y * g⁻¹ = y
      rw [hc, mul_inv_cancel_right]
  have h2 : Nat.card ((MulAction.stabilizer K y).map K.subtype) =
      {c | c ∈ K ∧ c * y = y * c}.ncard := by
    rw [← hstab, ← Nat.card_coe_set_eq]
    rfl
  have e := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K y)
  rw [Nat.card_prod, ← Subgroup.card_map_of_injective K.subtype_injective, h2,
    Nat.card_coe_set_eq, horb] at e
  exact e

theorem ncard_conj_z0 : {y | ∃ g : GL (Fin 6) (ZMod 2), y = g * z₀ * g⁻¹}.ncard = 234360 := by
  have h := ncard_conj_mul ⊤ z₀
  have h1 : {d | ∃ c ∈ (⊤ : Subgroup (GL (Fin 6) (ZMod 2))), d = c * z₀ * c⁻¹} =
      {y | ∃ g : GL (Fin 6) (ZMod 2), y = g * z₀ * g⁻¹} := by
    simp only [Subgroup.mem_top, true_and]
  have h2 : {c | c ∈ (⊤ : Subgroup (GL (Fin 6) (ZMod 2))) ∧ c * z₀ = z₀ * c} =
      ((Subgroup.centralizer {z₀} : Subgroup (GL (Fin 6) (ZMod 2))) :
        Set (GL (Fin 6) (ZMod 2))) := by
    ext c
    simp only [Subgroup.mem_top, true_and, Set.mem_setOf_eq, SetLike.mem_coe,
      Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact eq_comm
  have h3 : ((Subgroup.centralizer {z₀} : Subgroup (GL (Fin 6) (ZMod 2))) :
      Set (GL (Fin 6) (ZMod 2))).ncard = 86016 :=
    (Nat.card_coe_set_eq _).symm.trans card_centralizer_z0
  have key : {y | ∃ g : GL (Fin 6) (ZMod 2), y = g * z₀ * g⁻¹}.ncard * 86016 = 20158709760 := by
    rw [← h1, ← h3, ← h2, ← card_GL62, ← Subgroup.card_top]
    exact h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 86016) (key.trans (by norm_num))

theorem dg_eq_blockGL (A : GL (Fin 3) (ZMod 2)) : dg A = blockGL A 0 :=
  Units.ext (coe_dg_eq A)

theorem dg_mul_z0_eq (A : GL (Fin 3) (ZMod 2)) : dg A * z₀ = blockGL A A := by
  refine Units.ext ?_
  simp only [Units.val_mul, coe_dg_eq, coe_z0_eq, coe_blockGL, blockMat_mul, mul_one, zero_mul,
    add_zero]

def dgZSub : Subgroup (GL (Fin 6) (ZMod 2)) where
  carrier := {g | ∃ A : GL (Fin 3) (ZMod 2), g = dg A ∨ g = dg A * z₀}
  mul_mem' := by
    have hc : ∀ A : GL (Fin 3) (ZMod 2), dg A * z₀ = z₀ * dg A := fun A => by
      rw [dg_eq_blockGL]
      exact blockGL_mul_z0 A 0
    rintro _ _ ⟨A, rfl | rfl⟩ ⟨A', rfl | rfl⟩
    · exact ⟨A * A', Or.inl (map_mul dg A A').symm⟩
    · exact ⟨A * A', Or.inr (by rw [map_mul, mul_assoc])⟩
    · exact ⟨A * A', Or.inr (by rw [map_mul, mul_assoc, ← hc A', ← mul_assoc])⟩
    · refine ⟨A * A', Or.inl ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc z₀, ← hc, mul_assoc, z0_mul_self, mul_one]
  one_mem' := ⟨1, Or.inl (map_one dg).symm⟩
  inv_mem' := by
    rintro _ ⟨A, rfl | rfl⟩
    · exact ⟨A⁻¹, Or.inl (map_inv dg A).symm⟩
    · refine ⟨A⁻¹, Or.inr ?_⟩
      rw [_root_.mul_inv_rev, z0_inv, ← map_inv, dg_eq_blockGL]
      exact (blockGL_mul_z0 _ _).symm

theorem B₀_eq_dgZSub : B₀ = dgZSub := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rintro _ ⟨A, rfl⟩
    exact ⟨A, Or.inl rfl⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨1, Or.inr (by rw [map_one, one_mul])⟩
  · rintro _ ⟨A, rfl | rfl⟩
    · exact Subgroup.mem_sup_left (MonoidHom.mem_range.2 ⟨A, rfl⟩)
    · exact B₀.mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.2 ⟨A, rfl⟩))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀))

theorem mem_B₀_iff_block {g : GL (Fin 6) (ZMod 2)} :
    g ∈ B₀ ↔ ∃ A : GL (Fin 3) (ZMod 2), g = blockGL A 0 ∨ g = blockGL A A := by
  rw [B₀_eq_dgZSub]
  change (∃ A : GL (Fin 3) (ZMod 2), g = dg A ∨ g = dg A * z₀) ↔ _
  refine exists_congr fun A => ?_
  rw [dg_mul_z0_eq, dg_eq_blockGL]

theorem comm_z0_of_mem_B₀ {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ B₀) : g * z₀ = z₀ * g := by
  obtain ⟨A, rfl | rfl⟩ := mem_B₀_iff_block.1 hg <;> exact blockGL_mul_z0 _ _

theorem card_B₀ : Nat.card B₀ = 336 := by
  let ψ : GL (Fin 3) (ZMod 2) × Bool → GL (Fin 6) (ZMod 2) := fun p =>
    blockGL p.1 (if p.2 then (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) else 0)
  have hne : ∀ A : GL (Fin 3) (ZMod 2), (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 0 := fun A h =>
    one_ne_zero (by rw [← Units.mul_inv A, h, zero_mul] : (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0)
  have hψ : Function.Injective ψ := by
    rintro ⟨A, a⟩ ⟨B, b⟩ h
    obtain ⟨h1, h2⟩ := blockGL_inj h
    subst h1
    cases a <;> cases b
    · rfl
    · exact absurd h2.symm (hne A)
    · exact absurd h2 (hne A)
    · rfl
  have hset : (B₀ : Set (GL (Fin 6) (ZMod 2))) = Set.range ψ := by
    ext g
    rw [SetLike.mem_coe, mem_B₀_iff_block]
    constructor
    · rintro ⟨A, rfl | rfl⟩
      · exact ⟨(A, false), rfl⟩
      · exact ⟨(A, true), rfl⟩
    · rintro ⟨⟨A, b⟩, rfl⟩
      cases b
      · exact ⟨A, Or.inl rfl⟩
      · exact ⟨A, Or.inr rfl⟩
  have h : Nat.card B₀ = Nat.card (Set.range ψ) := by
    rw [← hset]
    rfl
  rw [h, Nat.card_range_of_injective hψ, Nat.card_prod, card_GL32, Nat.card_eq_fintype_card,
    Fintype.card_bool]

@[expose] def orb (y : GL (Fin 6) (ZMod 2)) : Set (GL (Fin 6) (ZMod 2)) :=
  {d | ∃ c ∈ B₀, d = c * y * c⁻¹}

@[expose] def Bad (y : GL (Fin 6) (ZMod 2)) : Prop :=
  ∃ e ∈ Subgroup.closure (insert y (B₀ : Set (GL (Fin 6) (ZMod 2)))), e * z₀ = z₀ * e ∧ e ∉ B₀

theorem ncard_orb_mul (y : GL (Fin 6) (ZMod 2)) :
    (orb y).ncard * {c | c ∈ B₀ ∧ c * y = y * c}.ncard = 336 := by
  rw [← card_B₀]
  exact ncard_conj_mul B₀ y

end CFSG.KC.GL62
