module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryAffineEightLinearStabilizer
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullCosetMiddleSubgroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix Module

namespace BinarySymThreeOrbit

scoped instance (priority := high) zmodTwoAddCommGroup : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

theorem finrank_symProd : finrank (ZMod 2) (↥(binarySymMatrices 3) × ZMod 2) = 7 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(binarySymMatrices 3) × ZMod 2)
  rw [Nat.card_prod, SymThreeCosetData.card_sym, Nat.card_zmod] at h
  exact Nat.pow_right_injective le_rfl (h.symm.trans (by norm_num : 64 * 2 = 2 ^ 7))

theorem f2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

@[expose] def label (v : Fin 3 → ZMod 2) : binarySymMatrices 3 :=
  ⟨vecMulVec v v, MatrixExtension.vecMulVec_self_mem_binarySymMatrices v⟩

theorem coe_label (v : Fin 3 → ZMod 2) :
    (label v : Matrix (Fin 3) (Fin 3) (ZMod 2)) = vecMulVec v v :=
  rfl

theorem diag_vecMulVec_self (v : Fin 3 → ZMod 2) : symThreeDiag (vecMulVec v v) = v := by
  funext k
  exact symThree_zmod_mul_self (v k)

theorem label_injective : Function.Injective label := fun u v h => by
  have h' := congrArg
    (fun B : binarySymMatrices 3 => symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  simpa only [coe_label, diag_vecMulVec_self] using h'

theorem label_zero : label 0 = 0 :=
  Subtype.ext (zero_vecMulVec _)

theorem vecMulVec_add_self (u v : Fin 3 → ZMod 2) :
    vecMulVec (u + v) (u + v) = vecMulVec u u + vecMulVec v v + symThreePolar u v := by
  rw [add_vecMulVec, vecMulVec_add, vecMulVec_add, symThreePolar]
  abel

theorem vecMulVec_mulVec_self (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    vecMulVec (L *ᵥ v) (L *ᵥ v) = L * vecMulVec v v * Lᵀ := by
  ext i j
  simp only [vecMulVec_apply, mulVec, dotProduct, Matrix.mul_apply, transpose_apply,
    Fin.sum_univ_three]
  ring

theorem symThreePolar_add_right (a u w : Fin 3 → ZMod 2) :
    symThreePolar a (u + w) = symThreePolar a u + symThreePolar a w := by
  rw [symThreePolar, symThreePolar, symThreePolar, vecMulVec_add, add_vecMulVec]
  abel

theorem congr_mem (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) (B : binarySymMatrices 3) :
    L * (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Lᵀ ∈ binarySymMatrices 3 := by
  rw [mem_binarySymMatrices, transpose_mul, transpose_mul, transpose_transpose,
    show (B : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = B from B.2, Matrix.mul_assoc]

theorem single_eq_label (k : Fin 3) :
    (⟨single k k 1, MatrixExtension.single_mem_binarySymMatrices k⟩ : binarySymMatrices 3) =
      label (Pi.single k 1) :=
  Subtype.ext (vecMulVec_single_single k k).symm

theorem binaryOff_eq_label (i j : Fin 3) :
    (⟨MatrixExtension.binaryOff i j, MatrixExtension.binaryOff_mem_binarySymMatrices i j⟩ :
        binarySymMatrices 3) =
      label (Pi.single i 1 + Pi.single j 1) + label (Pi.single i 1) + label (Pi.single j 1) := by
  apply Subtype.ext
  change MatrixExtension.binaryOff i j =
    vecMulVec (Pi.single i 1 + Pi.single j 1) (Pi.single i 1 + Pi.single j 1) +
      vecMulVec (Pi.single i 1) (Pi.single i 1) + vecMulVec (Pi.single j 1) (Pi.single j 1)
  rw [MatrixExtension.vecMulVec_single_add_single, vecMulVec_single_single,
    vecMulVec_single_single]
  have hi := binary_add_self (single i i (1 : ZMod 2))
  have hj := binary_add_self (single j j (1 : ZMod 2))
  calc MatrixExtension.binaryOff i j
      = single i i 1 + single j j 1 + MatrixExtension.binaryOff i j +
          single i i 1 + single j j 1 - (single i i 1 + single i i 1) -
            (single j j 1 + single j j 1) := by abel
    _ = _ := by rw [hi, hj, sub_zero, sub_zero]

theorem eq_top_of_label_mem {S : AddSubgroup (binarySymMatrices 3)} (h : ∀ v, label v ∈ S) :
    S = ⊤ := by
  have hD : ∀ k : Fin 3, (⟨single k k 1, MatrixExtension.single_mem_binarySymMatrices k⟩ :
      binarySymMatrices 3) ∈ S := fun k => by
    rw [single_eq_label]
    exact h _
  have hO : ∀ i j : Fin 3, (⟨MatrixExtension.binaryOff i j,
      MatrixExtension.binaryOff_mem_binarySymMatrices i j⟩ : binarySymMatrices 3) ∈ S :=
    fun i j => by
      rw [binaryOff_eq_label]
      exact add_mem (add_mem (h _) (h _)) (h _)
  refine eq_top_iff.mpr fun B _ => ?_
  rw [MatrixExtension.binarySym_eq_sum B]
  exact add_mem (sum_mem fun p _ => nsmul_mem (hO _ _) _) (sum_mem fun k _ => nsmul_mem (hD k) _)

theorem prod_eq_top_of_label_mem {S : AddSubgroup (binarySymMatrices 3 × ZMod 2)}
    (h : ∀ v, (label v, (1 : ZMod 2)) ∈ S) : S = ⊤ := by
  have h0 : ((0 : binarySymMatrices 3), (1 : ZMod 2)) ∈ S := by
    have := h 0
    rwa [label_zero] at this
  have hB : ∀ B : binarySymMatrices 3, (B, (0 : ZMod 2)) ∈ S := by
    have htop := eq_top_of_label_mem (S := S.comap (AddMonoidHom.inl _ _)) fun v => by
      rw [AddSubgroup.mem_comap, AddMonoidHom.inl_apply]
      have := sub_mem (h v) h0
      rwa [Prod.mk_sub_mk, sub_zero, sub_self] at this
    intro B
    have hBm : B ∈ S.comap (AddMonoidHom.inl _ _) := by
      rw [htop]
      exact AddSubgroup.mem_top B
    exact hBm
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨B, ε⟩ := x
  have hx : ((B, ε) : binarySymMatrices 3 × ZMod 2) = (B, 0) + (0, ε) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  rw [hx]
  refine add_mem (hB B) ?_
  rcases f2_cases ε with rfl | rfl
  · exact zero_mem S
  · exact h0

theorem addMonoidHom_ext_label {X : Type*} [AddMonoid X]
    {f g : (binarySymMatrices 3 × ZMod 2) →+ X} (h : ∀ v, f (label v, 1) = g (label v, 1)) :
    f = g := by
  have htop := prod_eq_top_of_label_mem (S := AddMonoidHom.eqLocus f g) h
  refine AddMonoidHom.ext fun x => ?_
  have hx : x ∈ AddMonoidHom.eqLocus f g := by
    rw [htop]
    exact AddSubgroup.mem_top x
  exact hx

@[expose] def affineSym (a : Fin 3 → ZMod 2) (L : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (B : binarySymMatrices 3) (ε : ZMod 2) : binarySymMatrices 3 :=
  ⟨L * (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Lᵀ +
      symThreePolar a (L *ᵥ symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) +
      ε • vecMulVec a a,
    add_mem (add_mem (congr_mem L B) (symThreePolar_mem _ _))
      (symThree_smul_mem ε (MatrixExtension.vecMulVec_self_mem_binarySymMatrices a))⟩

theorem coe_affineSym (a : Fin 3 → ZMod 2) (L : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (B : binarySymMatrices 3) (ε : ZMod 2) :
    (affineSym a L B ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      L * (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Lᵀ +
        symThreePolar a (L *ᵥ symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) +
        ε • vecMulVec a a :=
  rfl

@[expose] def affineAdd (a : Fin 3 → ZMod 2) (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    (binarySymMatrices 3 × ZMod 2) →+ (binarySymMatrices 3 × ZMod 2) where
  toFun x := (affineSym a L x.1 x.2, x.2)
  map_zero' := by
    refine Prod.ext (Subtype.ext ?_) rfl
    change L * 0 * Lᵀ + symThreePolar a (L *ᵥ symThreeDiag 0) + (0 : ZMod 2) • vecMulVec a a = 0
    rw [symThreeDiag_zero, mulVec_zero, symThreePolar_comm, symThreePolar_zero_left, zero_smul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]
  map_add' x y := by
    refine Prod.ext (Subtype.ext ?_) rfl
    change L * ((x.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + y.1) * Lᵀ +
        symThreePolar a (L *ᵥ symThreeDiag ((x.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + y.1)) +
        (x.2 + y.2) • vecMulVec a a =
      (L * x.1 * Lᵀ + symThreePolar a (L *ᵥ symThreeDiag x.1) + x.2 • vecMulVec a a) +
        (L * y.1 * Lᵀ + symThreePolar a (L *ᵥ symThreeDiag y.1) + y.2 • vecMulVec a a)
    rw [symThreeDiag_add, mulVec_add, symThreePolar_add_right, Matrix.mul_add, Matrix.add_mul,
      add_smul]
    abel

theorem affineAdd_apply (a : Fin 3 → ZMod 2) (L : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (B : binarySymMatrices 3) (ε : ZMod 2) : affineAdd a L (B, ε) = (affineSym a L B ε, ε) :=
  rfl

theorem affineAdd_label (a : Fin 3 → ZMod 2) (L : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (v : Fin 3 → ZMod 2) : affineAdd a L (label v, 1) = (label (a + L *ᵥ v), 1) := by
  rw [affineAdd_apply]
  refine Prod.ext (Subtype.ext ?_) rfl
  rw [coe_affineSym, coe_label, coe_label, diag_vecMulVec_self, vecMulVec_add_self,
    vecMulVec_mulVec_self, one_smul]
  abel

@[expose] noncomputable def glEquiv (L : GL (Fin 3) (ZMod 2)) :
    (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (L : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (Matrix.toLin' (↑L⁻¹ : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.toLin'_one])

theorem glEquiv_apply (L : GL (Fin 3) (ZMod 2)) (v : Fin 3 → ZMod 2) :
    glEquiv L v = (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v :=
  Matrix.toLin'_apply _ _

@[expose] noncomputable def toGL (A : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    GL (Fin 3) (ZMod 2) :=
  ⟨LinearMap.toMatrix' (A : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)),
    LinearMap.toMatrix' (A.symm : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)),
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]⟩

theorem toGL_mulVec (A : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (v : Fin 3 → ZMod 2) :
    ((toGL A : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v = A v :=
  LinearMap.toMatrix'_mulVec _ v

section Group

variable {G : Type*} [Group G] {R : Subgroup G}
  (θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2))

@[expose] def ell (v : Fin 3 → ZMod 2) : G :=
  θ.symm (.ofAdd (label v, 1))

theorem ell_mem (v : Fin 3 → ZMod 2) : ell θ v ∈ R :=
  (θ.symm _).2

theorem ell_zero : ell θ 0 = θ.symm (.ofAdd (0, 1)) := by
  rw [ell, label_zero]

theorem ell_injective : Function.Injective (ell θ) := fun u v h => by
  have h1 := θ.symm.injective (Subtype.ext h)
  exact label_injective (congrArg (fun x => (Multiplicative.toAdd x).1) h1)

include θ in
theorem comm_of_mem {r s : G} (hr : r ∈ R) (hs : s ∈ R) : r * s = s * r := by
  have h : (⟨r, hr⟩ : R) * ⟨s, hs⟩ = ⟨s, hs⟩ * ⟨r, hr⟩ :=
    θ.injective (by rw [map_mul, map_mul, mul_comm])
  exact congrArg Subtype.val h

include θ in
theorem card_R : Nat.card R = 128 := by
  rw [Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd), Nat.card_prod,
    SymThreeCosetData.card_sym, Nat.card_zmod]

structure IsAffineOrbit : Prop where
  maps : ∀ (m : G) (v : Fin 3 → ZMod 2), ∃ w, m⁻¹ * ell θ v * m = ell θ w
  faithful : ∀ m : G, (∀ v, m⁻¹ * ell θ v * m = ell θ v) → m ∈ R
  transitive : ∀ v w : Fin 3 → ZMod 2, ∃ m : G, m⁻¹ * ell θ v * m = ell θ w
  stab_linear : ∀ m : G, m⁻¹ * ell θ 0 * m = ell θ 0 → ∃ L : GL (Fin 3) (ZMod 2),
    ∀ v, m⁻¹ * ell θ v * m = ell θ ((L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)
  linear_stab : ∀ L : GL (Fin 3) (ZMod 2), ∃ m : G,
    ∀ v, m⁻¹ * ell θ v * m = ell θ ((L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v)

section Conj

variable [R.Normal]

noncomputable def conjAdd (m : G) :
    (binarySymMatrices 3 × ZMod 2) →+ (binarySymMatrices 3 × ZMod 2) where
  toFun x := Multiplicative.toAdd (θ ⟨m * θ.symm (.ofAdd x) * m⁻¹,
    Subgroup.Normal.conj_mem inferInstance _ (θ.symm _).2 m⟩)
  map_zero' := by
    have h : (⟨m * θ.symm (.ofAdd 0) * m⁻¹,
        Subgroup.Normal.conj_mem inferInstance _ (θ.symm _).2 m⟩ : R) = 1 := by
      apply Subtype.ext
      change m * (θ.symm (.ofAdd 0) : G) * m⁻¹ = 1
      rw [ofAdd_zero, map_one, OneMemClass.coe_one, mul_one, mul_inv_cancel]
    rw [h, map_one, toAdd_one]
  map_add' x y := by
    have h : (⟨m * θ.symm (.ofAdd (x + y)) * m⁻¹,
        Subgroup.Normal.conj_mem inferInstance _ (θ.symm _).2 m⟩ : R) =
        ⟨m * θ.symm (.ofAdd x) * m⁻¹, Subgroup.Normal.conj_mem inferInstance _ (θ.symm _).2 m⟩ *
          ⟨m * θ.symm (.ofAdd y) * m⁻¹,
            Subgroup.Normal.conj_mem inferInstance _ (θ.symm _).2 m⟩ := by
      apply Subtype.ext
      change m * (θ.symm (.ofAdd (x + y)) : G) * m⁻¹ =
        m * (θ.symm (.ofAdd x) : G) * m⁻¹ * (m * (θ.symm (.ofAdd y) : G) * m⁻¹)
      rw [ofAdd_add, map_mul, Subgroup.coe_mul]
      group
    rw [h, map_mul, toAdd_mul]

theorem conjAdd_spec (m : G) (x : binarySymMatrices 3 × ZMod 2) :
    m * θ.symm (.ofAdd x) * m⁻¹ = θ.symm (.ofAdd (conjAdd θ m x)) := by
  change _ = ((θ.symm (Multiplicative.ofAdd (Multiplicative.toAdd (θ _))) : R) : G)
  rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]

end Conj

namespace IsAffineOrbit

variable {θ} (H : IsAffineOrbit θ)
include H

@[expose] noncomputable def act (m : G) (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  Classical.choose (H.maps m⁻¹ v)

theorem act_spec (m : G) (v : Fin 3 → ZMod 2) : m * ell θ v * m⁻¹ = ell θ (H.act m v) := by
  have h := Classical.choose_spec (H.maps m⁻¹ v)
  calc m * ell θ v * m⁻¹ = m⁻¹⁻¹ * ell θ v * m⁻¹ := by rw [inv_inv]
    _ = ell θ (H.act m v) := h

theorem act_eq_iff {m : G} {v w : Fin 3 → ZMod 2} :
    H.act m v = w ↔ m * ell θ v * m⁻¹ = ell θ w := by
  rw [H.act_spec]
  exact (ell_injective θ).eq_iff.symm

theorem act_mul (m n : G) (v : Fin 3 → ZMod 2) : H.act (m * n) v = H.act m (H.act n v) := by
  rw [H.act_eq_iff, ← H.act_spec m, ← H.act_spec n]
  group

theorem act_one (v : Fin 3 → ZMod 2) : H.act 1 v = v := by
  rw [H.act_eq_iff, one_mul, inv_one, mul_one]

@[expose] noncomputable def permHom : G →* Equiv.Perm (Fin 3 → ZMod 2) where
  toFun m :=
    { toFun := H.act m
      invFun := H.act m⁻¹
      left_inv := fun v => by rw [← H.act_mul, inv_mul_cancel, H.act_one]
      right_inv := fun v => by rw [← H.act_mul, mul_inv_cancel, H.act_one] }
  map_one' := Equiv.ext H.act_one
  map_mul' m n := Equiv.ext fun v => H.act_mul m n v

theorem permHom_spec (m : G) (v : Fin 3 → ZMod 2) :
    m * ell θ v * m⁻¹ = ell θ (H.permHom m v) :=
  H.act_spec m v

theorem permHom_eq_iff {m : G} {v w : Fin 3 → ZMod 2} :
    H.permHom m v = w ↔ m * ell θ v * m⁻¹ = ell θ w :=
  H.act_eq_iff

theorem conj_ell (m : G) (v : Fin 3 → ZMod 2) :
    m⁻¹ * ell θ v * m = ell θ (H.permHom m⁻¹ v) := by
  have h := H.permHom_spec m⁻¹ v
  rwa [inv_inv] at h

theorem permHom_inv_eq_iff {m : G} {v w : Fin 3 → ZMod 2} :
    H.permHom m⁻¹ v = w ↔ m⁻¹ * ell θ v * m = ell θ w := by
  rw [H.conj_ell]
  exact (ell_injective θ).eq_iff.symm

theorem mem_ker_permHom {m : G} : m ∈ H.permHom.ker ↔ m ∈ R := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' : H.permHom m⁻¹ = 1 := by rw [map_inv, h, inv_one]
    refine H.faithful m fun v => ?_
    rw [H.conj_ell, h', Equiv.Perm.coe_one, id]
  · intro h
    refine Equiv.ext fun v => ?_
    rw [Equiv.Perm.coe_one, id, H.permHom_eq_iff, comm_of_mem θ h (ell_mem θ v),
      mul_inv_cancel_right]

theorem ker_permHom : H.permHom.ker = R := by
  ext m
  exact H.mem_ker_permHom

theorem range_transitive (v w : Fin 3 → ZMod 2) : ∃ k ∈ H.permHom.range, k v = w := by
  obtain ⟨m, hm⟩ := H.transitive v w
  exact ⟨H.permHom m⁻¹, ⟨m⁻¹, rfl⟩, H.permHom_inv_eq_iff.mpr hm⟩

theorem range_inf_stabilizer :
    H.permHom.range ⊓ MulAction.stabilizer (Equiv.Perm (Fin 3 → ZMod 2)) (0 : Fin 3 → ZMod 2) =
      linearPerms (Fin 3 → ZMod 2) := by
  ext σ
  constructor
  · rintro ⟨⟨m, rfl⟩, hσ0⟩
    have h0 : H.permHom (m⁻¹)⁻¹ 0 = 0 := by rw [inv_inv]; exact hσ0
    obtain ⟨L, hL⟩ := H.stab_linear m⁻¹ (H.permHom_inv_eq_iff.mp h0)
    refine ⟨glEquiv L, fun v => ?_⟩
    rw [glEquiv_apply, ← inv_inv m]
    exact H.permHom_inv_eq_iff.mpr (hL v)
  · rintro ⟨A, hA⟩
    obtain ⟨m, hmv⟩ := H.linear_stab (toGL A)
    have hσ : H.permHom m⁻¹ = σ := Equiv.ext fun v => by
      rw [hA, H.permHom_inv_eq_iff, ← toGL_mulVec]
      exact hmv v
    refine ⟨⟨m⁻¹, hσ⟩, ?_⟩
    change σ 0 = 0
    rw [hA, map_zero]

theorem range_permHom : H.permHom.range = affinePerms (Fin 3 → ZMod 2) ∧
    Nat.card H.permHom.range = 1344 := by
  have h := binary_affine_eight_full_linear_point_stabilizer (E := Fin 3 → ZMod 2)
    (Module.finrank_fin_fun (ZMod 2)) H.permHom.range H.range_transitive H.range_inf_stabilizer
  exact ⟨h.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem card_eq : Nat.card G = 128 * 1344 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup H.permHom.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange H.permHom).toEquiv,
    H.ker_permHom, card_R θ, H.range_permHom.2] at h1
  rw [h1, mul_comm]

theorem exists_affine (m : G) : ∃ (a : Fin 3 → ZMod 2) (L : GL (Fin 3) (ZMod 2)),
    ∀ v, H.permHom m v = a + (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := by
  have hm : H.permHom m ∈ affinePerms (Fin 3 → ZMod 2) := by
    rw [← H.range_permHom.1]
    exact ⟨m, rfl⟩
  obtain ⟨a, A, hA⟩ := hm
  exact ⟨a, toGL A, fun v => by rw [hA, toGL_mulVec]⟩

variable [R.Normal]

theorem conjAdd_label (m : G) (v : Fin 3 → ZMod 2) :
    conjAdd θ m (label v, 1) = (label (H.permHom m v), 1) := by
  have h := conjAdd_spec θ m (label v, 1)
  change m * ell θ v * m⁻¹ = _ at h
  rw [H.permHom_spec] at h
  exact (Multiplicative.ofAdd.injective (θ.symm.injective (Subtype.ext h))).symm

theorem conjAdd_eq {m : G} {a : Fin 3 → ZMod 2} {L : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hm : ∀ v, H.permHom m v = a + L *ᵥ v) : conjAdd θ m = affineAdd a L :=
  addMonoidHom_ext_label fun v => by rw [H.conjAdd_label, affineAdd_label, hm]

theorem conj_eq_affine {m : G} {a : Fin 3 → ZMod 2} {L : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hm : ∀ v, m⁻¹ * ell θ v * m = ell θ (a + L *ᵥ v)) (B : binarySymMatrices 3) (ε : ZMod 2) :
    m⁻¹ * (θ.symm (.ofAdd (B, ε)) : G) * m = θ.symm (.ofAdd (affineSym a L B ε, ε)) := by
  have hm' : ∀ v, H.permHom m⁻¹ v = a + L *ᵥ v := fun v => H.permHom_inv_eq_iff.mpr (hm v)
  have h := conjAdd_spec θ m⁻¹ (B, ε)
  rw [inv_inv, H.conjAdd_eq hm', affineAdd_apply] at h
  exact h

end IsAffineOrbit

end Group

end BinarySymThreeOrbit

end CFSG.LocalAnalysis.ComponentInitial
