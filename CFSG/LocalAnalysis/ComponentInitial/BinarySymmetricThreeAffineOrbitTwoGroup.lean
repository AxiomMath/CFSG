module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeAffineOrbitAction

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix Module
open scoped commutatorElement

namespace BinarySymThreeOrbit

section Layers

variable {G : Type*} [Group G] {R : Subgroup G}
  (θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2))

theorem prod_add_self (x : binarySymMatrices 3 × ZMod 2) : x + x = 0 :=
  Prod.ext (symThree_add_self x.1) (symThree_zmod_add_self x.2)

theorem symm_mul_symm (x y : binarySymMatrices 3 × ZMod 2) :
    (θ.symm (.ofAdd x) : G) * θ.symm (.ofAdd y) = θ.symm (.ofAdd (x + y)) := by
  rw [ofAdd_add, map_mul, Subgroup.coe_mul]

theorem symm_inj {x y : binarySymMatrices 3 × ZMod 2} :
    (θ.symm (.ofAdd x) : G) = θ.symm (.ofAdd y) ↔ x = y :=
  ⟨fun h => Multiplicative.ofAdd.injective (θ.symm.injective (Subtype.ext h)),
    fun h => by rw [h]⟩

theorem symm_zero : (θ.symm (.ofAdd 0) : G) = 1 := by
  rw [ofAdd_zero, map_one, OneMemClass.coe_one]

theorem symm_mul_self (x : binarySymMatrices 3 × ZMod 2) :
    (θ.symm (.ofAdd x) : G) * θ.symm (.ofAdd x) = 1 := by
  rw [symm_mul_symm, prod_add_self, symm_zero]

theorem symm_inv (x : binarySymMatrices 3 × ZMod 2) :
    (θ.symm (.ofAdd x) : G)⁻¹ = θ.symm (.ofAdd x) :=
  inv_eq_of_mul_eq_one_right (symm_mul_self θ x)

theorem symm_mem (x : binarySymMatrices 3 × ZMod 2) : (θ.symm (.ofAdd x) : G) ∈ R :=
  (θ.symm _).2

theorem exists_symm {r : G} (hr : r ∈ R) : ∃ x, r = θ.symm (.ofAdd x) :=
  ⟨Multiplicative.toAdd (θ ⟨r, hr⟩), by rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]⟩

@[expose] def layerSub (S : AddSubgroup (binarySymMatrices 3)) : Subgroup G where
  carrier := {g | ∃ B ∈ S, g = θ.symm (.ofAdd (B, 0))}
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨C, hC, rfl⟩
    exact ⟨B + C, add_mem hB hC, by rw [symm_mul_symm, Prod.mk_add_mk, add_zero]⟩
  one_mem' := ⟨0, zero_mem S, by rw [Prod.mk_zero_zero, symm_zero]⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    exact ⟨B, hB, symm_inv θ _⟩

theorem mem_layerSub {S : AddSubgroup (binarySymMatrices 3)} {g : G} :
    g ∈ layerSub θ S ↔ ∃ B ∈ S, g = θ.symm (.ofAdd (B, 0)) :=
  Iff.rfl

theorem layerSub_le (S : AddSubgroup (binarySymMatrices 3)) : layerSub θ S ≤ R := by
  rintro _ ⟨B, -, rfl⟩
  exact symm_mem θ _

theorem layerSub_mono {S T : AddSubgroup (binarySymMatrices 3)} (h : S ≤ T) :
    layerSub θ S ≤ layerSub θ T := by
  rintro _ ⟨B, hB, rfl⟩
  exact ⟨B, h hB, rfl⟩

theorem symm_mem_layerSub {S : AddSubgroup (binarySymMatrices 3)} {B : binarySymMatrices 3}
    (hB : B ∈ S) : (θ.symm (.ofAdd (B, 0)) : G) ∈ layerSub θ S :=
  ⟨B, hB, rfl⟩

theorem symm_mem_layerSub_iff {S : AddSubgroup (binarySymMatrices 3)} {B : binarySymMatrices 3}
    {ε : ZMod 2} : (θ.symm (.ofAdd (B, ε)) : G) ∈ layerSub θ S ↔ B ∈ S ∧ ε = 0 := by
  constructor
  · rintro ⟨C, hC, h⟩
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp ((symm_inj θ).mp h)
    have h1' : B = C := h1
    exact ⟨h1' ▸ hC, h2⟩
  · rintro ⟨hB, rfl⟩
    exact ⟨B, hB, rfl⟩

@[expose] def altSym : AddSubgroup (binarySymMatrices 3) :=
  (binaryAltMatrices 3).comap (binarySymMatrices 3).subtype

theorem mem_altSym {B : binarySymMatrices 3} :
    B ∈ altSym ↔ (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3 :=
  Iff.rfl

theorem mem_altSym_iff {B : binarySymMatrices 3} :
    B ∈ altSym ↔ symThreeDiag (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 := by
  rw [mem_altSym, mem_binaryAltMatrices]
  constructor
  · rintro ⟨-, h⟩
    funext k
    exact h k
  · intro h
    exact ⟨B.2, fun k => congrFun h k⟩

include θ in
theorem sq_eq_one_of_mem {x : G} (hx : x ∈ R) : x ^ 2 = 1 := by
  obtain ⟨y, rfl⟩ := exists_symm θ hx
  rw [pow_two, symm_mul_self]

theorem card_layerSub_top : Nat.card (layerSub θ ⊤ : Subgroup G) = 64 := by
  rw [← SymThreeCosetData.card_sym]
  refine (Nat.card_eq_of_bijective (fun B : binarySymMatrices 3 =>
    (⟨θ.symm (.ofAdd (B, 0)), symm_mem_layerSub θ trivial⟩ : layerSub θ ⊤)) ⟨?_, ?_⟩).symm
  · intro B C h
    have h' := congrArg Subtype.val h
    exact (Prod.ext_iff.mp ((symm_inj θ).mp h')).1
  · rintro ⟨_, B, -, rfl⟩
    exact ⟨B, rfl⟩

@[expose] noncomputable def diagR : R →* Multiplicative (Fin 3 → ZMod 2) where
  toFun x := Multiplicative.ofAdd
    (symThreeDiag ((Multiplicative.toAdd (θ x)).1 : Matrix (Fin 3) (Fin 3) (ZMod 2)))
  map_one' := by
    rw [map_one, toAdd_one, Prod.fst_zero, ZeroMemClass.coe_zero, symThreeDiag_zero, ofAdd_zero]
  map_mul' x y := by
    rw [map_mul, toAdd_mul, Prod.fst_add, AddSubgroup.coe_add, symThreeDiag_add, ofAdd_add]

end Layers

theorem vec_add_self (a : Fin 3 → ZMod 2) : a + a = 0 :=
  funext fun i => symThree_zmod_add_self (a i)

theorem affine_unique {a a' : Fin 3 → ZMod 2} {L L' : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ v, a + L *ᵥ v = a' + L' *ᵥ v) : a = a' ∧ L = L' := by
  have ha : a = a' := by simpa only [mulVec_zero, add_zero] using h 0
  subst ha
  refine ⟨rfl, ?_⟩
  ext i j
  have h1 := add_left_cancel (h (Pi.single j 1))
  have h2 := congrFun h1 i
  rwa [mulVec_single_one, mulVec_single_one, col_apply, col_apply] at h2

theorem affineSym_one_coe (a : Fin 3 → ZMod 2) (B : binarySymMatrices 3) (ε : ZMod 2) :
    (affineSym a 1 B ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + vecMulVec a (symThreeDiag B) +
        vecMulVec (symThreeDiag B) a + ε • vecMulVec a a := by
  rw [coe_affineSym, Matrix.one_mul, transpose_one, Matrix.mul_one, one_mulVec, symThreePolar]
  abel

theorem transSym_mem (a : Fin 3 → ZMod 2) (B : binarySymMatrices 3) (ε : ZMod 2) :
    (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + vecMulVec a (symThreeDiag B) +
      vecMulVec (symThreeDiag B) a + ε • vecMulVec a a ∈ binarySymMatrices 3 :=
  affineSym_one_coe a B ε ▸ (affineSym a 1 B ε).2

theorem affineSym_zero_coe (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) (B : binarySymMatrices 3)
    (ε : ZMod 2) :
    (affineSym 0 L B ε : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      L * (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Lᵀ := by
  rw [coe_affineSym, symThreePolar_zero_left, zero_vecMulVec, smul_zero, add_zero, add_zero]

theorem finrank_vec : finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 :=
  Module.finrank_fin_fun (ZMod 2)

section Group

variable {G : Type*} [Group G] {R : Subgroup G}
  {θ : R ≃* Multiplicative (binarySymMatrices 3 × ZMod 2)}

namespace IsAffineOrbit

variable (H : IsAffineOrbit θ)
include H

theorem exists_affine_right (m : G) : ∃ (a : Fin 3 → ZMod 2) (L : GL (Fin 3) (ZMod 2)),
    ∀ v, m⁻¹ * ell θ v * m = ell θ (a + (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := by
  obtain ⟨a, L, h⟩ := H.exists_affine m⁻¹
  exact ⟨a, L, fun v => by rw [H.conj_ell, h]⟩

@[expose] noncomputable def transSub : Subgroup G :=
  (translationPerms (Fin 3 → ZMod 2)).comap H.permHom

theorem mem_transSub_iff_permHom {m : G} :
    m ∈ H.transSub ↔ ∃ a, ∀ v, H.permHom m v = a + v :=
  Iff.rfl

theorem le_transSub : R ≤ H.transSub := fun r hr =>
  ⟨0, fun v => by rw [(H.mem_ker_permHom.mpr hr : H.permHom r = 1), zero_add]; rfl⟩

theorem permHom_transSub (d : H.transSub) (v : Fin 3 → ZMod 2) :
    H.permHom d v = v + H.permHom d 0 := by
  obtain ⟨a, ha⟩ := (H.mem_transSub_iff_permHom).mp d.2
  rw [ha, ha, add_zero, add_comm]

theorem transSub_normal : H.transSub.Normal := by
  refine ⟨fun d hd g => (H.mem_transSub_iff_permHom).mpr ?_⟩
  obtain ⟨b, L, hg⟩ := H.exists_affine g
  obtain ⟨a, ha⟩ := (H.mem_transSub_iff_permHom).mp hd
  refine ⟨(L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a, fun v => ?_⟩
  have hw : H.permHom g (H.permHom g⁻¹ v) = v := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  rw [hg] at hw
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha, hg, mulVec_add]
  calc b + ((L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a +
        (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ H.permHom g⁻¹ v)
      = (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a +
          (b + (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ H.permHom g⁻¹ v) := by abel
    _ = (L : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a + v := by rw [hw]

@[expose] noncomputable def transVec : H.transSub →* Multiplicative (Fin 3 → ZMod 2) where
  toFun d := Multiplicative.ofAdd (H.permHom d 0)
  map_one' := by
    rw [OneMemClass.coe_one, map_one, Equiv.Perm.one_apply, ofAdd_zero]
  map_mul' d e := by
    rw [Subgroup.coe_mul, map_mul, Equiv.Perm.mul_apply, H.permHom_transSub d, ← ofAdd_add,
      add_comm]

theorem transVec_apply (d : H.transSub) :
    Multiplicative.toAdd (H.transVec d) = H.permHom d 0 :=
  rfl

theorem permHom_eq_add_transVec (d : H.transSub) (v : Fin 3 → ZMod 2) :
    H.permHom d v = v + Multiplicative.toAdd (H.transVec d) :=
  H.permHom_transSub d v

theorem conj_ell_transSub (d : H.transSub) (v : Fin 3 → ZMod 2) :
    (d : G)⁻¹ * ell θ v * d = ell θ (v + Multiplicative.toAdd (H.transVec d)) := by
  refine H.permHom_inv_eq_iff.mp ?_
  rw [map_inv, Equiv.Perm.inv_eq_iff_eq, H.permHom_eq_add_transVec, add_assoc, vec_add_self,
    add_zero]

theorem transVec_surjective : Function.Surjective H.transVec := by
  intro a
  have hmem : Equiv.addLeft (Multiplicative.toAdd a) ∈ affinePerms (Fin 3 → ZMod 2) :=
    ⟨Multiplicative.toAdd a, LinearEquiv.refl _ _, fun v => rfl⟩
  rw [← H.range_permHom.1] at hmem
  obtain ⟨m, hm⟩ := hmem
  have hmD : m ∈ H.transSub := ⟨Multiplicative.toAdd a, fun v => by rw [hm]; rfl⟩
  refine ⟨⟨m, hmD⟩, ?_⟩
  change Multiplicative.ofAdd (H.permHom m 0) = a
  rw [hm]
  change Multiplicative.ofAdd (Multiplicative.toAdd a + 0) = a
  rw [add_zero, ofAdd_toAdd]

theorem ker_transVec : H.transVec.ker = R.subgroupOf H.transSub := by
  ext d
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← H.mem_ker_permHom, MonoidHom.mem_ker]
  constructor
  · intro h
    refine Equiv.ext fun v => ?_
    rw [H.permHom_eq_add_transVec, h, toAdd_one, add_zero]
    rfl
  · intro h
    change Multiplicative.ofAdd (H.permHom d 0) = 1
    rw [h, Equiv.Perm.one_apply, ofAdd_zero]

theorem permHom_conj_zero (g d : G) (hd : d ∈ H.transSub) {L : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    {b : Fin 3 → ZMod 2} (hg : ∀ v, H.permHom g v = b + L *ᵥ v) :
    H.permHom (g * d * g⁻¹) 0 = L *ᵥ H.permHom d 0 := by
  have hw : H.permHom g (H.permHom g⁻¹ 0) = 0 := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
  rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    H.permHom_transSub ⟨d, hd⟩, hg, mulVec_add]
  rw [hg] at hw
  calc b + (L *ᵥ H.permHom g⁻¹ 0 + L *ᵥ H.permHom d 0)
      = (b + L *ᵥ H.permHom g⁻¹ 0) + L *ᵥ H.permHom d 0 := by rw [add_assoc]
    _ = L *ᵥ H.permHom d 0 := by rw [hw, zero_add]

theorem card_transSub [Finite G] : Nat.card H.transSub = 1024 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup H.transVec.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ H.transVec_surjective).toEquiv,
    H.ker_transVec, Nat.card_congr (Subgroup.subgroupOfEquivOfLe H.le_transSub).toEquiv,
    card_R θ] at h1
  rw [h1]
  have h8 : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [h8]

@[expose] noncomputable def linPartFun (m : G) : GL (Fin 3) (ZMod 2) :=
  Classical.choose (Classical.choose_spec (H.exists_affine m))

theorem permHom_eq_linPart (m : G) (v : Fin 3 → ZMod 2) :
    H.permHom m v = H.permHom m 0 + (H.linPartFun m : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v := by
  have h := Classical.choose_spec (Classical.choose_spec (H.exists_affine m))
  rw [h v, h 0, mulVec_zero, add_zero]
  rfl

theorem linPartFun_unique {m : G} {a : Fin 3 → ZMod 2} {L : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ v, H.permHom m v = a + L *ᵥ v) :
    (H.linPartFun m : Matrix (Fin 3) (Fin 3) (ZMod 2)) = L :=
  (affine_unique fun v => (H.permHom_eq_linPart m v).symm.trans (h v)).2

@[expose] noncomputable def linPart : G →* GL (Fin 3) (ZMod 2) where
  toFun := H.linPartFun
  map_one' := Units.ext (H.linPartFun_unique (a := 0) fun v => by
    rw [map_one, Equiv.Perm.one_apply, Units.val_one, one_mulVec, zero_add])
  map_mul' m n := Units.ext (H.linPartFun_unique (a := H.permHom m (H.permHom n 0)) fun v => by
    rw [map_mul, Equiv.Perm.mul_apply, H.permHom_eq_linPart n v, H.permHom_eq_linPart m,
      H.permHom_eq_linPart m (H.permHom n 0), mulVec_add, Units.val_mul, ← mulVec_mulVec,
      add_assoc])

theorem permHom_eq_linPart' (m : G) (v : Fin 3 → ZMod 2) :
    H.permHom m v = H.permHom m 0 + (H.linPart m : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v :=
  H.permHom_eq_linPart m v

theorem linPart_eq {m : G} {a : Fin 3 → ZMod 2} {L : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ v, H.permHom m v = a + L *ᵥ v) :
    (H.linPart m : Matrix (Fin 3) (Fin 3) (ZMod 2)) = L :=
  H.linPartFun_unique h

theorem linPart_inv_eq {m : G} {b : Fin 3 → ZMod 2} {L : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ v, m⁻¹ * ell θ v * m = ell θ (b + L *ᵥ v)) :
    (H.linPart m⁻¹ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = L :=
  H.linPart_eq fun v => H.permHom_inv_eq_iff.mpr (h v)

theorem permHom_conj_zero' (g d : G) (hd : d ∈ H.transSub) :
    H.permHom (g * d * g⁻¹) 0 = (H.linPart g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
      H.permHom d 0 :=
  H.permHom_conj_zero g d hd (H.permHom_eq_linPart' g)

theorem mem_R_of_permHom_zero {x : G} (hx : x ∈ H.transSub) (h0 : H.permHom x 0 = 0) :
    x ∈ R := by
  rw [← H.mem_ker_permHom, MonoidHom.mem_ker]
  refine Equiv.ext fun v => ?_
  rw [H.permHom_transSub ⟨x, hx⟩, h0, add_zero]
  rfl

theorem permHom_mul_zero {d e : G} (hd : d ∈ H.transSub) :
    H.permHom (d * e) 0 = H.permHom e 0 + H.permHom d 0 := by
  rw [map_mul, Equiv.Perm.mul_apply, H.permHom_transSub ⟨d, hd⟩]

variable [R.Normal]

theorem conj_symm_trans {d : G} {a : Fin 3 → ZMod 2}
    (hd : ∀ v, d⁻¹ * ell θ v * d = ell θ (v + a)) (B : binarySymMatrices 3) (ε : ZMod 2) :
    d⁻¹ * (θ.symm (.ofAdd (B, ε)) : G) * d = θ.symm (.ofAdd
      (⟨(B : Matrix (Fin 3) (Fin 3) (ZMod 2)) + vecMulVec a (symThreeDiag B) +
        vecMulVec (symThreeDiag B) a + ε • vecMulVec a a, transSym_mem a B ε⟩, ε)) := by
  rw [H.conj_eq_affine (a := a) (L := 1) (fun v => by rw [hd, one_mulVec, add_comm]) B ε]
  congr 4
  exact Subtype.ext (affineSym_one_coe a B ε)

theorem conj_symm_linear {m : G} {L : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (hm : ∀ v, m⁻¹ * ell θ v * m = ell θ (L *ᵥ v)) (B : binarySymMatrices 3) (ε : ZMod 2) :
    m⁻¹ * (θ.symm (.ofAdd (B, ε)) : G) * m =
      θ.symm (.ofAdd (⟨L * (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Lᵀ, congr_mem L B⟩, ε)) := by
  rw [H.conj_eq_affine (a := 0) (L := L) (fun v => by rw [hm, zero_add]) B ε]
  congr 4
  exact Subtype.ext (affineSym_zero_coe L B ε)

theorem conj_symm (g : G) (B : binarySymMatrices 3) (ε : ZMod 2) :
    ∃ B' : binarySymMatrices 3, g * (θ.symm (.ofAdd (B, ε)) : G) * g⁻¹ =
      θ.symm (.ofAdd (B', ε)) ∧ (B ∈ altSym → ε = 0 → B' ∈ altSym) := by
  obtain ⟨a, L, hL⟩ := H.exists_affine_right g⁻¹
  refine ⟨affineSym a L B ε, ?_, fun hB hε => ?_⟩
  · have h := H.conj_eq_affine hL B ε
    rwa [inv_inv] at h
  · rw [mem_altSym_iff] at hB ⊢
    subst hε
    rw [coe_affineSym, zero_smul, add_zero, hB, mulVec_zero, symThreePolar_comm,
      symThreePolar_zero_left, add_zero, symThreeDiag_congr _ _ B.2, hB, mulVec_zero]

omit [R.Normal] in
theorem normal_pGroup_le {N : Subgroup G} (hN : N.Normal) (hP : IsPGroup 2 N) :
    N ≤ H.transSub := by
  have h := binary_affine_eight_full_linear_point_stabilizer (E := Fin 3 → ZMod 2)
    finrank_vec H.permHom.range H.range_transitive H.range_inf_stabilizer
  have hnorm : ((N.map H.permHom).subgroupOf H.permHom.range).Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨g, hg⟩ := k.2
    refine ⟨g * n * g⁻¹, hN.conj_mem n hn g, ?_⟩
    rw [map_mul, map_mul, map_inv, hg, hnx]
    rfl
  have hle := h.2.2.2.2.2.2.2.2.1 (N.map H.permHom) (Subgroup.map_le_range _ _) hnorm
    (hP.map H.permHom)
  exact fun n hn => hle ⟨n, hn, rfl⟩

omit [R.Normal] in
theorem transSub_eq_pCore [Finite G] : H.transSub = CFSG.Assembly.pCore 2 G := by
  refine le_antisymm (CFSG.Assembly.Dichotomy.CentralizerContainment.le_pCore_assembly
    H.transSub_normal (IsPGroup.of_card (n := 10) ?_)) (H.normal_pGroup_le
      (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly 2 G)
      (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_isPGroup_assembly 2 G))
  rw [H.card_transSub]
  norm_num

end IsAffineOrbit

end Group

end BinarySymThreeOrbit

end CFSG.LocalAnalysis.ComponentInitial
