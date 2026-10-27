module

public import CFSG.LargeExtraspecial.S111ABasic
public import CFSG.LargeExtraspecial.S111CBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

variable (S) in
@[expose] def ptFix (W : Submodule (ZMod 2) S.Qt) : Subgroup S.O where
  carrier := {x | ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w}
  mul_mem' := fun {x y} hx hy w hw => by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy w hw, hx w hw]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {x} hx w hw => by
    conv_lhs => rw [← hx w hw]
    exact LinearEquiv.symm_apply_apply _ w

theorem mem_ptFix {W : Submodule (ZMod 2) S.Qt} {x : S.O} :
    x ∈ ptFix S W ↔ ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := Iff.rfl

theorem mem_normalizer_ptFix {W : Submodule (ZMod 2) S.Qt} {x : S.O}
    (h1 : ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (h2 : ∀ w ∈ W, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) :
    x ∈ normalizer (ptFix S W : Set S.O) := by
  rw [mem_normalizer_iff]
  intro y
  have e1 : ∀ w, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w :=
    fun w => by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have e2 : ∀ w, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w :=
    fun w => by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  constructor
  · intro hy w hw
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
    rw [hy _ (h2 w hw), e2]
  · intro hy w hw
    have h := hy _ (h1 w hw)
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, e1] at h
    have h' := congrArg ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h
    rwa [e1, e1] at h'

variable {g : G} {A : Subgroup G}

variable (S) in
@[expose] noncomputable def Kbar (A : Subgroup G) (k : G) : Subgroup S.O :=
  S.Lbar k ⊓ ptFix S (S.clSub A)

variable (S) in
@[expose] noncomputable def Ybar (A : Subgroup G) : Subgroup S.O :=
  sSup {X | ∃ k : G, k * S.z * k⁻¹ ∈ A ∧ k * S.z * k⁻¹ ≠ S.z ∧ X = Kbar S A k}

theorem Kbar_le_Ybar {k : G} (hk : k * S.z * k⁻¹ ∈ A) (hkz : k * S.z * k⁻¹ ≠ S.z) :
    Kbar S A k ≤ Ybar S A :=
  le_sSup ⟨k, hk, hkz, rfl⟩

theorem Ybar_le_Mbar : Ybar S A ≤ S.Mbar :=
  sSup_le fun _ ⟨k, _, _, e⟩ => e ▸ inf_le_left.trans (S.Lbar_le_Mbar k)

theorem isPGroup_Kbar (hA : IncClosed S A) {k : G} (hk : k * S.z * k⁻¹ ∈ A) :
    IsPGroup 2 (Kbar S A k) := by
  have := S.isElementaryAbelian_Lbar (hA.le_QG hk)
  exact (CFSG.IsElementaryAbelian.isPGroup 2 (S.Lbar k)).to_le inf_le_left

theorem mem_normalizer_Lbar_of_fix {k j : G} {x : S.O} (hx : x ∈ S.Lbar k)
    (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hjz : j * S.z * j⁻¹ ≠ S.z)
    (hfix : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (j * S.z * j⁻¹)) = S.cl (j * S.z * j⁻¹)) :
    x ∈ normalizer (S.Lbar j : Set S.O) := by
  obtain ⟨y, hy, rfl⟩ := (mem_Lbar S).mp hx
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  change (S.Lbar j).map (MulAut.conj (S.ρ y)).toMonoidHom = S.Lbar j
  rw [← Lbar_mul]
  refine Lbar_eq_of_cl_eq S hjQ hjz (conj_mem_QG' S y.2 hjQ) ?_
  rw [← ρ_cl_conj_z S y hjQ, hfix]

theorem Kbar_le_normalizer (hA : IncClosed S A) {k j : G} (hj : j * S.z * j⁻¹ ∈ A)
    (hjz : j * S.z * j⁻¹ ≠ S.z) : Kbar S A k ≤ normalizer (Kbar S A j : Set S.O) := by
  intro x hx
  refine mem_normalizer_inf ?_ (le_normalizer hx.2)
  exact mem_normalizer_Lbar_of_fix hx.1 (hA.le_QG hj) hjz
    (hx.2 _ (S.cl_mem_clSub hj (hA.le_QG hj)))

theorem isPGroup_Ybar (hA : IncClosed S A) : IsPGroup 2 (Ybar S A) := by
  refine isPGroup_sSup_of_le_normalizer ?_ ?_
  · rintro _ ⟨k, hk, -, rfl⟩
    exact isPGroup_Kbar hA hk
  · rintro _ ⟨k, -, -, rfl⟩ _ ⟨j, hj, hjz, rfl⟩
    exact Kbar_le_normalizer hA hj hjz

end CFSG.LargeExtraspecial.S11
