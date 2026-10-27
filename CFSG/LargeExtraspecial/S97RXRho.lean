module

public import CFSG.LargeExtraspecial.S97RXLam
public import CFSG.LargeExtraspecial.S111BA5Tv
public import CFSG.LargeExtraspecial.S97RXAbs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G} {h k : G}
  {m : S.M} {O : Subgroup S.O}

variable (S k m) in
@[expose] noncomputable def rhoX97 : ↥(S9.X97 S k m) →*
    (↥(S9.Ut S k (S9.X97 S k m)) ≃ₗ[ZMod 2] ↥(S9.Ut S k (S9.X97 S k m))) :=
  S4.restrictHom (S.O.subtype.comp (S9.X97 S k m).subtype) (S9.Ut S k (S9.X97 S k m))
    (fun x _ hu => S9.apply_mem_Ut x.2 hu)

theorem rhoX97_eq_one_iff (x : ↥(S9.X97 S k m)) :
    rhoX97 S k m x = 1 ↔
      ∀ u ∈ S9.Ut S k (S9.X97 S k m), ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u :=
  S4.restrictHom_eq_one_iff _ _ _ x

namespace H97

variable (X : S9.Hyp97 S k m O) (hodd : Odd (Nat.card (center (S9.Q97 S k m))))
include X hodd

theorem fix_iff (u y : ↥(S9.X97 S k m)) :
    ((u : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹))) =
        ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) ↔
      pi97 S k m u ∈
        normalizer (conjSubgroup (pi97 S k m y) (T97 S k m k) : Set (Lam97 S k m)) := by
  have e : (pi97 S k m y)⁻¹ * pi97 S k m u * pi97 S k m y = pi97 S k m (y⁻¹ * u * y) := by
    simp only [map_mul, map_inv]
  refine Iff.trans ?_ (mem_normalizer_conj_iff97.trans
    (congrArg (fun w => w ∈ normalizer (T97 S k m k : Set (Lam97 S k m))) e).to_iff).symm
  rw [H97.pi97_mem_normalizer_iff X hodd le_sup_left X.hyp4 X.cons]
  have hyu : ((y⁻¹ * u * y : ↥(S9.X97 S k m)) : S.O) = (y : S.O)⁻¹ * u * y := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hyu]
  constructor
  · intro hfix
    have hM : (y : S.O)⁻¹ * u * y ∈ S.Mbar :=
      S9.X97_le_Mbar (S := S) (g := k) (k := m) (y⁻¹ * u * y).2
    have h1 : (((y : S.O)⁻¹ * u * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) =
        S.cl (k * S.z * k⁻¹) := by
      rw [coe_mul_apply, coe_mul_apply, hfix, inv_apply_apply_O]
    have h2 := mem_normalizer_of_fix X.hyp4.conj_mem X.hyp4.conj_ne (h := 1) hM (by
      simp only [OneMemClass.coe_one, one_mul]
      exact h1)
    simpa only [OneMemClass.coe_one, one_mul] using h2
  · intro hN
    have h1 := fix_of_mem_normalizer X.hyp4 hN
    rw [coe_mul_apply, coe_mul_apply] at h1
    have h2 := congrArg ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [apply_inv_apply_O] at h2

theorem fix_of_pi97_eq_one {x : ↥(S9.X97 S k m)} (hx : pi97 S k m x = 1) {u : S.Qt}
    (hu : u ∈ S9.Ut S k (S9.X97 S k m)) : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
  have hgen : ∀ y : ↥(S9.X97 S k m), ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹))) =
      ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) := fun y =>
    (H97.fix_iff X hodd x y).mpr ((congrArg (fun w => w ∈ normalizer
      (conjSubgroup (pi97 S k m y) (T97 S k m k) : Set (Lam97 S k m))) hx).mpr (one_mem _))
  set W : Submodule (ZMod 2) S.Qt :=
    LinearMap.ker ((((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - LinearMap.id)
    with hW
  have hle : S9.Ut S k (S9.X97 S k m) ≤ W := by
    rw [S9.Ut, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, hW, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact hgen ⟨y, hy⟩
  have h1 := hle hu
  rwa [hW, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h1

@[expose] noncomputable def rhoLam97 : Lam97 S k m →*
    (↥(S9.Ut S k (S9.X97 S k m)) ≃ₗ[ZMod 2] ↥(S9.Ut S k (S9.X97 S k m))) :=
  QuotientGroup.lift (center (S9.Q97 S k m))
    (QuotientGroup.lift (CFSG.pCore 2 ↥(S9.X97 S k m)) (rhoX97 S k m) (fun x hx => by
      rw [MonoidHom.mem_ker, rhoX97_eq_one_iff]
      intro u hu
      have hxO : (x : S.O) ∈ O := by
        rw [← X.subgroupOf_eq_pCore] at hx
        exact mem_subgroupOf.mp hx
      exact X.fix_Ut hxO hu))
    (fun c hc => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
      rw [MonoidHom.mem_ker, QuotientGroup.lift_mk, rhoX97_eq_one_iff]
      intro u hu
      exact H97.fix_of_pi97_eq_one X hodd ((QuotientGroup.eq_one_iff _).mpr hc) hu)

end H97

theorem Pair111.cl_ne {k' : G} (P : Pair111 S g A h k k') :
    S.cl (k * S.z * k⁻¹) ≠ S.cl (k' * S.z * k'⁻¹) := by
  intro he
  have h1 : S.cl (k' * S.z * k'⁻¹) ∈ S.clSub A := he ▸ S.cl_mem_clSub P.mem P.memQ
  have h2 : S.cl (k' * S.z * k'⁻¹) ∈ S.clSub (A.map (MulAut.conj h).toMonoidHom) :=
    S.cl_mem_clSub P.mem' P.memQ'
  exact cl_conj_z_ne_zero S P.memQ' P.ne' (P.eq_zero_of_mem_clSub h1 h2)

end CFSG.LargeExtraspecial.S11
