module

public import CFSG.CGT.Stroth77.Section224

public section

namespace CFSG.CGT.Stroth77

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

instance instIsMulCommutativeD (Z : StrothDatum X) : IsMulCommutative ↥Z.D :=
  Z.dataD.isMulCommutative

instance instIsMulCommutativeOmegaInOne (Z : StrothDatum X) :
    IsMulCommutative ↥(omegaIn 1 Z.D) :=
  IsMulCommutative.of_comm fun a b => Subtype.ext (by
    change (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm
        ⟨(a : G), omegaIn_le 1 Z.D a.2⟩ ⟨(b : G), omegaIn_le 1 Z.D b.2⟩))

@[expose]
def conjOnD (Z : StrothDatum X) (x : G) (hx : x ∈ Z.normalizerIn) : Z.D →* Z.D where
  toFun d :=
    ⟨x * (d : G) * x⁻¹,
      (Subgroup.mem_normalizer_iff.mp hx.2 (d : G)).mp d.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subtype.coe_mk]
    group

@[expose]
def deviationMul (Z : StrothDatum X) (x : G) (hx : x ∈ Z.centralizerInMho) :
    Z.D →* ↥(omegaIn 1 Z.D) where
  toFun d :=
    ⟨((conjOnD Z x hx.1 d) * d⁻¹ : Z.D), by
      have h := commutator_mem_omegaIn_one_of_mem_centralizerInMho hx d.2
      simpa [conjOnD, Subgroup.coe_mul, Subgroup.coe_inv] using h⟩
  map_one' := by
    apply Subtype.ext
    simp [conjOnD]
  map_mul' a b := by
    apply Subtype.ext
    haveI : IsMulCommutative Z.D := Z.dataD.isMulCommutative
    have h : ((conjOnD Z x hx.1 (a * b)) * (a * b)⁻¹ : Z.D) =
        (((conjOnD Z x hx.1 a) * a⁻¹) * ((conjOnD Z x hx.1 b) * b⁻¹) : Z.D) := by
      rw [map_mul]
      have h1 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
        rw [mul_inv_rev]
        exact mul_comm' b⁻¹ a⁻¹
      rw [h1]
      calc conjOnD Z x hx.1 a * conjOnD Z x hx.1 b * (a⁻¹ * b⁻¹)
          = conjOnD Z x hx.1 a * a⁻¹ * (conjOnD Z x hx.1 b * b⁻¹) := by
            ac_rfl
        _ = (conjOnD Z x hx.1 a * a⁻¹) * (conjOnD Z x hx.1 b * b⁻¹) := rfl
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val h

@[simp]
theorem deviationMul_apply (Z : StrothDatum X) (x : G)
    (hx : x ∈ Z.centralizerInMho) (d : Z.D) :
    ((deviationMul Z x hx d : ↥(omegaIn 1 Z.D)) : G) =
      x * (d : G) * x⁻¹ * (d : G)⁻¹ :=
  rfl

@[expose]
def deviation (Z : StrothDatum X) (x : G) (hx : x ∈ Z.centralizerInMho) :
    Additive Z.D →+ Additive ↥(omegaIn 1 Z.D) :=
  (deviationMul Z x hx).toAdditive

@[simp]
theorem deviation_apply (Z : StrothDatum X) (x : G)
    (hx : x ∈ Z.centralizerInMho) (d : Z.D) :
    ((deviation Z x hx (Additive.ofMul d)).toMul : G) =
      x * (d : G) * x⁻¹ * (d : G)⁻¹ :=
  rfl

theorem deviation_sq_eq_zero (Z : StrothDatum X) (x : G)
    (hx : x ∈ Z.centralizerInMho) (d : Z.D) :
    deviation Z x hx (Additive.ofMul (d * d)) = 0 := by
  have hd2 : ((d : G) * (d : G)) ∈ mhoOne Z.D := by
    simpa [pow_two] using
      CFSG.GroupTheory.HuppertProduct.pow_mem_mho (S := Z.D) (n := 2) d.2
  have hcomm : ((d : G) * (d : G)) * x = x * ((d : G) * (d : G)) :=
    Subgroup.mem_centralizer_iff.mp hx.2 ((d : G) * (d : G)) hd2
  have hxdx : (x * (d : G) * x⁻¹) * (x * (d : G) * x⁻¹) = (d : G) * (d : G) := by
    have h1 : x * ((d : G) * (d : G)) * x⁻¹ = (d : G) * (d : G) := by
      rw [← hcomm]
      group
    calc (x * (d : G) * x⁻¹) * (x * (d : G) * x⁻¹)
        = x * ((d : G) * (d : G)) * x⁻¹ := by group
      _ = (d : G) * (d : G) := h1
  have hconj : x * ((d : G) * (d : G)) * x⁻¹ = (d : G) * (d : G) := by
    calc x * ((d : G) * (d : G)) * x⁻¹
        = (x * (d : G) * x⁻¹) * (x * (d : G) * x⁻¹) := by group
      _ = (d : G) * (d : G) := hxdx
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [deviation_apply]
  simp only [toMul_zero, Subgroup.coe_one, Subgroup.coe_mul]
  rw [hconj]
  group

instance instNormalSubgroupOfD (Z : StrothDatum X) :
    (Z.D.subgroupOf Z.centralizerInMho).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer Z.D_le_centralizerInMho]
  intro x hx
  exact hx.1.2

end CFSG.CGT.Stroth77
