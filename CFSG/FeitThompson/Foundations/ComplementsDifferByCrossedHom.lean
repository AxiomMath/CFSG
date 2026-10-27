module

public import Mathlib.GroupTheory.Complement
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import CFSG.FeitThompson.Foundations.QuotientActsOnAbelianNormal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open IsMulCommutative

variable {G : Type*} [Group G] {A H K : Subgroup G} [A.Normal]

theorem mk_coe_quotientMulEquiv (hH : H.IsComplement' A) (x : G ⧸ A) :
    ((hH.QuotientMulEquiv x : G) : G ⧸ A) = x := by
  rw [Subgroup.IsComplement'.QuotientMulEquiv_apply]
  exact hH.quotientGroupMk_leftQuotientEquiv x

theorem quotientMulEquiv_mk_coe (hH : H.IsComplement' A) (h : ↥H) :
    hH.QuotientMulEquiv ((h : G) : G ⧸ A) = h := by
  obtain ⟨x, rfl⟩ := hH.QuotientMulEquiv.surjective h
  rw [mk_coe_quotientMulEquiv]

noncomputable def complementDiff (hH : H.IsComplement' A) (hK : K.IsComplement' A) (x : G ⧸ A) :
    ↥A :=
  ⟨(hK.QuotientMulEquiv x : G) * (hH.QuotientMulEquiv x : G)⁻¹, by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_coe_quotientMulEquiv,
      mk_coe_quotientMulEquiv, mul_inv_cancel]⟩

@[simp] theorem coe_complementDiff (hH : H.IsComplement' A) (hK : K.IsComplement' A) (x : G ⧸ A) :
    (complementDiff hH hK x : G)
      = (hK.QuotientMulEquiv x : G) * (hH.QuotientMulEquiv x : G)⁻¹ := (rfl)

theorem complementDiff_mul_section (hH : H.IsComplement' A) (hK : K.IsComplement' A) (x : G ⧸ A) :
    (complementDiff hH hK x : G) * (hH.QuotientMulEquiv x : G) = (hK.QuotientMulEquiv x : G) := by
  rw [coe_complementDiff, inv_mul_cancel_right]

theorem complementDiff_mul_section_mem (hH : H.IsComplement' A) (hK : K.IsComplement' A)
    (x : G ⧸ A) : (complementDiff hH hK x : G) * (hH.QuotientMulEquiv x : G) ∈ K := by
  rw [complementDiff_mul_section]; exact (hK.QuotientMulEquiv x).2

@[simp] theorem complementDiff_one (hH : H.IsComplement' A) (hK : K.IsComplement' A) :
    complementDiff hH hK 1 = 1 := by
  ext; rw [coe_complementDiff, map_one, map_one]; simp

theorem coe_eq_range_complementDiff (hH : H.IsComplement' A) (hK : K.IsComplement' A) :
    (K : Set G) = Set.range fun x : G ⧸ A =>
      (complementDiff hH hK x : G) * (hH.QuotientMulEquiv x : G) := by
  ext g
  simp only [Set.mem_range, complementDiff_mul_section, SetLike.mem_coe]
  refine ⟨fun hg => ⟨(g : G ⧸ A), ?_⟩, ?_⟩
  · rw [quotientMulEquiv_mk_coe hK ⟨g, hg⟩]
  · rintro ⟨x, rfl⟩
    exact (hK.QuotientMulEquiv x).2

theorem eq_complementDiff (hH : H.IsComplement' A) (hK : K.IsComplement' A) {f : G ⧸ A → ↥A}
    (hf : (K : Set G) = Set.range fun x : G ⧸ A => (f x : G) * (hH.QuotientMulEquiv x : G)) :
    f = complementDiff hH hK := by
  funext x
  have hmem : (f x : G) * (hH.QuotientMulEquiv x : G) ∈ K := by
    rw [← SetLike.mem_coe, hf]; exact ⟨x, rfl⟩
  have hq : (((f x : G) * (hH.QuotientMulEquiv x : G) : G) : G ⧸ A) = x := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (f x).2, one_mul,
      mk_coe_quotientMulEquiv]
  have h1 := quotientMulEquiv_mk_coe hK ⟨_, hmem⟩
  rw [hq] at h1
  have h2 : (hK.QuotientMulEquiv x : G) = (f x : G) * (hH.QuotientMulEquiv x : G) :=
    congrArg Subtype.val h1
  ext
  rw [coe_complementDiff, h2, mul_inv_cancel_right]

theorem existsUnique_complementDiff (hH : H.IsComplement' A) (hK : K.IsComplement' A) :
    ∃! f : G ⧸ A → ↥A, (K : Set G) = Set.range fun x : G ⧸ A =>
      (f x : G) * (hH.QuotientMulEquiv x : G) :=
  ⟨complementDiff hH hK, coe_eq_range_complementDiff hH hK,
    fun _ hf => eq_complementDiff hH hK hf⟩

variable [IsMulCommutative ↥A]

theorem coe_smul_quotientMulEquiv (hH : H.IsComplement' A) (x : G ⧸ A) (a : ↥A) :
    ((x • a : ↥A) : G)
      = (hH.QuotientMulEquiv x : G) * (a : G) * (hH.QuotientMulEquiv x : G)⁻¹ := by
  conv_lhs => rw [← mk_coe_quotientMulEquiv hH x]
  rw [coe_quotientMk_smul]

theorem complementDiff_mul (hH : H.IsComplement' A) (hK : K.IsComplement' A) (x y : G ⧸ A) :
    complementDiff hH hK (x * y)
      = complementDiff hH hK x * x • complementDiff hH hK y := by
  ext
  rw [Subgroup.coe_mul, coe_smul_quotientMulEquiv hH, coe_complementDiff, coe_complementDiff,
    coe_complementDiff, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  group

theorem ofMul_complementDiff_mul (hH : H.IsComplement' A) (hK : K.IsComplement' A) (x y : G ⧸ A) :
    Additive.ofMul (complementDiff hH hK (x * y))
      = Additive.ofMul (complementDiff hH hK x) + x • Additive.ofMul (complementDiff hH hK y) := by
  rw [complementDiff_mul, ofMul_mul, ofMul_smul]

theorem isCocycle₁_complementDiff (hH : H.IsComplement' A) (hK : K.IsComplement' A) :
    groupCohomology.IsCocycle₁ (fun x : G ⧸ A => Additive.ofMul (complementDiff hH hK x)) := by
  intro x y
  change Additive.ofMul (complementDiff hH hK (x * y)) = _
  rw [ofMul_complementDiff_mul, add_comm]

end CFSG.FeitThompson
