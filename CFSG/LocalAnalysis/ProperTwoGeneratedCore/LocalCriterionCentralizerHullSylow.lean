module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

@[expose] def sylowTwoOfOddIndex [Finite G] (H : Subgroup G) (hindex : Odd H.index)
    (T : Sylow 2 H) : Sylow 2 G :=
  (T.isPGroup'.map H.subtype).toSylow (by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two T.not_dvd_index hindex.not_two_dvd_nat)

theorem sylowTwoOfOddIndex_subgroup [Finite G] (H : Subgroup G) (hindex : Odd H.index)
    (T : Sylow 2 H) :
    (sylowTwoOfOddIndex H hindex T : Subgroup G) = (T : Subgroup H).map H.subtype := rfl

theorem central_square_one_mem_every_sylow
    (u : G) (huZ : u ∈ Subgroup.center G) (hu : u ^ 2 = 1) (T : Sylow 2 G) : u ∈ T := by
  have hle : Subgroup.zpowers u ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr huZ
  let : (Subgroup.zpowers u).Normal := Subgroup.normal_of_le_center hle
  let : IsElementaryAbelian 2 (Subgroup.zpowers u) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hu
  exact (IsElementaryAbelian.isPGroup 2 (Subgroup.zpowers u)).le_sylow_of_normal T
    (Subgroup.mem_zpowers u)

theorem omega_one_eq_involution_closure :
    CFSG.omega₁ (G := G) (p := 2) = Subgroup.closure {x : G | IsInvolution x} := by
  change Subgroup.closure {x : G | x ^ (2 ^ 1) = 1} = _
  have hset : {x : G | x ^ (2 ^ 1) = 1} = insert 1 {x : G | IsInvolution x} := by
    ext x
    simp only [pow_one, Set.mem_ofPred_eq, Set.mem_insert_iff]
    constructor
    · intro hx
      by_cases h : x = 1
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (rfl | hx)
      · exact one_pow 2
      · exact hx.sq_eq_one
  rw [hset, Subgroup.closure_insert_one]

theorem omega_one_map_eq_entire_involution_closure (T : Subgroup G) :
    (CFSG.omega₁ (G := T) (p := 2)).map T.subtype =
      Subgroup.closure {x : G | x ∈ T ∧ IsInvolution x} := by
  rw [omega_one_eq_involution_closure, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, fun h => hy.ne_one (Subtype.ext h),
      congrArg Subtype.val hy.sq_eq_one⟩
  · rintro ⟨hxT, hx⟩
    refine ⟨⟨x, hxT⟩, ?_, rfl⟩
    exact ⟨fun h => hx.ne_one (congrArg Subtype.val h), Subtype.ext hx.sq_eq_one⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
