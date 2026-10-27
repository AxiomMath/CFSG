module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import CFSG.LocalAnalysis.LargeEvenClassification.ExtensionGenerators
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped IsMulCommutative

theorem exists_finset_closure_eq_top_of_generatorRank_le {G : Type*} [Group G] [Finite G]
    {n : ℕ} (h : CFSG.generatorRank G ≤ n) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ S.card ≤ n := by
  obtain ⟨S, hS, hcl⟩ := Group.rank_spec G
  refine ⟨S, hcl, ?_⟩
  rw [hS, ← CFSG.generatorRank_eq_group_rank]
  exact h

theorem exists_finset_closure_eq_top_of_closure_eq {G : Type*} [Group G] {H : Subgroup G}
    {S : Finset G} (hS : Subgroup.closure (S : Set G) = H) :
    ∃ T : Finset H, Subgroup.closure (T : Set H) = ⊤ ∧ T.card ≤ S.card := by
  classical
  subst hS
  have hfin : (Subtype.val ⁻¹' (S : Set G) : Set (Subgroup.closure (S : Set G))).Finite :=
    S.finite_toSet.preimage Subtype.val_injective.injOn
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Subgroup.closure_closure_coe_preimage
  · apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      simpa using hx
    · exact Subtype.val_injective.injOn

theorem closure_map_subtype_eq {G : Type*} [Group G] {K : Subgroup G} {T : Finset K}
    (hT : Subgroup.closure (T : Set K) = ⊤) :
    Subgroup.closure ((T.map (Function.Embedding.subtype _) : Finset G) : Set G) = K := by
  rw [Finset.coe_map, Function.Embedding.coe_subtype,
    show (Subtype.val : K → G) = K.subtype from rfl, ← MonoidHom.map_closure, hT,
    ← MonoidHom.range_eq_map, range_subtype]

theorem exists_two_generators_units_two_pow (k : ℕ) (U : Subgroup (ZMod (2 ^ k))ˣ) :
    ∃ S : Finset (ZMod (2 ^ k))ˣ, S.card ≤ 2 ∧ Subgroup.closure (S : Set (ZMod (2 ^ k))ˣ) = U := by
  classical
  by_cases hk : k ≤ 2
  · have : IsCyclic (ZMod (2 ^ k))ˣ := (ZMod.isCyclic_units_two_pow_iff k).mpr hk
    obtain ⟨g, hg⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := U)).mp inferInstance
    refine ⟨{(g : (ZMod (2 ^ k))ˣ)}, by simp, ?_⟩
    rw [Finset.coe_singleton, ← zpowers_eq_closure]
    have h := congrArg (map U.subtype) hg
    rwa [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at h
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
  have hcop : Nat.Coprime 5 (2 ^ (n + 3)) := Nat.Coprime.pow_right _ (by norm_num)
  set u5 : (ZMod (2 ^ (n + 3)))ˣ := ZMod.unitOfCoprime 5 hcop with hu5
  have hord : orderOf u5 = 2 ^ (n + 1) := by
    rw [← orderOf_units, hu5, ZMod.coe_unitOfCoprime]
    exact ZMod.orderOf_five (n + 1)
  have hcard : Nat.card (ZMod (2 ^ (n + 3)))ˣ = 2 ^ (n + 2) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    norm_num
  have hindex : (zpowers u5).index = 2 := by
    have h := card_mul_index (zpowers u5)
    rw [Nat.card_zpowers, hord, hcard] at h
    have h' : 2 ^ (n + 1) * (zpowers u5).index = 2 ^ (n + 1) * 2 := by
      rw [h, pow_succ]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  set C : Subgroup (ZMod (2 ^ (n + 3)))ˣ := U ⊓ zpowers u5 with hC
  have hCcyc : IsCyclic C := by
    have : IsCyclic (C.subgroupOf (zpowers u5)) := Subgroup.isCyclic _
    let e := (subgroupOfEquivOfLe (inf_le_right : C ≤ zpowers u5)).symm
    exact isCyclic_of_injective e.toMonoidHom e.injective
  obtain ⟨g₁, hg₁⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := C)).mp hCcyc
  have hg₁' : zpowers (g₁ : (ZMod (2 ^ (n + 3)))ˣ) = C := by
    have h := congrArg (map C.subtype) hg₁
    rwa [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype] at h
  by_cases hU : U ≤ zpowers u5
  · refine ⟨{(g₁ : (ZMod (2 ^ (n + 3)))ˣ)}, by simp, ?_⟩
    rw [Finset.coe_singleton, ← zpowers_eq_closure, hg₁', hC, inf_eq_left.mpr hU]
  · obtain ⟨g₂, hg₂U, hg₂⟩ := Set.not_subset.mp hU
    refine ⟨{(g₁ : (ZMod (2 ^ (n + 3)))ˣ), g₂}, Finset.card_le_two, ?_⟩
    apply le_antisymm
    · rw [closure_le]
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact (mem_inf.mp g₁.2).1
      · exact hg₂U
    · intro u hu
      have hg₁cl : C ≤ Subgroup.closure
          (({(g₁ : (ZMod (2 ^ (n + 3)))ˣ), g₂} : Finset _) : Set (ZMod (2 ^ (n + 3)))ˣ) := by
        intro x hx
        rw [← hg₁'] at hx
        exact (zpowers_le.mpr (subset_closure (by simp))) hx
      have hg₂cl : g₂ ∈ Subgroup.closure
          (({(g₁ : (ZMod (2 ^ (n + 3)))ˣ), g₂} : Finset _) : Set (ZMod (2 ^ (n + 3)))ˣ) :=
        subset_closure (by simp)
      by_cases hu5 : u ∈ zpowers u5
      · exact hg₁cl (mem_inf.mpr ⟨hu, hu5⟩)
      · have h1 : u * g₂⁻¹ ∈ zpowers u5 := by
          rw [mul_mem_iff_of_index_two hindex, inv_mem_iff]
          exact iff_of_false hu5 hg₂
        have h2 : u * g₂⁻¹ ∈ C := mem_inf.mpr ⟨mul_mem hu (inv_mem hg₂U), h1⟩
        have h3 : u = u * g₂⁻¹ * g₂ := by group
        rw [h3]
        exact mul_mem (hg₁cl h2) hg₂cl

theorem exists_two_generators_mulAut_of_isCyclic {Y : Type*} [Group Y] [Finite Y] [IsCyclic Y]
    (hY : IsPGroup 2 Y) (H : Subgroup (MulAut Y)) :
    ∃ S : Finset (MulAut Y), S.card ≤ 2 ∧ Subgroup.closure (S : Set (MulAut Y)) = H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  let e : MulAut Y ≃* (ZMod (2 ^ k))ˣ :=
    (IsCyclic.mulAutMulEquiv Y).trans (Units.mapEquiv (ZMod.ringEquivCongr hk).toMulEquiv)
  obtain ⟨S, hScard, hS⟩ := exists_two_generators_units_two_pow k (H.map e.toMonoidHom)
  refine ⟨S.image e.symm, Finset.card_image_le.trans hScard, ?_⟩
  rw [Finset.coe_image, ← MulEquiv.coe_toMonoidHom, ← MonoidHom.map_closure, hS,
    map_map]
  convert map_id H using 2
  ext x
  simp

theorem cyclic_central_layer_automorphism_extension_generator_bound {P : Type*} [Group P]
    [Finite P] (hP : IsPGroup 2 P) {D : Subgroup P} [D.Normal] {Y : Subgroup P}
    (_hYZ : Y ≤ (center D).map D.subtype) (_hY1 : Y ≠ ⊥) [IsCyclic Y] [Y.Normal]
    [IsElementaryAbelian 2 (D ⧸ Y.subgroupOf D)] {d : ℕ}
    (hd : Nat.card (D ⧸ Y.subgroupOf D) = 2 ^ d)
    (hPD : ∃ A : Subgroup (MulAut Y), Nonempty (P ⧸ D ≃* A)) (K : Subgroup P) :
    ∃ S : Finset P, S.card ≤ d + 3 ∧ Subgroup.closure (S : Set P) = K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, ⟨eA⟩⟩ := hPD
  let ψ : K →* MulAut Y :=
    A.subtype.comp (eA.toMonoidHom.comp ((QuotientGroup.mk' D).comp K.subtype))
  have hψker : ∀ k : K, ψ k = 1 ↔ (k : P) ∈ D := by
    intro k
    rw [← QuotientGroup.eq_one_iff]
    change ((eA (QuotientGroup.mk (k : P)) : A) : MulAut Y) = 1 ↔ _
    constructor
    · intro h
      exact eA.injective ((Subtype.ext h : eA (QuotientGroup.mk (k : P)) = 1).trans
        (map_one eA).symm)
    · intro h
      rw [h, map_one]
      rfl
  have himg : ∃ T : Finset ψ.range, Subgroup.closure (T : Set ψ.range) = ⊤ ∧ T.card ≤ 2 := by
    obtain ⟨S, hScard, hS⟩ := exists_two_generators_mulAut_of_isCyclic (hP.to_subgroup Y) ψ.range
    obtain ⟨T, hT, hTcard⟩ := exists_finset_closure_eq_top_of_closure_eq hS
    exact ⟨T, hT, hTcard.trans hScard⟩
  have hLD : ∀ x : ψ.rangeRestrict.ker, ((x : K) : P) ∈ D := fun x => by
    have h : ψ.rangeRestrict (x : K) = 1 := MonoidHom.mem_ker.mp x.2
    have h2 : ψ (x : K) = 1 := by
      have h3 := congrArg Subtype.val h
      simpa using h3
    exact (hψker _).mp h2
  let φ : ψ.rangeRestrict.ker →* D ⧸ Y.subgroupOf D :=
    { toFun := fun x => QuotientGroup.mk (⟨((x : K) : P), hLD x⟩ : D)
      map_one' := rfl
      map_mul' := fun x y => rfl }
  have hker : ∃ T : Finset φ.rangeRestrict.ker,
      Subgroup.closure (T : Set φ.rangeRestrict.ker) = ⊤ ∧ T.card ≤ 1 := by
    have hYmem : ∀ x : φ.rangeRestrict.ker, ((((x : ψ.rangeRestrict.ker) : K)) : P) ∈ Y := by
      intro x
      have h : φ.rangeRestrict (x : ψ.rangeRestrict.ker) = 1 := MonoidHom.mem_ker.mp x.2
      have h2 : φ (x : ψ.rangeRestrict.ker) = 1 := by
        have h3 := congrArg Subtype.val h
        simpa using h3
      exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff
        (⟨(((x : ψ.rangeRestrict.ker) : K) : P), hLD _⟩ : D)).mp h2)
    let ι : φ.rangeRestrict.ker →* Y :=
      { toFun := fun x => ⟨_, hYmem x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y h
      have h' : (((x : ψ.rangeRestrict.ker) : K) : P) = (((y : ψ.rangeRestrict.ker) : K) : P) :=
        congrArg (fun w : Y => (w : P)) h
      exact Subtype.ext (Subtype.ext (Subtype.ext h'))
    have : IsCyclic φ.rangeRestrict.ker := isCyclic_of_injective ι hι
    exact exists_finset_closure_eq_top_of_generatorRank_le
      (CFSG.generatorRank_le_one_of_isCyclic inferInstance)
  have hran : ∃ T : Finset φ.range, Subgroup.closure (T : Set φ.range) = ⊤ ∧ T.card ≤ d := by
    have hpow : ∀ u : D ⧸ Y.subgroupOf D, u ^ 2 = 1 := fun u =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (D ⧸ Y.subgroupOf D)) u
    have : IsElementaryAbelian 2 φ.range :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (mul_comm' (a : D ⧸ Y.subgroupOf D) b)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (by simpa using hpow (a : D ⧸ Y.subgroupOf D)) }
    have hfr : Module.finrank (ZMod 2) (Additive φ.range) ≤ d := by
      have : Fintype (Additive φ.range) := Fintype.ofFinite _
      have h1 : Nat.card (Additive φ.range) = 2 ^ Module.finrank (ZMod 2) (Additive φ.range) := by
        rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
      have h2 : Nat.card (Additive φ.range) ≤ 2 ^ d := by
        rw [← hd]
        exact card_le_card_group φ.range
      rw [h1] at h2
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    exact exists_finset_closure_eq_top_of_generatorRank_le
      ((CFSG.generatorRank_le_finrank_of_elementaryAbelian _).trans hfr)
  obtain ⟨TL, hTL, hTLcard⟩ := CFSG.LargeEvenClassification.Helpers.extension_generator_bound
    φ.rangeRestrict φ.rangeRestrict_surjective hker hran
  obtain ⟨TK, hTK, hTKcard⟩ := CFSG.LargeEvenClassification.Helpers.extension_generator_bound
    ψ.rangeRestrict ψ.rangeRestrict_surjective ⟨TL, hTL, hTLcard⟩ himg
  refine ⟨TK.map (Function.Embedding.subtype _), ?_, closure_map_subtype_eq hTK⟩
  rw [Finset.card_map]
  omega

end CFSG.LocalAnalysis.GorensteinLyons
