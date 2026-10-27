module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightPointCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒟₁" => ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
local notation "τ₁" => ptTr hzC hsup hinf hz hb hnd hV φ he halt

abbrev pt₁ (x : (𝔼 × ZMod 2) × ZMod 2) : G := ptHom he hb φ hzC hz (Multiplicative.ofAdd x)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_add (x y : (𝔼 × ZMod 2) × ZMod 2) :
    pt₁ hzC hz hb φ he (x + y) = pt₁ hzC hz hb φ he x * pt₁ hzC hz hb φ he y := by
  rw [pt₁, ofAdd_add, map_mul]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_zero : pt₁ hzC hz hb φ he 0 = 1 := by
  rw [pt₁, ofAdd_zero, map_one]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_inv (x : (𝔼 × ZMod 2) × ZMod 2) :
    (pt₁ hzC hz hb φ he x)⁻¹ = pt₁ hzC hz hb φ he x := by
  rw [inv_eq_iff_mul_eq_one, ← pt₁_add, add_self_eq_zero_zmod_two, pt₁_zero]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hinf in
theorem pt₁_injective : Function.Injective (pt₁ hzC hz hb φ he) := fun _ _ h =>
  Multiplicative.ofAdd.injective (ptHom_injective he hb φ hzC hz hinf h)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_mem (x : (𝔼 × ZMod 2) × ZMod 2) : pt₁ hzC hz hb φ he x ∈ ptSub φ z hb e := by
  rw [← range_ptHom he hb φ hzC hz]
  exact ⟨_, rfl⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem exists_pt₁_eq {x : G} (hx : x ∈ ptSub φ z hb e) :
    ∃ v, pt₁ hzC hz hb φ he v = x := by
  rw [← range_ptHom he hb φ hzC hz] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Multiplicative.toAdd y, rfl⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_z : pt₁ hzC hz hb φ he ((0, 0), 1) = z := by
  rw [pt₁, Prod.mk_zero_zero, ptHom_z]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem pt₁_mem_ptA (v : 𝔼 × ZMod 2) : pt₁ hzC hz hb φ he (v, 0) ∈ 𝒜₁ := by
  rw [pt₁, ptHom_pt]
  exact (mem_ptA_iff he hb φ).2 ⟨v, rfl⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hinf in
theorem mem_ptA_iff_pt₁ (x : (𝔼 × ZMod 2) × ZMod 2) :
    pt₁ hzC hz hb φ he x ∈ 𝒜₁ ↔ x.2 = 0 := by
  obtain ⟨v, s⟩ := x
  constructor
  · intro h
    rcases zmod_two_cases s with h0 | h1
    · exact h0
    · exfalso
      subst h1
      have hsplit : ((v, 1) : (𝔼 × ZMod 2) × ZMod 2) = (v, 0) + ((0, 0), 1) := by
        rw [Prod.mk_zero_zero, Prod.mk_add_mk, add_zero, zero_add]
      have h2 := mul_mem (inv_mem (pt₁_mem_ptA hzC hz hb φ he v)) h
      rw [hsplit, pt₁_add, ← mul_assoc, inv_mul_cancel, one_mul, pt₁_z] at h2
      have h3 : z ∈ L ⊓ zpowers z := ⟨pullSub_le φ _ h2, mem_zpowers z⟩
      rw [hinf, mem_bot] at h3
      rw [h3, orderOf_one] at hz
      exact absurd hz (by norm_num)
  · intro h
    change s = 0 at h
    subst h
    exact pt₁_mem_ptA hzC hz hb φ he _

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptB₁_eq : ptB₁ hzC hz hb φ he = pt₁ hzC hz hb φ he ((0, 1), 0) :=
  rfl

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hinf in
theorem mem_ptI_iff_pt₁ (x : (𝔼 × ZMod 2) × ZMod 2) :
    pt₁ hzC hz hb φ he x ∈ zpowers (ptB₁ hzC hz hb φ he) ↔ x.1.1 = 0 ∧ x.2 = 0 := by
  have hsq : ptB₁ hzC hz hb φ he ^ 2 = 1 := by
    rw [ptB₁_eq, sq, ← pt₁_add, add_self_eq_zero_zmod_two, pt₁_zero]
  have hne : ptB₁ hzC hz hb φ he ≠ 1 := by
    rw [ptB₁_eq, ← pt₁_zero hzC hz hb φ he]
    intro h
    have h1 := congrArg (fun x : (𝔼 × ZMod 2) × ZMod 2 => x.1.2)
      (pt₁_injective hzC hinf hz hb φ he h)
    exact one_ne_zero h1
  have hord : orderOf (ptB₁ hzC hz hb φ he) = 2 := orderOf_eq_prime hsq hne
  constructor
  · intro h
    rcases eq_one_or_eq_of_mem_zpowers hord h with h1 | h1
    · rw [← pt₁_zero hzC hz hb φ he] at h1
      rw [pt₁_injective hzC hinf hz hb φ he h1]
      exact ⟨rfl, rfl⟩
    · rw [ptB₁_eq] at h1
      rw [pt₁_injective hzC hinf hz hb φ he h1]
      exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨⟨w, t⟩, s⟩ := x
    simp only at h1 h2
    subst h1 h2
    rcases zmod_two_cases t with rfl | rfl
    · rw [Prod.mk_zero_zero, Prod.mk_zero_zero, pt₁_zero]
      exact one_mem _
    · exact mem_zpowers _

theorem inv_mul_pt₁_mul (d : 𝒟₁) (x : (𝔼 × ZMod 2) × ZMod 2) :
    (d : G)⁻¹ * pt₁ hzC hz hb φ he x * d =
      pt₁ hzC hz hb φ he (trMap (Multiplicative.toAdd (τ₁ d)) x) :=
  inv_mul_ptHom_mul hzC hsup hinf hz hb hnd hV φ he halt d x

theorem conj_mem_ptD₁ {n : G} (hn : n ∈ 𝒩₁) {d : G} (hd : d ∈ 𝒟₁) : n * d * n⁻¹ ∈ 𝒟₁ := by
  have h := (ptD₁_normal hzC hsup hinf hz hb hnd hV φ he halt).conj_mem
    ⟨d, ptD₁_le hzC hsup hinf hz hb hnd hV φ he halt hd⟩ (mem_subgroupOf.2 hd) ⟨n, hn⟩
  rw [mem_subgroupOf] at h
  exact h

omit [FiniteDimensional (ZMod 2) V] in
theorem trMap_z (a : 𝔼) :
    ((0, 0), 1) + trMap a (((0, 0), 1) : (𝔼 × ZMod 2) × ZMod 2) = ((a, ptQuad e a), 0) := by
  rw [trMap_apply]
  simp only [Prod.mk_add_mk, one_smul, one_mul, zero_add, ZeroMemClass.coe_zero, map_zero,
    LinearMap.zero_apply]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem trMap_u (a u : 𝔼) :
    ((u, 0), 0) + trMap a (((u, 0), 0) : (𝔼 × ZMod 2) × ZMod 2) = ((0, b u a), 0) := by
  rw [trMap_apply]
  simp only [Prod.mk_add_mk, zero_smul, add_zero, zero_mul, zero_add]
  rw [add_self_eq_zero_zmod_two]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hz in
theorem z_inv_eq : z⁻¹ = z := by
  have h := pow_orderOf_eq_one z
  rw [hz, sq] at h
  exact inv_eq_of_mul_eq_one_right h

theorem comm_z_pt₁ (d : 𝒟₁) :
    z⁻¹ * (d : G)⁻¹ * z * d = pt₁ hzC hz hb φ he
      ((Multiplicative.toAdd (τ₁ d), ptQuad e (Multiplicative.toAdd (τ₁ d))), 0) := by
  have h := inv_mul_pt₁_mul hzC hsup hinf hz hb hnd hV φ he halt d ((0, 0), 1)
  rw [pt₁_z] at h
  have hcalc := congrArg (pt₁ hzC hz hb φ he) (trMap_z (Multiplicative.toAdd (τ₁ d)))
  rw [pt₁_add, pt₁_z] at hcalc
  calc z⁻¹ * (d : G)⁻¹ * z * d = z * ((d : G)⁻¹ * z * d) := by
        rw [z_inv_eq hz]
        group
    _ = _ := by rw [h, hcalc]

theorem comm_pt₁_pt₁ (d : 𝒟₁) (u : 𝔼) :
    (pt₁ hzC hz hb φ he ((u, 0), 0))⁻¹ * (d : G)⁻¹ * pt₁ hzC hz hb φ he ((u, 0), 0) * d =
      pt₁ hzC hz hb φ he ((0, b u (Multiplicative.toAdd (τ₁ d) : 𝔼)), 0) := by
  rw [mul_assoc _ (d : G)⁻¹, mul_assoc, inv_mul_pt₁_mul hzC hsup hinf hz hb hnd hV φ he halt,
    pt₁_inv, ← pt₁_add, trMap_u]

include hinf in
theorem sq_mem_ptA (d : 𝒟₁) : (d : G) ^ 2 ∈ 𝒜₁ := by
  have hsqB : (d : G) ^ 2 ∈ ptSub φ z hb e := by
    have h : d ^ 2 ∈ (τ₁).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul, add_self_eq_zero_zmod_two]
    rw [ker_ptTr, mem_subgroupOf] at h
    exact h
  obtain ⟨⟨⟨w, t⟩, s⟩, hv⟩ := exists_pt₁_eq hzC hz hb φ he hsqB
  rw [← hv, mem_ptA_iff_pt₁ hzC hinf hz hb φ he]
  by_cases ha : Multiplicative.toAdd (τ₁ d) = 0
  ·
    have hdB : (d : G) ∈ ptSub φ z hb e := by
      have h : d ∈ (τ₁).ker := by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective ha
      rw [ker_ptTr, mem_subgroupOf] at h
      exact h
    obtain ⟨-, hBe, -, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
    have h1 : (d : G) ^ 2 = 1 := by rw [sq, mul_self_of_isElementaryAbelian hBe hdB]
    rw [h1, ← pt₁_zero hzC hz hb φ he] at hv
    have h2 := pt₁_injective hzC hinf hz hb φ he hv
    exact congrArg Prod.snd h2
  ·
    have hfix : (d : G)⁻¹ * (d : G) ^ 2 * d = (d : G) ^ 2 := by group
    rw [← hv, inv_mul_pt₁_mul hzC hsup hinf hz hb hnd hV φ he halt] at hfix
    have h := congrArg (fun x : (𝔼 × ZMod 2) × ZMod 2 => x.1.1)
      (pt₁_injective hzC hinf hz hb φ he hfix)
    simp only [trMap_apply, add_eq_left] at h
    rcases zmod_two_cases s with h0 | h1
    · exact h0
    · rw [h1, one_smul] at h
      exact absurd h ha

theorem commutator_ptD₁ : ⁅𝒟₁, 𝒟₁⁆ = 𝒜₁ := by
  apply le_antisymm
  · refine (OddQuadraticFive.commutator_le_closure_sq 𝒟₁).trans ((closure_le _).2 ?_)
    rintro _ ⟨d, hd, rfl⟩
    exact sq_mem_ptA hzC hsup hinf hz hb hnd hV φ he halt ⟨d, hd⟩
  · intro x hx
    obtain ⟨⟨w, t⟩, rfl⟩ := (mem_ptA_iff he hb φ).1 hx
    have hzD : z ∈ 𝒟₁ := ptSub_le_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
      (mem_sup_right (mem_zpowers z))
    have hcomm : ∀ d : 𝒟₁, z⁻¹ * (d : G)⁻¹ * z * d ∈ ⁅𝒟₁, 𝒟₁⁆ := fun d => by
      have h := commutator_mem_commutator (inv_mem hzD) (inv_mem d.2)
      rwa [commutatorElement_def, inv_inv, inv_inv] at h
    obtain ⟨dw, hdw⟩ := ptTr_surjective hzC hsup hinf hz hb hnd hV φ he halt
      (Multiplicative.ofAdd w)
    have h1 := comm_z_pt₁ hzC hsup hinf hz hb hnd hV φ he halt dw
    rw [hdw, toAdd_ofAdd] at h1
    obtain ⟨df, hdf⟩ := ptTr_surjective hzC hsup hinf hz hb hnd hV φ he halt
      (Multiplicative.ofAdd (ptF₂ he))
    have h2 := comm_pt₁_pt₁ hzC hsup hinf hz hb hnd hV φ he halt df (ptE₂ he)
    rw [hdf, toAdd_ofAdd, show b (ptE₂ he) (ptF₂ he) = 1 from restrict_ptE₂_ptF₂ he] at h2
    have hb₁ : pt₁ hzC hz hb φ he ((0, 1), 0) ∈ ⁅𝒟₁, 𝒟₁⁆ := by
      rw [← h2]
      have hu : pt₁ hzC hz hb φ he ((ptE₂ he, 0), 0) ∈ 𝒟₁ :=
        ptSub_le_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt (pt₁_mem hzC hz hb φ he _)
      have h := commutator_mem_commutator (inv_mem hu) (inv_mem df.2)
      rwa [commutatorElement_def, inv_inv, inv_inv] at h
    have hsplit : (((w, t), 0) : (𝔼 × ZMod 2) × ZMod 2) =
        ((w, ptQuad e w), 0) + (t + ptQuad e w) • ((0, 1), 0) := by
      simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero]
      congr 2
      rw [add_left_comm, add_self_eq_zero_zmod_two, add_zero]
    have hfinal : pt₁ hzC hz hb φ he ((w, t), 0) ∈ ⁅𝒟₁, 𝒟₁⁆ := by
      rw [hsplit, pt₁_add, ← h1]
      refine mul_mem (hcomm dw) ?_
      rcases zmod_two_cases (t + ptQuad e w) with h0 | h0
      · rw [h0, zero_smul, pt₁_zero]
        exact one_mem _
      · rw [h0, one_smul]
        exact hb₁
    rw [pt₁, ptHom_pt] at hfinal
    exact hfinal

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
