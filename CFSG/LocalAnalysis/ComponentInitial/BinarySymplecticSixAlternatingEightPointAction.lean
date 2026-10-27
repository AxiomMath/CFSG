module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightPointFusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

section Coord

variable {G : Type*} [Group G] {X : Type*} [AddCommGroup X] {B : Subgroup G}

@[expose] def conjCoord (θ : B ≃* Multiplicative X) {m : G} (hm : m ∈ normalizer (B : Set G)) :
    X →+ X :=
  AddMonoidHom.mk' (fun x => Multiplicative.toAdd (θ ⟨m * θ.symm (Multiplicative.ofAdd x) * m⁻¹,
    (mem_normalizer_iff.1 hm _).1 (θ.symm _).2⟩)) fun x y => by
      rw [← toAdd_mul, ← map_mul]
      congr 2
      apply Subtype.ext
      simp only [ofAdd_add, map_mul, Subgroup.coe_mul]
      group

theorem coe_symm_conjCoord (θ : B ≃* Multiplicative X) {m : G}
    (hm : m ∈ normalizer (B : Set G)) (x : X) :
    ((θ.symm (Multiplicative.ofAdd (conjCoord θ hm x)) : B) : G) =
      m * θ.symm (Multiplicative.ofAdd x) * m⁻¹ := by
  simp only [conjCoord, AddMonoidHom.mk'_apply, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem conjCoord_inv (θ : B ≃* Multiplicative X) {m : G}
    (hm : m ∈ normalizer (B : Set G)) (x : X) :
    conjCoord θ (inv_mem hm) (conjCoord θ hm x) = x := by
  apply Multiplicative.ofAdd.injective
  apply θ.symm.injective
  apply Subtype.ext
  rw [coe_symm_conjCoord, coe_symm_conjCoord]
  group

theorem conjCoord_inv' (θ : B ≃* Multiplicative X) {m : G}
    (hm : m ∈ normalizer (B : Set G)) (x : X) :
    conjCoord θ hm (conjCoord θ (inv_mem hm) x) = x := by
  apply Multiplicative.ofAdd.injective
  apply θ.symm.injective
  apply Subtype.ext
  rw [coe_symm_conjCoord, coe_symm_conjCoord]
  group

end Coord

theorem exists_sp_of_isometry {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] {β : BilinForm (ZMod 2) E} (hnd : β.Nondegenerate)
    (S : E →+ E) (hS : ∀ x y, β (S x) (S y) = β x y) :
    ∃ s : bilinIsometryGroup β, ∀ w, OddQuadraticFive.sE s w = S w := by
  set S' : E →ₗ[ZMod 2] E := AddMonoidHom.toZModLinearMap 2 S with hS'
  have hinj : Function.Injective S' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine hnd.1 x fun y => ?_
    rw [← hS x y]
    change β (S' x) (S y) = 0
    rw [hx, map_zero, LinearMap.zero_apply]
  refine ⟨⟨LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.ofInjectiveEndo S' hinj),
    fun x y => hS x y⟩, fun w => rfl⟩

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)

variable (z e) in
abbrev AltOrbit : Prop :=
  conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 2 ∧ ∀ i, B i i = 0)

omit [FiniteDimensional (ZMod 2) V] in
include he in
theorem mem_pairOrth_inr_one : e (Sum.inr 1) ∈ 𝔼 := by
  rw [mem_pairOrth, bilin_inl he, bilin_inr he]
  simp

abbrev ptF₂ : 𝔼 := ⟨e (Sum.inr 1), mem_pairOrth_inr_one he⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem restrict_ptE₂_ptF₂ : (b.restrict 𝔼) (ptE₂ he) (ptF₂ he) = 1 := by
  change b (e (Sum.inl 1)) (e (Sum.inr 1)) = 1
  rw [bilin_inl he, e.repr_self, Finsupp.single_eq_same]

include hb in
omit [FiniteDimensional (ZMod 2) V] in
theorem restrict_isAlt : (b.restrict 𝔼).IsAlt := fun x => hb x

include hb hnd he in
omit [FiniteDimensional (ZMod 2) V] in
theorem restrict_nondegenerate : (b.restrict 𝔼).Nondegenerate :=
  hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) hnd

include hzC hsup hinf hz hb hnd hV he in
theorem ptGr_mem_conjClass (halt : AltOrbit z φ e) (w : 𝔼) :
    ptGr hzC hz hb φ he w ∈ conjClass 𝒩₁ z := by
  rw [conjClass_ptSub_eq hzC hsup hinf hz hb hnd hV φ he halt]
  exact ⟨w, rfl⟩

@[expose] def ptOrbitEquiv (halt : AltOrbit z φ e) : 𝔼 ≃ conjClass 𝒩₁ z :=
  Equiv.ofBijective
    (fun w => ⟨ptGr hzC hz hb φ he w, ptGr_mem_conjClass hzC hsup hinf hz hb hnd hV φ he halt w⟩)
    ⟨fun w w' h => ptGr_injective hzC hinf hz hb φ he (congrArg Subtype.val h), fun x => by
      obtain ⟨w, hw⟩ : (x : G) ∈ Set.range (ptGr hzC hz hb φ he) := by
        rw [← conjClass_ptSub_eq hzC hsup hinf hz hb hnd hV φ he halt]
        exact x.2
      exact ⟨w, Subtype.ext hw⟩⟩

@[expose] def ptAct (halt : AltOrbit z φ e) : 𝒩₁ →* Equiv.Perm 𝔼 :=
  DegreeEight.labelPerm (ptOrbitEquiv hzC hsup hinf hz hb hnd hV φ he halt)

theorem ptGr_ptAct (halt : AltOrbit z φ e) (m : 𝒩₁) (w : 𝔼) :
    ptGr hzC hz hb φ he (ptAct hzC hsup hinf hz hb hnd hV φ he halt m w) =
      m * ptGr hzC hz hb φ he w * (m : G)⁻¹ :=
  DegreeEight.coe_labelPerm (ptOrbitEquiv hzC hsup hinf hz hb hnd hV φ he halt) m w

theorem ptAct_eq_iff (halt : AltOrbit z φ e) {m : 𝒩₁} {w w' : 𝔼} :
    ptAct hzC hsup hinf hz hb hnd hV φ he halt m w = w' ↔
      (m : G) * ptGr hzC hz hb φ he w * (m : G)⁻¹ = ptGr hzC hz hb φ he w' :=
  DegreeEight.labelPerm_eq_iff (ptOrbitEquiv hzC hsup hinf hz hb hnd hV φ he halt)

theorem ptAct_ptLevi (halt : AltOrbit z φ e) (s : bilinIsometryGroup (b.restrict 𝔼)) (w : 𝔼) :
    ptAct hzC hsup hinf hz hb hnd hV φ he halt
      ⟨ptLevi he hb φ s, ptLevi_mem_normalizer he hb φ hzC hz s⟩ w =
        OddQuadraticFive.sE s w :=
  (ptAct_eq_iff hzC hsup hinf hz hb hnd hV φ he halt).2 (ptLevi_conj_ptGr hzC hz hb φ he s w)

abbrev ptConj (m : 𝒩₁) : (𝔼 × ZMod 2) × ZMod 2 →+ (𝔼 × ZMod 2) × ZMod 2 :=
  conjCoord (ptLabel he hb φ hzC hz hinf) m.2

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptHom_ptConj (m : 𝒩₁) (x : (𝔼 × ZMod 2) × ZMod 2) :
    ptHom he hb φ hzC hz (Multiplicative.ofAdd (ptConj hzC hinf hz hb φ he m x)) =
      m * ptHom he hb φ hzC hz (Multiplicative.ofAdd x) * (m : G)⁻¹ := by
  have h := coe_symm_conjCoord (ptLabel he hb φ hzC hz hinf) m.2 x
  rwa [coe_ptLabel_symm, coe_ptLabel_symm] at h

theorem ptConj_grV (halt : AltOrbit z φ e) (m : 𝒩₁) (w : 𝔼) :
    ptConj hzC hinf hz hb φ he m (grV (ptQuad e) w) =
      grV (ptQuad e) (ptAct hzC hsup hinf hz hb hnd hV φ he halt m w) := by
  apply Multiplicative.ofAdd.injective
  apply ptHom_injective he hb φ hzC hz hinf
  rw [ptHom_ptConj]
  exact (ptGr_ptAct hzC hsup hinf hz hb hnd hV φ he halt m w).symm

include hsup hnd hV in
theorem ptConj_rX_and_affine (halt : AltOrbit z φ e) (m : 𝒩₁) :
    ptConj hzC hinf hz hb φ he m ((0, 1), 0) = ((0, 1), 0) ∧
      ∃ s : bilinIsometryGroup (b.restrict 𝔼), ∀ w,
        ptAct hzC hsup hinf hz hb hnd hV φ he halt m w = OddQuadraticFive.sE s w +
          ptAct hzC hsup hinf hz hb hnd hV φ he halt m 0 := by
  have hQ := polarBilin_ptQuad he
  obtain ⟨hr, S, a, hS, hSa⟩ := exists_isometry_of_graph hQ (restrict_isAlt hb)
    (restrict_nondegenerate hb hnd he) (restrict_ptE₂_ptF₂ he) (ptConj hzC hinf hz hb φ he m)
    (ptConj hzC hinf hz hb φ he m⁻¹) (conjCoord_inv _ m.2) (conjCoord_inv' _ m.2)
    (fun w => ⟨_, ptConj_grV hzC hsup hinf hz hb hnd hV φ he halt m w⟩)
    (fun w => ⟨_, ptConj_grV hzC hsup hinf hz hb hnd hV φ he halt m⁻¹ w⟩)
  have hact : ∀ w, ptAct hzC hsup hinf hz hb hnd hV φ he halt m w = S w + a := fun w =>
    grV_injective (Q := ptQuad e)
      ((ptConj_grV hzC hsup hinf hz hb hnd hV φ he halt m w).symm.trans (hSa w))
  obtain ⟨s, hs⟩ := exists_sp_of_isometry (restrict_nondegenerate hb hnd he) S hS
  refine ⟨hr, s, fun w => ?_⟩
  rw [hact, hact, hs, map_zero, zero_add]

abbrev ptB₁ : G := ptHom he hb φ hzC hz (Multiplicative.ofAdd ((0, 1), 0))

include hsup hinf hnd hV in
theorem conj_ptB₁ (halt : AltOrbit z φ e) (m : 𝒩₁) :
    (m : G) * ptB₁ hzC hz hb φ he * (m : G)⁻¹ = ptB₁ hzC hz hb φ he := by
  rw [← ptHom_ptConj hzC hinf hz hb φ he m,
    (ptConj_rX_and_affine hzC hsup hinf hz hb hnd hV φ he halt m).1]

@[expose] def ptLinFun (halt : AltOrbit z φ e) (m : 𝒩₁) : bilinIsometryGroup (b.restrict 𝔼) :=
  Classical.choose (ptConj_rX_and_affine hzC hsup hinf hz hb hnd hV φ he halt m).2

theorem ptLinFun_spec (halt : AltOrbit z φ e) (m : 𝒩₁) (w : 𝔼) :
    ptAct hzC hsup hinf hz hb hnd hV φ he halt m w =
      OddQuadraticFive.sE (ptLinFun hzC hsup hinf hz hb hnd hV φ he halt m) w +
        ptAct hzC hsup hinf hz hb hnd hV φ he halt m 0 :=
  Classical.choose_spec (ptConj_rX_and_affine hzC hsup hinf hz hb hnd hV φ he halt m).2 w

theorem ptLinFun_eq (halt : AltOrbit z φ e) {m : 𝒩₁} {s : bilinIsometryGroup (b.restrict 𝔼)}
    (hs : ∀ w, ptAct hzC hsup hinf hz hb hnd hV φ he halt m w =
      OddQuadraticFive.sE s w + ptAct hzC hsup hinf hz hb hnd hV φ he halt m 0) :
    ptLinFun hzC hsup hinf hz hb hnd hV φ he halt m = s := by
  refine Subtype.ext (Units.ext (LinearMap.ext fun w => ?_))
  have h := (ptLinFun_spec hzC hsup hinf hz hb hnd hV φ he halt m w).symm.trans (hs w)
  exact add_right_cancel h

@[expose] def ptLin (halt : AltOrbit z φ e) : 𝒩₁ →* bilinIsometryGroup (b.restrict 𝔼) where
  toFun := ptLinFun hzC hsup hinf hz hb hnd hV φ he halt
  map_one' := ptLinFun_eq hzC hsup hinf hz hb hnd hV φ he halt fun w => by
    rw [map_one, Equiv.Perm.one_apply, Equiv.Perm.one_apply, add_zero]
    rfl
  map_mul' m m' := ptLinFun_eq hzC hsup hinf hz hb hnd hV φ he halt fun w => by
    rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ptLinFun_spec hzC hsup hinf hz hb hnd hV φ he halt m,
      ptLinFun_spec hzC hsup hinf hz hb hnd hV φ he halt m',
      ptLinFun_spec hzC hsup hinf hz hb hnd hV φ he halt m (ptAct _ _ _ _ _ _ _ _ _ halt m' 0),
      map_add, OddQuadraticFive.sE_mul, add_assoc]

theorem ptLin_spec (halt : AltOrbit z φ e) (m : 𝒩₁) (w : 𝔼) :
    ptAct hzC hsup hinf hz hb hnd hV φ he halt m w =
      OddQuadraticFive.sE (ptLin hzC hsup hinf hz hb hnd hV φ he halt m) w +
        ptAct hzC hsup hinf hz hb hnd hV φ he halt m 0 :=
  ptLinFun_spec hzC hsup hinf hz hb hnd hV φ he halt m w

theorem ptLin_eq (halt : AltOrbit z φ e) {m : 𝒩₁} {s : bilinIsometryGroup (b.restrict 𝔼)}
    (hs : ∀ w, ptAct hzC hsup hinf hz hb hnd hV φ he halt m w =
      OddQuadraticFive.sE s w + ptAct hzC hsup hinf hz hb hnd hV φ he halt m 0) :
    ptLin hzC hsup hinf hz hb hnd hV φ he halt m = s :=
  ptLinFun_eq hzC hsup hinf hz hb hnd hV φ he halt hs

theorem ptLin_ptLevi (halt : AltOrbit z φ e) (s : bilinIsometryGroup (b.restrict 𝔼)) :
    ptLin hzC hsup hinf hz hb hnd hV φ he halt
      ⟨ptLevi he hb φ s, ptLevi_mem_normalizer he hb φ hzC hz s⟩ = s :=
  ptLin_eq hzC hsup hinf hz hb hnd hV φ he halt fun w => by
    rw [ptAct_ptLevi, ptAct_ptLevi, map_zero, add_zero]

theorem ptLin_surjective (halt : AltOrbit z φ e) :
    Function.Surjective (ptLin hzC hsup hinf hz hb hnd hV φ he halt) :=
  fun s => ⟨_, ptLin_ptLevi hzC hsup hinf hz hb hnd hV φ he halt s⟩

include hsup hnd hV in
theorem mem_range_ptAct_iff (halt : AltOrbit z φ e) (k : Equiv.Perm 𝔼) :
    k ∈ (ptAct hzC hsup hinf hz hb hnd hV φ he halt).range ↔
      ∃ (s : bilinIsometryGroup (b.restrict 𝔼)) (a : 𝔼),
        ∀ w, k w = OddQuadraticFive.sE s w + a := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨_, _, ptLin_spec hzC hsup hinf hz hb hnd hV φ he halt m⟩
  · rintro ⟨s, a, hk⟩
    obtain ⟨m₁, hm₁, hm₁a⟩ := ptGr_mem_conjClass hzC hsup hinf hz hb hnd hV φ he halt a
    have h0 : ptAct hzC hsup hinf hz hb hnd hV φ he halt ⟨m₁, hm₁⟩ 0 = a := by
      rw [ptAct_eq_iff, ptGr_zero]
      exact hm₁a
    set s₁ := ptLin hzC hsup hinf hz hb hnd hV φ he halt ⟨m₁, hm₁⟩ with hs₁
    refine ⟨⟨m₁, hm₁⟩ * ⟨ptLevi he hb φ (s₁⁻¹ * s), ptLevi_mem_normalizer he hb φ hzC hz _⟩,
      Equiv.ext fun w => ?_⟩
    rw [map_mul, Equiv.Perm.mul_apply, ptAct_ptLevi, ptLin_spec, ← hs₁, h0,
      OddQuadraticFive.sE_mul, OddQuadraticFive.sE_apply_inv, hk]

include hsup hnd in
theorem ker_ptAct (halt : AltOrbit z φ e) :
    (ptAct hzC hsup hinf hz hb hnd hV φ he halt).ker = (ptSub φ z hb e).subgroupOf 𝒩₁ := by
  ext m
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    have hfix : ∀ w, (m : G) * ptGr hzC hz hb φ he w * (m : G)⁻¹ = ptGr hzC hz hb φ he w :=
      fun w => (ptAct_eq_iff hzC hsup hinf hz hb hnd hV φ he halt).1 (by rw [h]; rfl)
    have hext : ((MulAut.conj (m : G)).toMonoidHom.comp (ptHom he hb φ hzC hz)) =
        ptHom he hb φ hzC hz :=
      hom_ext_grV (polarBilin_ptQuad he) (restrict_ptE₂_ptF₂ he) fun w => hfix w
    have hc : (m : G) ∈ centralizer ((ptSub φ z hb e : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      rw [← range_ptHom he hb φ hzC hz] at hx
      obtain ⟨y, rfl⟩ := hx
      have h1 := congrArg (fun f => f y) hext
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      calc ptHom he hb φ hzC hz y * m = (m * ptHom he hb φ hzC hz y * (m : G)⁻¹) * m := by
            rw [h1]
        _ = m * ptHom he hb φ hzC hz y := by group
    rwa [centralizer_ptSub he hb hnd φ hzC hsup hinf hz] at hc
  · intro hm
    obtain ⟨-, hBe, -, -⟩ := ptSub_facts he hb hnd φ hzC hinf hz
    refine Equiv.ext fun w => (ptAct_eq_iff hzC hsup hinf hz hb hnd hV φ he halt).2 ?_
    rw [mul_comm_of_isElementaryAbelian hBe hm (ptGr_mem hzC hz hb φ he w), mul_inv_cancel_right]
    rfl

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
