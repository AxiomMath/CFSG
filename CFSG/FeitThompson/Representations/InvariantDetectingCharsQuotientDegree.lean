module

public import CFSG.FeitThompson.Representations.FrobeniusKernelInductionIrreducible
public import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
public import Mathlib.LinearAlgebra.FixedSubmodule
public import CFSG.FeitThompson.Representations.InvariantDetectingCharsQuotientDegreeSupport
import CFSG.FeitThompson.Representations.BlockDifferenceOrthogonalConstantOffCore
import CFSG.FeitThompson.Representations.PrimeInvariantCharsInnerKernel
import CFSG.FeitThompson.Representations.CyclicPermutedSummandsFixedSpace
import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible
import CFSG.FeitThompson.Representations.CentralLayerDegreeSquareDivisor
import CFSG.FeitThompson.Local.CoprimeActionNonnilpotentFixedSection

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Aux

variable {p q : ℕ} [Fact p.Prime] {V U : Type*} [AddCommGroup V] [Module (ZMod p) V] [Group U]

theorem isComplement'_range_inl_range_inr {H Q : Type*} [Group H] [Group Q] (ρ : Q →* MulAut H) :
    Subgroup.IsComplement' (inl : H →* H ⋊[ρ] Q).range (inr : Q →* H ⋊[ρ] Q).range := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff]; exact range_inl_inf_range_inr ρ
  · have hn : ((inl : H →* H ⋊[ρ] Q).range).Normal := range_inl_normal
    rw [← Subgroup.normal_mul, range_inl_sup_range_inr ρ]; rfl

theorem coe_pow_linearEquiv (f : V ≃ₗ[ZMod p] V) (n : ℕ) :
    ((f ^ n : V ≃ₗ[ZMod p] V) : V →ₗ[ZMod p] V) = (f : V →ₗ[ZMod p] V) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem natCard_eq_of_finrank_eq_one [Finite V] (W : Submodule (ZMod p) V)
    (h : finrank (ZMod p) W = 1) : Nat.card W = p := by
  have : Fintype V := Fintype.ofFinite V
  have : Fintype W := Fintype.ofFinite _
  have hc := Module.card_eq_pow_finrank (K := ZMod p) (V := W)
  rw [h, pow_one, ZMod.card] at hc
  rw [Nat.card_eq_fintype_card, hc]

theorem natCard_conjClasses_eq_natCard_of_comm {G : Type*} [Group G]
    (hcomm : ∀ x y : G, x * y = y * x) : Nat.card (ConjClasses G) = Nat.card G := by
  refine (Nat.card_congr (Equiv.ofBijective (ConjClasses.mk : G → ConjClasses G)
    ⟨fun x y hxy => ?_, ConjClasses.mk_surjective⟩)).symm
  obtain ⟨c, hc⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hxy)
  rw [← hc, hcomm c x]
  group

theorem natCard_fixed_Irr_eq_natCard_autFixedSubgroup {K : Type*} [Group K] [Finite K]
    {b : MulAut K} (hq : q.Prime) (hqK : ¬ q ∣ Nat.card K) (hbq : b ^ q = 1)
    (hcomm : ∀ x y : autFixedSubgroup b, x * y = y * x) :
    Nat.card {χ : Irr K // irrAut b χ = χ} = Nat.card (autFixedSubgroup b) := by
  rw [natCard_fixed_Irr_eq_natCard_conjClasses_autFixed hq hqK hbq,
    natCard_conjClasses_eq_natCard_of_comm hcomm]

theorem natCard_nonprincipal_fixed_Irr {K : Type*} [Group K] [Finite K] {b : MulAut K} :
    Nat.card {χ : Irr K // irrAut b χ = χ ∧ (χ : K → ℂ) ≠ 1}
      = Nat.card {χ : Irr K // irrAut b χ = χ} - 1 := by
  classical
  have : Fintype {χ : Irr K // irrAut b χ = χ} := Fintype.ofFinite _
  set a : {χ : Irr K // irrAut b χ = χ} :=
    ⟨⟨1, one_mem_Irr⟩, (irrAut_eq_self_iff b _).2 fun _ => rfl⟩ with ha
  have hequiv : {χ : Irr K // irrAut b χ = χ ∧ (χ : K → ℂ) ≠ 1}
      ≃ {χ : {χ : Irr K // irrAut b χ = χ} // χ ≠ a} := by
    refine ⟨fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩, fun y => ⟨y.1.1, y.1.2, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · intro hc
      exact x.2.2 (congrArg (fun t : {χ : Irr K // irrAut b χ = χ} => ((t : Irr K) : K → ℂ)) hc)
    · intro hc
      exact y.2 (Subtype.ext (Subtype.ext hc))
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl]
  simp

noncomputable def zmodPowHom {G : Type*} [Group G] {n : ℕ} [NeZero n] {g : G} (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G where
  toFun a := g ^ (Multiplicative.toAdd a).val
  map_one' := by
    change g ^ (0 : ZMod n).val = 1
    simp
  map_mul' a b := by
    have hord : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hg
    have key : ∀ m : ℕ, g ^ (m % n) = g ^ m := fun m =>
      pow_eq_pow_iff_modEq.2 ((Nat.mod_modEq m n).of_dvd hord)
    change g ^ ((Multiplicative.toAdd a + Multiplicative.toAdd b) : ZMod n).val
      = g ^ (Multiplicative.toAdd a).val * g ^ (Multiplicative.toAdd b).val
    rw [ZMod.val_add, key, pow_add]

theorem zmodPowHom_apply {G : Type*} [Group G] {n : ℕ} [NeZero n] {g : G} (hg : g ^ n = 1)
    (a : ZMod n) : zmodPowHom hg (Multiplicative.ofAdd a) = g ^ a.val := (rfl)

theorem zmodPowHom_one_gen {G : Type*} [Group G] {n : ℕ} [NeZero n] (hn : 1 < n) {g : G}
    (hg : g ^ n = 1) : zmodPowHom hg (Multiplicative.ofAdd (1 : ZMod n)) = g := by
  rw [zmodPowHom_apply, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn, pow_one]

section SemidirectChars

variable {K B : Type*} [Group K] [Group B] {φ : B →* MulAut K}

theorem conj_inl_eq (a k : K) (β : B) :
    ((inl a * inr β : K ⋊[φ] B))⁻¹ * inl k * (inl a * inr β)
      = inl (φ β⁻¹ (a⁻¹ * k * a)) := by
  have h0 := inl_aut (φ := φ) β⁻¹ (a⁻¹ * k * a)
  rw [inv_inv] at h0
  calc ((inl a * inr β : K ⋊[φ] B))⁻¹ * inl k * (inl a * inr β)
      = (inr β)⁻¹ * ((inl a)⁻¹ * inl k * inl a) * inr β := by group
    _ = (inr β)⁻¹ * inl (a⁻¹ * k * a) * inr β := by rw [map_mul, map_mul, map_inv]
    _ = (inr β⁻¹) * inl (a⁻¹ * k * a) * inr β := by rw [map_inv]
    _ = inl (φ β⁻¹ (a⁻¹ * k * a)) := h0.symm

theorem apply_conj_inv {θ : K → ℂ} (hθ : θ ∈ classFun K) (c x : K) :
    θ (c⁻¹ * x * c) = θ x := by
  have h := classFun.apply_conj hθ x c⁻¹
  rw [inv_inv] at h
  exact h

def charStabilizer (φ : B →* MulAut K) (θ : K → ℂ) : Subgroup B where
  carrier := {β | ∀ k : K, θ (φ β k) = θ k}
  one_mem' k := by simp
  mul_mem' {a b} ha hb k := by rw [map_mul, MulAut.mul_apply, ha, hb]
  inv_mem' {a} ha k := by
    have h := ha (φ a⁻¹ k)
    have hk : (φ a) (φ a⁻¹ k) = k := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [hk] at h
    exact h.symm

theorem mem_charStabilizer {θ : K → ℂ} {β : B} :
    β ∈ charStabilizer φ θ ↔ ∀ k : K, θ (φ β k) = θ k := Iff.rfl

theorem mem_inertiaGroup_range_inl_iff {θ : K → ℂ} (hθ : θ ∈ classFun K) {x : K ⋊[φ] B} :
    x ∈ inertiaGroup (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ)
      ↔ x.right ∈ charStabilizer φ θ := by
  have key : ∀ k : K, (((MulAut.conjNormal x⁻¹) (⟨inl k, ⟨k, rfl⟩⟩ :
      (inl : K →* K ⋊[φ] B).range) : K ⋊[φ] B))
      = inl (φ x.right⁻¹ (x.left⁻¹ * k * x.left)) := by
    intro k
    rw [MulAut.conjNormal_apply, inv_inv]
    have hx : (inl x.left * inr x.right : K ⋊[φ] B) = x := inl_left_mul_inr_right x
    calc (x : K ⋊[φ] B)⁻¹ * (inl k) * x
        = ((inl x.left * inr x.right : K ⋊[φ] B))⁻¹ * inl k * (inl x.left * inr x.right) := by
          rw [hx]
      _ = inl (φ x.right⁻¹ (x.left⁻¹ * k * x.left)) := conj_inl_eq x.left k x.right
  rw [mem_inertiaGroup]
  constructor
  · intro h
    refine (charStabilizer φ θ).inv_mem_iff.1 (mem_charStabilizer.2 fun k => ?_)
    have hk := congrFun h ⟨inl k, ⟨k, rfl⟩⟩
    rw [NormalInduction.conjClassFun_apply, kernelClassFun_apply, kernelClassFun_apply,
      key k] at hk
    simp only [left_inl] at hk
    rw [map_mul, map_mul, map_inv, apply_conj_inv hθ] at hk
    exact hk
  · intro hst
    have h : ∀ k : K, θ (φ x.right⁻¹ k) = θ k :=
      mem_charStabilizer.1 ((charStabilizer φ θ).inv_mem hst)
    funext n
    obtain ⟨k, hk⟩ := n.2
    have hn : n = (⟨inl k, ⟨k, rfl⟩⟩ : (inl : K →* K ⋊[φ] B).range) := Subtype.ext hk.symm
    subst hn
    rw [NormalInduction.conjClassFun_apply, kernelClassFun_apply, kernelClassFun_apply, key k]
    simp only [left_inl]
    rw [map_mul, map_mul, map_inv, apply_conj_inv hθ, h]

theorem inertiaGroup_range_inl_eq_comap {θ : K → ℂ} (hθ : θ ∈ classFun K) :
    inertiaGroup (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ)
      = (charStabilizer φ θ).comap (rightHom : K ⋊[φ] B →* B) := by
  ext x
  rw [Subgroup.mem_comap, rightHom_eq_right]
  exact mem_inertiaGroup_range_inl_iff hθ

theorem relIndex_range_inl_comap [Finite K] [Finite B] (J : Subgroup B) :
    ((inl : K →* K ⋊[φ] B).range).relIndex (J.comap (rightHom : K ⋊[φ] B →* B))
      = Nat.card J := by
  have hr : (rightHom : K ⋊[φ] B →* B).range = ⊤ :=
    MonoidHom.range_eq_top.2 rightHom_surjective
  rw [range_inl_eq_ker_rightHom, Subgroup.relIndex_ker, Subgroup.map_comap_eq, hr, top_inf_eq]

theorem cfInner_self_indClassFun_kernelClassFun_eq [Finite K] [Finite B] [Fintype (K ⋊[φ] B)]
    {θ : K → ℂ} (hθ : θ ∈ Irr K) :
    cfInner (indClassFun (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ))
        (indClassFun (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ))
      = (Nat.card (charStabilizer φ θ) : ℂ) := by
  rw [cfInner_self_indClassFun _ (kernelClassFun_mem_Irr hθ),
    inertiaGroup_range_inl_eq_comap (Irr_subset_classFun hθ), relIndex_range_inl_comap]

theorem indClassFun_mem_Irr_of_charStabilizer_eq_bot [Finite K] [Finite B] [Fintype (K ⋊[φ] B)]
    {θ : K → ℂ} (hθ : θ ∈ Irr K) (hst : charStabilizer φ θ = ⊥) :
    indClassFun (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ) ∈ Irr (K ⋊[φ] B) := by
  refine indClassFun_mem_Irr_of_inertiaGroup_eq (kernelClassFun_mem_Irr hθ) ?_
  rw [inertiaGroup_range_inl_eq_comap (Irr_subset_classFun hθ), hst, range_inl_eq_ker_rightHom]
  simp [MonoidHom.ker]

theorem indClassFun_ne_of_charStabilizer_eq_top [Finite K] [Finite B] [Fintype (K ⋊[φ] B)]
    {θ θ' : K → ℂ} (hθ : θ ∈ Irr K) (hθ' : θ' ∈ Irr K)
    (hinv : charStabilizer φ θ' = ⊤) (hne : θ ≠ θ') :
    indClassFun (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ)
      ≠ indClassFun (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ') := by
  intro heq
  have hzero : cfInner (indClassFun (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ))
      (indClassFun (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ')) = 0 := by
    refine cfInner_indClassFun_indClassFun_eq_zero _ (kernelClassFun_mem_Irr hθ)
      (kernelClassFun_mem_Irr hθ') fun t hc => ?_
    have ht : t ∈ inertiaGroup (inl : K →* K ⋊[φ] B).range (kernelClassFun φ θ') := by
      rw [inertiaGroup_range_inl_eq_comap (Irr_subset_classFun hθ'), hinv]
      simp
    rw [mem_inertiaGroup] at ht
    rw [ht] at hc
    exact hne (kernelClassFun_injective hc.symm)
  rw [heq, cfInner_self_indClassFun_kernelClassFun_eq hθ'] at hzero
  exact (Nat.card_pos (α := (charStabilizer φ θ' : Type _))).ne' (Nat.cast_eq_zero.1 hzero)

end SemidirectChars

variable (S : ScalarCoordinateSystem p q V U)

theorem base_eq_range_inl : S.base = (inl : Multiplicative V →* S.grp).range := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨y, hy⟩ := S.baseEquiv.surjective ⟨x, hx⟩
    refine ⟨y, ?_⟩
    have h1 : ((S.baseEquiv y : S.base) : S.grp) = x := congrArg Subtype.val hy
    rw [S.baseEquiv_apply, S.coe_baseHom_apply] at h1
    exact h1
  · rintro x ⟨y, rfl⟩
    exact S.inl_mem_base y

noncomputable def core : Subgroup S.grp := S.totalCentralizer.map (inr : U →* S.grp)

theorem inr_mem_core {c : U} (hc : c ∈ S.totalCentralizer) : (inr c : S.grp) ∈ core S :=
  ⟨c, hc, rfl⟩

theorem core_le_range_inr : core S ≤ (inr : U →* S.grp).range := by
  rintro x ⟨c, -, rfl⟩; exact ⟨c, rfl⟩

theorem inr_commute_inl {c : U} (hc : c ∈ S.totalCentralizer) (x : Multiplicative V) :
    (inr c : S.grp) * inl x = inl x * inr c := by
  have h : (S.mulAutHom c) x = x := by
    obtain ⟨v, rfl⟩ : ∃ v : V, Multiplicative.ofAdd v = x := ⟨Multiplicative.toAdd x, rfl⟩
    rw [S.mulAutHom_apply, S.mem_totalCentralizer.1 hc]
  have h2 := inl_aut (φ := S.mulAutHom) c x
  rw [h, map_inv] at h2
  conv_rhs => rw [h2]
  group

theorem core_le_centralizer_base : core S ≤ Subgroup.centralizer (S.base : Set S.grp) := by
  rintro x ⟨c, hc, rfl⟩
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [SetLike.mem_coe, base_eq_range_inl] at hy
  obtain ⟨z, rfl⟩ := hy
  exact (inr_commute_inl S hc z).symm

theorem core_eq_centralizer_inf :
    core S = Subgroup.centralizer (S.base : Set S.grp) ⊓ (inr : U →* S.grp).range := by
  refine le_antisymm (le_inf (core_le_centralizer_base S) (core_le_range_inr S)) ?_
  rintro x ⟨hx1, u, rfl⟩
  refine inr_mem_core S (S.mem_totalCentralizer.2 fun v => ?_)
  have h := Subgroup.mem_centralizer_iff.1 hx1 (inl (Multiplicative.ofAdd v))
    (by rw [SetLike.mem_coe, base_eq_range_inl]; exact ⟨_, rfl⟩)
  have h2 := inl_aut (φ := S.mulAutHom) u (Multiplicative.ofAdd v)
  rw [S.mulAutHom_apply] at h2
  have h3 : (inl (Multiplicative.ofAdd (S.act u v)) : S.grp) = inl (Multiplicative.ofAdd v) := by
    rw [h2, ← h, map_inv]
    group
  exact congrArg Multiplicative.toAdd (inl_injective h3)

instance core_normal : (core S).Normal := by
  rw [core_eq_centralizer_inf]
  refine normal_centralizer_inf_of_isComplement _ _ ?_
  rw [base_eq_range_inl]
  exact isComplement'_range_inl_range_inr S.mulAutHom

noncomputable def baseCore : Subgroup S.grp := S.totalCentralizer.comap (rightHom : S.grp →* U)

theorem mem_baseCore {x : S.grp} : x ∈ baseCore S ↔ x.right ∈ S.totalCentralizer := by
  rw [baseCore, Subgroup.mem_comap, rightHom_eq_right]

instance baseCore_normal : (baseCore S).Normal := (S.totalCentralizer_normal).comap _

theorem base_le_baseCore : S.base ≤ baseCore S := by
  intro x hx
  rw [base_eq_range_inl] at hx
  obtain ⟨v, rfl⟩ := hx
  rw [mem_baseCore]
  simp

theorem inr_mem_baseCore {c : U} (hc : c ∈ S.totalCentralizer) : (inr c : S.grp) ∈ baseCore S := by
  rw [mem_baseCore]
  simpa using hc

theorem index_baseCore : (baseCore S).index = S.totalCentralizer.index :=
  Subgroup.index_comap_of_surjective _ rightHom_surjective

def baseCoreEquiv : baseCore S ≃ Multiplicative V × S.totalCentralizer where
  toFun x := ((x : S.grp).left, ⟨(x : S.grp).right, (mem_baseCore S).1 x.2⟩)
  invFun z := ⟨⟨z.1, (z.2 : U)⟩, (mem_baseCore S).2 z.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

theorem coe_baseCoreEquiv_symm (v : Multiplicative V) (c : S.totalCentralizer) :
    (((baseCoreEquiv S).symm (v, c) : baseCore S) : S.grp) = inl v * inr (c : U) := by
  rw [← inl_left_mul_inr_right (((baseCoreEquiv S).symm (v, c) : baseCore S) : S.grp)]
  rfl

theorem left_coe_baseCoreEquiv_symm (v : Multiplicative V) (c : S.totalCentralizer) :
    ((((baseCoreEquiv S).symm (v, c) : baseCore S) : S.grp)).left = v := (rfl)

noncomputable def coreExtendHom (χ : Multiplicative V →* ℂˣ) : baseCore S →* ℂˣ where
  toFun x := χ (x : S.grp).left
  map_one' := by simp
  map_mul' x y := by
    have hx : (x : S.grp).right ∈ S.totalCentralizer := (mem_baseCore S).1 x.2
    have hl : ((x * y : baseCore S) : S.grp).left = (x : S.grp).left * (y : S.grp).left := by
      change ((x : S.grp) * (y : S.grp)).left = _
      rw [SemidirectProduct.mul_left]
      congr 1
      obtain ⟨v, hv⟩ : ∃ v : V, Multiplicative.ofAdd v = (y : S.grp).left :=
        ⟨Multiplicative.toAdd (y : S.grp).left, rfl⟩
      rw [← hv, S.mulAutHom_apply, S.mem_totalCentralizer.1 hx]
    rw [hl, map_mul]

theorem coreExtendHom_apply (χ : Multiplicative V →* ℂˣ) (x : baseCore S) :
    coreExtendHom S χ x = χ (x : S.grp).left := (rfl)

theorem coreExtendHom_restrict (χ : Multiplicative V →* ℂˣ) {lam : S.base → ℂ}
    (hχ : ∀ y : Multiplicative V, (χ y : ℂ) = lam (S.baseHom y)) (x : S.base) :
    ((coreExtendHom S χ ⟨(x : S.grp), base_le_baseCore S x.2⟩ : ℂˣ) : ℂ) = lam x := by
  obtain ⟨y, hy⟩ : ∃ y : Multiplicative V, (inl y : S.grp) = (x : S.grp) := by
    have hx : (x : S.grp) ∈ (inl : Multiplicative V →* S.grp).range := by
      rw [← base_eq_range_inl]; exact x.2
    exact hx
  rw [coreExtendHom_apply]
  have hleft : ((⟨(x : S.grp), base_le_baseCore S x.2⟩ : baseCore S) : S.grp).left = y := by
    change (x : S.grp).left = y
    rw [← hy]
    rfl
  rw [hleft, hχ y]
  congr 1
  refine Subtype.ext ?_
  rw [S.coe_baseHom_apply]
  exact hy

theorem inertiaGroup_le_baseCore {lam : S.base → ℂ} (hlam : lam ∈ Irr S.base)
    (χ : Multiplicative V →* ℂˣ) (hχ : ∀ y : Multiplicative V, (χ y : ℂ) = lam (S.baseHom y))
    (hsupp : ∀ i : Fin q, ∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1) :
    inertiaGroup S.base lam ≤ baseCore S := by
  have hbaseI : S.base ≤ inertiaGroup S.base lam :=
    le_inertiaGroup S.base (Irr_subset_classFun hlam)
  intro g hg
  rw [mem_baseCore, S.totalCentralizer_eq_iInf, Subgroup.mem_iInf]
  intro i
  obtain ⟨v, hvline, hvne⟩ := hsupp i
  have hinr : (inr (rightHom g) : S.grp) ∈ inertiaGroup S.base lam := by
    have hgg : (inl g.left : S.grp) * inr g.right = g := inl_left_mul_inr_right g
    have h1 : (inl g.left : S.grp) ∈ inertiaGroup S.base lam := hbaseI (S.inl_mem_base _)
    have h2 : (inr g.right : S.grp) = (inl g.left)⁻¹ * g := eq_inv_mul_of_mul_eq hgg
    rw [rightHom_eq_right, h2]
    exact (inertiaGroup S.base lam).mul_mem ((inertiaGroup S.base lam).inv_mem h1) hg
  have hfix : NormalInduction.conjClassFun S.base (inr (rightHom g)) lam = lam :=
    mem_inertiaGroup.1 hinr
  have hkey : χ (Multiplicative.ofAdd (S.act (rightHom g)⁻¹ v)) = χ (Multiplicative.ofAdd v) := by
    refine Units.ext ?_
    have h := congrFun hfix (S.baseHom (Multiplicative.ofAdd v))
    rw [S.conjClassFun_inr_apply lam (rightHom g) (Multiplicative.ofAdd v), S.mulAutHom_apply] at h
    rw [hχ, hχ, h]
  have hinv : (rightHom g)⁻¹ ∈ S.lineCentralizer i :=
    S.mem_lineCentralizer_of_apply_eq χ hvline hvne hkey
  have hmem := (S.lineCentralizer i).inv_mem hinv
  rw [inv_inv] at hmem
  rw [← rightHom_eq_right]
  exact hmem

theorem baseCore_le_inertiaGroup_coreExtendHom (χ : Multiplicative V →* ℂˣ) :
    baseCore S ≤ inertiaGroup (baseCore S) (fun x => ((coreExtendHom S χ x : ℂˣ) : ℂ)) :=
  le_inertiaGroup _ (mem_classFun_units_coe _)

theorem inertiaGroup_coreExtendHom_eq {lam : S.base → ℂ} (hlam : lam ∈ Irr S.base)
    (χ : Multiplicative V →* ℂˣ) (hχ : ∀ y : Multiplicative V, (χ y : ℂ) = lam (S.baseHom y))
    (hsupp : ∀ i : Fin q, ∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1) :
    inertiaGroup (baseCore S) (fun x => ((coreExtendHom S χ x : ℂˣ) : ℂ)) = baseCore S := by
  refine le_antisymm ?_ (baseCore_le_inertiaGroup_coreExtendHom S χ)
  have hres : (fun x : S.base => ((coreExtendHom S χ
      ⟨(x : S.grp), base_le_baseCore S x.2⟩ : ℂˣ) : ℂ)) = lam :=
    funext (coreExtendHom_restrict S χ hχ)
  have h := inertiaGroup_le_inertiaGroup_of_le (N := S.base) (M := baseCore S)
    (base_le_baseCore S) (fun x => ((coreExtendHom S χ x : ℂˣ) : ℂ))
  rw [hres] at h
  exact h.trans (inertiaGroup_le_baseCore S hlam χ hχ hsupp)

section Degree

variable [Finite S.grp]

include S in
theorem finite_multiplicative_of_finite_grp : Finite (Multiplicative V) :=
  Finite.of_injective (inl : Multiplicative V →* S.grp) inl_injective

include S in
theorem finite_units_of_finite_grp : Finite U :=
  Finite.of_surjective (rightHom : S.grp →* U) rightHom_surjective

theorem cfInner_resClassFun_baseCore [Fintype (baseCore S)] [Fintype S.base]
    {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hker : ((core S : Subgroup S.grp) : Set S.grp) ⊆ charValueKernel θ)
    {lam : S.base → ℂ} (χ : Multiplicative V →* ℂˣ)
    (hχ : ∀ y : Multiplicative V, (χ y : ℂ) = lam (S.baseHom y)) :
    cfInner (resClassFun (baseCore S) θ) (fun x => ((coreExtendHom S χ x : ℂˣ) : ℂ))
      = cfInner (resClassFun S.base θ) lam := by
  have hfinV : Finite (Multiplicative V) := finite_multiplicative_of_finite_grp S
  have hfinU : Finite U := finite_units_of_finite_grp S
  letI : Fintype (Multiplicative V) := Fintype.ofFinite _
  letI : Fintype S.totalCentralizer := Fintype.ofFinite _
  have hTriv : θ ∈ irrTrivialOn (core S) :=
    mem_irrTrivialOn.2 ⟨hθ, fun n hn => mem_charValueKernel.1 (hker hn)⟩
  have hval : ∀ (v : Multiplicative V) (c : S.totalCentralizer),
      θ (inl v * inr (c : U)) = θ (inl v) :=
    fun v c => apply_mul_eq_of_mem_irrTrivialOn hTriv _ (inr_mem_core S c.2)
  have hcpos : 0 < Nat.card S.totalCentralizer := Nat.card_pos
  set A : ℂ := ∑ v : Multiplicative V, θ (inl v) * (starRingEnd ℂ) ((χ v : ℂ)) with hA
  have hL : cfInner (resClassFun (baseCore S) θ) (fun x => ((coreExtendHom S χ x : ℂˣ) : ℂ))
      = ((Nat.card (Multiplicative V) : ℂ) * (Nat.card S.totalCentralizer : ℂ))⁻¹ *
        ((Nat.card S.totalCentralizer : ℂ) * A) := by
    rw [cfInner_def]
    congr 1
    · rw [Nat.card_congr (baseCoreEquiv S), Nat.card_prod]
      push_cast
      ring
    · rw [← Fintype.sum_equiv (baseCoreEquiv S).symm
        (fun z => resClassFun (baseCore S) θ ((baseCoreEquiv S).symm z) *
          (starRingEnd ℂ) ((coreExtendHom S χ ((baseCoreEquiv S).symm z) : ℂˣ) : ℂ))
        (fun x => resClassFun (baseCore S) θ x *
          (starRingEnd ℂ) ((coreExtendHom S χ x : ℂˣ) : ℂ)) (fun z => by simp)]
      rw [Fintype.sum_prod_type, hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hterm : ∀ c : S.totalCentralizer,
          resClassFun (baseCore S) θ ((baseCoreEquiv S).symm (v, c)) *
            (starRingEnd ℂ) ((coreExtendHom S χ ((baseCoreEquiv S).symm (v, c)) : ℂˣ) : ℂ)
            = θ (inl v) * (starRingEnd ℂ) ((χ v : ℂ)) := by
        intro c
        rw [resClassFun_apply, coe_baseCoreEquiv_symm, hval, coreExtendHom_apply,
          left_coe_baseCoreEquiv_symm]
      rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hR : cfInner (resClassFun S.base θ) lam
      = ((Nat.card (Multiplicative V) : ℂ))⁻¹ * A := by
    rw [cfInner_def]
    congr 1
    · rw [Nat.card_congr S.baseEquiv.toEquiv]
    · rw [← Fintype.sum_equiv S.baseEquiv.toEquiv
        (fun v => resClassFun S.base θ (S.baseEquiv v) *
          (starRingEnd ℂ) (lam (S.baseEquiv v)))
        (fun x => resClassFun S.base θ x * (starRingEnd ℂ) (lam x)) (fun v => by simp)]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [resClassFun_apply, S.baseEquiv_apply, S.coe_baseHom_apply, ← hχ v]
  rw [hL, hR]
  have hcne : (Nat.card S.totalCentralizer : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hcpos.ne'
  field_simp

theorem apply_one_eq_index_totalCentralizer [Fintype S.grp] [Fintype (baseCore S)]
    [Fintype S.base] {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hker : ((core S : Subgroup S.grp) : Set S.grp) ⊆ charValueKernel θ)
    {lam : S.base → ℂ} (hlamT : lam ∈ resConstituents S.base θ)
    (χ : Multiplicative V →* ℂˣ) (hχ : ∀ y : Multiplicative V, (χ y : ℂ) = lam (S.baseHom y))
    (hsupp : ∀ i : Fin q, ∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1) :
    θ 1 = ((S.totalCentralizer.index : ℕ) : ℂ) := by
  obtain ⟨hlam, hpos⟩ := mem_resConstituents.1 hlamT
  set ν : baseCore S → ℂ := fun x => ((coreExtendHom S χ x : ℂˣ) : ℂ) with hν
  have hνIrr : ν ∈ Irr (baseCore S) := mem_Irr_units_coe _
  have hind : indClassFun (baseCore S) ν ∈ Irr S.grp :=
    indClassFun_mem_Irr_of_inertiaGroup_eq hνIrr
      (inertiaGroup_coreExtendHom_eq S hlam χ hχ hsupp)
  have hfrob : cfInner (indClassFun (baseCore S) ν) θ = cfInner ν (resClassFun (baseCore S) θ) :=
    cfInner_indClassFun _ ν (Irr_subset_classFun hθ)
  have hconj : cfInner ν (resClassFun (baseCore S) θ)
      = (starRingEnd ℂ) (cfInner (resClassFun (baseCore S) θ) ν) := by
    rw [conj_cfInner]
  have hEC : cfInner (resClassFun (baseCore S) θ) ν = cfInner (resClassFun S.base θ) lam :=
    cfInner_resClassFun_baseCore S hθ hker χ hχ
  have hne : cfInner (indClassFun (baseCore S) ν) θ ≠ 0 := by
    rw [hfrob, hconj, hEC]
    intro h
    have h0 : cfInner (resClassFun S.base θ) lam = 0 := by
      have hc := congrArg (starRingEnd ℂ) h
      rwa [RingHom.map_zero, RingHomCompTriple.comp_apply, RingHom.id_apply] at hc
    rw [h0] at hpos
    exact absurd hpos (by simp)
  have heq : indClassFun (baseCore S) ν = θ := by
    by_contra hcon
    exact hne (cfInner_eq_zero_of_mem_Irr hind hθ hcon)
  rw [← heq, indClassFun_apply_one, hν]
  simp only [map_one, Units.val_one, mul_one]
  rw [index_baseCore]

end Degree

end Aux

structure ScalarInvariantSystem (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (V U : Type*)
    [AddCommGroup V] [Module (ZMod p) V] [Group U]
    extends ScalarCoordinateSystem p q V U where
  not_dvd_card_units : ¬ q ∣ Nat.card U
  ne_prime : q ≠ p
  a : ℕ
  index_lineCentralizer_eq : ∀ i, (toScalarCoordinateSystem.lineCentralizer i).index = a
  one_lt_a : 1 < a
  lineAut : V ≃ₗ[ZMod p] V
  unitAut : MulAut U
  act_unitAut : ∀ u : U, act (unitAut u) = lineAut * act u * lineAut⁻¹
  map_lineAut : ∀ i : Fin q, (line i).map (lineAut : V →ₗ[ZMod p] V) = line (i + 1)
  lineAut_pow : lineAut ^ q = 1
  unitAut_pow : unitAut ^ q = 1
  unitAut_free : ∀ u : U, unitAut u = u → u = 1

namespace ScalarInvariantSystem

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {V U : Type*} [AddCommGroup V]
  [Module (ZMod p) V] [Group U] (S : ScalarInvariantSystem p q V U)

def lineAutMul : Multiplicative V ≃* Multiplicative V :=
  AddEquiv.toMultiplicative S.lineAut.toAddEquiv

@[simp] theorem lineAutMul_apply (v : V) :
    S.lineAutMul (Multiplicative.ofAdd v) = Multiplicative.ofAdd (S.lineAut v) := (rfl)

def semiAut : MulAut S.grp :=
  SemidirectProduct.congr S.lineAutMul S.unitAut (by
    intro u
    refine MulEquiv.ext fun x => ?_
    obtain ⟨v, rfl⟩ : ∃ v : V, Multiplicative.ofAdd v = x := ⟨Multiplicative.toAdd x, rfl⟩
    simp only [MulEquiv.trans_apply, S.mulAutHom_apply, lineAutMul_apply]
    rw [S.act_unitAut u]
    simp)

@[simp] theorem semiAut_left (x : S.grp) : (S.semiAut x).left
    = Multiplicative.ofAdd (S.lineAut (Multiplicative.toAdd x.left)) := (rfl)

@[simp] theorem semiAut_right (x : S.grp) : (S.semiAut x).right = S.unitAut x.right := (rfl)

theorem semiAut_inr (u : U) : S.semiAut (inr u) = inr (S.unitAut u) :=
  SemidirectProduct.ext (by simp) (by simp)

theorem semiAut_inl (x : Multiplicative V) : S.semiAut (inl x) = inl (S.lineAutMul x) :=
  SemidirectProduct.ext (by simp [lineAutMul]) (by simp)

theorem semiAut_pow_left (n : ℕ) (x : S.grp) : ((S.semiAut ^ n) x).left
    = Multiplicative.ofAdd ((S.lineAut ^ n) (Multiplicative.toAdd x.left)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, semiAut_left, ih, pow_succ']; rfl

theorem semiAut_pow_right (n : ℕ) (x : S.grp) :
    ((S.semiAut ^ n) x).right = (S.unitAut ^ n) x.right := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', MulAut.mul_apply, semiAut_right, ih, pow_succ']; rfl

theorem semiAut_pow_eq_one : S.semiAut ^ q = 1 := by
  ext x
  · have h := S.semiAut_pow_left q x
    rw [S.lineAut_pow] at h
    rw [h]; rfl
  · have h := S.semiAut_pow_right q x
    rw [S.unitAut_pow] at h
    rw [h]; rfl

include S in
theorem finite_base : Finite V := S.finite_of_finite_line

include S in
theorem finite_units : Finite U := by
  have h := S.coprime_card
  rcases Nat.eq_zero_or_pos (Nat.card U) with h0 | h0
  · rw [h0] at h
    exact absurd ((Nat.coprime_zero_right p).1 h) (Nat.Prime.ne_one (Fact.out))
  · exact Nat.finite_of_card_ne_zero h0.ne'

instance finite_grp : Finite S.grp := by
  have : Finite V := S.finite_base
  have : Finite U := S.finite_units
  infer_instance

include S in
theorem not_dvd_natCard_grp : ¬ q ∣ Nat.card S.grp := by
  have hfin : Finite V := S.finite_base
  have hV : ¬ q ∣ Nat.card (Multiplicative V) := by
    have : Fintype V := Fintype.ofFinite V
    have hc := Module.card_eq_pow_finrank (K := ZMod p) (V := V)
    rw [ZMod.card] at hc
    have hcard : Nat.card (Multiplicative V) = p ^ finrank (ZMod p) V := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, hc]
    rw [hcard]
    intro hd
    exact S.ne_prime ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).1
      (Nat.Prime.dvd_of_dvd_pow (Fact.out) hd))
  intro hd
  rw [SemidirectProduct.card] at hd
  rcases (Nat.Prime.dvd_mul (Fact.out)).1 hd with h | h
  · exact hV h
  · exact S.not_dvd_card_units h

def fixedLine : Submodule (ZMod p) V := (S.lineAut : V →ₗ[ZMod p] V).fixedSubmodule

theorem fixedLine_eq : S.fixedLine = (S.lineAut : V →ₗ[ZMod p] V).fixedSubmodule := (rfl)

theorem mem_fixedLine {v : V} : v ∈ S.fixedLine ↔ S.lineAut v = v := Iff.rfl

theorem natCard_fixedLine : Nat.card S.fixedLine = p := by
  classical
  set e := (ZMod.finEquiv q).symm with he
  set W : ZMod q → Submodule (ZMod p) V := fun j => S.line (e j) with hW
  have hinj : Function.Injective (fun j : ZMod q => e j) := (ZMod.finEquiv q).symm.injective
  have hindep : iSupIndep W := S.indep_line.comp hinj
  have hsup : iSup W = ⊤ := by
    rw [hW, ← S.iSup_line]
    exact (ZMod.finEquiv q).toEquiv.symm.iSup_comp (g := S.line)
  have hint : DirectSum.IsInternal W :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W).2 ⟨hindep, hsup⟩
  have hmapW : ∀ j : ZMod q, (W j).map (S.lineAut : V →ₗ[ZMod p] V) = W (j + 1) := by
    intro j
    rw [hW]
    change (S.line (e j)).map (S.lineAut : V →ₗ[ZMod p] V) = S.line (e (j + 1))
    rw [S.map_lineAut (e j)]
    congr 1
    simp [he]
  have hpow : (S.lineAut : V →ₗ[ZMod p] V) ^ q = 1 := by
    rw [← coe_pow_linearEquiv, S.lineAut_pow]; rfl
  have hequiv := fixedSubmoduleEquivOfCyclicOrbit hint hmapW hpow
  have hfin : Finite V := S.finite_base
  refine natCard_eq_of_finrank_eq_one _ ?_
  rw [fixedLine_eq, hequiv.finrank_eq, hW]
  exact S.finrank_line _

theorem right_eq_one_of_mem_autFixed {x : S.grp} (hx : S.semiAut x = x) : x.right = 1 := by
  refine S.unitAut_free _ ?_
  have h := congrArg SemidirectProduct.right hx
  rwa [semiAut_right] at h

theorem left_mem_fixedLine_of_mem_autFixed {x : S.grp} (hx : S.semiAut x = x) :
    Multiplicative.toAdd x.left ∈ S.fixedLine := by
  have h := congrArg SemidirectProduct.left hx
  rw [semiAut_left] at h
  exact congrArg Multiplicative.toAdd h

def autFixedHom : autFixedSubgroup S.semiAut →* Multiplicative S.fixedLine where
  toFun x := Multiplicative.ofAdd
    (⟨Multiplicative.toAdd (x : S.grp).left,
      S.left_mem_fixedLine_of_mem_autFixed (mem_autFixedSubgroup.1 x.2)⟩ : S.fixedLine)
  map_one' := rfl
  map_mul' x y := by
    refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
    have hx1 : (x : S.grp).right = 1 := S.right_eq_one_of_mem_autFixed (mem_autFixedSubgroup.1 x.2)
    change Multiplicative.toAdd ((x : S.grp) * (y : S.grp)).left
      = Multiplicative.toAdd (x : S.grp).left + Multiplicative.toAdd (y : S.grp).left
    rw [SemidirectProduct.mul_left, hx1]
    simp

theorem autFixedHom_apply (x : autFixedSubgroup S.semiAut) :
    S.autFixedHom x = Multiplicative.ofAdd
      (⟨Multiplicative.toAdd (x : S.grp).left,
        S.left_mem_fixedLine_of_mem_autFixed (mem_autFixedSubgroup.1 x.2)⟩ : S.fixedLine) := (rfl)

noncomputable def autFixedMulEquiv : autFixedSubgroup S.semiAut ≃* Multiplicative S.fixedLine := by
  refine MulEquiv.ofBijective S.autFixedHom ⟨?_, ?_⟩
  · intro x y hxy
    rw [S.autFixedHom_apply, S.autFixedHom_apply] at hxy
    have hl : (x : S.grp).left = (y : S.grp).left := congrArg Multiplicative.ofAdd
      (congrArg Subtype.val (Multiplicative.ofAdd.injective hxy))
    have hx1 : (x : S.grp).right = 1 := S.right_eq_one_of_mem_autFixed (mem_autFixedSubgroup.1 x.2)
    have hy1 : (y : S.grp).right = 1 := S.right_eq_one_of_mem_autFixed (mem_autFixedSubgroup.1 y.2)
    exact Subtype.ext (SemidirectProduct.ext hl (by rw [hx1, hy1]))
  · intro w
    set v : V := ((Multiplicative.toAdd w : S.fixedLine) : V) with hvdef
    have hv : v ∈ S.fixedLine := (Multiplicative.toAdd w : S.fixedLine).2
    refine ⟨⟨inl (Multiplicative.ofAdd v), mem_autFixedSubgroup.2 ?_⟩, ?_⟩
    · refine SemidirectProduct.ext ?_ ?_
      · rw [semiAut_left]
        change Multiplicative.ofAdd (S.lineAut v) = Multiplicative.ofAdd v
        rw [S.mem_fixedLine.1 hv]
      · rw [semiAut_right]
        simp
    · rw [S.autFixedHom_apply]
      refine (Multiplicative.toAdd (α := S.fixedLine)).injective (Subtype.ext ?_)
      rfl

theorem natCard_autFixedSubgroup_semiAut :
    Nat.card (autFixedSubgroup S.semiAut) = p := by
  rw [Nat.card_congr S.autFixedMulEquiv.toEquiv,
    Nat.card_congr (Multiplicative.toAdd (α := S.fixedLine)), S.natCard_fixedLine]

theorem natCard_invariantNonprincipalIrr :
    Nat.card {χ : Irr S.grp // irrAut S.semiAut χ = χ ∧ (χ : S.grp → ℂ) ≠ 1} = p - 1 := by
  rw [natCard_nonprincipal_fixed_Irr,
    natCard_fixed_Irr_eq_natCard_autFixedSubgroup (Fact.out) S.not_dvd_natCard_grp
      S.semiAut_pow_eq_one ?_, S.natCard_autFixedSubgroup_semiAut]
  intro x y
  have hcomm : ∀ z w : autFixedSubgroup S.semiAut, (z : S.grp) * (w : S.grp)
      = (w : S.grp) * (z : S.grp) := by
    intro z w
    have hz1 : (z : S.grp).right = 1 := S.right_eq_one_of_mem_autFixed (mem_autFixedSubgroup.1 z.2)
    have hw1 : (w : S.grp).right = 1 := S.right_eq_one_of_mem_autFixed (mem_autFixedSubgroup.1 w.2)
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, hz1, hw1]
      simp [mul_comm]
    · rw [SemidirectProduct.mul_right, SemidirectProduct.mul_right, hz1, hw1]
  exact Subtype.ext (hcomm x y)

theorem core_subset_charValueKernel {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hθb : ∀ x : S.grp, θ (S.semiAut x) = θ x) :
    ((core S.toScalarCoordinateSystem : Subgroup S.grp) : Set S.grp) ⊆ charValueKernel θ := by
  have hcore := core_eq_centralizer_inf S.toScalarCoordinateSystem
  rw [hcore]
  refine subset_charValueKernel_centralizer_inf_of_fixed (E := S.base)
    (U := (inr : U →* S.grp).range) (Fact.out) S.not_dvd_natCard_grp S.semiAut_pow_eq_one ?_ ?_ ?_
    ?_ hθ hθb
  · rw [base_eq_range_inl]
    exact isComplement'_range_inl_range_inr S.mulAutHom
  · intro x hx
    rw [base_eq_range_inl] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨S.lineAutMul y, (S.semiAut_inl y).symm⟩
  · rintro x ⟨u, rfl⟩
    exact ⟨S.unitAut u, (S.semiAut_inr u).symm⟩
  · rintro x ⟨u, rfl⟩ hx
    rw [S.semiAut_inr u] at hx
    rw [S.unitAut_free u (inr_injective hx)]
    simp

theorem not_base_subset_charValueKernel {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hθb : ∀ x : S.grp, θ (S.semiAut x) = θ x) (hθ1 : θ ≠ 1) :
    ¬ ((S.base : Set S.grp) ⊆ charValueKernel θ) := by
  refine not_subset_charValueKernel_of_fixed_of_ne_one (E := S.base)
    (U := (inr : U →* S.grp).range) (Fact.out) S.not_dvd_natCard_grp S.semiAut_pow_eq_one ?_ ?_ ?_
    ?_ hθ hθb hθ1
  · rw [base_eq_range_inl]
    exact isComplement'_range_inl_range_inr S.mulAutHom
  · intro x hx
    rw [base_eq_range_inl] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨S.lineAutMul y, (S.semiAut_inl y).symm⟩
  · rintro x ⟨u, rfl⟩
    exact ⟨S.unitAut u, (S.semiAut_inr u).symm⟩
  · rintro x ⟨u, rfl⟩ hx
    rw [S.semiAut_inr u] at hx
    rw [S.unitAut_free u (inr_injective hx)]
    simp

noncomputable def bAutHom : Multiplicative (ZMod q) →* MulAut S.grp :=
  zmodPowHom S.semiAut_pow_eq_one

theorem bAutHom_gen : S.bAutHom (Multiplicative.ofAdd (1 : ZMod q)) = S.semiAut :=
  zmodPowHom_one_gen (Nat.Prime.one_lt (Fact.out)) S.semiAut_pow_eq_one

noncomputable abbrev bigGrp : Type _ := S.grp ⋊[S.bAutHom] Multiplicative (ZMod q)

noncomputable abbrev grpPart : Subgroup S.bigGrp := (inl : S.grp →* S.bigGrp).range

instance : Finite S.bigGrp := inferInstance

noncomputable instance : Fintype S.bigGrp := Fintype.ofFinite _

theorem charStabilizer_eq_top_iff {θ : S.grp → ℂ} :
    charStabilizer S.bAutHom θ = ⊤ ↔ ∀ x : S.grp, θ (S.semiAut x) = θ x := by
  constructor
  · intro h x
    have h1 : Multiplicative.ofAdd (1 : ZMod q) ∈ charStabilizer S.bAutHom θ := by
      rw [h]; trivial
    have h2 := mem_charStabilizer.1 h1 x
    rwa [S.bAutHom_gen] at h2
  · intro h
    refine eq_top_iff.2 fun β _ => mem_charStabilizer.2 fun x => ?_
    have key : ∀ n : ℕ, ∀ y : S.grp, θ ((S.semiAut ^ n) y) = θ y := by
      intro n
      induction n with
      | zero => intro y; rfl
      | succ n ih =>
        intro y
        rw [pow_succ', MulAut.mul_apply, h ((S.semiAut ^ n) y), ih]
    have hb : S.bAutHom β = S.semiAut ^ (Multiplicative.toAdd β).val := (rfl)
    rw [hb]
    exact key (Multiplicative.toAdd β).val x

theorem natCard_charStabilizer_of_invariant {θ : S.grp → ℂ}
    (hinv : ∀ x : S.grp, θ (S.semiAut x) = θ x) :
    Nat.card (charStabilizer S.bAutHom θ) = q := by
  rw [(S.charStabilizer_eq_top_iff).2 hinv]
  rw [Nat.card_congr (Subgroup.topEquiv (G := Multiplicative (ZMod q))).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem charStabilizer_eq_bot_of_not_invariant {θ : S.grp → ℂ}
    (hmove : ¬ (∀ x : S.grp, θ (S.semiAut x) = θ x)) :
    charStabilizer S.bAutHom θ = ⊥ := by
  have hcard : Nat.card (Multiplicative (ZMod q)) = q := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hdvd : Nat.card (charStabilizer S.bAutHom θ) ∣ q := by
    have h := Subgroup.card_subgroup_dvd_card (charStabilizer S.bAutHom θ)
    rwa [hcard] at h
  rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out) _ hdvd) with h | h
  · exact (Subgroup.card_eq_one).1 h
  · exact absurd (S.charStabilizer_eq_top_iff.1
      (Subgroup.eq_top_of_card_eq _ (by rw [h, hcard]))) hmove

theorem cfInner_self_indClassFun_of_invariant {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hinv : ∀ x : S.grp, θ (S.semiAut x) = θ x) :
    cfInner (indClassFun S.grpPart (kernelClassFun S.bAutHom θ))
        (indClassFun S.grpPart (kernelClassFun S.bAutHom θ)) = (q : ℂ) := by
  rw [cfInner_self_indClassFun_kernelClassFun_eq hθ, S.natCard_charStabilizer_of_invariant hinv]

theorem indClassFun_ne_indClassFun_of_invariant {θ θ' : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hθ' : θ' ∈ Irr S.grp) (hinv' : ∀ x : S.grp, θ' (S.semiAut x) = θ' x) (hne : θ ≠ θ') :
    indClassFun S.grpPart (kernelClassFun S.bAutHom θ)
      ≠ indClassFun S.grpPart (kernelClassFun S.bAutHom θ') :=
  indClassFun_ne_of_charStabilizer_eq_top hθ hθ' (S.charStabilizer_eq_top_iff.2 hinv') hne

theorem indClassFun_mem_Irr_of_not_invariant {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hmove : ¬ (∀ x : S.grp, θ (S.semiAut x) = θ x)) :
    indClassFun S.grpPart (kernelClassFun S.bAutHom θ) ∈ Irr S.bigGrp :=
  indClassFun_mem_Irr_of_charStabilizer_eq_bot hθ (S.charStabilizer_eq_bot_of_not_invariant hmove)

theorem mapsTo_base_semiAut : ∀ x ∈ S.base, S.semiAut x ∈ S.base := by
  intro x hx
  rw [base_eq_range_inl] at hx ⊢
  obtain ⟨v, rfl⟩ := hx
  exact ⟨S.lineAutMul v, (S.semiAut_inl v).symm⟩

theorem mapsTo_base_semiAut_symm : ∀ x ∈ S.base, S.semiAut.symm x ∈ S.base := by
  intro x hx
  rw [base_eq_range_inl] at hx ⊢
  obtain ⟨v, rfl⟩ := hx
  refine ⟨S.lineAutMul.symm v, ?_⟩
  refine S.semiAut.injective ?_
  rw [MulEquiv.apply_symm_apply, S.semiAut_inl]
  simp

noncomputable def baseAut : MulAut S.base :=
  mulAutSubgroupRestrict S.semiAut S.base S.mapsTo_base_semiAut S.mapsTo_base_semiAut_symm

theorem coe_baseAut (x : S.base) : ((S.baseAut x : S.base) : S.grp) = S.semiAut (x : S.grp) :=
  coe_mulAutSubgroupRestrict x

theorem baseAut_pow_eq_one : S.baseAut ^ q = 1 :=
  mulAutSubgroupRestrict_pow_eq_one S.semiAut_pow_eq_one

theorem baseAut_baseHom (v : V) : (S.baseAut (S.baseHom (Multiplicative.ofAdd v)) : S.base)
    = S.baseHom (Multiplicative.ofAdd (S.lineAut v)) := by
  refine Subtype.ext ?_
  rw [S.coe_baseAut, S.coe_baseHom_apply, S.coe_baseHom_apply, S.semiAut_inl, S.lineAutMul_apply]

noncomputable def lineZ (j : ZMod q) : Submodule (ZMod p) V := S.line ((ZMod.finEquiv q).symm j)

theorem lineZ_finEquiv (i : Fin q) : S.lineZ (ZMod.finEquiv q i) = S.line i := by
  rw [lineZ]; congr 1; simp

theorem map_lineAut_lineZ (j : ZMod q) :
    (S.lineZ j).map (S.lineAut : V →ₗ[ZMod p] V) = S.lineZ (j + 1) := by
  rw [lineZ, lineZ, S.map_lineAut]
  congr 1
  have : NeZero q := ⟨(Nat.Prime.pos (Fact.out)).ne'⟩
  simp

theorem mem_lineZ_add_iff (n : ℕ) (j : ZMod q) {v : V} :
    (S.lineAut ^ n) v ∈ S.lineZ (j + (n : ZMod q)) ↔ v ∈ S.lineZ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((S.lineAut ^ (n + 1) : V ≃ₗ[ZMod p] V)) v
        = S.lineAut ((S.lineAut ^ n : V ≃ₗ[ZMod p] V) v) := by
      rw [pow_succ']; rfl
    have h2 : (S.lineAut ((S.lineAut ^ n : V ≃ₗ[ZMod p] V) v)
        ∈ S.lineZ (j + ((n + 1 : ℕ) : ZMod q)))
        ↔ ((S.lineAut ^ n : V ≃ₗ[ZMod p] V) v ∈ S.lineZ (j + (n : ZMod q))) := by
      have hcast : j + ((n + 1 : ℕ) : ZMod q) = (j + (n : ZMod q)) + 1 := by push_cast; ring
      rw [hcast, ← S.map_lineAut_lineZ]
      constructor
      · rintro ⟨w, hw, hwe⟩
        have hwv : w = (S.lineAut ^ n : V ≃ₗ[ZMod p] V) v := S.lineAut.injective hwe
        rwa [← hwv]
      · intro h
        exact ⟨_, h, rfl⟩
    rw [h1, h2, ih]

theorem exists_mem_line_apply_ne_one_of_lineAut_invariant (χ : Multiplicative V →* ℂˣ)
    (hχinv : ∀ v : V, χ (Multiplicative.ofAdd (S.lineAut v)) = χ (Multiplicative.ofAdd v))
    (hχ1 : ∃ v : V, χ (Multiplicative.ofAdd v) ≠ 1) (i : Fin q) :
    ∃ v ∈ S.line i, χ (Multiplicative.ofAdd v) ≠ 1 := by
  have : NeZero q := ⟨(Nat.Prime.pos (Fact.out)).ne'⟩
  have hpow : ∀ (n : ℕ) (v : V),
      χ (Multiplicative.ofAdd ((S.lineAut ^ n : V ≃ₗ[ZMod p] V) v))
        = χ (Multiplicative.ofAdd v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      have h1 : ((S.lineAut ^ (n + 1) : V ≃ₗ[ZMod p] V)) v
          = (S.lineAut ^ n : V ≃ₗ[ZMod p] V) (S.lineAut v) := by
        rw [pow_succ]; rfl
      rw [h1, ih (S.lineAut v), hχinv]
  by_contra hcon
  push Not at hcon
  have hall : ∀ k : Fin q, ∀ w ∈ S.line k, χ (Multiplicative.ofAdd w) = 1 := by
    intro k w hw
    set jk := ZMod.finEquiv q k with hjk
    set ji := ZMod.finEquiv q i with hji
    set n := (jk - ji).val with hn
    have hnc : ((n : ℕ) : ZMod q) = jk - ji := by rw [hn]; simp
    have hwline : w ∈ S.lineZ (ji + (n : ZMod q)) := by
      rw [hnc]
      have hadd : ji + (jk - ji) = jk := by ring
      rw [hadd, hjk, S.lineZ_finEquiv]
      exact hw
    set v := ((S.lineAut ^ n : V ≃ₗ[ZMod p] V).symm) w with hv
    have hvw : (S.lineAut ^ n : V ≃ₗ[ZMod p] V) v = w := by rw [hv]; simp
    have hvline : v ∈ S.lineZ ji := by
      rw [← S.mem_lineZ_add_iff n ji, hvw]
      exact hwline
    rw [hji, S.lineZ_finEquiv] at hvline
    rw [← hvw, hpow n v]
    exact hcon v hvline
  obtain ⟨v, hv⟩ := hχ1
  exact hv (S.forall_apply_eq_one χ hall v)

theorem apply_one_eq_index_totalCentralizer_of_invariant {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hinv : ∀ x : S.grp, θ (S.semiAut x) = θ x) (hθ1 : θ ≠ 1) :
    θ 1 = ((S.totalCentralizer.index : ℕ) : ℂ) := by
  have hfinV : Finite V := S.finite_base
  have hfinU : Finite U := S.finite_units
  have hfin : Finite S.grp := S.finite_grp
  letI : Fintype S.grp := Fintype.ofFinite _
  letI : Fintype S.base := Fintype.ofFinite _
  letI : Fintype (baseCore S.toScalarCoordinateSystem) := Fintype.ofFinite _
  obtain ⟨lam, hlamT, hlamfix⟩ := exists_comp_eq_mem_resConstituents (N := S.base)
    (Fact.out) S.not_dvd_natCard_grp S.baseAut S.baseAut_pow_eq_one hθ
    (fun x => by rw [S.coe_baseAut, hinv])
  obtain ⟨hlam, hpos⟩ := mem_resConstituents.1 hlamT
  obtain ⟨χ, hχ⟩ := S.exists_monoidHom_units_eq_of_mem_Irr_base hlam
  have hne1 : lam ≠ 1 := by
    intro h
    exact one_notMem_resConstituents hθ (S.not_base_subset_charValueKernel hθ hinv hθ1) (h ▸ hlamT)
  have hχne : ∃ v : V, χ (Multiplicative.ofAdd v) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hne1 (funext fun x => ?_)
    obtain ⟨y, hy⟩ : ∃ y : Multiplicative V, (inl y : S.grp) = (x : S.grp) := by
      have hx : (x : S.grp) ∈ (inl : Multiplicative V →* S.grp).range := by
        rw [← base_eq_range_inl]; exact x.2
      exact hx
    have hxy : S.baseHom y = x := Subtype.ext (by rw [S.coe_baseHom_apply]; exact hy)
    have h1 : (χ y : ℂ) = lam x := by rw [hχ y, hxy]
    have h2 : (χ y : ℂ) = 1 := by
      have hy1 := hcon (Multiplicative.toAdd y)
      rw [show Multiplicative.ofAdd (Multiplicative.toAdd y) = y from rfl] at hy1
      rw [hy1]
      rfl
    rw [← h1, h2]
    rfl
  have hχinv : ∀ v : V, χ (Multiplicative.ofAdd (S.lineAut v))
      = χ (Multiplicative.ofAdd v) := by
    intro v
    refine Units.ext ?_
    rw [hχ, hχ]
    have h := congrFun hlamfix (S.baseHom (Multiplicative.ofAdd v))
    rw [Function.comp_apply, S.baseAut_baseHom] at h
    exact h
  have hsupp := S.exists_mem_line_apply_ne_one_of_lineAut_invariant χ hχinv hχne
  exact apply_one_eq_index_totalCentralizer S.toScalarCoordinateSystem hθ
    (S.core_subset_charValueKernel hθ hinv) hlamT χ hχ hsupp

theorem apply_one_indClassFun_of_invariant {θ : S.grp → ℂ} (hθ : θ ∈ Irr S.grp)
    (hinv : ∀ x : S.grp, θ (S.semiAut x) = θ x) (hθ1 : θ ≠ 1) :
    indClassFun S.grpPart (kernelClassFun S.bAutHom θ) 1
      = (q : ℂ) * ((S.totalCentralizer.index : ℕ) : ℂ) := by
  rw [indClassFun_apply_one, kernelClassFun_one,
    S.apply_one_eq_index_totalCentralizer_of_invariant hθ hinv hθ1,
    index_range_inl (φ := S.bAutHom), Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end ScalarInvariantSystem

end CFSG.FeitThompson
