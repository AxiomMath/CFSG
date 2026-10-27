module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Representations.CyclicTIColumnSumAxisNonvanishing
public import CFSG.FeitThompson.Representations.CyclicTITwoColumnHalfSelection
import CFSG.FeitThompson.Representations.VirtualCharacterNormCyclicGenerators
import CFSG.FeitThompson.Representations.PrimeTIEnlargedInduction
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Representations.CoprimeInvariantCharacterInductionSupport
import CFSG.FeitThompson.Representations.ProjectedRestrictionGenChars
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open CFSG.FeitThompson.Prep03

attribute [local instance] CFSG.FeitThompson.subgroupFintype

variable {G : Type*} [Group G]

noncomputable def irrEquivOfEnum {X : Type*} [Group X] {I : Type*} (α : I → X → ℂ)
    (hα : ∀ i, α i ∈ Irr X) (hinj : Function.Injective α)
    (hsurj : ∀ χ ∈ Irr X, ∃ i, α i = χ) : I ≃ Irr X :=
  Equiv.ofBijective (fun i => ⟨α i, hα i⟩)
    ⟨fun a b hab => hinj (Subtype.ext_iff.1 hab),
      fun χ => by obtain ⟨i, hi⟩ := hsurj (χ : X → ℂ) χ.2; exact ⟨i, Subtype.ext hi⟩⟩

@[simp] theorem coe_irrEquivOfEnum_apply {X : Type*} [Group X] {I : Type*} (α : I → X → ℂ)
    (hα : ∀ i, α i ∈ Irr X) (hinj : Function.Injective α)
    (hsurj : ∀ χ ∈ Irr X, ∃ i, α i = χ) (i : I) :
    ((irrEquivOfEnum α hα hinj hsurj i : Irr X) : X → ℂ) = α i := (rfl)

theorem irrEquivOfEnum_eq_principalIrr {X : Type*} [Group X] {I : Type*} (α : I → X → ℂ)
    (hα : ∀ i, α i ∈ Irr X) (hinj : Function.Injective α)
    (hsurj : ∀ χ ∈ Irr X, ∃ i, α i = χ) {i : I} (hi : α i = 1) :
    irrEquivOfEnum α hα hinj hsurj i = principalIrr X :=
  Subtype.ext (by rw [coe_irrEquivOfEnum_apply, coe_principalIrr, hi])

theorem irrEquivOfEnum_ne_principalIrr {X : Type*} [Group X] {I : Type*} (α : I → X → ℂ)
    (hα : ∀ i, α i ∈ Irr X) (hinj : Function.Injective α)
    (hsurj : ∀ χ ∈ Irr X, ∃ i, α i = χ) {i i0 : I} (hi0 : α i0 = 1) (hi : i ≠ i0) :
    irrEquivOfEnum α hα hinj hsurj i ≠ principalIrr X := by
  rw [← irrEquivOfEnum_eq_principalIrr α hα hinj hsurj hi0]
  exact fun h => hi ((irrEquivOfEnum α hα hinj hsurj).injective h)

theorem mem_conjSet_of_mem_zpowers {X : Subgroup G} {g x y : G}
    (hy : y ∈ conjSet (X : Set G) g) (hx : x ∈ Subgroup.zpowers y) :
    x ∈ conjSet (X : Set G) g := by
  obtain ⟨a, ha, rfl⟩ := hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine ⟨a ^ n, zpow_mem ha n, ?_⟩
  simpa [MulAut.conj_apply] using map_zpow (MulAut.conj g⁻¹).toMonoidHom a n

theorem mem_sat_of_mem_zpowers {X : Subgroup G} {x y : G}
    (hy : y ∈ sat (X : Set G)) (hx : x ∈ Subgroup.zpowers y) : x ∈ sat (X : Set G) := by
  simp only [sat, Set.mem_iUnion] at hy ⊢
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, mem_conjSet_of_mem_zpowers hg hx⟩

theorem mem_sat_of_isConj {X : Subgroup G} {x v : G} (hv : v ∈ X) (h : IsConj x v) :
    x ∈ sat (X : Set G) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine Set.mem_iUnion.2 ⟨c, v, hv, ?_⟩
  have h' : c * x * c⁻¹ = v := hc
  rw [← h']; group

theorem subgroupOf_fittingIn_self [Finite G] (M : Subgroup G) :
    (fittingIn M).subgroupOf M = fittingRaw ↥M := by
  rw [fittingIn, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]

theorem eq_zero_of_mem_detectInd_fittingIn [Fintype G] {M H : Subgroup G} {f : ↥M → ℂ}
    (hf : f ∈ detectInd M (fittingIn M) H) {y : ↥M} (hy : (y : G) ∉ fittingIn M) : f y = 0 := by
  obtain ⟨θ, -, -, rfl⟩ := hf
  have : ((fittingIn M).subgroupOf M).Normal := by
    rw [subgroupOf_fittingIn_self]; exact fittingRaw_normal ↥M
  exact indClassFun_eq_zero_of_notMem _ θ (by simpa [Subgroup.mem_subgroupOf] using hy)

theorem indG_eq_zero_of_notMem_sat [Fintype G] {M : Subgroup G} {f : ↥M → ℂ}
    (hf : ∀ y : ↥M, (y : G) ∉ fittingIn M → f y = 0) {x : G}
    (hx : x ∉ sat (fittingIn M : Set G)) : indG M f x = 0 :=
  indClassFun_apply_eq_zero_of_forall_not_isConj M (A := (fittingIn M : Set G)) hf
    (fun _ hv hconj => hx (mem_sat_of_isConj hv hconj))

theorem IsWitnessedPConfiguration.isCyclicTIPair_sup [Finite G] {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) (hodd : Odd (Nat.card G))
    (hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂)) :
    IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ where
  left_ne_bot := hc.ne_bot_W₁
  right_ne_bot := hc.ne_bot_W₂
  mul_eq := hc.coe_sup_W₁_W₂.symm
  inf_eq_bot := hc.inf_W₁_W₂
  commute x hx y hy := (hc.commute_W₁_W₂ hx hy).eq
  isCyclic := by
    have h1 := hc.isCyclic_W₁
    have h2 := hc.isCyclic_W₂
    have hprod : IsCyclic (↥W₁ × ↥W₂) := Group.isCyclic_prod_iff.2 ⟨h1, h2, hcop⟩
    exact isCyclic_of_surjective _
      (mulEquivProdOfCoeEqMul hc.coe_sup_W₁_W₂ hc.inf_W₁_W₂
        (fun _ hx _ hy => hc.commute_W₁_W₂ hx hy)).surjective
  odd_natCard := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  setOf_conj_eq_self := by
    rw [cyclicTIDiff_sup_eq_cyclicTIset, setOf_conj_eq_self_eq_normalizer,
      hc.isTIWithNormalizer_cyclicTIset.normalizer_eq]
  inter_eq_empty := fun g hg => Set.disjoint_iff_inter_eq_empty.1
    (by rw [cyclicTIDiff_sup_eq_cyclicTIset]
        exact (hc.isTIWithNormalizer_cyclicTIset.disjoint_image_conj_inv hg).symm)

theorem mem_classFun_of_mem_classFun_top {f : ↥(⊤ : Subgroup G) → ℂ}
    (hf : f ∈ classFun ↥(⊤ : Subgroup G)) :
    (fun x : G => f ⟨x, Subgroup.mem_top x⟩) ∈ classFun G := by
  refine mem_classFun.2 fun x y hxy => ?_
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  exact mem_classFun.1 hf _ _
    (isConj_iff.2 ⟨⟨c, Subgroup.mem_top c⟩, Subtype.ext (by simpa using hc)⟩)

theorem mem_virtualChars_of_mem_virtualChars_top [Finite G] {f : ↥(⊤ : Subgroup G) → ℂ}
    (hf : f ∈ virtualChars ↥(⊤ : Subgroup G)) :
    (fun x : G => f ⟨x, Subgroup.mem_top x⟩) ∈ virtualChars G :=
  comp_mem_virtualChars (Subgroup.topEquiv (G := G)).symm.toMonoidHom
    (mem_span_Irr_of_mem_virtualChars hf)

theorem cfInner_top_eq [Fintype G] (f g : G → ℂ) :
    cfInner (fun x : ↥(⊤ : Subgroup G) => f (x : G)) (fun x : ↥(⊤ : Subgroup G) => g (x : G))
      = cfInner f g :=
  cfInner_comp_equiv (Subgroup.topEquiv (G := G)).toEquiv f g

theorem indClassFun_subgroupOf_top_apply [Fintype G] (W : Subgroup G) (f : ↥W → ℂ) (x : G) :
    indClassFun (W.subgroupOf (⊤ : Subgroup G))
        (fun y : ↥(W.subgroupOf (⊤ : Subgroup G)) => f ⟨((y : ↥(⊤ : Subgroup G)) : G), y.2⟩)
        ⟨x, Subgroup.mem_top x⟩ = indClassFun W f x := by
  have h := indClassFun_comp_mulEquiv (Subgroup.topEquiv (G := G))
    (K := W.subgroupOf (⊤ : Subgroup G)) (K' := W) (fun _ => Iff.rfl)
    (θ := fun y : ↥(W.subgroupOf (⊤ : Subgroup G)) => f ⟨((y : ↥(⊤ : Subgroup G)) : G), y.2⟩)
    (θ' := f) (fun a b hab => congrArg f (Subtype.ext hab))
  exact (congrFun h ⟨x, Subgroup.mem_top x⟩).symm

noncomputable def tiExtensionHom [Fintype G] {W₁ W₂ : Subgroup G}
    {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G))) :
    classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G where
  toFun f := ⟨ω (f : ↥(W₁ ⊔ W₂) → ℂ),
    mem_classFun_of_mem_classFun_top (hω.maps_classFun (f : ↥(W₁ ⊔ W₂) → ℂ) f.2)⟩
  map_add' f g := by
    refine Subtype.ext (funext fun x => ?_)
    have h := congrFun (hω.map_add (f : ↥(W₁ ⊔ W₂) → ℂ) (g : ↥(W₁ ⊔ W₂) → ℂ))
      ⟨x, Subgroup.mem_top x⟩
    simpa using h
  map_smul' c f := by
    refine Subtype.ext (funext fun x => ?_)
    have h := congrFun (hω.map_smul c (f : ↥(W₁ ⊔ W₂) → ℂ)) ⟨x, Subgroup.mem_top x⟩
    simpa using h

@[simp] theorem coe_tiExtensionHom_apply [Fintype G] {W₁ W₂ : Subgroup G}
    {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    (f : classFun ↥(W₁ ⊔ W₂)) :
    (tiExtensionHom hω f : G → ℂ) = ω (f : ↥(W₁ ⊔ W₂) → ℂ) := (rfl)

theorem isCyclicTIIsometry_tiExtensionHom [Fintype G] {W₁ W₂ : Subgroup G}
    {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G))) :
    IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ (tiExtensionHom hω) where
  inner_eq f h := by
    have h1 := hω.inner_eq (f : ↥(W₁ ⊔ W₂) → ℂ) (h : ↥(W₁ ⊔ W₂) → ℂ)
    rw [coe_tiExtensionHom_apply, coe_tiExtensionHom_apply, ← cfInner_top_eq]
    exact h1
  map_virtualChars f hf :=
    mem_virtualChars_of_mem_virtualChars_top (hω.maps_virtualChars _ hf)
  map_principalClassFun := by
    refine Subtype.ext (funext fun x => ?_)
    have h := congrFun hω.map_one ⟨x, Subgroup.mem_top x⟩
    simpa using h
  eq_indClassFun f hf := by
    have hf' : ∀ z : ↥(W₁ ⊔ W₂), (z : G) ∉ cyclicTIset W₁ W₂ → (f : ↥(W₁ ⊔ W₂) → ℂ) z = 0 :=
      fun z hz => hf z (by rwa [cyclicTIDiff_sup_eq_cyclicTIset])
    funext x
    have h := congrFun (hω.eq_ind (f : ↥(W₁ ⊔ W₂) → ℂ) hf') ⟨x, Subgroup.mem_top x⟩
    rw [coe_tiExtensionHom_apply]
    simp only at h
    rw [h, indClassFun_subgroupOf_top_apply]

theorem prodChar_eq_of_tensor {W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂) {lam : ↥W₁ → ℂ} {mu : ↥W₂ → ℂ}
    {f : ↥(W₁ ⊔ W₂) → ℂ}
    (hf : ∀ (x : ↥W₁) (y : ↥W₂) (z : ↥(W₁ ⊔ W₂)), (z : G) = (x : G) * (y : G) →
      f z = lam x * mu y) :
    f = hW.prodChar lam mu := by
  funext z
  have hz : (z : G) ∈ ((W₁ : Set G) * (W₂ : Set G)) := by rw [hW.mul_eq]; exact z.2
  obtain ⟨x, hx, y, hy, hxy⟩ := hz
  have hzz : z = (⟨x * y, mul_mem (hW.left_le hx) (hW.right_le hy)⟩ : ↥(W₁ ⊔ W₂)) :=
    Subtype.ext hxy.symm
  rw [hf ⟨x, hx⟩ ⟨y, hy⟩ z (by rw [← hxy]), hzz, hW.prodChar_apply_mul lam mu hx hy]

theorem eta_eq_prodCharEta [Fintype G] {W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    {I J : Type} {α : I → ↥W₁ → ℂ} {β : J → ↥W₂ → ℂ}
    (hα : ∀ i, α i ∈ Irr ↥W₁) (hβ : ∀ j, β j ∈ Irr ↥W₂)
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hαsurj : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ) (hβsurj : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ)
    {w : I → J → ↥(W₁ ⊔ W₂) → ℂ}
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * β j y)
    {η : I → J → G → ℂ} (hη : ∀ i j, η i j = ω (w i j)) (i : I) (j : J) :
    η i j = hW.prodCharEta (tiExtensionHom hω)
      (irrEquivOfEnum α hα hαinj hαsurj i) (irrEquivOfEnum β hβ hβinj hβsurj j) := by
  rw [hη i j, IsCyclicTIPair.prodCharEta_eq_coe_apply, coe_tiExtensionHom_apply,
    IsCyclicTIPair.coe_basisProdIrr_apply, coe_irrEquivOfEnum_apply, coe_irrEquivOfEnum_apply,
    ← prodChar_eq_of_tensor hW (fun x y z hz => hw i j x y z hz)]

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup
open CFSG.FeitThompson
open CFSG.FeitThompson.Prep03

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

variable {G : Type*} [Group G] [Fintype G]

open scoped Classical in
theorem sumSq_bound {G0 : Set G} {ρ τ : G → ℂ}
    (hρ : ρ ∈ Submodule.span ℤ (Irr G)) (hτ : τ ∈ Submodule.span ℤ (Irr G))
    (hclosed : ∀ x ∈ G0, ∀ y : G, Subgroup.zpowers y = Subgroup.zpowers x → y ∈ G0)
    (hcov : ∀ x ∈ G0, ρ x ≠ 0 ∨ τ x ≠ 0) :
    (G0.ncard : ℝ) ≤ ∑ x : G, Set.indicator G0 (fun y => ‖ρ y‖ ^ 2 + ‖τ y‖ ^ 2) x := by
  set A : Finset G := G0.toFinset with hA
  have hAcoe : (A : Set G) = G0 := Set.coe_toFinset G0
  have hsum : ∑ x : G, Set.indicator G0 (fun y => ‖ρ y‖ ^ 2 + ‖τ y‖ ^ 2) x
      = ∑ x ∈ A, (‖ρ x‖ ^ 2 + ‖τ x‖ ^ 2) := by
    have h := Finset.sum_indicator_subset (fun y => ‖ρ y‖ ^ 2 + ‖τ y‖ ^ 2)
      (s := A) (t := Finset.univ) (Finset.subset_univ _)
    rw [hAcoe] at h
    exact h
  have hcard : G0.ncard = A.card := by rw [← hAcoe, Set.ncard_coe_finset]
  rw [hsum, hcard]
  have hstep := card_le_sum_sum_sq_norm (G := G) (k := 2) (fun j => if j = 0 then ρ else τ)
    (fun j => by rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> simp [h, hρ, hτ]) A
    (fun x hx y hy => Set.mem_toFinset.2 (hclosed x (Set.mem_toFinset.1 hx) y hy))
    (fun x _ => isOfFinOrder_of_finite x)
    (fun x hx => by
      rcases hcov x (Set.mem_toFinset.1 hx) with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩)
  refine hstep.trans_eq (Finset.sum_congr rfl fun x _ => ?_)
  simp [Fin.sum_univ_two]

theorem FCH_type_p_complementary_fitting_norm
    (h₁ : Statements.FNI_type_p_elementary_core_structure.{u}) :
    Statements.FCH_type_p_complementary_fitting_norm.{u} := by
  classical
  intro G _ _ hG M U W₁ W₂ hcfg u hu I J _ _ i0 j0 α β hα hβ hαinj hβinj hαsurj hβsurj hα0 hβ0
    w hw σ ω hσ hω δ μ0 ell μ Mrow η hδ hμ0 hμ0Irr hell hμ hMrow hη
    Sfam Tfam hSfam hTfam Q G0 hG0 ν hνiso hTS hdeg hνind j₁ j₂ ε hj₁ hj₂ hε hMrowT hνMrow
    lam hlamT iStar hiStar
  have hG' : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.forall_isSolvable⟩
  obtain ⟨-, hpp, hqp, -, -, hpq, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₁ G hG' M U W₁ W₂ hcfg.isCoatom hcfg.config _ _ rfl rfl
  have hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂) :=
    (Nat.coprime_primes hqp hpp).2 (fun h => hpq h.symm)
  have hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ :=
    hcfg.config.isCyclicTIPair_sup hG.odd_natCard hcop
  have hωiso : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ (tiExtensionHom hω) :=
    isCyclicTIIsometry_tiExtensionHom hω
  set eI := irrEquivOfEnum α hα hαinj hαsurj with heI
  set eJ := irrEquivOfEnum β hβ hβinj hβsurj with heJ
  have hspanT : (Submodule.span ℤ Tfam : Submodule ℤ (↥M → ℂ)) ≤ Submodule.span ℤ Sfam :=
    Submodule.span_le.2 hTS
  have hlamS : lam ∈ Submodule.span ℤ Sfam := hTS hlamT
  have hMrowS : Mrow j₁ ∈ Submodule.span ℤ Sfam := hTS hMrowT
  have hdiffT : lam - Mrow j₁ ∈ Submodule.span ℤ Tfam :=
    Submodule.sub_mem _ (Submodule.subset_span hlamT) (Submodule.subset_span hMrowT)
  have hdiffS : lam - Mrow j₁ ∈ Submodule.span ℤ Sfam := hspanT hdiffT
  have hdeg0 : (lam - Mrow j₁) 1 = 0 := by
    simp only [Pi.sub_apply, hdeg lam hlamT, hdeg _ hMrowT, sub_self]
  have hνdiff : ν (lam - Mrow j₁) = fun x => indG M (lam - Mrow j₁) x := hνind _ hdiffT hdeg0
  have hadd : ν lam = ν (lam - Mrow j₁) + ν (Mrow j₁) := by
    have h := hνiso.1 (lam - Mrow j₁) hdiffS (Mrow j₁) hMrowS
    rw [sub_add_cancel] at h
    exact h
  have hvanish : ∀ y : ↥M, (y : G) ∉ fittingIn M → (lam - Mrow j₁) y = 0 := by
    intro y hy
    rw [hTfam] at hlamT hMrowT
    simp only [Pi.sub_apply, eq_zero_of_mem_detectInd_fittingIn hlamT hy,
      eq_zero_of_mem_detectInd_fittingIn hMrowT hy, sub_self]
  have hkey : ∀ y ∈ G0, ν lam y
      = ε * hW.prodCharEtaColSum (tiExtensionHom hω) (eJ j₂) y := by
    intro x hx
    have hxF : x ∉ sat (fittingIn M : Set G) := by
      rw [hG0] at hx; exact fun hc => hx.2 (Or.inl hc)
    have h1 : ν lam x = indG M (lam - Mrow j₁) x + ν (Mrow j₁) x := by
      rw [hadd]; simp [hνdiff]
    have hcol : hW.prodCharEtaColSum (tiExtensionHom hω) (eJ j₂) x = ∑ i : I, η i j₂ x := by
      have : Fintype (Irr ↥W₁) := Fintype.ofEquiv I eI
      rw [hW.prodCharEtaColSum_eq_sum, Finset.sum_apply]
      refine (Fintype.sum_equiv eI _ _ fun i => ?_).symm
      rw [eta_eq_prodCharEta hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη i j₂]
    rw [h1, indG_eq_zero_of_notMem_sat hvanish hxF, zero_add, hνMrow, hcol]
  have hcov : ∀ x ∈ G0, ν lam x ≠ 0 ∨ η iStar j0 x ≠ 0 := by
    intro x hx
    have hcover := hW.apply_ne_zero_or_prodCharEta_axis_ne_zero hωiso hqp
      (i₀ := eI iStar) (irrEquivOfEnum_ne_principalIrr α hα hαinj hαsurj hα0 hiStar)
      (j₀ := eJ j₂) (irrEquivOfEnum_ne_principalIrr β hβ hβinj hβsurj hβ0 hj₂)
      hε (h := ν lam) (B₀ := G0) hkey hx
    have hj0 : eJ j0 = principalIrr ↥W₂ := irrEquivOfEnum_eq_principalIrr β hβ hβinj hβsurj hβ0
    rw [eta_eq_prodCharEta hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη iStar j0, hj0]
    exact hcover
  refine sumSq_bound ?_ ?_ ?_ hcov
  · exact mem_span_Irr_of_mem_virtualChars (hνiso.2.1 lam hlamS)
  · rw [eta_eq_prodCharEta hW hω hα hβ hαinj hβinj hαsurj hβsurj hw hη iStar j0]
    exact mem_span_Irr_of_mem_virtualChars (hW.prodCharEta_mem_virtualChars hωiso _ _)
  · intro x hx y hy
    rw [hG0] at hx ⊢
    refine ⟨Set.mem_univ y, fun hc => hx.2 ?_⟩
    rcases hc with hc | hc
    · exact Or.inl (mem_sat_of_mem_zpowers hc (hy ▸ Subgroup.mem_zpowers x))
    · exact Or.inr (mem_sat_of_mem_zpowers hc (hy ▸ Subgroup.mem_zpowers x))

end CFSG.FeitThompson.Proofs

end
