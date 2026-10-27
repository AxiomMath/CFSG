module

public import CFSG.ClassicalInvolution.SubnormalClosure
import CFSG.ClassicalInvolution.OrderForm
import CFSG.GroupTheory.NonabelianSimpleOrderSixty
import CFSG.Adapters.GeneralizedFitting
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.ClassicalInvolution.Q3.Split

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

@[expose] def AschbacherCIT3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], classicalInvolutionOddCore G = ⊥ →
    ∀ z : G, orderOf z = 2 → ∀ K : Subgroup G, z ∈ K →
    IsSubnormal K (Subgroup.centralizer ({z} : Set G)) → Group.IsSolvable K →
    classicalInvolutionWitness K → subnormalClosure K = ⊤ →
    (CFSG.Open.IsQuasisimple G ∧ (CFSG.Blueprint.OddLieType (G ⧸ Subgroup.center G) ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .M11)) ∨
      (K = ⊤ ∧ Nonempty (G ≃* SL(2, ZMod 3)))

@[expose] def M11Facts : Prop :=
  IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 ∧
    Nat.card ↥CFSG.Blueprint.NativeSporadic.M11 = 7920

theorem oddLieType_or_isSporadic_of_aschbacherCIT3 (hCIT : AschbacherCIT3) {G : Type} [Group G]
    [Finite G] (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a) (hC : Subgroup.centralizer (F : Set G) = ⊥)
    (hO : classicalInvolutionOddCore G = ⊥) {z : G} (hz : orderOf z = 2) {J : Subgroup G}
    (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (hsol : Group.IsSolvable J) (hw : classicalInvolutionWitness J) :
    CFSG.Blueprint.OddLieType F ∨ CFSG.Blueprint.NativeSporadic.IsSporadic F .M11 := by
  have hZ : Subgroup.center F = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot F hFnonab
  have hJbot : J ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.mem_bot] at hzJ
    rw [hzJ, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨H, hHsub, hJH, hcl, hFH⟩ : ∃ H : Subgroup G, IsSubnormal H ⊤ ∧ J ≤ H ∧
      subnormalClosure (J.subgroupOf H) = ⊤ ∧ F ≤ H :=
    ⟨subnormalClosure J, isSubnormal_subnormalClosure J, le_subnormalClosure J,
      subnormalClosure_subgroupOf_subnormalClosure J,
      le_subnormalClosure_of_isComponentOf (isComponentOf_top_of_normal_simple F hFnonab) hC hJbot⟩
  have hzH : z ∈ H := hJH hzJ
  have hOH : classicalInvolutionOddCore H = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hO H hHsub
  have hJ' : IsSubnormal (J.subgroupOf H) (Subgroup.centralizer ({(⟨z, hzH⟩ : H)} : Set H)) := by
    have h1 : IsSubnormal J (Subgroup.centralizer ({z} : Set G) ⊓ H) := by
      have := isSubnormal_inf hJ H
      rwa [inf_eq_left.mpr hJH] at this
    rw [← subgroupOf_centralizer_inf hzH]
    exact isSubnormal_subgroupOf h1 H
  have hw' : classicalInvolutionWitness (J.subgroupOf H) :=
    classicalInvolutionWitness_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJH).symm hw
  have hsol' : Group.IsSolvable (J.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hJH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJH).injective
  rcases hCIT H hOH ⟨z, hzH⟩ (by rwa [Subgroup.orderOf_mk]) (J.subgroupOf H)
      (Subgroup.mem_subgroupOf.mpr hzJ) hJ' hsol' hw' hcl with ⟨hq, hlie⟩ | ⟨-, ⟨e⟩⟩
  · obtain rfl := eq_of_isQuasisimple_of_le hFH hq hFnonab
    let e : H ⧸ Subgroup.center H ≃* H :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact hlie.imp (oddLieType_congr e).mp id
  · have hdvd : Nat.card F ∣ 24 := by
      rw [← natCard_sl2Three, ← Nat.card_congr e.toEquiv]
      exact Subgroup.card_dvd_of_le hFH
    have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty ‹IsSimpleGroup F›
      hFnonab
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem centralizer_fstar_eq_bot_and_oddCore_eq_bot {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a) :
    Subgroup.centralizer (genFittingFStar G : Set G) = ⊥ ∧ classicalInvolutionOddCore G = ⊥ := by
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have hFc : IsComponentOf (genFittingFStar G) ⊤ :=
    isComponentOf_top_of_normal_simple _ hFnonab
  have hC : Subgroup.centralizer (genFittingFStar G : Set G) = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxF : x ∈ genFittingFStar G := CFSG.Adapters.generalized_fitting_self_centralizing G hx
    have hcen : (⟨x, hxF⟩ : genFittingFStar G) ∈ Subgroup.center (genFittingFStar G) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx g.1 g.2)
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot _ hFnonab, Subgroup.mem_bot] at hcen
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcen)
  refine ⟨hC, ?_⟩
  have : Group.IsSolvable (classicalInvolutionOddCore G) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card G)
  have hsub : IsSubnormal (classicalInvolutionOddCore G) ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hcomm := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
    (genFittingFStar G) (classicalInvolutionOddCore G) hFc hsub
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, hC] at hcomm
  exact le_bot_iff.mp hcomm

theorem partOneSolvable_of_aschbacherCIT3 (h : AschbacherCIT3) : PartOneSolvable := by
  intro G _ _ _ hFnonab z hz J hzJ hJ _ _ hw hsol
  obtain ⟨hC, hO⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hFnonab
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  exact oddLieType_or_isSporadic_of_aschbacherCIT3 h (genFittingFStar G) hFnonab hC hO hz hzJ hJ
    hsol hw

section FromInductive

theorem LieSystemData3.range_normal {ι X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) : ((D.hom i).range).Normal := by
  have key : ∀ g ∈ (⨆ k, (D.hom k).range : Subgroup X), ∀ n ∈ (D.hom i).range,
      g * n * g⁻¹ ∈ (D.hom i).range := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact ((D.hom k).range).mul_mem (((D.hom k).range).mul_mem hy hn)
          (((D.hom k).range).inv_mem hy)
      · obtain ⟨a, rfl⟩ := hy
        obtain ⟨b, rfl⟩ := hn
        rw [D.commute k i hki a b, mul_assoc, mul_inv_cancel, mul_one]
        exact ⟨b, rfl⟩
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  refine ⟨fun n hn g => key g ?_ n hn⟩
  rw [D.generate]
  trivial

theorem center_eq_map_center_of_central_kernel {K G : Type} [Group K] [Group G] (ψ : K →* G)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center K) (hperf : commutator K = ⊤) :
    Subgroup.center G = (Subgroup.center K).map ψ := by
  refine le_antisymm (fun g hg => ?_) (Subgroup.map_center_le_center hsurj)
  obtain ⟨x, rfl⟩ := hsurj g
  have hcen : ∀ k : K, x * k * x⁻¹ * k⁻¹ ∈ Subgroup.center K := by
    intro k
    apply hker
    rw [MonoidHom.mem_ker]
    have := Subgroup.mem_center_iff.mp hg (ψ k)
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact this.symm
  let φ : K →* Subgroup.center K :=
    { toFun := fun k => ⟨x * k * x⁻¹ * k⁻¹, hcen k⟩
      map_one' := by simp
      map_mul' := fun k₁ k₂ => by
        apply Subtype.ext
        have h2 := Subgroup.mem_center_iff.mp (hcen k₂) k₁
        calc x * (k₁ * k₂) * x⁻¹ * (k₁ * k₂)⁻¹
            = (x * k₁ * x⁻¹ * k₁⁻¹) * (k₁ * (x * k₂ * x⁻¹ * k₂⁻¹) * k₁⁻¹) := by group
          _ = (x * k₁ * x⁻¹ * k₁⁻¹) * ((x * k₂ * x⁻¹ * k₂⁻¹) * k₁ * k₁⁻¹) := by rw [← h2]
          _ = (x * k₁ * x⁻¹ * k₁⁻¹) * (x * k₂ * x⁻¹ * k₂⁻¹) := by group }
  have hker' : commutator K ≤ φ.ker := Abelianization.commutator_subset_ker φ
  refine ⟨x, ?_, rfl⟩
  show x ∈ Subgroup.center K
  rw [Subgroup.mem_center_iff]
  intro k
  have hk : k ∈ φ.ker := hker' (by rw [hperf]; exact Subgroup.mem_top _)
  have h1 : x * k * x⁻¹ * k⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
  calc k * x = x * k * x⁻¹ * k⁻¹ * (k * x) := by rw [h1, one_mul]
    _ = x * k := by group

theorem conclusion_of_component (h0 : ModelClauseZero) (hM : M11Facts) {G : Type} [Group G]
    [Finite G] (c : CompData) (hc : c.Valid) (ψ : c.G →* G) (hsurj : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center _) (K : Subgroup G) (hKcard : Nat.card K = 24)
    (hKfund : ∃ R ∈ c.fund, K = R.map ψ) :
    (CFSG.Open.IsQuasisimple G ∧ (CFSG.Blueprint.OddLieType (G ⧸ Subgroup.center G) ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .M11)) ∨
      (K = ⊤ ∧ Nonempty (G ≃* SL(2, ZMod 3))) := by
  rcases hc with ⟨t, n, hFT, hadm, rfl⟩ | rfl | rfl
  · obtain ⟨hqs, hmodel⟩ := h0 t n 3 1 Nat.prime_three hFT hadm
    have hperf : commutator (modelUniv t n 3 1 Nat.prime_three).K = ⊤ := hqs.1
    have hZ := center_eq_map_center_of_central_kernel ψ hsurj hker hperf
    let e := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective ψ hsurj hker hZ
    have : IsSimpleGroup ((modelUniv t n 3 1 Nat.prime_three).K ⧸
        Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K) := hqs.2
    have hsimple : IsSimpleGroup (G ⧸ Subgroup.center G) := e.symm.isSimpleGroup
    have : Group.IsPerfect (modelUniv t n 3 1 Nat.prime_three).K := ⟨hperf⟩
    have hGperf : Group.IsPerfect G := Group.IsPerfect.ofSurjective (f := ψ) hsurj
    refine Or.inl ⟨⟨hGperf.commutator_eq_top, hsimple⟩, Or.inl ⟨t, n, 3, 1, Nat.prime_three,
        by norm_num, hadm, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel⟩⟩
  · obtain ⟨R, hR, rfl⟩ := hKfund
    have hR' : R = ⊤ := hR
    subst hR'
    have hK : Subgroup.map ψ ⊤ = ⊤ := Subgroup.map_top_of_surjective ψ hsurj
    refine Or.inr ⟨hK, ?_⟩
    have hGcard : Nat.card G = 24 := by
      rw [← hKcard, hK, Subgroup.card_top]
    have hinj : Function.Injective ψ := by
      have hcard : Nat.card SL(2, ZMod 3) = Nat.card G := by rw [natCard_sl2Three, hGcard]
      exact (hsurj.bijective_of_nat_card_le hcard.le).1
    exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩
  · have hsimple : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M11 := hM.1
    have hnab : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      let _ : CommGroup ↥CFSG.Blueprint.NativeSporadic.M11 :=
        { (inferInstance : Group ↥CFSG.Blueprint.NativeSporadic.M11) with
          mul_comm := hcon }
      have := IsSimpleGroup.prime_card (α := ↥CFSG.Blueprint.NativeSporadic.M11)
      rw [hM.2] at this
      exact absurd this (by norm_num)
    have hc : (Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11) = ⊥ :=
      CFSG.ComponentClassification.Helpers.center_eq_bot _ hnab
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff]
      exact le_bot_iff.mp (hker.trans hc.le)
    let e : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* G := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
    have hsimpleG : IsSimpleGroup G := e.symm.isSimpleGroup
    have hnabG : ∃ a b : G, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
    have hGperf : Group.IsPerfect G :=
      ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top G hnabG⟩
    refine Or.inl ⟨CFSG.ComponentClassification.Quasisimple.simple_of_perfect G, Or.inr ?_⟩
    exact ⟨e.symm⟩

theorem inClass3_conjugates_of_closure {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (h : IsClassicalMember3 K z) (hcl : subnormalClosure K = ⊤) :
    InClass3 (Set.range fun g : G => conjSub g K) where
  nonempty := ⟨K, 1, conjSub_one K⟩
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul n g K⟩
  generated := by
    have hinv : ConjInvariant (Set.range fun g : G => conjSub g K) := by
      rintro n _ ⟨g, rfl⟩
      exact ⟨n * g, conjSub_mul n g K⟩
    have hN : (⨆ L ∈ Set.range (fun g : G => conjSub g K), L).Normal := normal_biSup hinv
    have hKN : K ≤ ⨆ L ∈ Set.range (fun g : G => conjSub g K), L :=
      le_iSup₂_of_le K ⟨1, conjSub_one K⟩ le_rfl
    have hsub : IsSubnormal (⨆ L ∈ Set.range (fun g : G => conjSub g K), L) ⊤ :=
      isSubnormal_of_normal_subgroupOf le_top inferInstance
    exact eq_top_iff.mpr (hcl ▸ subnormalClosure_le hKN hsub)
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨g * z * g⁻¹, h.conj g⟩

theorem aschbacherCIT3_of_cit3Inductive (h : CIT3Inductive) (h0 : ModelClauseZero)
    (hM : M11Facts) : AschbacherCIT3 := by
  intro G _ _ hO z hz K hzK hK hsol hw hcl
  have hmem : IsClassicalMember3 K z := IsClassicalMember3.of_witness hz hzK hK hsol hw
  have hΛ := inClass3_conjugates_of_closure hmem hcl
  have hKΛ : K ∈ Set.range (fun g : G => conjSub g K) := ⟨1, conjSub_one K⟩
  obtain ⟨ι, hι, ⟨D⟩⟩ := lieSystem3_of_lieSystemMod3_corefree hO (h G _ hΛ)
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental K hKΛ
  have hKrange : K ≤ (D.hom i).range := hKR.le.trans (Subgroup.map_le_range _ _)
  have := D.range_normal i
  have hsub : IsSubnormal (D.hom i).range ⊤ :=
    isSubnormal_of_normal_subgroupOf le_top inferInstance
  have hsurj : Function.Surjective (D.hom i) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hcl]
    exact subnormalClosure_le hKrange hsub
  exact conclusion_of_component h0 hM (D.kind i) (D.valid i) (D.hom i) hsurj (D.ker_le_center i) K
    (D.card_eq K hKΛ) ⟨R, hR, hKR⟩

theorem partOneSolvable_of_cit3Inductive (h : CIT3Inductive) (h0 : ModelClauseZero)
    (hM : M11Facts) : PartOneSolvable :=
  partOneSolvable_of_aschbacherCIT3 (aschbacherCIT3_of_cit3Inductive h h0 hM)

end FromInductive

end CFSG.ClassicalInvolution.Q3
