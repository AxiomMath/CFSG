module

public import CFSG.LieType.Chevalley.OddToralInvolutionFixedComponents

public noncomputable section

namespace CFSG.LieType.Chevalley.OddToralOrdinary

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification (AssemblyBPredicates.isQuasisimple_iff_native)

section Components

variable {G : Type*} [Group G]

theorem assembly_isSubnormal_inf {L K : Subgroup G} (h : CFSG.Assembly.IsSubnormal L K)
    (H : Subgroup G) : CFSG.Assembly.IsSubnormal (L ⊓ H) (K ⊓ H) :=
  h.inf H

theorem isSubnormal_subgroupOf_of_assembly {L K : Subgroup G}
    (h : CFSG.Assembly.IsSubnormal L K) : (L.subgroupOf K).IsSubnormal :=
  h.subgroupOf

theorem isComponentOf_of_le_of_le {L K H : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L K)
    (hLH : L ≤ H) (hHK : H ≤ K) : CFSG.Assembly.IsComponentOf L H :=
  hL.of_le_of_le hLH hHK

theorem isComponent_subgroupOf_of_isComponentOf {L K : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L K) : CFSG.IsComponent (L.subgroupOf K) :=
  (isComponentOf_iff_isComponent_subgroupOf hL.1).1 hL

theorem range_eq_bot_of_commutator_eq_top {P Q : Type*} [Group P] [Group Q] [Group.IsSolvable Q]
    (hP : commutator P = ⊤) (f : P →* Q) : f.range = ⊥ := by
  have h : ∀ n, f.range ≤ derivedSeries Q n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, MonoidHom.range_eq_map, ← hP, commutator_def,
        Subgroup.map_commutator, ← MonoidHom.range_eq_map]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := Q)
  exact le_bot_iff.1 (hn ▸ h n)

theorem exists_mul_ne_mul_of_isQuasisimple {L : Subgroup G} (hL : CFSG.IsQuasisimple L) :
    ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  obtain ⟨-, -, ⟨u, v, huv⟩⟩ := hL
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
  refine ⟨x, x.2, y, y.2, fun h => huv ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext h)

end Components

section Classes

variable {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}

theorem mk_eq_mk_of_kernelRoots_subset (h : kernelRoots χ ⊆ kernelRoots χ')
    {x y : kernelRoots χ} (hxy : (⟦x⟧ : KernelComponent χ) = ⟦y⟧) :
    (⟦⟨x.1, h x.2⟩⟧ : KernelComponent χ') = ⟦⟨y.1, h y.2⟩⟧ := by
  have hr : Relation.EqvGen _ x y := Quotient.exact hxy
  clear hxy
  apply Quotient.sound
  change Relation.EqvGen _ _ _
  induction hr with
  | rel a b hab => exact Relation.EqvGen.rel _ _ hab
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem componentRoots_eq_of_kernelRoots_eq (h : kernelRoots χ = kernelRoots χ')
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) (hα' : α ∈ kernelRoots χ') :
    componentRoots χ ⟦⟨α, hα⟩⟧ = componentRoots χ' ⟦⟨α, hα'⟩⟧ := by
  ext β
  constructor
  · rintro ⟨hβ, hβα⟩
    exact ⟨h.le hβ, mk_eq_mk_of_kernelRoots_subset h.le (x := ⟨β, hβ⟩) (y := ⟨α, hα⟩) hβα⟩
  · rintro ⟨hβ, hβα⟩
    exact ⟨h.ge hβ, mk_eq_mk_of_kernelRoots_subset h.ge (x := ⟨β, hβ⟩) (y := ⟨α, hα'⟩) hβα⟩

theorem componentRootSpan_quasisimple_or_solvable
    {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (χ₀ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ)
    (hχ : kernelRoots χ = kernelRoots χ₀) (i : KernelComponent χ) :
    CFSG.IsQuasisimple (componentRootSpan K χ i) ∨
      Group.IsSolvable (componentRootSpan K χ i) := by
  induction i using Quotient.inductionOn with
  | h a =>
  obtain ⟨α, hα⟩ := a
  have hΨ := isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  by_cases h2 : 2 < (componentRoots χ ⟦⟨α, hα⟩⟧).ncard
  · left
    have heq := componentRoots_eq_of_kernelRoots_eq hχ hα (hχ ▸ hα)
    have hspan : componentRootSpan K χ ⟦⟨α, hα⟩⟧ = componentRootSpan K χ₀ ⟦⟨α, hχ ▸ hα⟩⟧ := by
      change rootSpan τ K (componentRoots χ _) = rootSpan τ K (componentRoots χ₀ _)
      rw [heq]
    rw [hspan]
    exact (odd_sign_root_component_quasisimple τ K χ₀ _).2.2 hK (heq ▸ h2)
  ·
    have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots χ ⟦⟨α, hα⟩⟧ :=
      Set.insert_subset hαΨ (Set.singleton_subset_iff.2 (hΨ.neg_mem α hαΨ))
    have hfin : (componentRoots χ ⟦⟨α, hα⟩⟧).Finite :=
      (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ
    have hne : α ≠ -α := fun h => (hΨ.isRoot α hαΨ).ne_zero (funext fun j => by
      have := congrFun h j
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega)
    have hcard : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard = 2 := Set.ncard_pair hne
    have heq : componentRoots χ ⟦⟨α, hα⟩⟧ = {α, -α} :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; omega) hfin).symm
    have hS : componentRootSpan K χ ⟦⟨α, hα⟩⟧ = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
      change rootSpan τ K (componentRoots χ ⟦⟨α, hα⟩⟧) = _
      rw [heq, OddToralFixed.rootSpan_pair]
    obtain ⟨-, -, -, hfinK⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK
      (hΨ.isRoot α hαΨ)
    obtain ⟨h3, h5⟩ := @hfinK inferInstance
    rw [hS]
    have : Fintype K := Fintype.ofFinite K
    have hodd : Nat.card K % 2 = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.odd_card_of_char_ne_two hK
    have hq2 : 1 < Nat.card K := Finite.one_lt_card
    rcases (show Nat.card K = 3 ∨ 5 ≤ Nat.card K by omega) with h | h
    · exact Or.inr (h3 h).1
    · exact Or.inl (h5 h).1

end Classes

theorem pinnedX_pow_eq_nsmul
    (τ : Tag) (R : Type*) [CommRing R] (α : Fin τ.rank → ℤ) (c : R)
    (n : ℕ) : pinnedX τ R α c ^ n = pinnedX τ R α (n • c) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, pinnedX_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, pinnedX_add]

theorem orderOf_pinnedX_one
    (τ : Tag) (K : Type) [Field K] (r : ℕ) [Fact r.Prime] [CharP K r]
    (α : Fin τ.rank → ℤ) : orderOf (pinnedX τ K α 1) = r := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [pinnedX_pow_eq_nsmul, nsmul_eq_mul, mul_one, CharP.cast_eq_zero, pinnedX_zero]
  · rw [← pinnedX_zero τ K α] at h
    exact one_ne_zero (pinnedX_injective τ K α h)

theorem _root_.CFSG.LieType.Chevalley.odd_toral_ordinary_component_root_factor_and_prime_divisor
    (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (k : Type) [Field k] [Finite k] [CharP k r] (τ : Tag)
    (a : Fin τ.rank → kˣ) (ha : ∀ i, a i = 1 ∨ a i = -1) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (hχ : kernelRoots χ = rootCharKernel a)
    (K : Subgroup (ModGL τ k)) (hK : CFSG.Assembly.IsComponentOf K (toralCentralizer τ k a)) :
    ∃ Ψ : KernelComponent χ, K = componentRootSpan k χ Ψ ∧
      (∀ α ∈ componentRoots χ Ψ, rootSubgroup τ k α ≤ K) ∧
      (∃ g ∈ K, orderOf g = r) ∧ r ∣ Nat.card K := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k r]; exact hr2
  have : Finite (ModGL τ k) := finite_modGL
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction τ k hk2 a ha
  set X := toralCentralizer τ k a with hXdef
  set S := rootSpan τ k (rootCharKernel a) with hSdef
  obtain ⟨hKX, hKsub, hKq⟩ := hK
  have hKq' : CFSG.IsQuasisimple K := (AssemblyBPredicates.isQuasisimple_iff_native K).1 hKq
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := exists_mul_ne_mul_of_isQuasisimple hKq'
  have hKS : K ≤ S := by
    intro y hy
    have hf := MonoidHom.range_eq_bot_iff.1 (range_eq_bot_of_commutator_eq_top hKq.1
      ((QuotientGroup.mk' (S.subgroupOf X)).comp (Subgroup.inclusion hKX)))
    have hy' : (QuotientGroup.mk (Subgroup.inclusion hKX ⟨y, hy⟩) : X ⧸ S.subgroupOf X) = 1 :=
      DFunLike.congr_fun hf ⟨y, hy⟩
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hKX ⟨y, hy⟩)).1 hy'
  obtain ⟨-, -, -, hnorm, -, -⟩ := root_character_kernel_orthogonal_central_product τ k χ
  rw [hχ] at hnorm
  have hKcS : CFSG.IsComponent (K.subgroupOf S) :=
    isComponent_subgroupOf_of_isComponentOf
      (isComponentOf_of_le_of_le ⟨hKX, hKsub, hKq⟩ hKS hSX)
  have hex : ∃ Ψ : KernelComponent χ, K ≤ componentRootSpan k χ Ψ := by
    by_contra hne
    push Not at hne
    have hc : ∀ Ψ, componentRootSpan k χ Ψ ≤ Subgroup.centralizer (K : Set (ModGL τ k)) := by
      intro Ψ z hz
      rcases component_normal_subgroup hKcS (hnorm Ψ).2 with h | h
      · exact absurd (fun y hy => h (show (⟨y, hKS hy⟩ : S) ∈ K.subgroupOf S from hy)) (hne Ψ)
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
          (show (⟨y, hKS hy⟩ : S) ∈ K.subgroupOf S from hy)
        rw [Subgroup.mem_centralizer_iff] at hyc
        exact (congrArg Subtype.val (hyc ⟨z, (hnorm Ψ).1 hz⟩ hz)).symm
    have hSc : S ≤ Subgroup.centralizer (K : Set (ModGL τ k)) := by
      rw [hSdef, ← hχ, ← iSup_componentRootSpan k]
      exact iSup_le hc
    exact hxy₀ (Subgroup.mem_centralizer_iff.1 (hSc (hKS hy₀)) x₀ hx₀)
  obtain ⟨Ψ, hKΨ⟩ := hex
  have hKcΨ := isComponentOf_of_le_of_le ⟨hKX, hKsub, hKq⟩ hKΨ ((hnorm Ψ).1.trans hSX)
  have hsubΨ := isSubnormal_subgroupOf_of_assembly hKcΨ.2.1
  have hset : kernelRoots χ = kernelRoots (maskChar (signTupleBits a)) :=
    hχ.trans (rootCharKernel_eq_kernelRoots hk2 ha)
  have hKeq : K = componentRootSpan k χ Ψ := by
    rcases componentRootSpan_quasisimple_or_solvable hk2 _ hset Ψ with hq | hs
    · rcases quasisimple_subnormal_subgroups hq hsubΨ with h | h
      · exact le_antisymm hKΨ (Subgroup.subgroupOf_eq_top.1 h)
      · exfalso
        apply hxy₀
        have := Subgroup.mem_center_iff.1
          (h (show (⟨y₀, hKΨ hy₀⟩ : componentRootSpan k χ Ψ) ∈ K.subgroupOf _ from hy₀))
          ⟨x₀, hKΨ hx₀⟩
        exact congrArg Subtype.val this
    · exfalso
      have hf := MonoidHom.range_eq_bot_iff.1 (range_eq_bot_of_commutator_eq_top hKq.1
        (Subgroup.inclusion hKΨ))
      have hx' := congrArg Subtype.val (DFunLike.congr_fun hf ⟨x₀, hx₀⟩)
      have hy' := congrArg Subtype.val (DFunLike.congr_fun hf ⟨y₀, hy₀⟩)
      have hx : x₀ = 1 := hx'
      have hy : y₀ = 1 := hy'
      exact hxy₀ (by rw [hx, hy])
  refine ⟨Ψ, hKeq, fun α hα => ?_, ?_⟩
  · obtain ⟨hα', hαΨ⟩ := hα
    rw [hKeq, ← hαΨ]
    exact rootSubgroup_le_componentRootSpan k ⟨α, hα'⟩
  · obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep Ψ
    have hg : pinnedX τ k α 1 ∈ K := by
      rw [hKeq]
      exact rootSubgroup_le_componentRootSpan k ⟨α, hα⟩ (Subgroup.subset_closure ⟨1, rfl⟩)
    have hord := orderOf_pinnedX_one τ k r α
    refine ⟨⟨_, hg, hord⟩, ?_⟩
    rw [← hord, ← Subgroup.orderOf_mk _ hg]
    exact orderOf_dvd_natCard _

end CFSG.LieType.Chevalley.OddToralOrdinary
