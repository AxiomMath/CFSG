module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBLinearTwo

section Components

variable {G : Type*} [Group G]

theorem isComponent_subgroupOf_of_le {A B C : Subgroup G} [Finite C] (hAB : A ≤ B)
    (hBC : B ≤ C) (h : CFSG.IsComponent (A.subgroupOf C)) :
    CFSG.IsComponent (A.subgroupOf B) := by
  have h1 := component_overgroup h (H := B.subgroupOf C) fun x hx => hAB hx
  have h2 := isComponent_map_of_isComponent (Subgroup.subgroupOfEquivOfLe hBC) h1
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨⟨x, hBC x.2⟩, x.2⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem le_of_isComponent_subgroupOf {A B N : Subgroup G}
    (hA : CFSG.IsComponent (A.subgroupOf B)) (hAB : A ≤ B) [(N.subgroupOf B).Normal]
    [Group.IsSolvable (B ⧸ N.subgroupOf B)] : A ≤ N := by
  have := hA.1.1
  have h := perfect_le_normal_of_solvable_quotient (N.subgroupOf B) (A.subgroupOf B)
  intro a ha
  exact h (show (⟨a, hAB ha⟩ : B) ∈ A.subgroupOf B from ha)

end Components

namespace OrthogonalSemilinearFixedRootDatum

variable
    {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orderOf_orbitX_one
    {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    orderOf (D.orbitX O 1) = p₀ := by
  have hpow : ∀ n : ℕ, D.orbitX O 1 ^ n = D.orbitX O (n • 1) := by
    intro n
    induction n with
    | zero => rw [pow_zero, zero_smul, D.orbitX_zero]
    | succ n ih => rw [pow_succ, ih, succ_nsmul, D.orbitX_add hO]
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [hpow, nsmul_eq_mul, mul_one, CharP.cast_eq_zero, D.orbitX_zero]
  · rw [← D.orbitX_zero O] at h
    exact one_ne_zero (D.orbitX_injective hO h)

theorem exists_eq_orbitGroupC_of_isComponent
    (hX : Finite D.totalFixedGroup)
    {A : Subgroup (adjointGroup τ k)} (hAX : A ≤ D.totalFixedGroup)
    (hA : CFSG.IsComponent (A.subgroupOf D.totalFixedGroup)) :
    ∃ J' : Set.range D.classOrbit, (D.withOrbit J').orbits.Nonempty ∧
      A = (D.withOrbit J').orbitGroupC := by
  have hRX := D.kernelFixedGroup_le_totalFixedGroup
  have hUR := D.orbitFixedJoin_le_kernelFixedGroup
  have hR : Finite D.kernelFixedGroup :=
    Finite.of_injective _ (Subgroup.inclusion_injective hRX)
  have hU : Finite D.orbitFixedJoin := Finite.of_injective _ (Subgroup.inclusion_injective hUR)
  have hAq : CFSG.IsQuasisimple A :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hAX)).1 hA.1
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := OddToralOrdinary.exists_mul_ne_mul_of_isQuasisimple hAq
  obtain ⟨hN₁, hS₁⟩ := normal_isSolvable_subgroupOf (A := D.kernelFixedGroup)
    (B := D.totalFixedGroup) (fun x hx a ha => D.conj_mem_kernelFixedGroup hx ha)
    (fun x hx y hy => D.commutatorElement_mem_kernelFixedGroup hx hy)
  have hAR : A ≤ D.kernelFixedGroup := le_of_isComponent_subgroupOf hA hAX
  have hA₁ := isComponent_subgroupOf_of_le hAR hRX hA
  obtain ⟨hN₂, hS₂⟩ := normal_isSolvable_subgroupOf (A := D.orbitFixedJoin)
    (B := D.kernelFixedGroup) (fun x hx a ha => D.conj_mem_orbitFixedJoin hx ha)
    (fun x hx y hy => D.commutatorElement_mem_orbitFixedJoin hx hy)
  have hAU : A ≤ D.orbitFixedJoin := le_of_isComponent_subgroupOf hA₁ hAR
  have hA₂ := isComponent_subgroupOf_of_le hAU hUR hA₁
  obtain ⟨J', hAΓ⟩ : ∃ J' : Set.range D.classOrbit, A ≤ (D.withOrbit J').fixedGroup := by
    by_contra hne
    push Not at hne
    have hc : ∀ J' : Set.range D.classOrbit,
        (D.withOrbit J').fixedGroup ≤ Subgroup.centralizer (A : Set (adjointGroup τ k)) := by
      intro J' z hz
      have hN : ((D.withOrbit J').fixedGroup.subgroupOf D.orbitFixedJoin).Normal :=
        ⟨fun n hn g => Subgroup.mem_subgroupOf.2
          (D.conj_mem_fixedGroup_withOrbit (hUR g.2) (Subgroup.mem_subgroupOf.1 hn))⟩
      rcases component_normal_subgroup hA₂ hN with h | h
      · exact absurd (fun y hy => h (show (⟨y, hAU hy⟩ : D.orbitFixedJoin) ∈
          A.subgroupOf D.orbitFixedJoin from hy)) (hne J')
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
          (show (⟨y, hAU hy⟩ : D.orbitFixedJoin) ∈ A.subgroupOf D.orbitFixedJoin from hy)
        rw [Subgroup.mem_centralizer_iff] at hyc
        exact (congrArg Subtype.val
          (hyc ⟨z, D.fixedGroup_withOrbit_le_orbitFixedJoin J' hz⟩ hz)).symm
    have hUc : D.orbitFixedJoin ≤ Subgroup.centralizer (A : Set (adjointGroup τ k)) :=
      iSup_le hc
    exact hxy₀ (Subgroup.mem_centralizer_iff.1 (hUc (hAU hy₀)) x₀ hx₀)
  set D' := D.withOrbit J' with hD'
  have hΓ : Finite D'.fixedGroup := D'.finite_fixedGroup
  have hA₃ := isComponent_subgroupOf_of_le hAΓ (D.fixedGroup_withOrbit_le_orbitFixedJoin J') hA₂
  obtain ⟨hN₃, hS₃⟩ := normal_isSolvable_subgroupOf (A := D'.orbitGroupC) (B := D'.fixedGroup)
    (fun x hx a ha => Subgroup.mem_subgroupOf.1
      (D'.orbitGroupC_normal.conj_mem ⟨a, D'.orbitGroupC_le_fixedGroup ha⟩ ha ⟨x, hx⟩))
    (fun x hx y hy => D'.commutator_fixedGroup_le (Subgroup.commutator_mem_commutator hx hy))
  have hAC : A ≤ D'.orbitGroupC := le_of_isComponent_subgroupOf hA₃ hAΓ
  have hA₄ := isComponent_subgroupOf_of_le hAC D'.orbitGroupC_le_fixedGroup hA₃
  have hne : D'.orbits.Nonempty := by
    by_contra hne
    have hbot : D'.orbitGroup = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨O, hO, -⟩
      exact absurd ⟨O, hO⟩ hne
    have h1 : ∀ x ∈ A, x = 1 := fun x hx => by
      have h2 : (x : ModGL τ k) ∈ D'.orbitGroup := hAC hx
      rw [hbot, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    exact hxy₀ (by rw [h1 x₀ hx₀, h1 y₀ hy₀])
  refine ⟨J', hne, le_antisymm hAC ?_⟩
  have e := Subgroup.subgroupOfEquivOfLe D'.orbitGroup_le_adjointGroup
  rcases D'.isQuasisimple_or_isSolvable with hq | hs
  · have hq' : CFSG.IsQuasisimple D'.orbitGroupC := (isQuasisimple_congr e).2 hq
    rcases quasisimple_subnormal_subgroups hq' hA₄.2 with h | h
    · exact Subgroup.subgroupOf_eq_top.1 h
    · exfalso
      apply hxy₀
      have := Subgroup.mem_center_iff.1 (h (show (⟨y₀, hAC hy₀⟩ : D'.orbitGroupC) ∈
        A.subgroupOf D'.orbitGroupC from hy₀)) ⟨x₀, hAC hx₀⟩
      exact congrArg Subtype.val this
  · exfalso
    have : Group.IsSolvable D'.orbitGroupC :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hf := MonoidHom.range_eq_bot_iff.1
      (OddToralOrdinary.range_eq_bot_of_commutator_eq_top hAq.1.commutator_eq_top
        (Subgroup.inclusion hAC))
    have hx' := congrArg Subtype.val (DFunLike.congr_fun hf ⟨x₀, hx₀⟩)
    have hy' := congrArg Subtype.val (DFunLike.congr_fun hf ⟨y₀, hy₀⟩)
    have hx : x₀ = 1 := hx'
    have hy : y₀ = 1 := hy'
    exact hxy₀ (by rw [hx, hy])

end OrthogonalSemilinearFixedRootDatum

theorem orthogonal_semilinear_fixed_components_defining_prime_divisibility
    {τ : Tag} {p₀ : ℕ}
    [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
    (D : OrthogonalSemilinearFixedRootDatum τ p₀ k) (hX : Finite D.totalFixedGroup) :
    (∀ K : Subgroup D.totalFixedGroup, CFSG.IsComponent K →
      (∃ g ∈ K, orderOf g = p₀) ∧ p₀ ∣ Nat.card K) ∧
    (∀ ℓ : ℕ, ℓ.Prime → ∀ K : Subgroup D.totalFixedGroup, CFSG.IsPComponent ℓ K →
      (∃ g ∈ K, orderOf g = p₀) ∧ p₀ ∣ Nat.card K) := by
  have hcomp : ∀ K : Subgroup D.totalFixedGroup, CFSG.IsComponent K →
      (∃ g ∈ K, orderOf g = p₀) ∧ p₀ ∣ Nat.card K := by
    intro K hK
    have hAX : K.map D.totalFixedGroup.subtype ≤ D.totalFixedGroup := Subgroup.map_subtype_le K
    have hAK : (K.map D.totalFixedGroup.subtype).subgroupOf D.totalFixedGroup = K :=
      Subgroup.comap_map_eq_self_of_injective D.totalFixedGroup.subtype_injective K
    obtain ⟨J', ⟨O, hO⟩, hAeq⟩ :=
      D.exists_eq_orbitGroupC_of_isComponent hX hAX (by rw [hAK]; exact hK)
    have hxA : (⟨(D.withOrbit J').orbitX O 1, (D.withOrbit J').orbitMap_mem_adjointGroup O _⟩ :
        adjointGroup τ k) ∈ K.map D.totalFixedGroup.subtype := by
      rw [hAeq]
      exact (D.withOrbit J').orbitMap_mem_orbitGroup hO _
    obtain ⟨g, hg, hge⟩ := hxA
    have hord : orderOf g = p₀ := by
      have hge' : ((g : adjointGroup τ k) : ModGL τ k) = (D.withOrbit J').orbitX O 1 :=
        congrArg Subtype.val hge
      rw [← Subgroup.orderOf_coe g, ← Subgroup.orderOf_coe (g : adjointGroup τ k), hge']
      exact (D.withOrbit J').orderOf_orbitX_one hO
    have hdvd := Subgroup.orderOf_dvd_natCard K hg
    rw [hord] at hdvd
    exact ⟨⟨g, hg, hord⟩, hdvd⟩
  exact ⟨hcomp, fun ℓ hℓ K hK => hcomp K
    ⟨orthogonal_semilinear_total_fixed_p_components D hX ℓ hℓ K hK, hK.choose_spec.2.1⟩⟩

end CFSG.LieType.Chevalley
