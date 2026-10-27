module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToralBasic
public import CFSG.ClassicalInvolution.Omega
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents
public import CFSG.LieType.Chevalley.OddToralInvolutionFixedComponents
public import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

section TwoComponent

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem isPComponent_two_of_isClassicalMember
    (h4 : 4 ≤ Nat.card (GaloisField p f)) {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) :
    CFSG.IsPComponent 2 (L.subgroupOf (Subgroup.centralizer ({z} : Set Y))) := by
  have hq : CFSG.Open.IsQuasisimple (L ⧸ classicalInvolutionOddCore L) := by
    obtain ⟨e⟩ := h.nonempty_equiv
    exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e
      (isQuasisimple_specialLinearGroup_two h4)
  have hperf : commutator L = ⊤ := h.perfect.commutator_eq_top
  exact (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).2
    (isTwoComponent_subgroupOf_of_perfect h.subnormal hperf hq)

end TwoComponent

section Identify

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem eq_top_of_isPComponent_of_isQuasisimple {G : Type*} [Group G] (hG : CFSG.IsQuasisimple G)
    {p : ℕ} {L : Subgroup G} (hL : CFSG.IsPComponent p L) : L = ⊤ := by
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hL
  have := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hL
  rcases quasisimple_subnormal_subgroups hG hL.choose_spec.2.1 with h | h
  · exact h
  · exfalso
    exact Group.IsPerfect.not_isMulCommutative L
      ⟨⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.1 (h x.2) y).symm⟩⟩

theorem isQuasisimple_componentRootSpan_of_five_le (hK : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ) :
    CFSG.IsQuasisimple (componentRootSpan K χ i) := by
  by_cases h2 : 2 < (componentRoots χ i).ncard
  · exact (odd_sign_root_component_quasisimple τ K χ i).2.2 hK h2
  · induction i using Quotient.inductionOn with
    | h a =>
    obtain ⟨α, hα⟩ := a
    have hΨ := isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧
    have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
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
      rw [heq, CFSG.LieType.Chevalley.OddToralFixed.rootSpan_pair]
    obtain ⟨-, -, -, hfinK⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK
      (hΨ.isRoot α hαΨ)
    obtain ⟨-, h5'⟩ := @hfinK inferInstance
    rw [hS]
    exact (h5' h5).1

theorem exists_le_componentRootSpan_of_isPComponent
    {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ} (L : Subgroup (ModGL τ K))
    (hLS : L ≤ rootSpan τ K (kernelRoots χ))
    (hL : CFSG.IsPComponent 2 (L.subgroupOf (rootSpan τ K (kernelRoots χ)))) :
    ∃ i : KernelComponent χ, L ≤ componentRootSpan K χ i := by
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨-, -, -, hnorm, -, -⟩ := root_character_kernel_orthogonal_central_product τ K χ
  let N : KernelComponent χ → Subgroup ↥(rootSpan τ K (kernelRoots χ)) :=
    fun i => (componentRootSpan K χ i).subgroupOf (rootSpan τ K (kernelRoots χ))
  have hN : ∀ i, (N i).IsSubnormal := fun i => (hnorm i).2.isSubnormal
  have hjoin : iSup N = ⊤ := by
    apply Subgroup.map_injective (rootSpan τ K (kernelRoots χ)).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp only [N, Subgroup.subgroupOf_map_subtype]
    calc ⨆ i, componentRootSpan K χ i ⊓ rootSpan τ K (kernelRoots χ) =
          ⨆ i, componentRootSpan K χ i :=
          iSup_congr fun i => inf_eq_left.2 (componentRootSpan_le K i)
      _ = rootSpan τ K (kernelRoots χ) := iSup_componentRootSpan K
  obtain ⟨i, hi⟩ := CFSG.ComponentClassification.CatalogueBPrimeJoin.exists_le_of_le_iSup 2 _ hL
    N hN (by rw [hjoin]; exact le_top)
  exact ⟨i, fun y hy => hi (show (⟨y, hLS hy⟩ : rootSpan τ K (kernelRoots χ)) ∈
    L.subgroupOf _ from hy)⟩

theorem exists_eq_componentRootSpan_of_isPComponent (hK : ringChar K ≠ 2)
    (h5 : 5 ≤ Nat.card K) (b : Fin τ.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (J : Subgroup (toralCentralizer τ K b)) (hJ : CFSG.IsPComponent 2 J) :
    ∃ i : KernelComponent (maskChar (signTupleBits b)),
      J.map (toralCentralizer τ K b).subtype =
        componentRootSpan K (maskChar (signTupleBits b)) i ∧
      CFSG.IsQuasisimple (componentRootSpan K (maskChar (signTupleBits b)) i) := by
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨hSX, hnormX, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction τ K hK b hb
  have hJX : (J.map (toralCentralizer τ K b).subtype).subgroupOf (toralCentralizer τ K b) = J :=
    Subgroup.comap_map_eq_self_of_injective (toralCentralizer τ K b).subtype_injective J
  have h1 : J.map (toralCentralizer τ K b).subtype ≤ toralCentralizer τ K b ∧
      CFSG.IsPComponent 2 ((J.map (toralCentralizer τ K b).subtype).subgroupOf
        (toralCentralizer τ K b)) :=
    ⟨Subgroup.map_subtype_le J, by rw [hJX]; exact hJ⟩
  obtain ⟨hJS, hJS'⟩ :=
    (CFSG.LieType.AlgebraicGroups.isPComponent_subgroupOf_iff_of_isSolvable hSX 2
      Nat.prime_two (J.map (toralCentralizer τ K b).subtype)).1 h1
  have hSeq : rootSpan τ K (rootCharKernel b) =
      rootSpan τ K (kernelRoots (maskChar (signTupleBits b))) := by
    rw [rootCharKernel_eq_kernelRoots hK hb]
  rw [hSeq] at hJS hJS'
  obtain ⟨i, hi⟩ := exists_le_componentRootSpan_of_isPComponent _ hJS hJS'
  have hq := isQuasisimple_componentRootSpan_of_five_le hK h5 (maskChar (signTupleBits b)) i
  refine ⟨i, le_antisymm hi ?_, hq⟩
  have hcomp := CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_subgroupOf_of_le
    (p := 2) hi (componentRootSpan_le K i) hJS'
  exact Subgroup.subgroupOf_eq_top.1 (eq_top_of_isPComponent_of_isQuasisimple hq hcomp)

theorem neg_mem_kernelRoots {χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ}
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots χ) : -γ ∈ kernelRoots χ :=
  ⟨IsRoot.neg hγ.1, chi_neg hγ.2⟩

theorem exists_eq_rankOne_of_isPComponent (hK : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K)
    (b : Fin τ.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (J : Subgroup (toralCentralizer τ K b)) (hJ : CFSG.IsPComponent 2 J)
    {Y : Type} [Group Y] (φ : Y ≃* J) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    (eY : Y ⧸ O ≃* SL(2, K)) :
    ∃ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      J.map (toralCentralizer τ K b).subtype =
          componentRootSpan K (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ ∧
        componentRootSpan K (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
  have : Finite (ModGL τ K) := finite_modGL
  have : Fintype K := Fintype.ofFinite K
  have hodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hK)
  set χ := maskChar (signTupleBits b) with hχ
  obtain ⟨i, hJi, hq⟩ := exists_eq_componentRootSpan_of_isPComponent hK h5 b hb J hJ
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
  refine ⟨γ, hγ, hJi, ?_⟩
  have hneg : (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) = ⟦⟨-γ, neg_mem_kernelRoots hγ⟩⟧ := by
    refine mk_eq_of_iform_ne_zero ?_
    change iform γ (-γ) ≠ 0
    rw [← neg_one_smul ℤ γ, iform_smul_right]
    have := iform_self_pos hγ.1.ne_zero
    omega
  have hRS : rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) ≤
      componentRootSpan K χ ⟦⟨γ, hγ⟩⟧ := by
    refine sup_le (rootSubgroup_le_componentRootSpan K ⟨γ, hγ⟩) ?_
    rw [hneg]
    exact rootSubgroup_le_componentRootSpan K ⟨-γ, neg_mem_kernelRoots hγ⟩
  obtain ⟨-, ⟨eR⟩, -, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK hγ.1
  let eJS : Y ≃* componentRootSpan K χ ⟦⟨γ, hγ⟩⟧ :=
    φ.trans ((J.equivMapOfInjective _ (toralCentralizer τ K b).subtype_injective).trans
      (MulEquiv.subgroupCongr hJi))
  have : Finite Y := Finite.of_equiv _ eJS.symm.toEquiv
  let ι : SL(2, K) →* Y := eJS.symm.toMonoidHom.comp
    ((Subgroup.inclusion hRS).comp eR.toMonoidHom)
  have hι : Function.Injective ι := eJS.symm.injective.comp
    ((Subgroup.inclusion_injective hRS).comp eR.injective)
  have hYq : CFSG.IsQuasisimple Y := (isQuasisimple_congr eJS).2 hq
  have hsurj := surjective_of_injective_of_isQuasisimple_of_equiv_sl2 hodd (by omega) hYq O hO eY
    ι hι
  refine le_antisymm (fun s hs => ?_) hRS
  obtain ⟨x, hx⟩ := hsurj (eJS.symm ⟨s, hs⟩)
  have h2 : Subgroup.inclusion hRS (eR x) = ⟨s, hs⟩ := by
    have h3 := congrArg eJS hx
    simpa [ι] using h3
  have h3 : ((eR x : ↥(rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ))) :
      (Module.End K (RootModule τ K))ˣ) = s := congrArg Subtype.val h2
  rw [← h3]
  exact (eR x).2

end Identify

section Classical

variable {τ : Tag} {p f : ℕ} [Fact p.Prime]

theorem centralizer_eq_subgroupOf_toralCentralizer {K : Type} [Field K]
    (b : Fin τ.rank → Kˣ) (z : ↥(adjointGroup τ K))
    (hz : (z : ModGL τ K) = rootDiagUnit τ b) :
    Subgroup.centralizer ({z} : Set ↥(adjointGroup τ K)) =
      (toralCentralizer τ K b).subgroupOf (adjointGroup τ K) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, mem_toralCentralizer]
  refine ⟨fun hg => ⟨g.2, ?_⟩, fun hg => ?_⟩
  · have h1 := congrArg Subtype.val hg
    change (g : ModGL τ K) * z = z * g at h1
    rw [hz] at h1
    rw [← h1]
    group
  · apply Subtype.ext
    change (g : ModGL τ K) * z = z * g
    rw [hz]
    calc (g : ModGL τ K) * rootDiagUnit τ b =
        (rootDiagUnit τ b * g * (rootDiagUnit τ b)⁻¹) * rootDiagUnit τ b := by rw [hg.2]
      _ = rootDiagUnit τ b * g := by group

theorem toralCentralizer_le_adjointGroup {K : Type} [Field K] (b : Fin τ.rank → Kˣ) :
    toralCentralizer τ K b ≤ adjointGroup τ K := fun _ hg => (mem_toralCentralizer.1 hg).1

theorem exists_eq_rankOne_of_isClassicalMember_toral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (b : Fin τ.rank → (GaloisField p f)ˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    {L : Subgroup ↥(adjointGroup τ (GaloisField p f))}
    {z : ↥(adjointGroup τ (GaloisField p f))}
    (hz : (z : ModGL τ (GaloisField p f)) = rootDiagUnit τ b) (h : IsClassicalMember p f L z) :
    ∃ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      L.map (adjointGroup τ (GaloisField p f)).subtype =
          componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ ∧
        componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootSubgroup τ (GaloisField p f) γ ⊔ rootSubgroup τ (GaloisField p f) (-γ) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have : Finite (ModGL τ (GaloisField p f)) := finite_modGL
  have hK : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have hCz := centralizer_eq_subgroupOf_toralCentralizer b z hz
  have hXC := toralCentralizer_le_adjointGroup (K := GaloisField p f) (τ := τ) b
  let e : ↥(Subgroup.centralizer ({z} : Set ↥(adjointGroup τ (GaloisField p f)))) ≃*
      ↥(toralCentralizer τ (GaloisField p f) b) :=
    (MulEquiv.subgroupCongr hCz).trans (Subgroup.subgroupOfEquivOfLe hXC)
  have hLCz : L ≤ Subgroup.centralizer ({z} : Set ↥(adjointGroup τ (GaloisField p f))) :=
    isSubnormal_le h.subnormal
  have hP := isPComponent_two_of_isClassicalMember (by omega) h
  set Jx : Subgroup ↥(toralCentralizer τ (GaloisField p f) b) :=
    (L.subgroupOf (Subgroup.centralizer ({z} : Set ↥(adjointGroup τ (GaloisField p f))))).map
      e.toMonoidHom with hJx
  have hJxP : CFSG.IsPComponent 2 Jx := isPComponent_map_of_isPComponent 2 e hP
  let φ : ↥L ≃* ↥Jx := (Subgroup.subgroupOfEquivOfLe hLCz).symm.trans
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)
  obtain ⟨eY⟩ := h.nonempty_equiv
  obtain ⟨γ, hγ, h1, h2⟩ := exists_eq_rankOne_of_isPComponent hK (by omega) b hb Jx hJxP φ
    (classicalInvolutionOddCore L) (CFSG.ComponentClassification.OddCore.odd_card L) eY
  refine ⟨γ, hγ, ?_, h2⟩
  rw [← h1]
  ext y
  simp only [hJx, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨e ⟨g, hLCz hg⟩, ⟨⟨g, hLCz hg⟩, hg, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g.1, hg, rfl⟩

end Classical

end CFSG.ClassicalInvolution.ModelFacts
