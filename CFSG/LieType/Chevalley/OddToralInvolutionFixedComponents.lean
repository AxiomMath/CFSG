module

public import CFSG.LieType.Chevalley.OddToralInvolutionComponents
public import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.LieType.Chevalley.OddSignRootComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinJoins

public noncomputable section

namespace CFSG.LieType.Chevalley.OddToralFixed

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBAlternating (pComponent_nontrivial pComponent_perfect)
open CFSG.ComponentClassification.CatalogueBPrimeJoin (exists_le_of_le_iSup
  pComponent_restrict_overgroup)

theorem pComponents_quasisimple_of_iSup {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {ι : Type*} (N : ι → Subgroup G) (hN : ∀ i, (N i).IsSubnormal)
    (hjoin : iSup N = ⊤)
    (hq : ∀ i, ∀ L : Subgroup (N i), CFSG.IsPComponent p L → CFSG.IsQuasisimple L)
    (L : Subgroup G) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi⟩ := exists_le_of_le_iSup p L hL N hN (by rw [hjoin]; exact le_top)
  have hres := pComponent_restrict_overgroup p hL hi
  exact (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hi)).1 (hq i _ hres)

theorem pComponent_quasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ}
    (e : A ≃* B) (hB : ∀ J : Subgroup B, CFSG.IsPComponent p J → CFSG.IsQuasisimple J)
    (J : Subgroup A) (hJ : CFSG.IsPComponent p J) : CFSG.IsQuasisimple J :=
  (isQuasisimple_congr (J.equivMapOfInjective e.toMonoidHom e.injective)).2
    (hB _ (isPComponent_map_of_isPComponent p e hJ))

variable {τ : Tag} {K : Type} [Field K]

theorem pComponent_quasisimple_of_quasisimple {G : Type*} [Group G] (hG : CFSG.IsQuasisimple G)
    {p : ℕ} {L : Subgroup G} (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  have := pComponent_nontrivial hL
  have := pComponent_perfect hL
  rcases quasisimple_subnormal_subgroups hG hL.choose_spec.2.1 with h | h
  · subst h
    exact (isQuasisimple_congr Subgroup.topEquiv).2 hG
  · exfalso
    exact Group.IsPerfect.not_isMulCommutative L
      ⟨⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.1 (h x.2) y).symm⟩⟩

theorem rootSpan_pair
    (α : Fin τ.rank → ℤ) :
    rootSpan τ K {α, -α} = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
  rw [rootSpan, iSup_insert, iSup_singleton]

theorem componentRootSpan_pComponents
    [Finite K] (hK : ringChar K ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ) {p : ℕ}
    (L : Subgroup (componentRootSpan K χ i)) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
  by_cases h2 : 2 < (componentRoots χ i).ncard
  · exact pComponent_quasisimple_of_quasisimple
      ((odd_sign_root_component_quasisimple τ K χ i).2.2 hK h2) hL
  ·
    induction i using Quotient.inductionOn with
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
      rw [heq, rootSpan_pair]
    obtain ⟨-, -, -, hfinK⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK
      (hΨ.isRoot α hαΨ)
    obtain ⟨h3, h5⟩ := @hfinK inferInstance
    refine pComponent_quasisimple_of_mulEquiv (MulEquiv.subgroupCongr hS) (fun M hM => ?_) L hL
    have : Fintype K := Fintype.ofFinite K
    have hodd : Nat.card K % 2 = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.odd_card_of_char_ne_two hK
    have hq2 : 1 < Nat.card K := Finite.one_lt_card
    rcases (show Nat.card K = 3 ∨ 5 ≤ Nat.card K by omega) with h | h
    · exact absurd hM ((h3 h).2 p M)
    · exact ((h5 h).2 p M hM).2

theorem rootSpan_kernelRoots_pComponents
    [Finite K] (hK : ringChar K ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) {p : ℕ} (hp : p.Prime)
    (L : Subgroup (rootSpan τ K (kernelRoots χ))) (hL : CFSG.IsPComponent p L) :
    CFSG.IsQuasisimple L := by
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
  refine pComponents_quasisimple_of_iSup hp N hN hjoin (fun i M hM => ?_) L hL
  exact pComponent_quasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hnorm i).1)
    (fun M' hM' => componentRootSpan_pComponents hK χ i M' hM') M hM

theorem _root_.CFSG.LieType.Chevalley.odd_toral_involution_fixed_p_components
    (τ : Tag)
    (K : Type) [Field K] [Finite K] (hK : Odd (Nat.card K)) (a : Fin τ.rank → Kˣ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) :
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (toralCentralizer τ K a),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp L hL
  have : Fintype K := Fintype.ofFinite K
  have hK2 : ringChar K ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card] at this
    exact (Nat.not_even_iff_odd.2 hK) (Nat.even_iff.2 this)
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨hSX, -, -, -, hred⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction τ K hK2 a ha
  obtain ⟨hLS, hLS'⟩ := (hred p hp L).1 hL
  have hSeq : rootSpan τ K (rootCharKernel a) =
      rootSpan τ K (kernelRoots (maskChar (signTupleBits a))) := by
    rw [rootCharKernel_eq_kernelRoots hK2 ha]
  have e : ↥((rootSpan τ K (rootCharKernel a)).subgroupOf (toralCentralizer τ K a)) ≃*
      ↥(rootSpan τ K (kernelRoots (maskChar (signTupleBits a)))) :=
    (Subgroup.subgroupOfEquivOfLe hSX).trans (MulEquiv.subgroupCongr hSeq)
  have hq := pComponent_quasisimple_of_mulEquiv e
    (fun M hM => rootSpan_kernelRoots_pComponents hK2 _ hp M hM) _ hLS'
  exact (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hLS)).1 hq

end CFSG.LieType.Chevalley.OddToralFixed
