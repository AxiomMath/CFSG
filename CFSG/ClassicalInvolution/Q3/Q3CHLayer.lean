module

public import CFSG.ClassicalInvolution.Q3.Q3CHLift
public import CFSG.ClassicalInvolution.Q3.Q3CHModel
public import CFSG.ClassicalInvolution.Q3.Q3CPThin
public import CFSG.ClassicalInvolution.Q3.Q3NLExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3NL
open scoped MatrixGroups

section Normalizer

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem nbrs3_subset_of_same_involution (hz : IsClassicalMember3 K z)
    (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z)
    {K₁ K₁' K₂ : Subgroup G} {z₁ z₂ : G} (h₁' : K₁' ∈ conjClass3 K)
    (c₁ : IsClassicalMember3 K₁ z₁) (c₁' : IsClassicalMember3 K₁' z₁)
    (h₂ : K₂ ∈ conjClass3 K) (c₂ : IsClassicalMember3 K₂ z₂) (hne : z₁ ≠ z₂)
    (hc : z₁ * z₂ = z₂ * z₁) (hK₂z : K₂ ≤ Subgroup.centralizer ({z₁} : Set G))
    (c₁₂ : Commutes K₁ K₂) : nbrs3 (conjClass3 K) K₁ ⊆ nbrs3 (conjClass3 K) K₁' := by
  intro J hJ
  obtain ⟨hJΩ, hJne, hcomm⟩ := hJ
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  obtain ⟨w, hw⟩ := hΩ.classical J hJΩ
  have hzw : z₁ * w = w * z₁ := hcomm z₁ c₁.mem w hw.mem
  have hJz : J ≤ Subgroup.centralizer ({z₁} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z₁ c₁.mem y hy).symm
  have hwz : w ≠ z₁ := by
    intro hwz
    rw [hwz] at hw
    have cJ₂ : Commutes J K₂ := hC.of_le hJΩ h₂ hw c₂ hne hc hK₂z
    exact false_of_commuting_twins hB h₂ c₁ hw c₂ hne.symm hcomm c₁₂ cJ₂
  refine ⟨hJΩ, ?_, hC.of_le h₁' hJΩ c₁' hw hwz.symm hzw hJz⟩
  intro hJK
  rw [hJK] at hw
  exact hwz (involution_unique3 hw c₁')

theorem nbrs3_eq_of_same_involution (hz : IsClassicalMember3 K z)
    (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z)
    {K₁ K₁' K₂ : Subgroup G} {z₁ z₂ : G} (h₁ : K₁ ∈ conjClass3 K) (h₁' : K₁' ∈ conjClass3 K)
    (c₁ : IsClassicalMember3 K₁ z₁) (c₁' : IsClassicalMember3 K₁' z₁)
    (h₂ : K₂ ∈ conjClass3 K) (c₂ : IsClassicalMember3 K₂ z₂) (hne : z₁ ≠ z₂)
    (hc : z₁ * z₂ = z₂ * z₁) (hK₂z : K₂ ≤ Subgroup.centralizer ({z₁} : Set G))
    (c₁₂ : Commutes K₁ K₂) : nbrs3 (conjClass3 K) K₁ = nbrs3 (conjClass3 K) K₁' :=
  Set.Subset.antisymm
    (nbrs3_subset_of_same_involution hz hB hC h₁' c₁ c₁' h₂ c₂ hne hc hK₂z c₁₂)
    (nbrs3_subset_of_same_involution hz hB hC h₁ c₁' c₁ h₂ c₂ hne hc hK₂z
      (hC.of_le h₁' h₂ c₁' c₂ hne hc hK₂z))

theorem conjSub_nbrSpan3_of_mem_centralizer (hz : IsClassicalMember3 K z)
    (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G}
    {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z₁} : Set G)) :
    conjSub g (nbrSpan3 (conjClass3 K) K₁) = nbrSpan3 (conjClass3 K) K₁ := by
  have hΩ : ConjInvariant (conjClass3 K) := (inClass3_conjugates hz).conjInvariant
  have hgz : g * z₁ * g⁻¹ = z₁ := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [this]
    group
  have hc' : IsClassicalMember3 (conjSub g K₁) z₁ := by
    have := he.cls₁.conj g
    rwa [hgz] at this
  have heq := nbrs3_eq_of_same_involution hz hB hC he.mem₁ (hΩ g K₁ he.mem₁) he.cls₁ hc'
    he.mem₂ he.cls₂ he.ne he.comm_involutions he.le_centralizer_left he.comm
  rw [← conjSub_nbrSpan3 hΩ g K₁]
  unfold nbrSpan3
  rw [heq]

theorem mul_mul_inv_mem_nbrSpan3 (hz : IsClassicalMember3 K z) (hB : ¬ BootData3 (conjClass3 K))
    (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) {g : G}
    (hg : g ∈ Subgroup.centralizer ({z₁} : Set G)) {x : G}
    (hx : x ∈ nbrSpan3 (conjClass3 K) K₁) : g * x * g⁻¹ ∈ nbrSpan3 (conjClass3 K) K₁ := by
  have h := conjSub_nbrSpan3_of_mem_centralizer hz hB hC he hg
  rw [← h, mem_conjSub_iff]
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e]
  exact hx

end Normalizer

section Layer

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}


theorem exists_layer_bar_comp {Xb : Type} [Group Xb] {c : CompData}
    (hc : c = CompData.model .PSp 2) (ψ : c.G →* Xb) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center c.G) {f : c.G} (hf : f ∈ Subgroup.center c.G)
    (hfz : ψ f ≠ 1) {ub : Xb} (hub : ub * ub = ψ f) :
    ∃ Lb : Subgroup Xb, Lb ≤ Subgroup.centralizer ({ub} : Set Xb) ∧
      (∀ x ∈ Subgroup.centralizer ({ub} : Set Xb), ∀ y ∈ Lb, x * y * x⁻¹ ∈ Lb) ∧
      ub * ub ∈ Lb ∧ Nonempty (Lb ≃* SL(2, ZMod 3)) := by
  subst hc
  have : Fact (Nat.card (GaloisField 3 1) = 3) :=
    ⟨by simpa using GaloisField.card 3 1 (by norm_num)⟩
  exact exists_layer_bar (F := GaloisField 3 1) ψ hψ hker hf hfz hub

theorem exists_layer_of_shapeSp4 (hz : IsClassicalMember3 K z) (hB : ¬ BootData3 (conjClass3 K))
    (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂) {ι : Type}
    (D : LieSystemData3 ι (NbhdQuot (conjClass3 K) K₁) (nbhdFamily (conjClass3 K) K₁))
    (hzX : z₁ ∈ nbrSpan3 (conjClass3 K) K₁)
    (hS : ShapeSp4 D (nbhdMk (conjClass3 K) K₁ z₁ hzX)) {t w : G} (ht : t ∈ K₁)
    (hwX : w ∈ nbrSpan3 (conjClass3 K) K₁) (hw : w * w = z₁) :
    ∃ L : Subgroup G, IsSectionMember3 (Subgroup.centralizer ({t * w} : Set G)) L z₁ := by
  classical
  set X := nbrSpan3 (conjClass3 K) K₁ with hX
  obtain ⟨i₁, hall, hk, f, hf, hfz⟩ := hS
  have hz1sq : z₁ * z₁ = 1 := he.cls₁.isCentralInvolution.sq
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hπ
  let wX : ↥X := ⟨w, hwX⟩
  have hwwX : wX * wX = ⟨z₁, hzX⟩ := Subtype.ext hw
  have hz1ne : π ⟨z₁, hzX⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution X hzX hz1sq he.cls₁.ne_one
  have hfz' : D.hom i₁ f = π ⟨z₁, hzX⟩ := hfz
  have hfne : D.hom i₁ f ≠ 1 := by rw [hfz']; exact hz1ne
  have hub : π wX * π wX = D.hom i₁ f := by rw [← map_mul, hwwX, hfz']
  have hψs : Function.Surjective (D.hom i₁) :=
    MonoidHom.range_eq_top.mp (range_eq_top_of_forall_eq D hall)
  obtain ⟨Lb, hLc, hLn, hubL, hLiso⟩ := exists_layer_bar_comp hk (D.hom i₁) hψs
    (D.ker_le_center i₁) hf hfne hub
  have hw4 : wX ^ 4 = 1 := by
    have e1 : wX ^ 4 = (wX * wX) * (wX * wX) := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [e1, hwwX]
    exact Subtype.ext hz1sq
  obtain ⟨e⟩ := nonempty_equiv_layerOf hw4 hLc hLiso
  have hNorm := normal_layerOf (w := wX) hLn
  rw [Subgroup.normal_subgroupOf_iff (layerOf_le_centralizer wX Lb)] at hNorm
  set Lx := layerOf wX Lb with hLx
  set L : Subgroup G := Lx.map X.subtype with hL
  have hXC : ∀ x ∈ X, t * x = x * t := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (nbrSpan3_le_centralizer (conjClass3 K) K₁ hx) t ht
  have hcomm_iff : ∀ x ∈ X, (x * (t * w) = (t * w) * x ↔ x * w = w * x) := by
    intro x hx
    have h1 : x * t = t * x := (hXC x hx).symm
    constructor
    · intro h
      have : t * (x * w) = t * (w * x) := by
        calc t * (x * w) = (t * x) * w := by group
          _ = (x * t) * w := by rw [h1]
          _ = x * (t * w) := by group
          _ = (t * w) * x := h
          _ = t * (w * x) := by group
      exact mul_left_cancel this
    · intro h
      calc x * (t * w) = (x * t) * w := by group
        _ = (t * x) * w := by rw [h1]
        _ = t * (x * w) := by group
        _ = t * (w * x) := by rw [h]
        _ = (t * w) * x := by group
  have hLX : ∀ y ∈ L, y ∈ X ∧ y ∈ Subgroup.centralizer ({t * w} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine (hcomm_iff x x.2).mpr ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    exact congrArg Subtype.val this
  set R : Subgroup G := X ⊓ Subgroup.centralizer ({t * w} : Set G) with hR
  have hLR : L ≤ R := fun y hy => hLX y hy
  have hzcen : ∀ y ∈ X, y ∈ Subgroup.centralizer ({z₁} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (nbrSpan3_le_centralizer (conjClass3 K) K₁ hy) z₁
        he.cls₁.mem).symm
  have hRC : R ≤ Subgroup.centralizer ({z₁} : Set G) ⊓ Subgroup.centralizer ({t * w} : Set G) :=
    fun y hy => ⟨hzcen y hy.1, hy.2⟩
  refine ⟨L, ?_⟩
  refine
    { le := fun y hy => (hLX y hy).2
      orderOf_eq_two := he.cls₁.orderOf_eq_two
      mem := ?_
      subnormal := ?_
      nonempty_equiv := ?_ }
  · refine ⟨⟨z₁, hzX⟩, mem_layerOf_iff.mpr ⟨?_, ?_⟩, rfl⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
      show z₁ * w = w * z₁
      rw [← hw]
      group
    · rw [← hwwX, map_mul]
      exact hubL
  · refine IsSubnormal.step hLR ?_ (IsSubnormal.step hRC ?_ (IsSubnormal.refl _))
    · rw [Subgroup.normal_subgroupOf_iff hLR]
      rintro _ k ⟨x, hx, rfl⟩ hk
      have hkw : (k : G) * w = w * k := (hcomm_iff k hk.1).mp
        (Subgroup.mem_centralizer_singleton_iff.mp hk.2)
      have hk' : (⟨k, hk.1⟩ : ↥X) ∈ Subgroup.centralizer ({wX} : Set ↥X) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hkw)
      exact ⟨_, hNorm x ⟨k, hk.1⟩ hx hk', rfl⟩
    · rw [Subgroup.normal_subgroupOf_iff hRC]
      intro h k hh hk
      exact ⟨mul_mul_inv_mem_nbrSpan3 hz hB hC he hk.1 hh.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.2 hh.2) (Subgroup.inv_mem _ hk.2)⟩
  · have iL : ↥Lx ≃* ↥L :=
      Subgroup.equivMapOfInjective Lx X.subtype (Subgroup.subtype_injective X)
    have hOL : (classicalInvolutionOddCore ↥Lx).map iL.toMonoidHom =
        classicalInvolutionOddCore ↥L :=
      CFSG.ComponentClassification.OddCore.equiv_invariant iL
    exact ⟨((QuotientGroup.congr _ _ iL hOL).symm).trans e⟩

end Layer

end CFSG.ClassicalInvolution.Q3.Q3CH
