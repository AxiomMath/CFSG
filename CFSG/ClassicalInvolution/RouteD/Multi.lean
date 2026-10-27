module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.RouteD.GapsR2
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.RouteD.LocalRoot

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Abstract

variable {X : Type} [Group X]

theorem commute_left_of_relation {z' x₁ x₂ x₃ y : X} (hz : ∀ w, z' * w = w * z')
    (hrel : x₃ = z' * x₁ * x₂) (h3 : x₃ * y = y * x₃) (h2 : x₂ * y = y * x₂) :
    x₁ * y = y * x₁ := by
  subst hrel
  have key : z' * (x₁ * y) * x₂ = z' * (y * x₁) * x₂ :=
    calc z' * (x₁ * y) * x₂ = z' * x₁ * (y * x₂) := by group
      _ = z' * x₁ * (x₂ * y) := by rw [h2]
      _ = z' * x₁ * x₂ * y := by group
      _ = y * (z' * x₁ * x₂) := h3
      _ = (y * z') * x₁ * x₂ := by group
      _ = (z' * y) * x₁ * x₂ := by rw [hz y]
      _ = z' * (y * x₁) * x₂ := by group
  exact mul_left_cancel (mul_right_cancel key)

theorem commute_right_of_relation {z' x₁ x₂ x₃ y : X} (hz : ∀ w, z' * w = w * z')
    (hrel : x₃ = z' * x₁ * x₂) (h3 : x₃ * y = y * x₃) (h1 : x₁ * y = y * x₁) :
    x₂ * y = y * x₂ := by
  subst hrel
  have key : z' * x₁ * (x₂ * y) = z' * x₁ * (y * x₂) :=
    calc z' * x₁ * (x₂ * y) = z' * x₁ * x₂ * y := by group
      _ = y * (z' * x₁ * x₂) := h3
      _ = (y * z') * x₁ * x₂ := by group
      _ = (z' * y) * x₁ * x₂ := by rw [hz y]
      _ = z' * (y * x₁) * x₂ := by group
      _ = z' * (x₁ * y) * x₂ := by rw [h1]
      _ = z' * x₁ * (y * x₂) := by group
  exact mul_left_cancel key

end Abstract

section Component

variable [Finite G] {Ω : Set (Subgroup G)}

theorem not_central_locElt_of_nonA1 (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) {i : Fin D.card}
    (hi : locImg Ω x N ≤ (D.hom i).range) (hnA1 : ¬ (D.tag i = .PSL ∧ D.rank i = 2)) {w : G}
    (hw : IsClassicalMember p f N w)
    (hcent : ∀ y ∈ (D.hom i).range, locElt Ω x w (le_centralizingLayer hN hw.mem) * y =
      y * locElt Ω x w (le_centralizingLayer hN hw.mem)) : False := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hN hw.mem
  have hmem : locImg Ω x N ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨N, hN, rfl⟩
  obtain ⟨j, R, hR, hRN⟩ := D.fundamental _ hmem
  have hj : locImg Ω x N ≤ (D.hom j).range := hRN ▸ Subgroup.map_le_range _ _
  have hji : j = i := Gaps.eq_of_locImg_le_range hΩ hex D hN hj hi
  subst hji
  have hwmem : locElt Ω x w hwx ∈ R.map (D.hom j) :=
    hRN ▸ locElt_mem_locImg (le_centralizingLayer hN) hw.mem
  obtain ⟨r, hrR, hr⟩ := hwmem
  have hr1 : r = 1 := by
    refine Gaps.fundNoncentral p (D.tag j) (D.rank j) (D.exp j) (D.isFundTag j) (D.admissible j)
      hnA1 R hR r hrR fun y => D.ker_le_center j ?_
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hr]
    have := hcent (D.hom j y) ⟨y, rfl⟩
    calc locElt Ω x w hwx * D.hom j y * (locElt Ω x w hwx)⁻¹ * (D.hom j y)⁻¹
        = (D.hom j y * locElt Ω x w hwx) * (locElt Ω x w hwx)⁻¹ * (D.hom j y)⁻¹ := by
          rw [this]
      _ = 1 := by group
  rw [hr1, map_one] at hr
  have hO : (⟨w, hwx⟩ : ↥(locLayer Ω x)) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
    (QuotientGroup.eq_one_iff _).mp hr.symm
  have h2 : orderOf (⟨w, hwx⟩ : ↥(locLayer Ω x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hw.orderOf_eq_two
  have h3 : orderOf (⟨⟨w, hwx⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  have h4 := orderOf_dvd_natCard (⟨⟨w, hwx⟩, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
  rw [h3] at h4
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
    (even_iff_two_dvd.mpr h4)

theorem false_of_involution_relation (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {z : G}
    {K : Subgroup G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z)
    (D : LieSystemData p f (locQuot Ω z) (locFamily Ω z)) {i₁ i₂ : Fin D.card} (hi : i₁ ≠ i₂)
    (hn₁ : ¬ IsA1Comp D i₁) (hn₂ : ¬ IsA1Comp D i₂) {a₁ a₂ a₃ : Subgroup G}
    (h₁ : a₁ ∈ centralizingMembers Ω {z}) (h₂ : a₂ ∈ centralizingMembers Ω {z})
    (h₃ : a₃ ∈ centralizingMembers Ω {z}) {w₁ w₂ : G} (hw₁ : IsClassicalMember p f a₁ w₁)
    (hw₂ : IsClassicalMember p f a₂ w₂) (hw₃ : IsClassicalMember p f a₃ (z * w₁ * w₂))
    (ha₁ : locImg Ω z a₁ ≤ (D.hom i₁).range) (ha₂ : locImg Ω z a₂ ≤ (D.hom i₂).range) :
    False := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hzY : z ∈ locLayer Ω z := le_centralizingLayer hKz hz.mem
  have hw₁Y : w₁ ∈ locLayer Ω z := le_centralizingLayer h₁ hw₁.mem
  have hw₂Y : w₂ ∈ locLayer Ω z := le_centralizingLayer h₂ hw₂.mem
  have hw₃Y : z * w₁ * w₂ ∈ locLayer Ω z := le_centralizingLayer h₃ hw₃.mem
  have hzc : ∀ q : locQuot Ω z, locElt Ω z z hzY * q = q * locElt Ω z z hzY := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    show QuotientGroup.mk' _ (⟨z, hzY⟩ * y) = QuotientGroup.mk' _ (y * ⟨z, hzY⟩)
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} y.2)).symm
  have hrel : locElt Ω z (z * w₁ * w₂) hw₃Y =
      locElt Ω z z hzY * locElt Ω z w₁ hw₁Y * locElt Ω z w₂ hw₂Y := by
    rw [locElt_mul, locElt_mul]
  obtain ⟨i₃, hi₃⟩ := Gaps.exists_range_of_mem D (mem_locFamily_iff.mpr ⟨a₃, h₃, rfl⟩)
  have hm₃ : locElt Ω z (z * w₁ * w₂) hw₃Y ∈ (D.hom i₃).range :=
    hi₃ (locElt_mem_locImg (le_centralizingLayer h₃) hw₃.mem)
  have hm₁ : locElt Ω z w₁ hw₁Y ∈ (D.hom i₁).range :=
    ha₁ (locElt_mem_locImg (le_centralizingLayer h₁) hw₁.mem)
  have hm₂ : locElt Ω z w₂ hw₂Y ∈ (D.hom i₂).range :=
    ha₂ (locElt_mem_locImg (le_centralizingLayer h₂) hw₂.mem)
  by_cases h31 : i₃ = i₁
  ·
    rw [h31] at hm₃
    refine not_central_locElt_of_nonA1 hΩ hex D h₂ ha₂ hn₂ hw₂ fun y hy => ?_
    have h3 := (Gaps.commutes_range D (Ne.symm hi) y hy _ hm₃).symm
    have h1 := (Gaps.commutes_range D (Ne.symm hi) y hy _ hm₁).symm
    exact commute_right_of_relation hzc hrel h3 h1
  ·
    refine not_central_locElt_of_nonA1 hΩ hex D h₁ ha₁ hn₁ hw₁ fun y hy => ?_
    have h3 := (Gaps.commutes_range D (Ne.symm h31) y hy _ hm₃).symm
    have h2 := (Gaps.commutes_range D hi y hy _ hm₂).symm
    exact commute_left_of_relation hzc hrel h3 h2

end Component

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

@[expose] def D4Frame (p f : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), ConjInvariant Ω →
    ∀ (K a₁ a₂ β : Subgroup G) (z w₁ w₂ : G), K ∈ Ω → a₁ ∈ Ω → a₂ ∈ Ω → β ∈ Ω →
      IsClassicalMember p f K z → IsClassicalMember p f a₁ w₁ → IsClassicalMember p f a₂ w₂ →
      Commutes K a₁ → Commutes K a₂ → Commutes a₁ a₂ →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W a₁ β) →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W a₂ β) →
        ∃ a₃ ∈ Ω, Commutes a₃ K ∧ Commutes a₃ a₁ ∧ Commutes a₃ a₂ ∧
          IsClassicalMember p f a₃ (z * w₁ * w₂)

@[expose] def MultiStar (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      ∀ D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z),
        (∃ i j : Fin D.card, i ≠ j ∧ ¬ IsA1Comp D i ∧ ¬ IsA1Comp D j) →
          ∃ (i₁ i₂ : Fin D.card) (a₁ a₂ β : Subgroup G), i₁ ≠ i₂ ∧ ¬ IsA1Comp D i₁ ∧
            ¬ IsA1Comp D i₂ ∧ a₁ ∈ Gaps.compMembers (conjClass K) z D i₁ ∧
            a₂ ∈ Gaps.compMembers (conjClass K) z D i₂ ∧ β ∈ conjClass K ∧
            (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
            (∃ W, LinearBlockStandardPair (GaloisField p f) W a₁ β) ∧
            (∃ W, LinearBlockStandardPair (GaloisField p f) W a₂ β)

theorem multiPiece_of_star (hstar : MultiStar p f) (hd4 : D4Frame p f) : MultiPiece p f := by
  intro G _ _ _ hnab K z h hshape
  obtain ⟨D, hD⟩ := hshape
  obtain ⟨i₁, i₂, a₁, a₂, β, hi, hn₁, hn₂, ha₁, ha₂, hβ, hKβ, ha₁β, ha₂β⟩ :=
    hstar G hnab K z h D hD
  have hΩ := h.inClass
  have hex := h.exact
  have hP1 := h.p1
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember h.cls⟩
  obtain ⟨w₁, hw₁⟩ := hΩ.classical a₁ ha₁.1.1
  obtain ⟨w₂, hw₂⟩ := hΩ.classical a₂ ha₂.1.1
  have hcomm : ∀ {a : Subgroup G} {i : Fin D.card}, a ∈ Gaps.compMembers (conjClass K) z D i →
      ¬ IsA1Comp D i → Commutes K a := by
    intro a i ha hni
    rcases Gaps.commutes_or_eq_of_involution (Gaps.fundNoncentral p) hΩ hex hP1 D hKz ha.1 h.cls
      with hc | heq
    · exact hc
    · exfalso
      obtain ⟨iK, htag, hrk, hiK⟩ :=
        Gaps.locImg_eq_range_of_involution (Gaps.fundNoncentral p) D hKz h.cls
      have h1 : locImg (conjClass K) z a ≤ (D.hom iK).range := by
        rw [heq]
        exact hiK.le
      have hiiK := Gaps.eq_of_locImg_le_range hΩ hex D ha.1 ha.2 h1
      rw [hiiK] at hni
      exact hni ⟨htag, hrk⟩
  have hKa₁ := hcomm ha₁ hn₁
  have hKa₂ := hcomm ha₂ hn₂
  have ha₁a₂ : Commutes a₁ a₂ := Gaps.commutes_of_ne_comp hΩ hP1 D hi ha₁ ha₂
  obtain ⟨a₃, ha₃, hc₀, hc₁, hc₂, hw₃⟩ := hd4 h.odd h.five G (conjClass K) hΩ.conjInvariant K a₁ a₂ β
    z w₁ w₂ (mem_conjClass_self K) ha₁.1.1 ha₂.1.1 hβ h.cls hw₁ hw₂ hKa₁ hKa₂ ha₁a₂ hKβ ha₁β ha₂β
  have ha₃z : a₃ ∈ centralizingMembers (conjClass K) {z} :=
    ⟨ha₃, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hc₀ x hx z h.cls.mem)⟩
  exact (false_of_involution_relation hΩ hex (mem_conjClass_self K) h.cls D hi hn₁ hn₂ ha₁.1 ha₂.1
    ha₃z hw₁ hw₂ hw₃ ha₁.2 ha₂.2).elim

end CFSG.ClassicalInvolution.RouteD
