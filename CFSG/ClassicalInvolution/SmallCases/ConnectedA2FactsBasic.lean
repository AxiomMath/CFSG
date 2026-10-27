module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Frame
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Inputs

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped IsMulCommutative
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exists_lieSystemData_branch {K : Subgroup G} {z : G} (hb : Branch p f K z) {x : G}
    (hx : x ≠ 1) :
    Nonempty (LieSystemData p f (RouteD.locQuot (conjClass K) x)
      (RouteD.locFamily (conjClass K) x)) := by
  have hZ := center_eq_bot hb.nonabelian
  refine RouteD.NonClassical.exists_lieSystemData
    (localLieSystems_of_citBelowU (inClass_conjugates hb.member) hb.below) ?_
  intro h
  have := h (Set.mem_singleton x)
  rw [SetLike.mem_coe, hZ, Subgroup.mem_bot] at this
  exact hx this

theorem commutes_or_eq_of_branch {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) {x : G} (hx : x ≠ 1)
    (hP1 : LocalOddCentral (conjClass K) {x}) {N L : Subgroup G}
    (hN : N ∈ centralizingMembers (conjClass K) {x})
    (hL : L ∈ centralizingMembers (conjClass K) {x}) (hcl : IsClassicalMember p f N x) :
    Commutes N L ∨ L = N := by
  obtain ⟨D⟩ := exists_lieSystemData_branch hb hx
  exact RouteD.Gaps.commutes_or_eq_of_involution (RouteD.Gaps.fundNoncentral p)
    (inClass_conjugates hb.member) hex hP1 D hN hL hcl

section Frame

variable {F : Type} [Field F] {A : Subgroup G} {S : Set (Subgroup G)}

omit [IsSimpleGroup G] in
theorem frame_member_centralizes {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (Fr : RankFrame F (conjClass K) A S) {N : Subgroup G} (hN : N ∈ S) {w : G}
    (hw : IsUniqueInvolution N w) :
    IsClassicalMember p f N w ∧ N ∈ centralizingMembers (conjClass K) {w} := by
  have hcl := isClassicalMember_of_isUniqueInvolution hb.member (Fr.subset hN) hw
  exact ⟨hcl, Fr.subset hN, le_centralizer hcl⟩

theorem commutes_of_same_involution {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) (Fr : RankFrame F (conjClass K) A S)
    (hP1 : FrameP1 (conjClass K) A) {N L : Subgroup G} (hN : N ∈ S) (hL : L ∈ S) {w : G}
    (hwN : IsUniqueInvolution N w) (hwL : IsUniqueInvolution L w) (hne : N ≠ L) :
    Commutes N L := by
  obtain ⟨hclN, hNc⟩ := frame_member_centralizes hb Fr hN hwN
  obtain ⟨-, hLc⟩ := frame_member_centralizes hb Fr hL hwL
  have hwA : w ∈ A := Fr.mem_of_isUniqueInvolution hN hwN
  rcases commutes_or_eq_of_branch hb hex hwN.ne_one (hP1 w hwA hwN.ne_one) hNc hLc hclN with
    h | h
  · exact h
  · exact absurd h.symm hne

theorem not_le_centralizer_of_not_commutes {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) (Fr : RankFrame F (conjClass K) A S)
    (hP1 : FrameP1 (conjClass K) A) {N L : Subgroup G} (hN : N ∈ S) (hL : L ∈ S) (hne : N ≠ L)
    (hnc : ¬ Commutes N L) {w : G} (hw : IsUniqueInvolution N w) :
    ¬ L ≤ Subgroup.centralizer ({w} : Set G) := by
  intro hLc
  obtain ⟨hclN, hNc⟩ := frame_member_centralizes hb Fr hN hw
  have hwA : w ∈ A := Fr.mem_of_isUniqueInvolution hN hw
  rcases commutes_or_eq_of_branch hb hex hw.ne_one (hP1 w hwA hw.ne_one) hNc
    ⟨Fr.subset hL, hLc⟩ hclN with h | h
  · exact hnc h
  · exact hne h.symm


omit [Finite G] [IsSimpleGroup G] in
theorem closure_pair_mem {a b x : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hx : x ∈ Subgroup.closure ({a, b} : Set G)) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have habb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have haba : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have habab : a * b * (a * b) = 1 := by rw [mul_assoc, hbab, ha]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff.mp hy]; exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul y y' _ _ hy hy' =>
    rcases hy with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;> rw [h, h']
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [ha]
    · simp
    · simpa using Or.inr (Or.inr (Or.inl haab))
    · simp
    · exact Or.inr (Or.inr (Or.inr hba))
    · simp [hb]
    · exact Or.inr (Or.inl hbab)
    · simp
    · exact Or.inr (Or.inr (Or.inl haba))
    · exact Or.inr (Or.inl habb)
    · exact Or.inl habab
  | inv y _ hy =>
    rcases hy with h | h | h | h <;> rw [h]
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
      exact Or.inr (Or.inr (Or.inr hba))

end Frame

omit [Finite G] [IsSimpleGroup G] in
theorem ncard_klein_four {a b : G} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (ha : a * a = 1) : ({1, a, b, a * b} : Set G).ncard = 4 := by
  have hab1 : a * b ≠ 1 := fun h => hab (mul_left_cancel (h.trans ha.symm)).symm
  have h1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm, fun h => hab1 h.symm⟩
  have h2 : a ∉ ({b, a * b} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨hab, fun h => hb1 ?_⟩
    exact (mul_left_cancel (a := a) (by rw [mul_one]; exact h)).symm
  have h3 : b ≠ a * b := fun h => ha1 (mul_right_cancel (b := b) (by rw [one_mul]; exact h)).symm
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]

section FrameCount

variable {F : Type} [Field F] {Ω : Set (Subgroup G)} {A : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] [IsSimpleGroup G] in
theorem card_axisSub_mul_two (Fr : RankFrame F Ω A S) {K : Subgroup G} (hK : K ∈ S) :
    Nat.card (axisSub A K) * 2 = Nat.card A := by
  have hCA : axisSub A K ≤ A := inf_le_left
  have hidx : (axisSub A K).relIndex A = 2 := Fr.relIndex_axisSub hK
  have h1 := ((axisSub A K).subgroupOf A).card_mul_index
  have h3 : Nat.card ((axisSub A K).subgroupOf A) = Nat.card (axisSub A K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv
  rw [h3] at h1
  rw [Subgroup.relIndex] at hidx
  rw [hidx] at h1
  exact h1

end FrameCount

section Connected

variable {F : Type} [Field F] {A : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] [IsSimpleGroup G] in
theorem mul_comm_of_isUniqueInvolution {K : Subgroup G} {w : G} (hw : IsUniqueInvolution K w)
    {k : G} (hk : k ∈ K) : k * w = w * k := by
  have h := hw.conj_eq (n := k) (conjSub_eq_self_of_mem hk)
  exact (mul_inv_eq_iff_eq_mul.mp h)

theorem not_commutes_of_commutes_pair {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) (Fr : RankFrame F (conjClass K) A S)
    (hP1 : FrameP1 (conjClass K) A) (hcard : Nat.card A = 8) {K₁ K₂ M : Subgroup G}
    (h₁ : K₁ ∈ S) (h₂ : K₂ ∈ S) (hM : M ∈ S) (hne : K₁ ≠ K₂) (hnc : ¬ Commutes K₁ K₂) :
    ¬ (M ≠ K₁ ∧ M ≠ K₂ ∧ Commutes M K₁ ∧ Commutes M K₂) := by
  rintro ⟨hM₁, hM₂, hc₁, hc₂⟩
  obtain ⟨z₁, hz₁⟩ := Fr.exists_isUniqueInvolution h₁
  obtain ⟨z₂, hz₂⟩ := Fr.exists_isUniqueInvolution h₂
  obtain ⟨zM, hzM⟩ := Fr.exists_isUniqueInvolution hM
  have hz12 : z₁ ≠ z₂ := by
    intro h
    exact hnc (commutes_of_same_involution hb hex Fr hP1 h₁ h₂ hz₁ (h ▸ hz₂) hne)
  have hpa₁ : ¬ K₂ ≤ Subgroup.centralizer ({z₁} : Set G) :=
    not_le_centralizer_of_not_commutes hb hex Fr hP1 h₁ h₂ hne hnc hz₁
  have hpa₂ : ¬ K₁ ≤ Subgroup.centralizer ({z₂} : Set G) :=
    not_le_centralizer_of_not_commutes hb hex Fr hP1 h₂ h₁ hne.symm (fun h => hnc h.symm) hz₂
  have hCcard : Nat.card (axisSub A M) = 4 := by
    have := card_axisSub_mul_two Fr hM
    omega
  have hz₁C : z₁ ∈ axisSub A M :=
    mem_axisSub_iff.mpr ⟨Fr.mem_of_isUniqueInvolution h₁ hz₁, fun m hm => hc₁ m hm z₁ hz₁.mem⟩
  have hz₂C : z₂ ∈ axisSub A M :=
    mem_axisSub_iff.mpr ⟨Fr.mem_of_isUniqueInvolution h₂ hz₂, fun m hm => hc₂ m hm z₂ hz₂.mem⟩
  have hzMC : zM ∈ axisSub A M := Fr.mem_axisSub_of_isUniqueInvolution hM hzM
  have hsub : ({1, z₁, z₂, z₁ * z₂} : Set G) ⊆ (axisSub A M : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (axisSub A M).one_mem
    · exact hz₁C
    · exact hz₂C
    · exact (axisSub A M).mul_mem hz₁C hz₂C
  have hT : ({1, z₁, z₂, z₁ * z₂} : Set G) = (axisSub A M : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [ncard_klein_four hz₁.ne_one hz₂.ne_one hz12 hz₁.sq, ← Nat.card_coe_set_eq]
    exact hCcard.le
  have hzMT : zM ∈ ({1, z₁, z₂, z₁ * z₂} : Set G) := by
    rw [hT]
    exact hzMC
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzMT
  rcases hzMT with h | h | h | h
  · exact hzM.ne_one h
  ·
    apply hpa₁
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hc₂ zM (hzM.mem) k hk
    rw [h] at this
    exact this.symm
  · apply hpa₂
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hc₁ zM (hzM.mem) k hk
    rw [h] at this
    exact this.symm
  · apply hpa₂
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hc₁ zM (hzM.mem) k hk
    rw [h] at h1
    have h2 : k * z₁ = z₁ * k := mul_comm_of_isUniqueInvolution hz₁ hk
    have h3 : z₁ * (z₂ * k) = z₁ * (k * z₂) := by
      calc z₁ * (z₂ * k) = z₁ * z₂ * k := by rw [mul_assoc]
        _ = k * (z₁ * z₂) := h1
        _ = k * z₁ * z₂ := by rw [mul_assoc]
        _ = z₁ * k * z₂ := by rw [h2]
        _ = z₁ * (k * z₂) := by rw [mul_assoc]
    exact (mul_left_cancel h3).symm

theorem nonCommConnected_of_card_eight {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) (Fr : RankFrame F (conjClass K) A S)
    (hP1 : FrameP1 (conjClass K) A) (hcard : Nat.card A = 8) {K₁ K₂ : Subgroup G}
    (h₁ : K₁ ∈ S) (h₂ : K₂ ∈ S) (hne : K₁ ≠ K₂) (hnc : ¬ Commutes K₁ K₂) :
    NonCommConnected S := by
  have h12 : (nonCommGraph S).Adj ⟨K₁, h₁⟩ ⟨K₂, h₂⟩ :=
    nonCommGraph_adj.mpr ⟨fun h => hne (congrArg Subtype.val h), hnc⟩
  have key : ∀ M : ↥S, (nonCommGraph S).Reachable M ⟨K₁, h₁⟩ := by
    intro M
    by_cases hM1 : (M : Subgroup G) = K₁
    · have : M = ⟨K₁, h₁⟩ := Subtype.ext hM1
      rw [this]
    by_cases hM2 : (M : Subgroup G) = K₂
    · have : M = ⟨K₂, h₂⟩ := Subtype.ext hM2
      rw [this]
      exact h12.symm.reachable
    by_cases hc₁ : Commutes (M : Subgroup G) K₁
    · have hnc₂ : ¬ Commutes (M : Subgroup G) K₂ := fun hc₂ =>
        not_commutes_of_commutes_pair hb hex Fr hP1 hcard h₁ h₂ M.2 hne hnc ⟨hM1, hM2, hc₁, hc₂⟩
      have hadj : (nonCommGraph S).Adj M ⟨K₂, h₂⟩ :=
        nonCommGraph_adj.mpr ⟨fun h => hM2 (congrArg Subtype.val h), hnc₂⟩
      exact hadj.reachable.trans h12.symm.reachable
    · exact (nonCommGraph_adj.mpr ⟨fun h => hM1 (congrArg Subtype.val h), hc₁⟩).reachable
  rw [NonCommConnected, SimpleGraph.connected_iff]
  exact ⟨fun M N => (key M).trans (key N).symm, ⟨⟨K₁, h₁⟩⟩⟩

end Connected

end CFSG.ClassicalInvolution.ConnectedA2
