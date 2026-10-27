module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyRows
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedStatements
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedA2

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

section Control

variable {G : Type} [Group G]

theorem exists_involution_mem_zpowers {t : G} (ht1 : t ≠ 1)
    (ht : IsPGroup 2 (Subgroup.zpowers t)) : ∃ s ∈ Subgroup.zpowers t, orderOf s = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp ht) ⟨t, Subgroup.mem_zpowers t⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ht1 (orderOf_eq_one_iff.mp (by simpa using hk))
  refine ⟨t ^ (2 ^ (k - 1)), Subgroup.pow_mem _ (Subgroup.mem_zpowers t) _, ?_⟩
  have hdvd : 2 ^ (k - 1) ∣ orderOf t := by
    rw [hk]
    exact pow_dvd_pow 2 (Nat.sub_le k 1)
  rw [orderOf_pow_of_dvd (by positivity) hdvd, hk]
  have : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [this, Nat.mul_div_cancel _ (by positivity)]

theorem centralizer_singleton_le_of_mem_zpowers {t s : G} (hs : s ∈ Subgroup.zpowers t) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.centralizer ({s} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  exact (Commute.zpow_right (show Commute x t from hx) n).eq

@[expose] def ControlCInv (J : Subgroup G) : Prop :=
  ∀ t : G, orderOf t = 2 → ∀ A ∈ conjugateSet J, ∀ B ∈ conjugateSet J,
    A ≤ Subgroup.centralizer ({t} : Set G) → B ≤ Subgroup.centralizer ({t} : Set G) →
      B ∈ deltaComp J A

theorem controlC_iff_controlCInv (J : Subgroup G) : ControlC J ↔ ControlCInv J := by
  constructor
  · intro h t ht A hA B hB hAt hBt
    have ht1 : t ≠ 1 := by
      rintro rfl
      simp at ht
    exact h t ht1 (isPGroup_two_zpowers_of_orderOf_two ht) A hA B hB hAt hBt
  · intro h t ht1 ht A hA B hB hAt hBt
    obtain ⟨s, hs, hs2⟩ := exists_involution_mem_zpowers ht1 ht
    have hle := centralizer_singleton_le_of_mem_zpowers hs
    exact h s hs2 A hA B hB (hAt.trans hle) (hBt.trans hle)

theorem exists_involution_of_not_controlC {J : Subgroup G} (h : ¬ ControlC J) :
    ∃ t : G, orderOf t = 2 ∧ ∃ A ∈ conjugateSet J, ∃ B ∈ conjugateSet J,
      A ≤ Subgroup.centralizer ({t} : Set G) ∧ B ≤ Subgroup.centralizer ({t} : Set G) ∧
        B ∉ deltaComp J A := by
  rw [controlC_iff_controlCInv] at h
  simp only [ControlCInv, not_forall] at h
  obtain ⟨t, ht, A, hA, B, hB, hAt, hBt, hAB⟩ := h
  exact ⟨t, ht, A, hA, B, hB, hAt, hBt, hAB⟩

theorem not_commute_of_not_mem_deltaComp {J A B : Subgroup G} (hA : A ∈ conjugateSet J)
    (hB : B ∈ conjugateSet J) (h : B ∉ deltaComp J A) :
    A ≠ B ∧ ¬ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  refine ⟨?_, fun hc => ?_⟩
  · rintro rfl
    exact h Relation.ReflTransGen.refl
  · refine h (Relation.ReflTransGen.single ⟨hA, hB, ?_, hc⟩)
    rintro rfl
    exact h Relation.ReflTransGen.refl

end Control

section Branch

variable (p f : ℕ) [Fact p.Prime]

structure DBranch {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  below : CITBelowU p f (Nat.card G)
  member : IsClassicalMember p f K z
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  disconnected : ¬ DeltaConnected K

omit [Fact p.Prime] in
theorem smallDisconnected_iff [Fact p.Prime] :
    SmallDisconnected p f ↔ ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
      (K : Subgroup G) (z : G), DBranch p f K z →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 := by
  constructor
  · intro h G _ _ _ K z hb
    exact h G hb.nonabelian hb.odd hb.five hb.below K z hb.member hb.rank hb.notFourGenerated
      hb.disconnected
  · intro h G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ
    exact h G K z ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hΔ⟩

@[expose] def SmallDisconnectedControlled : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranch p f K z → ControlC K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def SmallDisconnectedUncontrolled : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranch p f K z → ¬ ControlC K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

variable {p f}

theorem smallDisconnected_of_split (hc : SmallDisconnectedControlled p f)
    (hu : SmallDisconnectedUncontrolled p f) : SmallDisconnected p f := by
  rw [smallDisconnected_iff]
  intro G _ _ _ K z hb
  by_cases hC : ControlC K
  · exact hc G K z hb hC
  · exact hu G K z hb hC

@[expose] def ControlImpliesFourGenerated (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f (Nat.card G) → ∀ (K : Subgroup G) (z : G),
      IsClassicalMember p f K z → 3 ≤ CFSG.Open.twoRank G → ¬ DeltaConnected K → ControlC K →
        TwoSubgroupsFourGenerated G

theorem smallDisconnectedControlled_of_fourGenerated (h : ControlImpliesFourGenerated p f) :
    SmallDisconnectedControlled p f := by
  intro G _ _ _ K z hb hC
  exact absurd (h G hb.nonabelian hb.odd hb.five hb.below K z hb.member hb.rank hb.disconnected hC)
    hb.notFourGenerated

theorem controlImpliesFourGenerated_of_controlSmallSylow (hfc : FrameConnected p f)
    (h : ControlSmallSylow) : ControlImpliesFourGenerated p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 hΔ hC
  by_contra h4
  exact h p f hp2 hq G hBelow z hz.orderOf_eq_two K hz.mem hz.subnormal hz.nonempty_equiv hΔ hC
    ⟨h3, h4, fun hE => hΔ (hfc G hnab hp2 hq K z hz hBelow hE)⟩

theorem smallDisconnectedUncontrolled_of_cit (hfc : FrameConnected p f)
    (h : CITDisconnectedUncontrolled) : SmallDisconnectedUncontrolled p f := by
  intro G _ _ _ K z hb hC
  have hz := hb.member
  have hnotE : ¬ HasEFrameRank4 K := fun hE =>
    hb.disconnected (hfc G hb.nonabelian hb.odd hb.five K z hz hb.below hE)
  exact h G hb.nonabelian z hz.orderOf_eq_two K hz.mem hz.subnormal
    (witness_of_isClassicalMember hb.odd hb.five hz) (not_isSolvable_of_isClassicalMember hz)
    ⟨⟨hb.rank, hb.notFourGenerated, hnotE⟩, sl2Witness_of_isClassicalMember hb.odd hb.five hz,
      hb.disconnected, hC⟩

theorem smallDisconnectedControlled_of_cit (hfc : FrameConnected p f)
    (h : CITDisconnectedControlled) : SmallDisconnectedControlled p f := by
  intro G _ _ _ K z hb hC
  have hz := hb.member
  have hnotE : ¬ HasEFrameRank4 K := fun hE =>
    hb.disconnected (hfc G hb.nonabelian hb.odd hb.five K z hz hb.below hE)
  exact h G hb.nonabelian z hz.orderOf_eq_two K hz.mem hz.subnormal
    (witness_of_isClassicalMember hb.odd hb.five hz) (not_isSolvable_of_isClassicalMember hz)
    ⟨⟨hb.rank, hb.notFourGenerated, hnotE⟩, sl2Witness_of_isClassicalMember hb.odd hb.five hz,
      hb.disconnected, hC⟩

end Branch

end CFSG.ClassicalInvolution.Disconnected
