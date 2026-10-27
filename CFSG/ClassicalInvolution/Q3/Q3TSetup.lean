module

public import CFSG.ClassicalInvolution.Q3.Q3TEdge
public import CFSG.ClassicalInvolution.Q3.M11OddCore
public import CFSG.ClassicalInvolution.Balance.Theorem5Untouched
public import CFSG.ClassicalInvolution.Q3.ExactDelta
public import CFSG.ClassicalInvolution.Q3.StrongBalance

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

theorem modelOddCentralizerFree3_proved : ModelOddCentralizerFree3 :=
  modelOddCentralizerFree3_of_tags fun t ht => by
    by_cases hex : ExceptionalFundTag3 t
    · rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact oddCentralizerFreeTag_G2
      · exact oddCentralizerFreeTag_F4
      · exact oddCentralizerFreeTag_E6
      · exact oddCentralizerFreeTag_E7
      · exact oddCentralizerFreeTag_E8
      · exact oddCentralizerFreeTag_twistedE6
      · exact oddCentralizerFreeTag_trialityD4
    · exact oddCentralizerFreeTag_of_classical ht hex

theorem lieSystemOddCentralizer3_proved : LieSystemOddCentralizer3 :=
  lieSystemOddCentralizer3_of_modelFacts CFSG.ClassicalInvolution.ModelFacts.modelClauseZero
    modelOddCentralizerFree3_proved

theorem IsEdge3.card_pair {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K₁ K₂ : Subgroup G} {z₁ z₂ : G} (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) = 4 :=
  card_closure_pair_eq_four h.cls₁.isCentralInvolution.sq h.cls₂.isCentralInvolution.sq
    h.cls₁.ne_one h.cls₂.ne_one h.ne h.comm_involutions

theorem IsEdge3.isElemAbelian_pair {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {K₁ K₂ : Subgroup G} {z₁ z₂ : G} (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    IsElemAbelian 2 (Subgroup.closure ({z₁, z₂} : Set G)) := by
  refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
  · intro s hs
    rcases hs with rfl | hs
    · exact h.cls₁.isCentralInvolution.sq
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact h.cls₂.isCentralInvolution.sq
  · intro s hs t ht
    rcases hs with rfl | hs <;> rcases ht with rfl | ht
    · rfl
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact h.comm_involutions
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact h.comm_involutions.symm
    · rw [Set.mem_singleton_iff] at hs ht
      subst hs ht
      rfl

section Alpha

variable {G : Type} [Group G]

theorem oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot3
    {F : Subgroup G} {x : G} (hxF : x ∈ F) (hx1 : x ≠ 1) (h : alphaCore F = ⊥) :
    oddCoreIn (Subgroup.centralizer ({x} : Set G)) ≤ Subgroup.centralizer (F : Set G) := by
  intro u hu
  have huF : u ∈ uCore F := involutionOddCore_le_uCore hxF hx1 hu
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h1 : ⁅u, f⁆ ∈ alphaCore F :=
    commutator_le_alphaCore (Subgroup.commutator_mem_commutator huF hf)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem le_centralizer_involutionOddCore_of_alpha [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) (hO : LocalOddCentralizer3 Ω) {F : Subgroup G} (hFab : IsElemAbelian 2 F)
    (hnc : ∀ b ∈ F, b ≠ 1 → b ∉ Subgroup.center G) (hα : alphaCore F = ⊥) {x : G} (hxF : x ∈ F)
    (hx1 : x ≠ 1) {L : Subgroup G} (hLΩ : L ∈ Ω) (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLF : L ≤ Subgroup.centralizer (F : Set G))
    (hxY : ∀ b ∈ F, b ≠ 1 → b ≠ x → x ∈ centralizingLayer Ω {b}) :
    L ≤ Subgroup.centralizer (involutionOddCore x : Set G) := by
  have hΔ : deltaCore F = ⊥ :=
    le_bot_iff.mp (by simpa [hα] using (deltaCore_le_alphaCore (F := F)))
  have hrF : involutionOddCore x ≤ Subgroup.centralizer (F : Set G) :=
    oddCoreIn_centralizer_le_centralizer_of_alphaCore_eq_bot3 hxF hx1 hα
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hcomm : ⁅r, u⁆ ∈ deltaCore F := by
    refine mem_deltaCore_iff.mpr fun b hb hb1 => ?_
    by_cases hbx : b = x
    · subst hbx
      have : ⁅r, u⁆ = r * (u * r⁻¹ * u⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact (involutionOddCore b).mul_mem hr
        (conj_mem_oddCoreIn (hLx hu) ((involutionOddCore b).inv_mem hr))
    · have hrb : r ∈ involutionOddCore x ⊓ Subgroup.centralizer ({b} : Set G) :=
        ⟨hr, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (hrF hr) b hb).symm⟩
      have hLb : L ≤ Subgroup.centralizer ({b} : Set G) :=
        hLF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
      have hLY : L ≤ centralizingLayer Ω {b} := le_centralizingLayer ⟨hLΩ, hLb⟩
      exact commutator_mem_involutionOddCore_of_localOddCentralizer3 hΩ hO (hnc b hb hb1)
        (hxY b hb hb1 hbx) (orderOf_eq_prime (hFab.2 x hxF) hx1) hrb ⟨hLY hu, hLx hu⟩
  rw [hΔ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
  exact hcomm

theorem alphaCore_eq_bot_of_oddCore_eq_bot {F : Subgroup G} {d : G} (hd : d ∈ F) (hd1 : d ≠ 1)
    (h : ∀ f ∈ F, f ≠ 1 → involutionOddCore f = ⊥) : alphaCore F = ⊥ := by
  have hU : uCore F = ⊥ :=
    le_bot_iff.mp (iSup₂_le fun f hf => iSup_le fun hf1 => by rw [h f hf hf1])
  have hD : deltaCore F = ⊥ :=
    le_bot_iff.mp ((deltaCore_le_involutionOddCore hd hd1).trans (by rw [h d hd hd1]))
  unfold alphaCore
  rw [hU, hD, Subgroup.commutator_bot_left, sup_bot_eq]
  unfold normalClosureIn
  simp

end Alpha

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

@[expose] def TypeC3Alpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥

@[expose] def TypeC3OddFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ x : G, orderOf x = 2 → involutionOddCore x = ⊥

theorem typeC3Alpha_of_oddFree (h : TypeC3OddFree) : TypeC3Alpha := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  have hFab := he.isElemAbelian_pair
  refine alphaCore_eq_bot_of_oddCore_eq_bot (d := z₁) (Subgroup.subset_closure (by simp))
    he.cls₁.ne_one fun f hf hf1 => ?_
  exact h G hnab K z hz hBelow h3 h4 hΔ hB hA2 f (orderOf_eq_prime (hFab.2 f hf) hf1)

theorem member_centralizes_oddCore_of_edge (hnab : ∃ a b : G, a * b ≠ b * a)
    {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (hO : LocalOddCentralizer3 Ω)
    {K₁ M : Subgroup G} {z₁ w : G} (he : IsEdge3 Ω K₁ M z₁ w)
    (hα : alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥) {L : Subgroup G} (hLΩ : L ∈ Ω)
    (hLz : L ≤ Subgroup.centralizer ({z₁} : Set G))
    (hLw : L ≤ Subgroup.centralizer ({w} : Set G)) :
    L ≤ Subgroup.centralizer (involutionOddCore z₁ : Set G) := by
  have hnc : ∀ b ∈ Subgroup.closure ({z₁, w} : Set G), b ≠ 1 → b ∉ Subgroup.center G :=
    fun b _ hb1 hbc => not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  have hFab := he.isElemAbelian_pair
  refine le_centralizer_involutionOddCore_of_alpha hΩ hO hFab hnc hα
    (Subgroup.subset_closure (by simp)) he.cls₁.ne_one hLΩ hLz ?_ ?_
  · rw [Subgroup.centralizer_closure]
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | hy
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLz hk)).symm
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hLw hk)).symm
  · intro b hb _ _
    have hK₁b : K₁ ≤ Subgroup.centralizer ({b} : Set G) :=
      he.le_centralizer_pair.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
    exact le_centralizingLayer (L := K₁) ⟨he.mem₁, hK₁b⟩ he.cls₁.mem

variable {K : Subgroup G} {z : G}

theorem setup3_of_alpha (hα : TypeC3Alpha) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G)) (h3 : 3 ≤ twoRank G)
    (h4 : ¬ TwoSubgroupsFourGenerated G) (hΔ : DeltaConnected K)
    (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) : Setup3 K z := by
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  obtain ⟨K₁, K₂, z₁, z₂, he⟩ := exists_edge3 hnab hz hΔ
  have hα₁ := hα G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  have hnc : ∀ b : G, b ≠ 1 → b ∉ Subgroup.center G := fun b hb1 hbc =>
    not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  have hex1 : classicalInvolutionOddCore ↥K₁ = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ hΩ.conjInvariant hIH he.mem₁ he.cls₁
      he.le_centralizer_pair (fun f _ hf1 => hnc f hf1)
      (le_bot_iff.mp (by simpa [hα₁] using (deltaCore_le_alphaCore
        (F := Subgroup.closure ({z₁, z₂} : Set G)))))
  obtain ⟨b, hb⟩ := he.mem₁
  have hexact : ExactMembers3 (conjClass3 K) := by
    refine exactMembers3_of_conjugates hex1 fun L hL => ?_
    obtain ⟨a, rfl⟩ := hL
    refine ⟨a * b⁻¹, ?_⟩
    show conjSub a K = conjSub (a * b⁻¹) K₁
    rw [← hb, ← conjSub_mul]
    simp
  refine ⟨hexact, ?_⟩
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := by
    refine localOddCentral3_of_members_centralize hΩ.conjInvariant fun L hLΩ hLz => ?_
    obtain ⟨w, hw⟩ := hΩ.classical L hLΩ
    have hwz : z₁ * w = w * z₁ :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hLz hw.mem)).symm
    by_cases hwz1 : w = z₁
    · subst hwz1
      have hc : Commutes L K₂ :=
        commutes_of_not_a2Configuration3 hz hA2 hLΩ he.mem₂ hw he.cls₂ he.ne he.comm_involutions
      refine member_centralizes_oddCore_of_edge hnab hΩ.conjInvariant hO he hα₁ hLΩ hLz ?_
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hc k hk z₂ he.cls₂.mem)
    · have hc : Commutes K₁ L :=
        commutes_of_not_a2Configuration3 hz hA2 he.mem₁ hLΩ he.cls₁ hw (Ne.symm hwz1) hwz
      have he' : IsEdge3 (conjClass3 K) K₁ L z₁ w :=
        ⟨he.mem₁, hLΩ, he.cls₁, hw, hc, Ne.symm hwz1⟩
      exact member_centralizes_oddCore_of_edge hnab hΩ.conjInvariant hO he'
        (hα G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ L z₁ w he') hLΩ hLz
        (isSubnormal_le hw.subnormal)
  obtain ⟨g, -, hg⟩ := conjClass3_involution hz he.mem₁ he.cls₁
  have h := RouteD.Gaps.localOddCentral_conj hΩ.conjInvariant g⁻¹ z₁ hP1
  rwa [hg, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h

end Setup

section Axis

variable {G : Type} [Group G]

structure EdgeAxis3 (z₁ z₂ : G) (A : Subgroup G) : Prop where
  pair_le : Subgroup.closure ({z₁, z₂} : Set G) ≤ A
  balance : RankThreeBalance A
  generation : rankTwoSpan A = ⊤

namespace EdgeAxis3

variable {z₁ z₂ : G} {A : Subgroup G}

theorem pair_mem [Finite G] {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G}
    (h : EdgeAxis3 z₁ z₂ A) (he : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    Subgroup.closure ({z₁, z₂} : Set G) ∈ signalizerFunctorEk 2 2 A :=
  ⟨h.pair_le, by rw [he.card_pair]; norm_num⟩

theorem alphaCore_eq_bot [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : EdgeAxis3 z₁ z₂ A) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk 2 2 A) :
    alphaCore F = ⊥ := by
  have hnorm : (Theorem5.alphaFrame A).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (Theorem5.alphaFrame A : Set G) :=
      Theorem5.rankTwoSpan_le_normalizer_alphaFrame h.balance
        (h.generation ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hle := CFSG.ComponentClassification.OddCore.maximal G (Theorem5.alphaFrame A) hnorm
    (Theorem5.odd_card_alphaFrame h.balance)
  rw [componentClassificationOddCore_eq_bot_of_simple hnab] at hle
  rw [← Theorem5.alphaFrame_eq_alphaCore h.balance hF]
  exact le_bot_iff.mp hle

end EdgeAxis3

end Axis

@[expose] def TypeC3Axes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → ¬ A2Configuration z K →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        ∃ A : Subgroup G, EdgeAxis3 z₁ z₂ A

theorem typeC3Alpha_of_axes (h : TypeC3Axes) : TypeC3Alpha := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  obtain ⟨A, hA⟩ := h G hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  exact hA.alphaCore_eq_bot hnab (hA.pair_mem he)

end CFSG.ClassicalInvolution.Q3
