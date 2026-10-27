module

public import CFSG.ClassicalInvolution.Q3.Q3NTLemmaD

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap

section Statement


@[expose] def AlphaCent3Under (P : ∀ {G : Type} [Group G], Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K → P K z →
      ∀ (K₁ L : Subgroup G) (z₁ w : G), K₁ ∈ conjClass3 K → L ∈ conjClass3 K →
        IsClassicalMember3 K₁ z₁ → IsClassicalMember3 L w → z₁ ≠ w →
        L ≤ Subgroup.centralizer ({z₁} : Set G) →
        alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥

theorem AlphaCent3Under.mono {P Q : ∀ {G : Type} [Group G], Subgroup G → G → Prop}
    (hQP : ∀ (G : Type) [Group G] (K : Subgroup G) (z : G), Q K z → P K z)
    (h : AlphaCent3Under P) : AlphaCent3Under Q := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hQ
  exact h G hnab K z hz hBelow h3 h4 hΔ (hQP G K z hQ)

@[expose] def FrameCent3Under (P : ∀ {G : Type} [Group G], Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K → P K z →
      ∀ (K₁ L : Subgroup G) (z₁ w : G), K₁ ∈ conjClass3 K → L ∈ conjClass3 K →
        IsClassicalMember3 K₁ z₁ → IsClassicalMember3 L w → z₁ ≠ w →
        L ≤ Subgroup.centralizer ({z₁} : Set G) → ∃ A : Subgroup G, EdgeAxis3 z₁ w A

theorem alphaCent3Under_of_frameCent3Under {P : ∀ {G : Type} [Group G], Subgroup G → G → Prop}
    (h : FrameCent3Under P) : AlphaCent3Under P := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hP K₁ L z₁ w hK₁ hL hz₁ hw hne hLz
  obtain ⟨A, hA⟩ := h G hnab K z hz hBelow h3 h4 hΔ hP K₁ L z₁ w hK₁ hL hz₁ hw hne hLz
  have hzw : z₁ * w = w * z₁ := (Subgroup.mem_centralizer_singleton_iff.mp (hLz hw.mem)).symm
  have hcard : Nat.card (Subgroup.closure ({z₁, w} : Set G)) = 4 :=
    card_closure_pair_eq_four (Q3NT.mul_self_eq_one_of_orderOf_eq_two hz₁.orderOf_eq_two)
      (Q3NT.mul_self_eq_one_of_orderOf_eq_two hw.orderOf_eq_two) hz₁.ne_one hw.ne_one hne hzw
  exact hA.alphaCore_eq_bot hnab ⟨hA.pair_le, by rw [hcard]; norm_num⟩

end Statement

section Pair

variable {G : Type} [Group G]

theorem Q3NT.le_centralizer_closure_pair {K : Subgroup G} {x y : G}
    (hx : K ≤ Subgroup.centralizer ({x} : Set G)) (hy : K ≤ Subgroup.centralizer ({y} : Set G)) :
    K ≤ Subgroup.centralizer (Subgroup.closure ({x, y} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rcases ht with rfl | ht
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (hx hk)).symm
  · rw [Set.mem_singleton_iff] at ht
    subst ht
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hy hk)).symm

theorem member_centralizes_oddCore_of_pair [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    (hO : LocalOddCentralizer3 Ω) {K₁ : Subgroup G} {z₁ w : G} (hK₁ : K₁ ∈ Ω)
    (hz₁ : IsClassicalMember3 K₁ z₁) (hw : orderOf w = 2) (hzw : z₁ * w = w * z₁)
    (hK₁w : K₁ ≤ Subgroup.centralizer ({w} : Set G))
    (hα : alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥) {L : Subgroup G} (hLΩ : L ∈ Ω)
    (hLz : L ≤ Subgroup.centralizer ({z₁} : Set G))
    (hLw : L ≤ Subgroup.centralizer ({w} : Set G)) :
    L ≤ Subgroup.centralizer (involutionOddCore z₁ : Set G) := by
  have hnc : ∀ b ∈ Subgroup.closure ({z₁, w} : Set G), b ≠ 1 → b ∉ Subgroup.center G :=
    fun b _ hb1 hbc => not_subset_center_of_ne_one hnab hb1 (Set.singleton_subset_iff.mpr hbc)
  have hFab : IsElemAbelian 2 (Subgroup.closure ({z₁, w} : Set G)) := by
    refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
    · intro s hs
      rcases hs with rfl | hs
      · exact Q3NT.mul_self_eq_one_of_orderOf_eq_two hz₁.orderOf_eq_two
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact Q3NT.mul_self_eq_one_of_orderOf_eq_two hw
    · intro s hs t ht
      rcases hs with rfl | hs <;> rcases ht with rfl | ht
      · rfl
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        exact hzw
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        exact hzw.symm
      · rw [Set.mem_singleton_iff] at hs ht
        subst hs ht
        rfl
  refine le_centralizer_involutionOddCore_of_alpha hΩ hO hFab hnc hα
    (Subgroup.subset_closure (by simp)) hz₁.ne_one hLΩ hLz
    (Q3NT.le_centralizer_closure_pair hLz hLw) ?_
  intro b hb _ _
  have hK₁b : K₁ ≤ Subgroup.centralizer ({b} : Set G) :=
    (Q3NT.le_centralizer_closure_pair (isSubnormal_le hz₁.subnormal) hK₁w).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  exact le_centralizingLayer (L := K₁) ⟨hK₁, hK₁b⟩ hz₁.mem

theorem le_centralizer_oddCore_of_conj_centralizer {K₁ : Subgroup G} {z₁ g : G}
    (hg : g ∈ Subgroup.centralizer ({z₁} : Set G))
    (hK₁ : K₁ ≤ Subgroup.centralizer (involutionOddCore z₁ : Set G)) :
    conjSub g K₁ ≤ Subgroup.centralizer (involutionOddCore z₁ : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ involutionOddCore z₁ :=
    conj_mem_oddCoreIn (Subgroup.inv_mem _ hg) hr
  have h1 := Subgroup.mem_centralizer_iff.mp (hK₁ hx) _ hr'
  have h2 : r * x = x * r := by
    calc r * x = g * ((g⁻¹ * r * g⁻¹⁻¹) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = x * r := by group
  exact h2

theorem exists_conj_centralizer_of_involution_eq [Finite G] {K : Subgroup G} {z : G}
    (hz : IsClassicalMember3 K z) {K₁ L : Subgroup G} {z₁ : G} (hK₁ : K₁ ∈ conjClass3 K)
    (hL : L ∈ conjClass3 K) (hz₁ : IsClassicalMember3 K₁ z₁) (hLz₁ : IsClassicalMember3 L z₁) :
    ∃ g ∈ Subgroup.centralizer ({z₁} : Set G), L = conjSub g K₁ := by
  obtain ⟨a, haL, haz⟩ := conjClass3_involution hz hL hLz₁
  obtain ⟨b, hbK, hbz⟩ := conjClass3_involution hz hK₁ hz₁
  refine ⟨a * b⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have : (a * b⁻¹) * z₁ * (a * b⁻¹)⁻¹ = z₁ := by
      calc (a * b⁻¹) * z₁ * (a * b⁻¹)⁻¹ = a * (b⁻¹ * z₁ * b) * a⁻¹ := by group
        _ = a * z * a⁻¹ := by rw [hbz]; group
        _ = z₁ := haz.symm
    calc (a * b⁻¹) * z₁ = (a * b⁻¹) * z₁ * (a * b⁻¹)⁻¹ * (a * b⁻¹) := by group
      _ = z₁ * (a * b⁻¹) := by rw [this]
  · rw [hbK, ← conjSub_mul, haL]
    simp

end Pair

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]


theorem setup3_of_alphaCent3Under {P : ∀ {G : Type} [Group G], Subgroup G → G → Prop}
    (h : AlphaCent3Under P) {K : Subgroup G} {z : G} (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hBelow : CIT3Below (Nat.card G)) (h3 : 3 ≤ twoRank G)
    (h4 : ¬ TwoSubgroupsFourGenerated G) (hΔ : DeltaConnected K) (hP : P K z) :
    Setup3 K z := by
  have hΩ : InClass3 (conjClass3 K) := inClass3_conjugates hz
  have hIH : LocalLieSystems3 (conjClass3 K) := localLieSystems3_of_cit3Below hΩ hBelow
  have hO : LocalOddCentralizer3 (conjClass3 K) :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  have hMFZ : RouteD.Gaps.FundNoncentral 3 := RouteD.Gaps.fundNoncentral 3
  obtain ⟨K₁, K₂, z₁, z₂, he⟩ := exists_edge3 hnab hz hΔ
  have hα₁ : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ :=
    h G hnab K z hz hBelow h3 h4 hΔ hP K₁ K₂ z₁ z₂ he.mem₁ he.mem₂ he.cls₁ he.cls₂ he.ne
      he.le_centralizer_left
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
    ·
      rw [hwz1] at hw
      obtain ⟨g, hg, rfl⟩ := exists_conj_centralizer_of_involution_eq hz he.mem₁ hLΩ he.cls₁ hw
      exact le_centralizer_oddCore_of_conj_centralizer hg
        (member_centralizes_oddCore_of_edge hnab hΩ.conjInvariant hO he hα₁ he.mem₁
          (isSubnormal_le he.cls₁.subnormal) he.le_centralizer_right)
    ·
      have hαw : alphaCore (Subgroup.closure ({z₁, w} : Set G)) = ⊥ :=
        h G hnab K z hz hBelow h3 h4 hΔ hP K₁ L z₁ w he.mem₁ hLΩ he.cls₁ hw (Ne.symm hwz1) hLz
      have hK₁w : K₁ ≤ Subgroup.centralizer ({w} : Set G) :=
        le_centralizer_of_alphaCore_eq_bot3 hMFZ hnab hΩ.conjInvariant hIH he.mem₁ hLΩ he.cls₁
          hw (Ne.symm hwz1) hLz hαw
      exact member_centralizes_oddCore_of_pair hnab hΩ.conjInvariant hO he.mem₁ he.cls₁
        hw.orderOf_eq_two hwz hK₁w hαw hLΩ hLz (isSubnormal_le hw.subnormal)
  obtain ⟨g, -, hg⟩ := conjClass3_involution hz he.mem₁ he.cls₁
  have h := RouteD.Gaps.localOddCentral_conj hΩ.conjInvariant g⁻¹ z₁ hP1
  rwa [hg, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h

theorem bootNoTriple3_of_alphaCent3
    (h : AlphaCent3Under fun K _ => BootData3 (conjClass3 K) ∧ ¬ IndepTriple3 (conjClass3 K)) :
    BootNoTriple3 := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hT
  exact setup3_of_alphaCent3Under h hnab hz hBelow h3 h4 hΔ ⟨hB, hT⟩

theorem smallTypeCSetup3_of_alphaCent3
    (h : AlphaCent3Under fun K z => ¬ BootData3 (conjClass3 K) ∧ ¬ A2Configuration z K) :
    SmallTypeCSetup3 := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA
  exact setup3_of_alphaCent3Under h hnab hz hBelow h3 h4 hΔ ⟨hB, hA⟩

theorem smallA2Setup3_of_alphaCent3
    (h : AlphaCent3Under fun K z => ¬ BootData3 (conjClass3 K) ∧ A2Configuration z K) :
    SmallA2Setup3 := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA
  exact setup3_of_alphaCent3Under h hnab hz hBelow h3 h4 hΔ ⟨hB, hA⟩

end Setup

end CFSG.ClassicalInvolution.Q3
