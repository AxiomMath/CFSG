module

public import CFSG.ClassicalInvolution.Balance.BootstrapP1
public import CFSG.ClassicalInvolution.Balance.BootstrapWeakBalance
public import CFSG.ClassicalInvolution.Balance.BootstrapBalance
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic

public section

namespace CFSG.ClassicalInvolution.Balance.BootRank3

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutator_le_of_closure_members [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {S : Set G}
    (hS : ∀ z ∈ S, z ∈ A ∧ ∃ K ∈ Ω, IsClassicalMember p f K z ∧
      K ≤ Subgroup.centralizer (A : Set G))
    {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1)
    (hgen : A = Subgroup.closure (S ∪ {a, b})) :
    ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b := by
  rw [Subgroup.commutator_le]
  intro r hr g hg
  have hbC : ∀ x ∈ A, x ∈ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨b, hb⟩))
  have hR : involutionOddCore a ⊓ Subgroup.centralizer {b} ≤
      oddCoreIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) := by
    refine le_oddCoreIn_of_normalizes (inf_le_inf (involutionOddCore_le_centralizer a) le_rfl)
      (fun x hx => mem_normalizer_inf (normalizer_oddCoreIn _ hx.1)
        (Subgroup.le_normalizer hx.2)) ?_
    exact (odd_card_oddCoreIn (Subgroup.centralizer {a})).of_dvd_nat
      (Subgroup.card_dvd_of_le inf_le_left)
  have hrR : r ∈ oddCoreIn (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}) := hR hr
  have key : ∀ x ∈ Subgroup.closure (S ∪ {a, b}), ⁅r, x⁆ ∈ involutionOddCore b := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x _ => ⁅r, x⁆ ∈ involutionOddCore b) ?_ ?_ ?_ ?_ hx
    · intro z hz
      rcases hz with hz | hz
      · obtain ⟨hzA, K, hKΩ, hzK, hKA⟩ := hS z hz
        exact commutator_oddCoreIn_le_of_member hnab hp2 hq h0 hA1 hΩ hIH hA hKΩ hzK hzA hKA
          ha ha1 hb hb1 (Subgroup.commutator_mem_commutator hrR hzK.mem)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · have : ⁅r, z⁆ = 1 := by
            rw [commutatorElement_eq_one_iff_mul_comm]
            exact Subgroup.mem_centralizer_singleton_iff.mp
              (involutionOddCore_le_centralizer z hr.1)
          rw [this]; exact one_mem _
        · have : ⁅r, z⁆ = 1 := by
            rw [commutatorElement_eq_one_iff_mul_comm]
            exact Subgroup.mem_centralizer_singleton_iff.mp hr.2
          rw [this]; exact one_mem _
    · simp
    · intro x y hx hy hxM hyM
      have hxA : x ∈ A := hgen ▸ hx
      have : ⁅r, x * y⁆ = ⁅r, x⁆ * (x * ⁅r, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact (involutionOddCore b).mul_mem hxM (conj_mem_oddCoreIn (hbC x hxA) hyM)
    · intro x hx hxM
      have hxA : x ∈ A := hgen ▸ hx
      have : ⁅r, x⁻¹⁆ = x⁻¹ * ⁅r, x⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact conj_mem_oddCoreIn (inv_mem (hbC x hxA)) ((involutionOddCore b).inv_mem hxM)
  exact key g (hgen ▸ hg)

theorem commutator_le_of_closure_member [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω)
    (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ A) (hb1 : b ≠ 1) (hgen : A = Subgroup.closure ({z₀, a, b} : Set G)) :
    ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b := by
  refine commutator_le_of_closure_members (S := {z₀}) hnab hp2 hq h0 hA1 hΩ hIH hA ?_ ha ha1 hb hb1
    ?_
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hz₀A, L₀, hL₀Ω, hz₀, hL₀A⟩
  · rw [Set.singleton_union]
    exact hgen

theorem weakBalanced_of_pairs [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω)
    (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G))
    (hbad : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → A ≠ Subgroup.closure ({z₀, a, b} : Set G) →
      ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b) :
    WeakBalanced A := by
  intro a ha ha1 b hb hb1
  by_cases hgen : A = Subgroup.closure ({z₀, a, b} : Set G)
  · exact commutator_le_of_closure_member hnab hp2 hq h0 hA1 hΩ hIH hA hL₀Ω hz₀ hz₀A hL₀A
      ha ha1 hb hb1 hgen
  · exact hbad a ha ha1 b hb hb1 hgen

theorem weakBalanced_of_pairs_members [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) {S : Set G}
    (hS : ∀ z ∈ S, z ∈ A ∧ ∃ K ∈ Ω, IsClassicalMember p f K z ∧
      K ≤ Subgroup.centralizer (A : Set G))
    (hbad : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → A ≠ Subgroup.closure (S ∪ {a, b}) →
      ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b) :
    WeakBalanced A := by
  intro a ha ha1 b hb hb1
  by_cases hgen : A = Subgroup.closure (S ∪ {a, b})
  · exact commutator_le_of_closure_members hnab hp2 hq h0 hA1 hΩ hIH hA hS ha ha1 hb hb1 hgen
  · exact hbad a ha ha1 b hb hb1 hgen

theorem exists_ne_one_mem_inf_of_card {A F D : Subgroup G} (hA : IsMulCommutative A) (hFA : F ≤ A)
    (hDA : D ≤ A) (hF4 : Nat.card F = 4) (hD4 : 4 ≤ Nat.card D) (hA8 : Nat.card A = 8) :
    ∃ f ∈ F, f ∈ D ∧ f ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : (D.subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := hA.is_comm.comm g n
    simpa [mul_assoc, this] using hn
  let φ : F →* (A ⧸ D.subgroupOf A) :=
    (QuotientGroup.mk' (D.subgroupOf A)).comp (Subgroup.inclusion hFA)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (Subgroup.inclusion hFA x) ∈ D.subgroupOf A := by
      simpa [φ, QuotientGroup.eq_one_iff] using hx
    have hxD : (x : G) ∈ D := hx'
    exact Subtype.ext (hcon x x.2 hxD)
  have h1 : Nat.card F ≤ Nat.card (A ⧸ D.subgroupOf A) := Nat.card_le_card_of_injective φ hinj
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf A)
  have h3 : Nat.card (D.subgroupOf A) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv
  rw [h3] at h2
  nlinarith [h1, h2, hF4, hD4, hA8]

@[expose] def LargeCentralizerOn (A : Subgroup G) (a : G) (L : Subgroup (OddQuot a)) : Prop :=
  ∃ D : Subgroup G, D ≤ A ∧ 4 ≤ Nat.card D ∧ ∀ f ∈ D,
    ∃ hf : f ∈ Subgroup.centralizer ({a} : Set G),
      ∀ y ∈ L, oddQuotMk a ⟨f, hf⟩ * y = y * oddQuotMk a ⟨f, hf⟩

theorem exists_mem_ne_one_centralizes_of_large {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8) {a : G} {L : Subgroup (OddQuot a)}
    (hL : LargeCentralizerOn A a L) {F₀ : Subgroup G} (hF₀A : F₀ ≤ A) (hF₀4 : Nat.card F₀ = 4) :
    ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f := by
  obtain ⟨D, hDA, hD4, hDc⟩ := hL
  obtain ⟨f, hfF, hfD, hf1⟩ := exists_ne_one_mem_inf_of_card hA.1 hF₀A hDA hF₀4 hD4 hcard
  obtain ⟨hfC, hc⟩ := hDc f hfD
  have hsq : (⟨f, hfC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨f, hfC⟩ = 1 :=
    Subtype.ext (by rw [← pow_two]; exact hA.2 f (hF₀A hfF))
  refine ⟨oddQuotMk a ⟨f, hfC⟩, oddQuotMk_mem_modOdd hfF hfC, ?_, hc⟩
  intro h
  exact hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))

theorem largeCentralizerOn_of_indexTwo (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {A : Subgroup G} {S : Set (Subgroup G)}
    (hSΩ : S ⊆ Ω) (hSA : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z)
    (hidx : ∀ b ∈ A, b ≠ 1 → 4 ≤ Nat.card (Subgroup.closure
      {z : G | ∃ K ∈ S, K ≤ Subgroup.centralizer ({b} : Set G) ∧ IsClassicalMember p f K z}))
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {L : Subgroup (OddQuot a)} (hL : OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) :
    LargeCentralizerOn A a L := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  set Z : Set G := {z : G | ∃ K ∈ S, K ≤ Subgroup.centralizer ({a} : Set G) ∧
    IsClassicalMember p f K z} with hZ
  have hDA : Subgroup.closure Z ≤ A := by
    rw [Subgroup.closure_le]
    rintro z ⟨K, hKS, -, hz⟩
    obtain ⟨z', hz'A, hz'⟩ := hSA K hKS
    have : z = z' := hz'.eq_of_isCentralInvolution hp2 hf hz.isCentralInvolution
    rw [this]
    exact hz'A
  refine ⟨Subgroup.closure Z, hDA, hidx a ha ha1, ?_⟩
  intro y hy
  refine Subgroup.closure_induction
    (p := fun y _ => ∃ hy : y ∈ Subgroup.centralizer ({a} : Set G),
      ∀ w ∈ L, oddQuotMk a ⟨y, hy⟩ * w = w * oddQuotMk a ⟨y, hy⟩) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨K, hKS, hKC, hz⟩
    have hzC : z ∈ Subgroup.centralizer ({a} : Set G) := hKC hz.mem
    refine ⟨hzC, fun w hw => ?_⟩
    exact oddQuotMk_centralizes_of_isCentralInvolution (hSΩ hKS) hKC hz.isCentralInvolution
      hzC hL w hw
  · refine ⟨one_mem _, fun w _ => ?_⟩
    have h1 : (⟨1, one_mem _⟩ : ↥(Subgroup.centralizer ({a} : Set G))) = 1 := rfl
    rw [h1, map_one, one_mul, mul_one]
  · rintro y₁ y₂ - - ⟨h₁, c₁⟩ ⟨h₂, c₂⟩
    refine ⟨mul_mem h₁ h₂, fun w hw => ?_⟩
    have : oddQuotMk a ⟨y₁ * y₂, mul_mem h₁ h₂⟩ =
        oddQuotMk a ⟨y₁, h₁⟩ * oddQuotMk a ⟨y₂, h₂⟩ := by
      rw [← map_mul]; rfl
    rw [this, mul_assoc, c₂ w hw, ← mul_assoc, c₁ w hw, mul_assoc]
  · rintro y - ⟨h, c⟩
    refine ⟨inv_mem h, fun w hw => ?_⟩
    have : oddQuotMk a ⟨y⁻¹, inv_mem h⟩ = (oddQuotMk a ⟨y, h⟩)⁻¹ := by
      rw [← map_inv]; rfl
    rw [this]
    have := c w hw
    calc (oddQuotMk a ⟨y, h⟩)⁻¹ * w = (oddQuotMk a ⟨y, h⟩)⁻¹ * (w * oddQuotMk a ⟨y, h⟩) *
        (oddQuotMk a ⟨y, h⟩)⁻¹ := by group
      _ = (oddQuotMk a ⟨y, h⟩)⁻¹ * (oddQuotMk a ⟨y, h⟩ * w) * (oddQuotMk a ⟨y, h⟩)⁻¹ := by
        rw [this]
      _ = w * (oddQuotMk a ⟨y, h⟩)⁻¹ := by group

theorem twoBalancedWrt_of_member_of_layers {A : Subgroup G} (hA : IsElemAbelian 2 A)
    {L₀ : Subgroup G} {z₀ : G} (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀)
    (hz₀A : z₀ ∈ A) (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G))
    (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a)
    (hfree : ∀ a ∈ A, a ≠ 1 → ∀ F₀ : Subgroup G, F₀ ≤ A → Nat.card F₀ = 4 → z₀ ∉ F₀ →
      ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → (OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) →
        ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f) :
    TwoBalancedWrt A := by
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hA.1 ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hA.1.is_comm.comm (⟨f, hF₀E hf⟩ : A) ⟨a, ha⟩)
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => by
    rw [← pow_two]
    exact hA.2 f (hF₀E hf)
  have hF2bar : ∀ f ∈ modOdd a F₀, f * f = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  have hcentral : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      (OmegaFreeAt Ω a L ∨ RankOneAt Ω a L) →
      ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ ∀ y ∈ L, f * y = y * f := by
    intro L hLc hL
    by_cases hz : z₀ ∈ F₀
    · have hzC : z₀ ∈ Subgroup.centralizer ({a} : Set G) := hFC hz
      refine ⟨oddQuotMk a ⟨z₀, hzC⟩, oddQuotMk_mem_modOdd hz hzC, ?_, fun y hy =>
        oddQuotMk_centralizes_of_isCentralInvolution hL₀Ω
          (hL₀A.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)))
          hz₀.isCentralInvolution hzC hL y hy⟩
      intro h
      have hsq : (⟨z₀, hzC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z₀, hzC⟩ = 1 :=
        Subtype.ext (by rw [← pow_two]; exact hA.2 z₀ hz₀A)
      exact hz₀.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
    · exact hfree a ha ha1 F₀ hF₀E h4 hz L hLc hL
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_oddCentralizerFree (pPrimeCore_oddQuot_eq_bot a)
    (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar ?_
  intro L hL hFn hfaith
  rcases hloc a ha ha1 L hL with h | h | hfree'
  · obtain ⟨f, hf, hf1, hfc⟩ := hcentral L hL (Or.inl h)
    exact absurd hfc (hfaith f hf hf1)
  · obtain ⟨f, hf, hf1, hfc⟩ := hcentral L hL (Or.inr h)
    exact absurd hfc (hfaith f hf hf1)
  · exact hfree' F₀ hF₀E h4 hFn hfaith


omit [Finite G] in
theorem isElemAbelian_two_conjSub {G : Type} [Group G] {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (g : G) : IsElemAbelian 2 (conjSub g A) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    have hx := mem_conjSub_iff.mp x.2
    have hy := mem_conjSub_iff.mp y.2
    have h := congrArg Subtype.val (hA.1.is_comm.comm (⟨_, hx⟩ : A) ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    have h2 : g * ((g⁻¹ * x.1 * g) * (g⁻¹ * y.1 * g)) * g⁻¹ =
        g * ((g⁻¹ * y.1 * g) * (g⁻¹ * x.1 * g)) * g⁻¹ := by rw [h]
    simpa [mul_assoc] using h2
  · intro x hx
    have hx' := mem_conjSub_iff.mp hx
    have h := hA.2 _ hx'
    have : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by simp only [pow_two]; group
    rw [this] at h
    have h3 : x ^ 2 = g * (g⁻¹ * x ^ 2 * g) * g⁻¹ := by group
    rw [h3, h]
    group

omit [Finite G] in
theorem deltaCore_eq_bot_conjSub {A : Subgroup G}
    (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 A, deltaCore Φ = ⊥) (g : G) :
    ∀ Φ ∈ signalizerFunctorEk 2 2 (conjSub g A), deltaCore Φ = ⊥ := by
  intro Φ hΦ
  obtain ⟨hΦA, hΦc⟩ := hΦ
  have hF : conjSub g⁻¹ Φ ∈ signalizerFunctorEk 2 2 A := by
    refine ⟨fun x hx => ?_, ?_⟩
    · have h1 := hΦA (mem_conjSub_iff.mp hx)
      have h2 := mem_conjSub_iff.mp h1
      simpa [mul_assoc] using h2
    · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hΦc
  have h1 := deltaCore_map g (conjSub g⁻¹ Φ)
  rw [hΔ _ hF, Subgroup.map_bot] at h1
  have h2 : Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (conjSub g⁻¹ Φ) = Φ :=
    conjSub_conjSub_inv g Φ
  rw [h2] at h1
  exact h1.symm


omit [Finite G] in
theorem conjSub_le_centralizer {L A : Subgroup G} (h : L ≤ Subgroup.centralizer (A : Set G))
    (g : G) : conjSub g L ≤ Subgroup.centralizer (conjSub g A : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp (h hl) a ha
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have e : g * a * g⁻¹ * (g * l * g⁻¹) = g * (a * l) * g⁻¹ := by group
  have e' : g * l * g⁻¹ * (g * a * g⁻¹) = g * (l * a) * g⁻¹ := by group
  rw [e, e', this]

theorem localOddCentral_of_conj_data [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8)
    (hΔ : ∀ Φ ∈ signalizerFunctorEk 2 2 A, deltaCore Φ = ⊥) {L₀ : Subgroup G} {z₀ : G}
    (hL₀Ω : L₀ ∈ Ω) (hz₀ : IsClassicalMember p f L₀ z₀) (hz₀A : z₀ ∈ A)
    (hL₀A : L₀ ≤ Subgroup.centralizer (A : Set G)) {x : G} (hx1 : x ≠ 1)
    (hcov : ∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
      InCommonComponent x K (conjSub g L₀)) :
    LocalOddCentral Ω {x} := by
  intro d hd
  rw [Subgroup.mem_center_iff]
  intro y
  by_cases hne : (centMembers Ω x).Nonempty
  · have hgen := (inClass_local hΩ {x} hne).generated
    have hle : (⨆ L ∈ restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}), L) ≤
        Subgroup.centralizer ({d} : Set ↥(centralizingLayer Ω {x})) := by
      refine iSup₂_le fun L hL => ?_
      obtain ⟨K, hK, hKY, rfl⟩ := hL
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨g, hxg, hcc⟩ := hcov K hK
      exact Subtype.ext (member_commutes_oddCore_of_deltaCore_eq_bot hnab hp2 hq h0 hA1 hΩ hIH
        (isElemAbelian_two_conjSub hA g)
        (by
          rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
          exact hcard)
        (deltaCore_eq_bot_conjSub hΔ g) hxg hx1 hK (hΩ.conjInvariant g L₀ hL₀Ω) (hz₀.conj g)
        (conj_mem_conjSub hz₀A) (conjSub_le_centralizer hL₀A g) hcc d hd k
        (Subgroup.mem_subgroupOf.mp hk)).symm
    have hy : y ∈ (⨆ L ∈ restrictFamily (centralizingMembers Ω {x}) (centralizingLayer Ω {x}), L) :=
      hgen ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  · have hY : centLayer Ω x = ⊥ := by
      refine le_bot_iff.mp (centLayer_le fun L hL => ?_)
      exact absurd ⟨L, hL⟩ hne
    have htriv : ∀ z : ↥(centLayer Ω x), z = 1 := fun z =>
      Subtype.ext (by
        have := z.2
        simpa only [hY, Subgroup.mem_bot, Subgroup.coe_one] using this)
    rw [htriv y, htriv d]

omit [Finite G] in
theorem commutator_le_of_centralizes {A : Subgroup G} {a b : G}
    (h : A ≤ Subgroup.centralizer
      ((involutionOddCore a ⊓ Subgroup.centralizer {b} : Subgroup G) : Set G)) :
    ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ ≤ involutionOddCore b := by
  have : ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h
  rw [this]
  exact bot_le

omit [Finite G] in
theorem badPairs_of_strongBalance {A : Subgroup G} {z₀ : G}
    (h : ∀ b ∈ A, b ≠ 1 → A ≤ Subgroup.centralizer (involutionOddCore b : Set G)) :
    ∀ b ∈ A, b ≠ 1 → ∀ c ∈ A, c ≠ 1 → A ≠ Subgroup.closure ({z₀, b, c} : Set G) →
      ⁅involutionOddCore b ⊓ Subgroup.centralizer {c}, A⁆ ≤ involutionOddCore c :=
  fun b hb hb1 _ _ _ _ =>
    commutator_le_of_centralizes
      ((h b hb hb1).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)))

end CFSG.ClassicalInvolution.Balance.BootRank3
