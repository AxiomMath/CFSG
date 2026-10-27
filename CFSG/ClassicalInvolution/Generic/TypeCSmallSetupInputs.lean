module

public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetup
public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupFrame
public import CFSG.ClassicalInvolution.Balance.BootNoTriple
public import CFSG.ClassicalInvolution.Balance.Theorem5Core
public import CFSG.ClassicalInvolution.Balance.BootstrapLevi
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyCanon
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Generic.TypeCSetup

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Alpha

variable [Finite G]

theorem alphaCore_eq_bot_of_rankTwoSpan_eq_top {A : Subgroup G}
    (hO : componentClassificationOddCore G = ⊥) (hA : RankThreeBalance A)
    (htop : rankTwoSpan A = ⊤) {F : Subgroup G} (hF : F ∈ signalizerFunctorEk 2 2 A) :
    alphaCore F = ⊥ := by
  have hnorm : (Theorem5.alphaFrame A).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (Theorem5.alphaFrame A : Set G) :=
      Theorem5.rankTwoSpan_le_normalizer_alphaFrame hA (htop ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hle := CFSG.ComponentClassification.OddCore.maximal G (Theorem5.alphaFrame A) hnorm
    (Theorem5.odd_card_alphaFrame hA)
  rw [hO] at hle
  rw [← Theorem5.alphaFrame_eq_alphaCore hA hF]
  exact le_bot_iff.mp hle

end Alpha

structure TypeCBranch (p f : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] (K : Subgroup G)
    (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  below : CITBelowU p f (Nat.card G)
  cls : IsClassicalMember p f K z
  rank : 3 ≤ CFSG.Open.twoRank G
  fiveGenerated : ¬ TwoSubgroupsFourGenerated G
  conn : CFSG.ClassicalInvolution.DeltaConnected K
  noBoot : ¬ BootData p f (CoreAssembly.conjClass K)
  noA2 : ¬ A2Configuration z K

structure BalancedEdge (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (K₁ K₂ : Subgroup G) (z₁ z₂ : G) (A : Subgroup G) : Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  cls₁ : IsClassicalMember p f K₁ z₁
  cls₂ : IsClassicalMember p f K₂ z₂
  comm : Commutes K₁ K₂
  ne : z₁ ≠ z₂
  pair_le : Subgroup.closure ({z₁, z₂} : Set G) ≤ A
  balance : RankThreeBalance A
  generation : rankTwoSpan A = ⊤

namespace BalancedEdge

variable [Finite G] {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {A : Subgroup G}

theorem card_pair (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) :
    Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) = 4 :=
  card_closure_pair_eq_four h.cls₁.isCentralInvolution.sq h.cls₂.isCentralInvolution.sq
    h.cls₁.ne_one h.cls₂.ne_one h.ne (h.comm z₁ h.cls₁.mem z₂ h.cls₂.mem)

theorem pair_mem (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) :
    Subgroup.closure ({z₁, z₂} : Set G) ∈ signalizerFunctorEk 2 2 A :=
  ⟨h.pair_le, by rw [h.card_pair]; norm_num⟩

theorem alphaCore_eq_bot [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) :
    alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ :=
  alphaCore_eq_bot_of_rankTwoSpan_eq_top (componentClassificationOddCore_eq_bot_of_simple hnab)
    h.balance h.generation h.pair_mem

theorem deltaCore_eq_bot [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) :
    deltaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥ :=
  le_bot_iff.mp (by simpa [h.alphaCore_eq_bot hnab] using
    (deltaCore_le_alphaCore (F := Subgroup.closure ({z₁, z₂} : Set G))))

omit [Finite G] in
theorem le_centralizer₁ (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) :
    K₁ ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact (Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.RouteD.le_centralizer_of_isClassicalMember h.cls₁ hk)).symm
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (h.comm k hk _ h.cls₂.mem).symm

theorem exactMembers_of_ne_nine [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (h : BalancedEdge p f Ω K₁ K₂ z₁ z₂ A) : ExactMembers Ω :=
  exactMembers_of_deltaCore_eq_bot hnab hp2 hq h9
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hsingle hIH h.mem₁
    h.cls₁
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 h.balance.elem h.pair_le)
    h.le_centralizer₁ (h.deltaCore_eq_bot hnab)

end BalancedEdge


@[expose] def TypeCBalancedFrame (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∃ (K₁ K₂ : Subgroup G) (z₁ z₂ : G) (A : Subgroup G),
      BalancedEdge p f (CoreAssembly.conjClass K) K₁ K₂ z₁ z₂ A

@[expose] def TypeCP1Step (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G) (A : Subgroup G),
      BalancedEdge p f (CoreAssembly.conjClass K) K₁ K₂ z₁ z₂ A →
        (p ^ f ≠ 9 → ExactMembers (CoreAssembly.conjClass K)) →
          LocalOddCentral (CoreAssembly.conjClass K) {z₁}

theorem smallTypeCSetup_of_inputs (hexotic : ExoticLeviBlock p f)
    (hframe : TypeCBalancedFrame p f) (hp1 : TypeCP1Step p f) : SmallTypeCSetup p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
  have hbr : TypeCBranch p f G K z := ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hΔ, hB, hA2⟩
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨K₁, K₂, z₁, z₂, A, hed⟩ := hframe G K z hbr
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  have hsingle := CoreAssembly.exists_single_class K
  have hex9 : p ^ f ≠ 9 → ExactMembers (CoreAssembly.conjClass K) := fun h9 =>
    hed.exactMembers_of_ne_nine hnab hp2 hq h9 hΩ hsingle hIH
  have hP1 : LocalOddCentral (CoreAssembly.conjClass K) {z₁} :=
    hp1 G K z hbr K₁ K₂ z₁ z₂ A hed hex9
  have hP1all := localOddCentral_of_classicalMember hp2 hf hΩ hsingle hed.mem₁ hed.cls₁ hP1
  refine ⟨?_, hP1all K (CoreAssembly.mem_conjClass_self K) z hz⟩
  by_cases h9 : p ^ f = 9
  · exact exactMembers_of_connected_nine hnab hp2 hq h9 hΩ hsingle hIH
      (BootRank3.omegaConnected_of_routeD ((CoreAssembly.deltaConnected_iff K).mp hΔ)) hP1all
      hexotic
  · exact hex9 h9


section Refined

variable [Finite G]

theorem exists_depTriple_of_distinctCentralTriple {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hBD : ¬ BootData p f (CoreAssembly.conjClass K))
    (h : DistinctCentralTriple z K) :
    ∃ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ : G), K₁ ∈ CoreAssembly.conjClass K ∧
      K₂ ∈ CoreAssembly.conjClass K ∧ K₃ ∈ CoreAssembly.conjClass K ∧
        DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃ := by
  obtain ⟨g, hcomm, hinj⟩ := h
  have hcls : ∀ i, IsClassicalMember p f (conjSub (g i)⁻¹ K) ((g i)⁻¹ * z * g i) := fun i => by
    simpa using hz.conj (g i)⁻¹
  have hmem : ∀ i, conjSub (g i)⁻¹ K ∈ CoreAssembly.conjClass K := fun i => ⟨(g i)⁻¹, rfl⟩
  have hc : ∀ i j, i ≠ j → Commutes (conjSub (g i)⁻¹ K) (conjSub (g j)⁻¹ K) :=
    fun i j hij => hcomm i j hij
  have hd : ∀ i j, i ≠ j → (g i)⁻¹ * z * g i ≠ (g j)⁻¹ * z * g j := fun i j hij => hinj.ne hij
  exact ⟨_, _, _, _, _, _, hmem 0, hmem 1, hmem 2,
    depTriple_of_not_bootData hBD (hmem 0) (hcls 0) (hcls 1) (hcls 2) (hc 0 1 (by decide))
      (hc 0 2 (by decide)) (hc 1 2 (by decide)) (hd 0 1 (by decide)) (hd 0 2 (by decide))
      (hd 1 2 (by decide))⟩

theorem injective_vec3 {α : Type*} {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;>
    first
      | exact hab h
      | exact hac h
      | exact hbc h
      | exact hab h.symm
      | exact hac h.symm
      | exact hbc h.symm

theorem distinctCentralTriple_of_commuting (hp2 : p ≠ 2) (hf : 0 < f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hA2 : ¬ A2Configuration z K) {a b c : G}
    (ha : ∃ g : G, a = g * z * g⁻¹) (hb : ∃ g : G, b = g * z * g⁻¹)
    (hc : ∃ g : G, c = g * z * g⁻¹) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (cab : a * b = b * a) (cac : a * c = c * a) (cbc : b * c = c * b) :
    DistinctCentralTriple z K := by
  obtain ⟨ga, rfl⟩ := ha
  obtain ⟨gb, rfl⟩ := hb
  obtain ⟨gc, rfl⟩ := hc
  have hcls : ∀ g : G, IsClassicalMember p f (conjSub g K) (g * z * g⁻¹) := fun g => hz.conj g
  have hmem : ∀ g : G, conjSub g K ∈ CoreAssembly.conjClass K := fun g => ⟨g, rfl⟩
  have key : ∀ {g h : G}, g * z * g⁻¹ ≠ h * z * h⁻¹ →
      (g * z * g⁻¹) * (h * z * h⁻¹) = (h * z * h⁻¹) * (g * z * g⁻¹) →
        ∀ x ∈ K.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom,
          ∀ y ∈ K.map (MulAut.conj (h⁻¹)⁻¹).toMonoidHom, x * y = y * x := by
    intro g h hne hcomm
    rw [inv_inv, inv_inv]
    exact commutes_of_not_a2Configuration hp2 hf hz hA2 (hmem _) (hmem _) (hcls _) (hcls _) hne
      hcomm
  have key' : ∀ {g h : G}, g * z * g⁻¹ ≠ h * z * h⁻¹ →
      (g * z * g⁻¹) * (h * z * h⁻¹) = (h * z * h⁻¹) * (g * z * g⁻¹) →
        ∀ x ∈ K.map (MulAut.conj (h⁻¹)⁻¹).toMonoidHom,
          ∀ y ∈ K.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom, x * y = y * x :=
    fun hne hcomm x hx y hy => (key hne hcomm y hy x hx).symm
  refine ⟨![ga⁻¹, gb⁻¹, gc⁻¹], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact key hab cab
    · exact key hac cac
    · exact key' hab cab
    · exact absurd rfl hij
    · exact key hbc cbc
    · exact key' hac cac
    · exact key' hbc cbc
    · exact absurd rfl hij
  · have : (fun i : Fin 3 => (![ga⁻¹, gb⁻¹, gc⁻¹] i)⁻¹ * z * ![ga⁻¹, gb⁻¹, gc⁻¹] i) =
        ![ga * z * ga⁻¹, gb * z * gb⁻¹, gc * z * gc⁻¹] := by
      funext i
      fin_cases i <;> simp
    rw [this]
    exact injective_vec3 hab hac hbc

structure AxisData (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (K₁ K₂ K₃ : Subgroup G)
    (z₁ z₂ z₃ t₁ t₂ t₃ w : G) : Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  mem₃ : K₃ ∈ Ω
  triple : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃
  ht₁ : t₁ ∈ K₁
  ht₂ : t₂ ∈ K₂
  ht₃ : t₃ ∈ K₃
  sq₁ : t₁ * t₁ = z₁
  sq₂ : t₂ * t₂ = z₂
  sq₃ : t₃ * t₃ = z₃
  hw : w ∈ K₁
  inv : w * t₁ = t₁ * z₁ * w

@[expose] def TypeCAxisBalance (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w : G),
      AxisData p f (CoreAssembly.conjClass K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w →
        RankThreeBalance (axis z₁ z₂ t₁ t₂ t₃)

@[expose] def TypeCAxisGeneration (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w : G),
      AxisData p f (CoreAssembly.conjClass K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w →
        rankTwoSpan (axis z₁ z₂ t₁ t₂ t₃) = ⊤

@[expose] def TypeCTriple (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → DistinctCentralTriple z K

theorem typeCBalancedFrame_of_inputs (h1 : TypeCTriple p f) (h2 : TypeCAxisBalance p f)
    (h3 : TypeCAxisGeneration p f) : TypeCBalancedFrame p f := by
  intro G _ _ _ K z hbr
  obtain ⟨K₁, K₂, K₃, z₁, z₂, z₃, hm₁, hm₂, hm₃, T⟩ :=
    exists_depTriple_of_distinctCentralTriple hbr.cls hbr.noBoot (h1 G K z hbr)
  obtain ⟨t₁, t₂, t₃, w, ht₁, ht₂, ht₃, hw, e₁, e₂, e₃, hwt, -, -⟩ :=
    T.exists_axis hbr.odd hbr.five
  have hdata : AxisData p f (CoreAssembly.conjClass K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w :=
    ⟨hm₁, hm₂, hm₃, T, ht₁, ht₂, ht₃, e₁, e₂, e₃, hw, hwt⟩
  exact ⟨K₁, K₂, z₁, z₂, axis z₁ z₂ t₁ t₂ t₃,
    ⟨hm₁, hm₂, T.cls₁, T.cls₂, T.comm₁₂, T.ne, axis_ge_pair z₁ z₂ t₁ t₂ t₃,
      h2 G K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hdata,
      h3 G K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hdata⟩⟩


theorem DepTriple.axisTriangle {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}
    (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) :
    AxisTriangle p f K₁ K₂ K₃ z₁ z₂ z₃ := by
  have cen : ∀ {K L : Subgroup G} {a : G}, Commutes K L → a ∈ L → ∀ j ∈ K, a * j = j * a :=
    fun hKL ha j hj => (hKL j hj _ ha).symm
  exact ⟨T.cls₁, T.cls₂, T.cls₃, T.comm₁₂ z₁ T.cls₁.mem z₂ T.cls₂.mem,
    T.comm₁₃ z₁ T.cls₁.mem z₃ T.cls₃.mem, T.comm₂₃ z₂ T.cls₂.mem z₃ T.cls₃.mem,
    mem_trivialOnQuot_of_centralizes (cen T.comm₁₂ T.cls₂.mem),
    mem_trivialOnQuot_of_centralizes (cen T.comm₁₃ T.cls₃.mem),
    mem_trivialOnQuot_of_centralizes (cen T.comm₁₂.symm T.cls₁.mem),
    mem_trivialOnQuot_of_centralizes (cen T.comm₂₃ T.cls₃.mem),
    mem_trivialOnQuot_of_centralizes (cen T.comm₁₃.symm T.cls₁.mem),
    mem_trivialOnQuot_of_centralizes (cen T.comm₂₃.symm T.cls₂.mem)⟩

theorem DepTriple.weakBalanced_pair [IsSimpleGroup G] {K₁ K₂ K₃ : Subgroup G}
    {z₁ z₂ z₃ : G} (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hBelow : CITBelowU p f (Nat.card G)) (T : DepTriple p f K₁ K₂ K₃ z₁ z₂ z₃) :
    WeakBalanced (Subgroup.closure ({z₁, z₂} : Set G)) := by
  have h := T.axisTriangle.weakBalanced hnab hp2 hq
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hBelow
  have e : triangleAxis z₁ z₂ z₃ = Subgroup.closure ({z₁, z₂} : Set G) :=
    T.exactTriple.group_eq_closure_pair T.prod
  rwa [e] at h

@[expose] def TypeCEdgeTriangle (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G),
      K₁ ∈ CoreAssembly.conjClass K → K₂ ∈ CoreAssembly.conjClass K →
        IsClassicalMember p f K₁ z₁ → IsClassicalMember p f K₂ z₂ → Commutes K₁ K₂ → z₁ ≠ z₂ →
          ∃ (K₃ : Subgroup G) (z₃ : G), K₃ ∈ CoreAssembly.conjClass K ∧
            IsClassicalMember p f K₃ z₃ ∧ Commutes K₁ K₃ ∧ Commutes K₂ K₃ ∧ z₃ ≠ z₁ ∧ z₃ ≠ z₂

theorem typeCTriple_of_edgeTriangle (h : TypeCEdgeTriangle p f) : TypeCTriple p f := by
  intro G _ _ _ K z hbr
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using hbr.five
    · exact h
  obtain ⟨K₁, K₂, z₁, z₂, h₁, h₂, c₁, c₂, hc, hne⟩ :=
    exists_edge_distinct_involutions hbr.nonabelian hbr.odd hf hbr.cls hbr.conn
  obtain ⟨K₃, z₃, h₃, c₃, m₁₃, m₂₃, d₁₃, d₂₃⟩ := h G K z hbr K₁ K₂ z₁ z₂ h₁ h₂ c₁ c₂ hc hne
  have hconj : ∀ {L : Subgroup G} {w : G}, L ∈ CoreAssembly.conjClass K →
      IsClassicalMember p f L w → ∃ g : G, w = g * z * g⁻¹ := by
    rintro L w ⟨g, rfl⟩ hw
    exact ⟨g, (hbr.cls.conj g).eq_of_isCentralInvolution hbr.odd hf hw.isCentralInvolution⟩
  exact distinctCentralTriple_of_commuting hbr.odd hf hbr.cls hbr.noA2 (hconj h₁ c₁) (hconj h₂ c₂)
    (hconj h₃ c₃) hne (Ne.symm d₁₃) (Ne.symm d₂₃) (hc z₁ c₁.mem z₂ c₂.mem)
    (m₁₃ z₁ c₁.mem z₃ c₃.mem) (m₂₃ z₂ c₂.mem z₃ c₃.mem)

@[expose] def TypeCAxisWeakClassical (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w : G),
      AxisData p f (CoreAssembly.conjClass K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w →
        ∀ a ∈ axis z₁ z₂ t₁ t₂ t₃, a ≠ 1 → ∀ b ∈ Subgroup.closure ({z₁, z₂} : Set G), b ≠ 1 →
          ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, axis z₁ z₂ t₁ t₂ t₃⁆ ≤
            involutionOddCore b

@[expose] def TypeCAxisWeakS (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w : G),
      AxisData p f (CoreAssembly.conjClass K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w →
        ∀ a ∈ axis z₁ z₂ t₁ t₂ t₃, a ≠ 1 → ∀ b ∈ axis z₁ z₂ t₁ t₂ t₃,
          b ∉ Subgroup.closure ({z₁, z₂} : Set G) →
            ⁅involutionOddCore a ⊓ Subgroup.centralizer {b}, axis z₁ z₂ t₁ t₂ t₃⁆ ≤
              involutionOddCore b

@[expose] def TypeCAxisTwo (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w : G),
      AxisData p f (CoreAssembly.conjClass K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w →
        TwoBalancedWrt (axis z₁ z₂ t₁ t₂ t₃)

theorem typeCAxisBalance_of_parts (h1 : TypeCAxisWeakClassical p f) (h2 : TypeCAxisWeakS p f)
    (h3 : TypeCAxisTwo p f) : TypeCAxisBalance p f := by
  intro G _ _ _ K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hd
  obtain ⟨-, -, -, -, -, hA, hcard⟩ :=
    hd.triple.axis_eight hd.ht₁ hd.ht₂ hd.ht₃ hd.sq₁ hd.sq₂ hd.sq₃ hd.hw hd.inv
  refine ⟨hA, hcard, fun a ha ha1 b hb hb1 => ?_, h3 G K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hd⟩
  by_cases hbB : b ∈ Subgroup.closure ({z₁, z₂} : Set G)
  · exact h1 G K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hd a ha ha1 b hbB hb1
  · exact h2 G K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hd a ha ha1 b hb hbB

@[expose] def TypeCFrameSide (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TypeCBranch p f G K z → ∀ (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ z₃ t₁ t₂ t₃ w : G),
      AxisData p f (CoreAssembly.conjClass K) K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w →
        FrameSideTwo p f (CoreAssembly.conjClass K) (axis z₁ z₂ t₁ t₂ t₃) {K₁, K₂, K₃}

theorem typeCAxisGeneration_of_frameSide (h : TypeCFrameSide p f) : TypeCAxisGeneration p f := by
  intro G _ _ _ K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hd
  exact rankTwoSpan_eq_top (inClass_conjugates hbr.cls)
    (h G K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hd)
    (BootRank3.omegaConnected_of_routeD ((CoreAssembly.deltaConnected_iff K).mp hbr.conn))

theorem smallTypeCSetup_of_parts (hexotic : ExoticLeviBlock p f) (h1 : TypeCEdgeTriangle p f)
    (h2a : TypeCAxisWeakClassical p f) (h2b : TypeCAxisWeakS p f) (h2c : TypeCAxisTwo p f)
    (h3 : TypeCFrameSide p f) (hp1 : TypeCP1Step p f) : SmallTypeCSetup p f :=
  smallTypeCSetup_of_inputs hexotic
    (typeCBalancedFrame_of_inputs (typeCTriple_of_edgeTriangle h1)
      (typeCAxisBalance_of_parts h2a h2b h2c) (typeCAxisGeneration_of_frameSide h3)) hp1

end Refined

end CFSG.ClassicalInvolution.Generic.TypeCSetup
