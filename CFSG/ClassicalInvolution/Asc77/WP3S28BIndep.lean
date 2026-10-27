module

public import CFSG.ClassicalInvolution.Asc77.WP3S28BBoot
public import CFSG.ClassicalInvolution.Asc77.WP3S28BComm
public import CFSG.ClassicalInvolution.Asc77.WP3FrameData


public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28B

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Balance.Q27 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77

section Pair

variable {G : Type} [Group G]

theorem card_closure_pair_eq_four [Finite G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 := by
  classical
  apply le_antisymm
  · have hsub : (Subgroup.closure ({a, b} : Set G) : Set G) ⊆ ({1, a, b, a * b} : Finset G) := by
      intro x hx
      simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] using ChainFrame.mem_closure_four ha hb hab hx
    calc Nat.card (Subgroup.closure ({a, b} : Set G))
        = Nat.card ((Subgroup.closure ({a, b} : Set G) : Set G)) := rfl
      _ ≤ Nat.card (({1, a, b, a * b} : Finset G) : Set G) :=
        Nat.card_mono (Set.toFinite _) hsub
      _ = Finset.card ({1, a, b, a * b} : Finset G) := Nat.card_eq_finsetCard _
      _ ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        simp
  · set A₁ : Subgroup G := Subgroup.closure ({a} : Set G) with hA₁
    have key1 : ∀ g ∈ A₁, g = 1 ∨ g = a := by
      intro g hg
      refine Subgroup.closure_induction (p := fun g _ => g = 1 ∨ g = a) ?_ ?_ ?_ ?_ hg
      · intro u hu
        right
        simpa using hu
      · left
        rfl
      · rintro u v - - (hu | hu) (hv | hv) <;> subst hu <;> subst hv
        · left; simp
        · right; simp
        · right; simp
        · left; exact ha
      · rintro u - (hu | hu) <;> subst hu
        · left; simp
        · right; exact inv_eq_of_mul_eq_one_right ha
    have h1 : (⊥ : Subgroup G) < A₁ := by
      refine lt_of_le_of_ne bot_le fun hh => ha1 ?_
      have : a ∈ A₁ := Subgroup.subset_closure rfl
      rwa [← hh, Subgroup.mem_bot] at this
    have h2 : A₁ < Subgroup.closure ({a, b} : Set G) := by
      refine lt_of_le_of_ne (Subgroup.closure_mono (by simp)) fun hh => ?_
      have hb' : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
      rw [← hh] at hb'
      rcases key1 b hb' with h | h
      · exact hb1 h
      · exact hba h
    have c1 := ChainFrame.two_mul_card_le_of_lt h1
    have c2 := ChainFrame.two_mul_card_le_of_lt h2
    have hbot : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
    omega

theorem isElemAbelian_closure_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : IsElemAbelian 2 (Subgroup.closure ({a, b} : Set G)) := by
  refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
  · rintro s (rfl | hs)
    · exact ha
    · rw [Set.mem_singleton_iff.mp hs]
      exact hb
  · rintro s (rfl | hs) t (rfl | ht)
    · rfl
    · rw [Set.mem_singleton_iff.mp ht]
      exact hab
    · rw [Set.mem_singleton_iff.mp hs]
      exact hab.symm
    · rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp ht]

end Pair

section Indep

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem indepTriple_of_fuzzy (hmodel : LayerGenerationHybrid p)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hΩmod : HypOmegaMod p f (CoreAssembly.conjClass K))
    (hBelow : CITBelowU p f (Nat.card G)) (hD : DConnected (CoreAssembly.conjClass K))
    (hfz : ∃ A₀ : Subgroup G, Theorem5.FuzzyFrameOn p f (CoreAssembly.conjClass K) A₀) :
    CoreAssembly.IndepTriple p f (CoreAssembly.conjClass K) := by
  classical
  have hα := fuzzy_alphaDelta_bot hmodel hMFC hnab hp2 hq hz hBelow hD hfz
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  have hIH := localLieSystems_of_citBelowU hΩ hBelow
  obtain ⟨A₀, hA₀⟩ := hfz
  have hA₀c := hA₀
  obtain ⟨J, zz, -, hAdef, hel, hcard, -⟩ := hA₀c
  obtain ⟨J₁, J₂, J₃, z₁, z₂, z₃, h1, h2, h3, hT, h12, h13, h23, -, hax⟩ :=
    hA₀.exists_axisTriangle
  have hA₀def : A₀ = Subgroup.closure ({z₁, z₂, z₃} : Set G) := by
    rw [← hax, triangleAxis]
  have hsq : ∀ {Jm : Subgroup G} {a : G}, IsClassicalMember p f Jm a → a * a = 1 :=
    fun h => h.isCentralInvolution.sq
  have hE : ∀ {a b : G}, a ∈ ({z₁, z₂, z₃} : Set G) → b ∈ ({z₁, z₂, z₃} : Set G) →
      a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 → b ≠ a →
      Subgroup.closure ({a, b} : Set G) ∈ signalizerFunctorEk 2 2 A₀ := by
    intro a b ha hb ha2 hb2 hab ha1 hb1 hba
    refine ⟨?_, card_closure_pair_eq_four ha2 hb2 hab ha1 hb1 hba⟩
    rw [hA₀def, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact Subgroup.subset_closure ha
    · rw [Set.mem_singleton_iff.mp hx]
      exact Subgroup.subset_closure hb
  have pair : ∀ (Ja Jb : Subgroup G) (a b : G), Ja ∈ CoreAssembly.conjClass K →
      IsClassicalMember p f Ja a → IsClassicalMember p f Jb b → a * b = b * a →
      b ∈ trivialOnQuot Ja → a ∈ trivialOnQuot Jb → b ≠ a →
      a ∈ ({z₁, z₂, z₃} : Set G) → b ∈ ({z₁, z₂, z₃} : Set G) →
        (∀ x ∈ Ja, b * x = x * b) ∧ (∀ x ∈ Jb, a * x = x * a) ∧ CFSG.Open.IsQuasisimple Ja := by
    intro Ja Jb a b hJa ha hb hcomm hbJa haJb hba haA hbA
    have hca := ha.isCentralInvolution
    have hcb := hb.isCentralInvolution
    have hF : Subgroup.closure ({a, b} : Set G) ∈ signalizerFunctorEk 2 2 A₀ :=
      hE haA hbA hca.sq hcb.sq hcomm hca.ne_one hcb.ne_one hba
    have hFα := hα A₀ hA₀ _ hF
    have h1 : ∀ x ∈ Ja, b * x = x * b :=
      Theorem5.mem_centralizer_of_alphaCore_eq_bot ha hbJa hcb.sq hca.ne_one hFα.1
    have hα' : alphaCore (Subgroup.closure ({b, a} : Set G)) = ⊥ := by
      rw [Set.pair_comm]
      exact hFα.1
    have h2 : ∀ x ∈ Jb, a * x = x * a :=
      Theorem5.mem_centralizer_of_alphaCore_eq_bot hb haJb hca.sq hcb.ne_one hα'
    have hFel : IsElemAbelian 2 (Subgroup.closure ({a, b} : Set G)) :=
      isElemAbelian_closure_pair hca.sq hcb.sq hcomm
    have hJaF : Ja ≤ Subgroup.centralizer ((Subgroup.closure ({a, b} : Set G) : Subgroup G) :
        Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.closure_le]
        rintro s (rfl | hs)
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          exact hca.central x hx
        · rw [Set.mem_singleton_iff.mp hs, SetLike.mem_coe,
            Subgroup.mem_centralizer_singleton_iff]
          exact h1 x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
    exact ⟨h1, h2, Theorem5.isQuasisimple_of_member_of_deltaCore_eq_bot hnab hp2 hq hΩ hIH hJa ha
      hFel hJaF hFα.2⟩
  have hz1u : IsUniqueInvolution J₁ z₁ :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hT.cls₁
  have hz2u : IsUniqueInvolution J₂ z₂ :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hT.cls₂
  have hz3u : IsUniqueInvolution J₃ z₃ :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hT.cls₃
  have p12 := pair J₁ J₂ z₁ z₂ h1 hT.cls₁ hT.cls₂ hT.comm₁₂ hT.tq₁₂ hT.tq₂₁ h12.symm
    (by simp) (by simp)
  have p13 := pair J₁ J₃ z₁ z₃ h1 hT.cls₁ hT.cls₃ hT.comm₁₃ hT.tq₁₃ hT.tq₃₁ h13.symm
    (by simp) (by simp)
  have p23 := pair J₂ J₃ z₂ z₃ h2 hT.cls₂ hT.cls₃ hT.comm₂₃ hT.tq₂₃ hT.tq₃₂ h23.symm
    (by simp) (by simp)
  have hqs : ∀ N ∈ CoreAssembly.conjClass K, CFSG.Open.IsQuasisimple N :=
    Theorem5.isQuasisimple_of_mem_of_single_class (CoreAssembly.exists_single_class K) h1
      p12.2.2
  have hne12 : J₂ ≠ J₁ := fun e => h12 (hz1u.eq (by rw [e] at hz2u; exact hz2u))
  have hne13 : J₃ ≠ J₁ := fun e => h13 (hz1u.eq (by rw [e] at hz3u; exact hz3u))
  have hne23 : J₃ ≠ J₂ := fun e => h23 (hz2u.eq (by rw [e] at hz3u; exact hz3u))
  have C12 : Commutes J₁ J₂ :=
    commutes_of_centralizes_involution hp2 hq hΩmod hqs h1 h2 hne12 hz1u p12.2.1
  have C13 : Commutes J₁ J₃ :=
    commutes_of_centralizes_involution hp2 hq hΩmod hqs h1 h3 hne13 hz1u p13.2.1
  have C23 : Commutes J₂ J₃ :=
    commutes_of_centralizes_involution hp2 hq hΩmod hqs h2 h3 hne23 hz2u p23.2.1
  have hsymm : ∀ {A B : Subgroup G}, Commutes A B → Commutes B A :=
    fun h b hb a ha => (h a ha b hb).symm
  have hrange : Set.range ![z₁, z₂, z₃] = ({z₁, z₂, z₃} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hAx : Subgroup.closure (Set.range ![z₁, z₂, z₃]) = A₀ := by rw [hrange, hA₀def]
  refine ⟨![J₁, J₂, J₃], ![z₁, z₂, z₃], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨h1, hT.cls₁⟩
    · exact ⟨h2, hT.cls₂⟩
    · exact ⟨h3, hT.cls₃⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact C12
    · exact C13
    · exact hsymm C12
    · exact absurd rfl hij
    · exact C23
    · exact hsymm C13
    · exact hsymm C23
    · exact absurd rfl hij
  · rw [hAx]
    exact hel
  · rw [hAx]
    exact hcard

end Indep

end CFSG.ClassicalInvolution.Asc77.S28B
