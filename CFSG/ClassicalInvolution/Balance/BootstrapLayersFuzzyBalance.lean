module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyGen
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped commutatorElement MatrixGroups

section Quasi

theorem isQuasisimple_map_of_ker_le_center {K X : Type*} [Group K] [Group X] (ψ : K →* X)
    (hker : ψ.ker ≤ Subgroup.center K) {R : Subgroup K} (hR : CFSG.Open.IsQuasisimple ↥R) :
    CFSG.Open.IsQuasisimple ↥(R.map ψ) := by
  set φ : ↥R →* X := ψ.comp R.subtype with hφ
  have hker' : φ.ker ≤ Subgroup.center ↥R := by
    intro r hr
    have hrc := hker (show (r : K) ∈ ψ.ker from hr)
    rw [Subgroup.mem_center_iff] at hrc ⊢
    intro s
    exact Subtype.ext (hrc s)
  have hq := Quasisimple.central_quotient hR φ.ker hker'
  have hrange : φ.range = R.map ψ := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have : CFSG.Open.IsQuasisimple ↥φ.range :=
    Components.quasisimple_of_equiv (QuotientGroup.quotientKerEquivRange φ).symm hq
  rwa [hrange] at this

end Quasi

section Inputs

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

structure FuzzyInputs (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Φ : Set (Subgroup G))
    (a : G) : Prop extends CommutingInputs p f Φ a where
  quasi : ∀ (D : LocalLieSystemAt p f Φ a) (j : Fin D.card),
    ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, CFSG.Open.IsQuasisimple ↥R

omit [Finite G] in
theorem FuzzyInputs.of_facts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hno : ∀ D : LocalLieSystemAt p f Φ a, ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    (hF3 : NoComponentOverF3 p f Φ a) (hMFC : ModelFacts.CommutingFundamentalFacts p) :
    FuzzyInputs p f Φ a where
  toCommutingInputs := CommutingInputs.of_facts hp2 hq hno hF3 hMFC
  quasi D j R hR := by
    have h5 : 5 ≤ p ^ D.exp j :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq j).imp id And.right) (hF3 D j)
    have he : D.exp j ≠ 0 := by
      rintro h
      rw [h] at h5
      simp at h5
    have h4 : 4 ≤ Nat.card (GaloisField p (D.exp j)) := by
      rw [GaloisField.card p (D.exp j) he]
      omega
    obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2
      (D.isFundTag j) (D.admissible j) (hno D j).1 (hno D j).2 hR
    exact Components.quasisimple_of_equiv e (isQuasisimple_specialLinearGroup_two h4)

theorem SecData.isQuasisimple_modOdd (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (hquasi : ∀ (j : Fin D.card), ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      CFSG.Open.IsQuasisimple ↥R)
    {K : Subgroup G} (hK : K ∈ Φ) : CFSG.Open.IsQuasisimple ↥(modOdd a K) := by
  have hKm : K ∈ centMembers Φ a := ⟨hK, hs.le K hK⟩
  set Y := centralizingLayer Φ {a} with hY
  have hKY : K ≤ Y := le_centralizingLayer hKm
  have hfam : modOddIn Y K ∈ localFamily Φ a := ⟨K.subgroupOf Y, ⟨K, hKm, hKY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hKR⟩ := D.fundamental _ hfam
  have h1 : modOdd a K = R.map (secComponentHom hs.normalizes D i) := by
    rw [← map_sectionQuotientHom_modOddIn hs.normalizes hKm, hKR]
    exact Subgroup.map_map _ _ _
  rw [h1]
  exact isQuasisimple_map_of_ker_le_center _ (secComponentHom_ker_le_center hs.normalizes D i)
    (hquasi i R hR)

end Inputs

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {J₁ J₂ J₃ : Subgroup G}
  {z₁ z₂ z₃ : G}

theorem AxisTriangle.secToral (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) {a : G}
    (ha : a ∈ triangleAxis z₁ z₂ z₃) (hcard : Nat.card (triangleAxis z₁ z₂ z₃) = 8)
    (hqs : ∀ K ∈ triangleSecFamily J₁ J₂ J₃ a, CFSG.Open.IsQuasisimple ↥(modOdd a K)) :
    SecToral (triangleSecFamily J₁ J₂ J₃ a) a (triangleAxis z₁ z₂ z₃) {z₁, z₂, z₃} := by
  obtain ⟨-, -, hA₁, hA₂, hA₃⟩ := hT.axis_data
  obtain ⟨m₁, m₂, m₃⟩ := hT.isSectionMember_at ha
  obtain ⟨r₁, r₂, r₃⟩ := hT.axisResidual_at ha
  have hs := hT.secData ha
  have hmemΦ : ∀ J ∈ ({J₁, J₂, J₃} : Set (Subgroup G)),
      triangleResidual J a ∈ triangleSecFamily J₁ J₂ J₃ a := fun J hJ =>
    ⟨1, one_mem _, triangleResidual J a, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hJ ⊢
      rcases hJ with rfl | rfl | rfl <;> simp, (conjSub_one _).symm⟩
  have vertex : ∀ (J : Subgroup G) (z : G), J ∈ ({J₁, J₂, J₃} : Set (Subgroup G)) →
      IsSectionMember p f (Subgroup.centralizer ({a} : Set G)) (triangleResidual J a) z →
      triangleAxis z₁ z₂ z₃ ≤ trivialOnQuot J →
      AxisResidual J (Subgroup.zpowers a) (triangleResidual J a) z →
      ∃ K ∈ triangleSecFamily J₁ J₂ J₃ a, K ≤ Subgroup.centralizer ({a} : Set G) ∧
        IsCentralInvolution K z ∧
        ∀ (g : G) (hg : g ∈ Subgroup.centralizer ({a} : Set G)), g ∈ triangleAxis z₁ z₂ z₃ →
          ∀ y ∈ modOdd a K, oddQuotMk a ⟨g, hg⟩ * y = y * oddQuotMk a ⟨g, hg⟩ := by
    intro J z hJ hm hAJ rb
    have hK := hmemΦ J hJ
    refine ⟨triangleResidual J a, hK, hs.le _ hK, hm.isCentralInvolution, ?_⟩
    intro g hg hgA y hy
    exact oddQuotMk_centralizes_of_commutator_mem (hs.le _ hK) hg (hqs _ hK)
      (fun l hl => commutator_mem_oddCoreIn_triangleResidual (hAJ hgA) hg rb hl) y hy
  refine ⟨hT.isElemAbelian, hcard, ha, ?_, rfl, ?_⟩
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact vertex J₁ _ (by simp) m₁ hA₁ r₁
    · exact vertex J₂ _ (by simp) m₂ hA₂ r₂
    · exact vertex J₃ _ (by simp) m₃ hA₃ r₃

end Triangle

section TwoBalance

variable {G : Type} [Group G] [Finite G]

theorem twoBalancedWrt_of_secToral {A : Subgroup G} {S : Set G} (hA : IsElemAbelian 2 A)
    (hloc : ∀ a ∈ A, a ≠ 1 → ∃ Φ : Set (Subgroup G),
      SecToral Φ a A S ∧ ComponentLayersAt Φ A a) : TwoBalancedWrt A := by
  refine twoBalancedWrt_of_quotient_deltaCore_eq_bot hA.1 ?_
  intro a ha ha1 F₀ hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  obtain ⟨Φ, T, hlay⟩ := hloc a ha ha1
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := fun g hg => T.mem_centralizer (hF₀E hg)
  have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => T.sq (hF₀E hg)
  have hF2bar : ∀ g ∈ modOdd a F₀, g * g = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  show deltaCore (modOdd a F₀) = ⊥
  refine deltaCore_eq_bot_of_oddCentralizerFree (pPrimeCore_oddQuot_eq_bot a)
    (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hF2bar ?_
  intro L hL hFn hfaith
  rcases hlay L hL with h | h | hfree
  · obtain ⟨g, hg, hg1, hgc⟩ := T.exists_mem_ne_one_centralizes hF₀E h4 (Or.inl h)
    exact absurd hgc (hfaith g hg hg1)
  · obtain ⟨g, hg, hg1, hgc⟩ := T.exists_mem_ne_one_centralizes hF₀E h4 (Or.inr h)
    exact absurd hgc (hfaith g hg hg1)
  · exact hfree F₀ hF₀E h4 hFn hfaith

end TwoBalance

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {J₁ J₂ J₃ : Subgroup G}
  {z₁ z₂ z₃ : G}

theorem AxisTriangle.card_axis (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) (hne₁₂ : z₁ ≠ z₂)
    (hne₁₃ : z₁ ≠ z₃) (hne₂₃ : z₂ ≠ z₃) (hind : z₁ * z₂ ≠ z₃) :
    Nat.card (triangleAxis z₁ z₂ z₃) = 8 := by
  have c₁ := isCentralInvolution_of_isClassicalMember hT.cls₁
  have c₂ := isCentralInvolution_of_isClassicalMember hT.cls₂
  have c₃ := isCentralInvolution_of_isClassicalMember hT.cls₃
  have hz : ∀ {z w : G}, z * w = w * z → ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers w,
      a * b = b * a := by
    intro z w hzw a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow hzw m n).eq
  have hc : ∀ {z : G}, ∀ k ∈ Subgroup.zpowers z, k * z = z * k := fun {z} k hk =>
    hz (show z * z = z * z from rfl) k hk z (Subgroup.mem_zpowers z)
  have T : ExactTriple (Subgroup.zpowers z₁) (Subgroup.zpowers z₂) (Subgroup.zpowers z₃) z₁ z₂ z₃ :=
    { mem₁ := Subgroup.mem_zpowers z₁
      mem₂ := Subgroup.mem_zpowers z₂
      mem₃ := Subgroup.mem_zpowers z₃
      central₁ := hc
      central₂ := hc
      central₃ := hc
      sq₁ := c₁.sq
      sq₂ := c₂.sq
      sq₃ := c₃.sq
      ne_one₁ := c₁.ne_one
      ne_one₂ := c₂.ne_one
      ne_one₃ := c₃.ne_one
      comm₁₂ := hz hT.comm₁₂
      comm₁₃ := hz hT.comm₁₃
      comm₂₃ := hz hT.comm₂₃
      ne₁₂ := hne₁₂
      ne₁₃ := hne₁₃
      ne₂₃ := hne₂₃ }
  exact T.card_eq_eight hind

theorem AxisTriangle.rankThreeBalance [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hBelow : CITBelowU p f (Nat.card G)) (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃)
    (hne₁₂ : z₁ ≠ z₂) (hne₁₃ : z₁ ≠ z₃) (hne₂₃ : z₂ ≠ z₃) (hind : z₁ * z₂ ≠ z₃)
    (hI : ∀ b ∈ triangleAxis z₁ z₂ z₃, b ≠ 1 →
      FuzzyInputs p f (triangleSecFamily J₁ J₂ J₃ b) b) :
    RankThreeBalance (triangleAxis z₁ z₂ z₃) := by
  have hcard := hT.card_axis hne₁₂ hne₁₃ hne₂₃ hind
  refine ⟨hT.isElemAbelian, hcard, hT.weakBalanced hnab hp2 hq h0 hA1 hBelow, ?_⟩
  refine twoBalancedWrt_of_secToral (S := {z₁, z₂, z₃}) hT.isElemAbelian fun a ha ha1 => ?_
  have hs := hT.secData ha
  have hnc := not_subset_center_of_ne_one hnab ha1
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
  have hqs : ∀ K ∈ triangleSecFamily J₁ J₂ J₃ a, CFSG.Open.IsQuasisimple ↥(modOdd a K) :=
    fun K hK => hs.isQuasisimple_modOdd Dsys ((hI a ha ha1).quasi Dsys) hK
  have T := hT.secToral ha hcard hqs
  exact ⟨_, T, componentLayersAt_sec hp2 hq h0 hBelow hs T hnc (hI a ha ha1).toCommutingInputs⟩

theorem FuzzyTriangle.rankThreeBalance [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hBelow : CITBelowU p f (Nat.card G)) (hT : FuzzyTriangle p f J₁ J₂ J₃ z₁ z₂ z₃)
    (hne₁₂ : z₁ ≠ z₂) (hne₁₃ : z₁ ≠ z₃) (hne₂₃ : z₂ ≠ z₃) (hind : z₁ * z₂ ≠ z₃)
    (hI : ∀ b ∈ triangleAxis z₁ z₂ z₃, b ≠ 1 →
      FuzzyInputs p f (triangleSecFamily J₁ J₂ J₃ b) b) :
    RankThreeBalance (triangleAxis z₁ z₂ z₃) :=
  hT.toAxisTriangle.rankThreeBalance hnab hp2 hq h0 hA1 hBelow hne₁₂ hne₁₃ hne₂₃ hind hI

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
