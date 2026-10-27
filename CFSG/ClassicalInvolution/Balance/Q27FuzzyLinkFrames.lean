module

public import CFSG.ClassicalInvolution.Balance.Q27FuzzyLinkStab
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyConnCross

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices mem_fuzzyVertices_map)

section Data

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

structure LinkDataFree (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (𝒞 : Set (Subgroup G)) (a : G) where
  sec : SecData p f a (linkFamily p f 𝒞 a)
  D : LocalLieSystemAt p f (linkFamily p f 𝒞 a) a
  D' : LieDecomposition (memberImages (linkFamily p f 𝒞 a) a) (memberJoin (linkFamily p f 𝒞 a) a)
  hD'Q : ∀ i, D'.Q i ∈ Set.range fun j : Fin D.card =>
    ((sectionQuotientHom sec.normalizes).comp (D.hom j)).range

theorem exists_linkDataFree [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hBelow : CITBelowU p f (Nat.card G)) (hinv : ConjInvariant 𝒞)
    {M : Subgroup G} (hM𝒞 : M ∈ 𝒞) (hM : IsClassicalMember p f M a) :
    Nonempty (LinkDataFree p f 𝒞 a) := by
  have hs := secData_linkFamily hinv hM𝒞 hM
  have hnc := not_subset_center_of_ne_one hnab hM.isCentralInvolution.ne_one
  obtain ⟨D⟩ := hs.nonempty_lieSystem hBelow hnc
  obtain ⟨D', hD'Q, -⟩ :=
    hs.lieDecomposition_comp hp2 ModelFacts.modelClauseZero fundamentalWholeA1 hq D
  exact ⟨⟨hs, D, D', hD'Q⟩⟩

end Data

section Cross

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

theorem exists_crossFrame_free (ld : LinkDataFree p f 𝒞 a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hinv : ConjInvariant 𝒞) (hcan : 𝒞 ⊆ canonicalMembers p f G) {M : Subgroup G} (hM𝒞 : M ∈ 𝒞)
    (hM : IsClassicalMember p f M a) {J : Subgroup G} {t : G} (hJ𝒞 : J ∈ 𝒞)
    (hJ : IsClassicalMember p f J t) (haJ : a ∈ trivialOnQuot J) (hta : t ≠ a) {N : Subgroup G}
    {u : G} (hN𝒞 : N ∈ 𝒞) (hN : IsClassicalMember p f N u) (haN : a ∈ trivialOnQuot N)
    (hua : u ≠ a) {j₁ j₂ : Fin ld.D.card} (hj : j₁ ≠ j₂)
    (h₁ : modOdd a (triangleResidual J a) ≤ (secComponentHom ld.sec.normalizes ld.D j₁).range)
    (h₂ : modOdd a (triangleResidual N a) ≤ (secComponentHom ld.sec.normalizes ld.D j₂).range)
    (hclass : ¬ SameClass a t u) :
    ∃ x ∈ involutionOddCore a, ∃ B : Subgroup G, FuzzyFrameOn p f 𝒞 B ∧
      a ∈ fuzzyVertices p f 𝒞 B ∧ t ∈ B ∧ B ≤ trivialOnQuot J ∧ x * u * x⁻¹ ∈ B ∧
      B ≤ trivialOnQuot (conjSub x N) := by
  have hRJ := triangleResidual_mem_linkFamily hJ𝒞 hJ haJ
  have hRN := triangleResidual_mem_linkFamily hN𝒞 hN haN
  obtain ⟨i₁, i₂, hij, hi, hj'⟩ :=
    ld.sec.exists_decomp_indices ld.D ld.D' ld.hD'Q hRJ hRN hj h₁ h₂
  have hMcan : IsCanonical M a := isCanonical_of_mem_canonicalMembers hp2 hq (hcan hM𝒞) hM
  have hJcan := isCanonical_of_mem_canonicalMembers hp2 hq (hcan hJ𝒞) hJ
  have hNcan := isCanonical_of_mem_canonicalMembers hp2 hq (hcan hN𝒞) hN
  have ha2 := (isCentralInvolution_of_isClassicalMember hM).sq
  have hsJ := isSectionMember_triangleResidual hJ ha2 haJ
  have hsN := isSectionMember_triangleResidual hN ha2 haN
  have htC : t ∈ Subgroup.centralizer ({a} : Set G) := hsJ.le hsJ.mem
  have huC : u ∈ Subgroup.centralizer ({a} : Set G) := hsN.le hsN.mem
  have htM := mem_trivialOnQuot_of_linkVertex ld.sec ld.D' hp2 hq hM𝒞 hM hMcan hJ𝒞 hJ haJ hta htC
  have huM := mem_trivialOnQuot_of_linkVertex ld.sec ld.D' hp2 hq hM𝒞 hM hMcan hN𝒞 hN haN hua huC
  have hJN := ld.sec.commutator_mem_oddCore ld.D' hRJ hRN hij hi hj'
  obtain ⟨x, hx, hT, hau, htu, hatu⟩ := exists_axisTriangle_of_residuals_commute_indep hM hJ hN hq
    hJcan hNcan htM huM haJ haN hJN (conj_notMem_of_not_sameClass htC hua hclass)
  obtain ⟨-, -, hA₁, hA₂, hA₃⟩ := hT.axis_data
  have haB : a ∈ triangleAxis a t (x * u * x⁻¹) := Subgroup.subset_closure (by simp)
  have htB : t ∈ triangleAxis a t (x * u * x⁻¹) := Subgroup.subset_closure (by simp)
  have huB : x * u * x⁻¹ ∈ triangleAxis a t (x * u * x⁻¹) := Subgroup.subset_closure (by simp)
  exact ⟨x, hx, triangleAxis a t (x * u * x⁻¹),
    fuzzyFrameOn_of_axisTriangle hT hM𝒞 hJ𝒞 (hinv x N hN𝒞) (Ne.symm hta) hau htu hatu,
    ⟨haB, M, hM𝒞, hM, hA₁⟩, htB, hA₂, huB, hA₃⟩

end Cross

section Frames

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {𝒞 : Set (Subgroup G)} {a : G}

theorem exists_frame_of_cross_free (ld : LinkDataFree p f 𝒞 a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hinv : ConjInvariant 𝒞) (hcan : 𝒞 ⊆ canonicalMembers p f G) {M : Subgroup G} (hM𝒞 : M ∈ 𝒞)
    (hM : IsClassicalMember p f M a) {J : Subgroup G} {t : G} (hJ𝒞 : J ∈ 𝒞)
    (hJ : IsClassicalMember p f J t) (haJ : a ∈ trivialOnQuot J) (hta : t ≠ a) {N : Subgroup G}
    {u : G} (hN𝒞 : N ∈ 𝒞) (hN : IsClassicalMember p f N u) (haN : a ∈ trivialOnQuot N)
    (hua : u ≠ a) {j₁ j₂ : Fin ld.D.card} (hj : j₁ ≠ j₂)
    (h₁ : modOdd a (triangleResidual J a) ≤ (secComponentHom ld.sec.normalizes ld.D j₁).range)
    (h₂ : modOdd a (triangleResidual N a) ≤ (secComponentHom ld.sec.normalizes ld.D j₂).range)
    (hclass : ¬ SameClass a t u) :
    ∃ B : Subgroup G, FuzzyFrameOn p f 𝒞 B ∧ a ∈ fuzzyVertices p f 𝒞 B ∧
      u ∈ fuzzyVertices p f 𝒞 B := by
  obtain ⟨x, hx, B, hB, haB, -, -, hxuB, hBN⟩ :=
    exists_crossFrame_free ld hp2 hq hinv hcan hM𝒞 hM hJ𝒞 hJ haJ hta hN𝒞 hN haN hua hj h₁ h₂ hclass
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [involutionOddCore_eq_oddCoreIn] at hx
    exact oddCoreIn_le _ hx
  refine ⟨B.map (MulAut.conj x⁻¹).toMonoidHom, FuzzyFrameOn.map hinv hB x⁻¹, ?_, ?_⟩
  · have := mem_fuzzyVertices_map hinv haB x⁻¹
    rwa [conj_eq_of_mem_centralizer_singleton (inv_mem hxC)] at this
  · have hv : x * u * x⁻¹ ∈ fuzzyVertices p f 𝒞 B :=
      ⟨hxuB, conjSub x N, hinv x N hN𝒞, hN.conj x, hBN⟩
    have := mem_fuzzyVertices_map hinv hv x⁻¹
    have e : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
    rwa [e] at this

theorem exists_frame_of_comp_free (ld : LinkDataFree p f 𝒞 a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hinv : ConjInvariant 𝒞)
    {A J N : Subgroup G} {t u : G} (hb : FrameBasis p f 𝒞 a A J t N u) {J₀ : Subgroup G} {u₀ : G}
    (hJ₀𝒞 : J₀ ∈ 𝒞) (hJ₀ : IsClassicalMember p f J₀ u₀) (ha₀ : a ∈ trivialOnQuot J₀)
    {j : Fin ld.D.card}
    (hcJ : modOdd a (triangleResidual J a) ≤ (secComponentHom ld.sec.normalizes ld.D j).range)
    (hc₀ : modOdd a (triangleResidual J₀ a) ≤ (secComponentHom ld.sec.normalizes ld.D j).range) :
    ∃ B : Subgroup G, FuzzyFrameOn p f 𝒞 B ∧ a ∈ fuzzyVertices p f 𝒞 B ∧
      u₀ ∈ fuzzyVertices p f 𝒞 B := by
  have ha2 : a * a = 1 := hb.sq hb.aB
  obtain ⟨g, hg, -, hgt⟩ := secData_exists_conj_of_vertices_free ld.sec ld.D hp2 hq j
    hb.linkJ (triangleResidual_mem_linkFamily hJ₀𝒞 hJ₀ ha₀)
    (isSectionMember_triangleResidual hb.clsJ ha2 (hb.tqJ hb.aB)).isCentralInvolution
    (isSectionMember_triangleResidual hJ₀ ha2 ha₀).isCentralInvolution hcJ hc₀
  refine ⟨A.map (MulAut.conj g).toMonoidHom, FuzzyFrameOn.map hinv hb.frame g, ?_, ?_⟩
  · have := mem_fuzzyVertices_map hinv hb.vertex g
    rwa [conj_eq_of_mem_centralizer_singleton hg] at this
  · have hv : t ∈ fuzzyVertices p f 𝒞 A := ⟨hb.tB, J, hb.memJ, hb.clsJ, hb.tqJ⟩
    have := mem_fuzzyVertices_map hinv hv g
    rwa [hgt] at this

theorem frames_link_of_cross_free (ld : LinkDataFree p f 𝒞 a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hinv : ConjInvariant 𝒞) (hcan : 𝒞 ⊆ canonicalMembers p f G)
    (hMFC : ModelFacts.CommutingFundamentalFactsFive p) {A J N : Subgroup G} {t u : G}
    (hb : FrameBasis p f 𝒞 a A J t N u) {A' J' N' : Subgroup G} {t' u' : G}
    (hb' : FrameBasis p f 𝒞 a A' J' t' N' u') {J₃ : Subgroup G} {t₃ : G} (hJ₃𝒞 : J₃ ∈ 𝒞)
    (hJ₃ : IsClassicalMember p f J₃ t₃) (ht₃A' : t₃ ∈ A') (hA'J₃ : A' ≤ trivialOnQuot J₃)
    (ht₃a : t₃ ≠ a) {j j₃ : Fin ld.D.card} (hj : j ≠ j₃)
    (hcJ : modOdd a (triangleResidual J a) ≤ (secComponentHom ld.sec.normalizes ld.D j).range)
    (hc₃ : modOdd a (triangleResidual J₃ a) ≤
      (secComponentHom ld.sec.normalizes ld.D j₃).range)
    (hclass : ¬ SameClass a t t₃) :
    Relation.ReflTransGen (frameLink p f 𝒞 a) A A' := by
  obtain ⟨-, M, hM𝒞, hM, -⟩ := hb.vertex
  obtain ⟨x, hx, B, hB, haB, htB, hBJ, hxuB, hBN⟩ := exists_crossFrame_free ld hp2 hq hinv hcan
    hM𝒞 hM hb.memJ hb.clsJ (hb.tqJ hb.aB) hb.ta hJ₃𝒞 hJ₃ (hA'J₃ hb'.aB) ht₃a hj hcJ hc₃ hclass
  have hx' : x ∈ oddCoreIn (Subgroup.centralizer ({a} : Set G)) := by
    rwa [involutionOddCore_eq_oddCoreIn] at hx
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := oddCoreIn_le _ hx'
  have h1 : Relation.ReflTransGen (frameLink p f 𝒞 a) A B :=
    reflTransGen_frameLink_of_comp_free hinv hp2 hq ld.sec ld.D hMFC hb hB haB j hb.memJ hb.clsJ
      hb.tB hb.tqJ hcJ hb.memJ hb.clsJ htB hBJ hb.ta hcJ
  have hconj : modOdd a (triangleResidual (conjSub x J₃) a) ≤
      (secComponentHom ld.sec.normalizes ld.D j₃).range := by
    rw [triangleResidual_conjSub J₃ hxC, modOdd_conjSub_of_mem_oddCoreIn hx']
    exact hc₃
  have hne : x * t₃ * x⁻¹ ≠ a := by
    intro h
    apply ht₃a
    have := conj_eq_of_mem_centralizer_singleton (inv_mem hxC)
    calc t₃ = x⁻¹ * (x * t₃ * x⁻¹) * x⁻¹⁻¹ := by group
      _ = x⁻¹ * a * x⁻¹⁻¹ := by rw [h]
      _ = a := this
  have h2 : Relation.ReflTransGen (frameLink p f 𝒞 a) A' B :=
    reflTransGen_frameLink_of_comp_free hinv hp2 hq ld.sec ld.D hMFC hb' hB haB j₃ hJ₃𝒞 hJ₃ ht₃A'
      hA'J₃ hc₃ (hinv x J₃ hJ₃𝒞) (hJ₃.conj x) hxuB hBN hne hconj
  exact h1.trans (reflTransGen_frameLink_symm h2)

end Frames

end CFSG.ClassicalInvolution.Balance.Q27
