module

public import CFSG.ClassicalInvolution.Balance.Theorem5Fuzzy
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyLink

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices MemberClass FuzzyAxisExact card_closure_singleton_le_two)
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Canonical

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def canonicalMembers (p f : ℕ) [Fact p.Prime] (G : Type) [Group G] :
    Set (Subgroup G) :=
  {J | ∃ z, IsClassicalMember p f J z ∧ IsCanonical J z}

@[expose] def canonMembers (p f : ℕ) [Fact p.Prime] : MemberClass :=
  fun {H : Type} [Group H] (_ : Subgroup H) => canonicalMembers p f H

theorem mem_canonicalMembers {J : Subgroup G} :
    J ∈ canonicalMembers p f G ↔ ∃ z, IsClassicalMember p f J z ∧ IsCanonical J z :=
  Iff.rfl

end Canonical

section Frames

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem conjInvariant_canonicalMembers : ConjInvariant (canonicalMembers p f G) := by
  rintro n J ⟨z, hJ, hcan⟩
  exact ⟨n * z * n⁻¹, hJ.conj n, hcan.conj n⟩

theorem conjInvariant_canonMembers (K : Subgroup G) : ConjInvariant (canonMembers p f K) :=
  conjInvariant_canonicalMembers

theorem canonMember_mem_canonicalMembers {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) : canonMember J z ∈ canonicalMembers p f G :=
  ⟨z, isClassicalMember_canonMember hJ, isCanonical_canonMember hJ.perfect⟩

theorem fuzzyFrameOn_canonical_of_indepTripleOn {Ω : Set (Subgroup G)} {A : Subgroup G}
    (h : IndepTripleOn p f Ω A) : FuzzyFrameOn p f (canonicalMembers p f G) A := by
  obtain ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩ := h
  refine ⟨fun i => canonMember (K i) (z i), z, fun i => ⟨canonMember_mem_canonicalMembers (hK i).2,
    isClassicalMember_canonMember (hK i).2⟩, hAdef, hel, hcard, fun i a ha => ?_⟩
  have hKA := triple_centralizes hK hcomm i
  rw [hAdef] at ha
  exact mem_trivialOnQuot_canonMember_of_centralizes (hK i).2 fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hKA hx) a ha

theorem fuzzyAxisExact_canonMembers (p f : ℕ) [Fact p.Prime] :
    FuzzyAxisExact p f (canonMembers p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA
  exact fuzzyFrameOn_canonical_of_indepTripleOn hA

theorem fuzzyFrameOn_of_axisTriangle {𝒞 : Set (Subgroup G)} {J₁ J₂ J₃ : Subgroup G}
    {z₁ z₂ z₃ : G} (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) (h₁ : J₁ ∈ 𝒞) (h₂ : J₂ ∈ 𝒞)
    (h₃ : J₃ ∈ 𝒞) (hne₁₂ : z₁ ≠ z₂) (hne₁₃ : z₁ ≠ z₃) (hne₂₃ : z₂ ≠ z₃) (hind : z₁ * z₂ ≠ z₃) :
    FuzzyFrameOn p f 𝒞 (triangleAxis z₁ z₂ z₃) := by
  obtain ⟨-, -, hA₁, hA₂, hA₃⟩ := hT.axis_data
  refine ⟨![J₁, J₂, J₃], ![z₁, z₂, z₃], ?_, ?_, hT.isElemAbelian,
    hT.card_axis hne₁₂ hne₁₃ hne₂₃ hind, ?_⟩
  · intro i
    fin_cases i
    exacts [⟨h₁, hT.cls₁⟩, ⟨h₂, hT.cls₂⟩, ⟨h₃, hT.cls₃⟩]
  · have hrange : Set.range ![z₁, z₂, z₃] = ({z₁, z₂, z₃} : Set G) := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl | rfl)
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
    rw [triangleAxis, hrange]
  · intro i
    fin_cases i
    exacts [hA₁, hA₂, hA₃]

omit [Finite G] in
theorem conjSub_closure_pair_le {a u x : G} {B : Subgroup G}
    (hx : x ∈ Subgroup.centralizer ({a} : Set G)) (ha : a ∈ B) (hu : x * u * x⁻¹ ∈ B) :
    conjSub x (Subgroup.closure ({a, u} : Set G)) ≤ B := by
  rw [conjSub, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro s (rfl | rfl)
  · show x * s * x⁻¹ ∈ B
    rwa [conj_eq_of_mem_centralizer_singleton hx]
  · exact hu

theorem exists_fuzzyFrame_of_residuals_commute {𝒞 : Set (Subgroup G)} (hconj : ConjInvariant 𝒞)
    {M J N : Subgroup G} {a t u : G} (hM𝒞 : M ∈ 𝒞) (hJ𝒞 : J ∈ 𝒞) (hN𝒞 : N ∈ 𝒞)
    (hM : IsClassicalMember p f M a) (hJ : IsClassicalMember p f J t)
    (hN : IsClassicalMember p f N u) (hq : 5 ≤ p ^ f) (hJcan : IsCanonical J t)
    (hNcan : IsCanonical N u) (htM : t ∈ trivialOnQuot M) (huM : u ∈ trivialOnQuot M)
    (haJ : a ∈ trivialOnQuot J) (haN : a ∈ trivialOnQuot N)
    (hJN : ∀ i ∈ triangleResidual J a, ∀ j ∈ triangleResidual N a,
      ⁅i, j⁆ ∈ involutionOddCore a) (hat : a ≠ t)
    (hind : ∀ x ∈ involutionOddCore a, x * u * x⁻¹ ∉ ({a, t, a * t} : Set G)) :
    ∃ x ∈ involutionOddCore a, FuzzyFrameOn p f 𝒞 (triangleAxis a t (x * u * x⁻¹)) ∧
      a ∈ fuzzyVertices p f 𝒞 (triangleAxis a t (x * u * x⁻¹)) ∧
      Subgroup.closure ({a, t} : Set G) ≤ triangleAxis a t (x * u * x⁻¹) ∧
      conjSub x (Subgroup.closure ({a, u} : Set G)) ≤ triangleAxis a t (x * u * x⁻¹) := by
  obtain ⟨x, hx, hT, hau, htu, hatu⟩ := exists_axisTriangle_of_residuals_commute_indep hM hJ hN hq
    hJcan hNcan htM huM haJ haN hJN hind
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [involutionOddCore_eq_oddCoreIn] at hx
    exact oddCoreIn_le _ hx
  have haB : a ∈ triangleAxis a t (x * u * x⁻¹) := Subgroup.subset_closure (by simp)
  have htB : t ∈ triangleAxis a t (x * u * x⁻¹) := Subgroup.subset_closure (by simp)
  have huB : x * u * x⁻¹ ∈ triangleAxis a t (x * u * x⁻¹) := Subgroup.subset_closure (by simp)
  refine ⟨x, hx, fuzzyFrameOn_of_axisTriangle hT hM𝒞 hJ𝒞 (hconj x N hN𝒞) hat hau htu hatu,
    ⟨haB, M, hM𝒞, hM, hT.axis_data.2.2.1⟩, ?_, conjSub_closure_pair_le hxC haB huB⟩
  rw [Subgroup.closure_le]
  rintro s (rfl | rfl)
  · exact haB
  · exact htB

theorem exists_vertex_ne_of_fuzzyFrameOn {𝒞 : Set (Subgroup G)} {A : Subgroup G}
    (h : FuzzyFrameOn p f 𝒞 A) (a : G) :
    ∃ (J : Subgroup G) (t : G), J ∈ 𝒞 ∧ IsClassicalMember p f J t ∧ t ∈ A ∧ t ≠ a ∧
      A ≤ trivialOnQuot J := by
  obtain ⟨J, z, hJ, hAdef, -, hcard, htriv⟩ := h
  by_contra hcon
  push Not at hcon
  have hall : ∀ i, z i = a := fun i => by
    by_contra hne
    exact hcon (J i) (z i) (hJ i).1 (hJ i).2 (hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩) hne
      (htriv i) |>.elim
  have hle : A ≤ Subgroup.closure ({a} : Set G) := by
    rw [hAdef, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [hall i]
    exact Subgroup.subset_closure rfl
  have h2 := card_closure_singleton_le_two (a := a) (by rw [← hall 0]; exact sq_eq_one (hJ 0).2)
  have h8 := Subgroup.card_le_of_le hle
  omega

end Frames

end CFSG.ClassicalInvolution.Balance.Bootstrap
