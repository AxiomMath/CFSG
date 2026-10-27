module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyFrames

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5 (FuzzyFrameOn FuzzyAxisExact MemberClass)
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf)

section Class

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem canonMember_conj (g : G) (J : Subgroup G) (z : G) :
    conjSub g (canonMember J z) = canonMember (conjSub g J) (g * z * g⁻¹) := by
  unfold canonMember
  have e : conjSub g J ⊔ conjSub g (involutionOddCore z) = conjSub g (J ⊔ involutionOddCore z) :=
    (Subgroup.map_sup _ _ _).symm
  rw [involutionOddCore_conj, e, perfectResidualOf_conjSub]

@[expose] def canonClass (p f : ℕ) [Fact p.Prime] : MemberClass :=
  fun {H : Type} [Group H] (K : Subgroup H) =>
    {J | ∃ M ∈ CoreAssembly.conjClass K, ∃ z, IsClassicalMember p f M z ∧ J = canonMember M z}

omit [Finite G] in
theorem canonMember_mem_canonClass {K M : Subgroup G} {z : G} (hM : M ∈ CoreAssembly.conjClass K)
    (hz : IsClassicalMember p f M z) : canonMember M z ∈ canonClass p f K :=
  ⟨M, hM, z, hz, rfl⟩

theorem canonClass_subset (K : Subgroup G) : canonClass p f K ⊆ canonicalMembers p f G := by
  rintro _ ⟨M, -, z, hz, rfl⟩
  exact canonMember_mem_canonicalMembers hz

theorem conjInvariant_canonClass (K : Subgroup G) : ConjInvariant (canonClass p f K) := by
  rintro n _ ⟨M, ⟨g, rfl⟩, z, hz, rfl⟩
  exact ⟨conjSub n (conjSub g K), ⟨n * g, conjSub_mul n g K⟩, n * z * n⁻¹, hz.conj n,
    canonMember_conj n _ z⟩

theorem fuzzyFrameOn_canonClass_of_indepTripleOn {K : Subgroup G} {A : Subgroup G}
    (h : IndepTripleOn p f (CoreAssembly.conjClass K) A) :
    FuzzyFrameOn p f (canonClass p f K) A := by
  obtain ⟨M, z, hM, hcomm, hAdef, hel, hcard⟩ := h
  refine ⟨fun i => canonMember (M i) (z i), z, fun i => ⟨canonMember_mem_canonClass (hM i).1
    (hM i).2, isClassicalMember_canonMember (hM i).2⟩, hAdef, hel, hcard, fun i a ha => ?_⟩
  have hMA := triple_centralizes hM hcomm i
  rw [hAdef] at ha
  exact mem_trivialOnQuot_canonMember_of_centralizes (hM i).2 fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hMA hx) a ha

theorem fuzzyAxisExact_canonClass (p f : ℕ) [Fact p.Prime] :
    FuzzyAxisExact p f (canonClass p f) := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn A hA
  exact fuzzyFrameOn_canonClass_of_indepTripleOn hA

end Class

end CFSG.ClassicalInvolution.Balance.Bootstrap
