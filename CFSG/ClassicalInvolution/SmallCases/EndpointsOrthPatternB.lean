module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternSpNode
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthRows

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL diagConj2 pair_normalize
  coe_blockSL_three_zero coe_blockSL_three_one coe_diagConj2)
open scoped MatrixGroups

theorem blockSL_neg_one_conj {F : Type} [Field F] (s : SL(2, F)) :
    blockSL F 3 2 0 (by omega) (-1) * blockSL F 3 2 1 (by omega) s *
        (blockSL F 3 2 0 (by omega) (-1))⁻¹ =
      blockSL F 3 2 1 (by omega) (diagConj2 (-1) 1 s) := by
  have hinv : (blockSL F 3 2 0 (by omega) (-1))⁻¹ = blockSL F 3 2 0 (by omega) (-1) := by
    rw [← map_inv]
    congr 1
    exact inv_eq_of_mul_eq_one_right (by ext; simp)
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL_three_zero, coe_blockSL_three_one,
      coe_diagConj2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_chart_of_standardPair (hp2 : p ≠ 2) {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {z z₁ : G} {K₁ K₂ : Subgroup G} (hz₁ : IsClassicalMember p f K₁ z₁)
    (hK₂ : K₂ ≤ locLayer Ω z) (hzz : z₁ * z * z₁⁻¹ = z)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) :
    ∃ θ : SL(2, GaloisField p f) →* locQuot Ω z, θ.range = locImg Ω z K₂ ∧
      ∀ s, Gaps.locAut hΩ hzz (θ s) = θ (diagConj2 (-1) 1 s) := by
  obtain ⟨W, hW⟩ := hpair
  obtain ⟨θ₃, -, hker, hU, hV⟩ := pair_normalize hW
  have hf : ringChar (GaloisField p f) = p := ringChar.eq (GaloisField p f) p
  have h2 : (2 : GaloisField p f) ≠ 0 := Ring.two_ne_zero (by rw [hf]; exact hp2)
  have hz₁mem : z₁ ∈ (blockSL (GaloisField p f) 3 2 0 (by omega)).range.map θ₃ := by
    have : z₁ ∈ K₁ := hz₁.mem
    rwa [← hU] at this
  have hz₁eq : z₁ = θ₃ (blockSL (GaloisField p f) 3 2 0 (by omega) (-1)) :=
    Gaps.eq_block_neg_one h2 hker (by omega) hz₁mem hz₁.orderOf_eq_two
  set φ₂ : SL(2, GaloisField p f) →* G :=
    θ₃.comp (blockSL (GaloisField p f) 3 2 1 (by omega)) with hφ₂
  have hφ₂range : φ₂.range = K₂ := by
    rw [hφ₂, MonoidHom.range_comp]
    exact hV
  have hmem : ∀ s, φ₂ s ∈ locLayer Ω z := fun s => hK₂ (hφ₂range ▸ ⟨s, rfl⟩)
  let θ : SL(2, GaloisField p f) →* locQuot Ω z :=
    (Gaps.locMk Ω z).comp (φ₂.codRestrict (locLayer Ω z) hmem)
  refine ⟨θ, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨φ₂ s, hmem s⟩, Subgroup.mem_subgroupOf.2 (hφ₂range ▸ ⟨s, rfl⟩), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : (w : G) ∈ φ₂.range := by rw [hφ₂range]; exact Subgroup.mem_subgroupOf.1 hw
      obtain ⟨s, hs⟩ := hw'
      exact ⟨s, by
        show Gaps.locMk Ω z ⟨φ₂ s, hmem s⟩ = Gaps.locMk Ω z w
        congr 1
        exact Subtype.ext hs⟩
  · intro s
    show Gaps.locAut hΩ hzz (Gaps.locMk Ω z ⟨φ₂ s, hmem s⟩) =
      Gaps.locMk Ω z ⟨φ₂ (diagConj2 (-1) 1 s), hmem _⟩
    rw [Gaps.locAut_mk]
    congr 1
    apply Subtype.ext
    show z₁ * φ₂ s * z₁⁻¹ = φ₂ (diagConj2 (-1) 1 s)
    rw [hz₁eq, hφ₂, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul,
      blockSL_neg_one_conj]

theorem exists_shortNode_of_standardPair [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x t : G} (hP1 : LocalOddCentral Ω {x}) {a : ℕ}
    (Λ : SpLayer p f a Ω x) {K₁ K₂ : Subgroup G} (hz₁ : IsClassicalMember p f K₁ t)
    (ht : t * x * t⁻¹ = x) (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hK₂ : K₂ ∈ centralizingMembers Ω {x}) (hK₂i : locImg Ω x K₂ ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ Us : Subgroup G, Λ.IsShortNode K₂ Us ∧ Us ≤ Subgroup.centralizer ({t} : Set G) := by
  have ht2 : t * t = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one t
    rwa [hz₁.orderOf_eq_two] at this
  obtain ⟨θ, hθr, hθτ⟩ := exists_chart_of_standardPair hp2 hΩ.conjInvariant hz₁
    (le_centralizingLayer hK₂) ht p12
  exact Λ.exists_shortNode_centralizer hp2 hq hΩ hP1 ht ht2 hK₂ hK₂i θ hθr hθτ

theorem omega9_shortNode [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {z₀ z₁ : G} (hP1 : LocalOddCentral Ω {z₀}) {a : ℕ}
    (Λ : SpLayer p f a Ω z₀) {K₀ K₁ K₂ : Subgroup G} (hz₀ : IsClassicalMember p f K₀ z₀)
    (hz₁ : IsClassicalMember p f K₁ z₁)
    (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hK₂ : K₂ ∈ centralizingMembers Ω {z₀})
    (hK₂i : locImg Ω z₀ K₂ ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ Us : Subgroup G, Λ.IsShortNode K₂ Us ∧ Us ≤ Subgroup.centralizer ({z₁} : Set G) :=
  exists_shortNode_of_standardPair hp2 hq hΩ hP1 Λ hz₁ (partner_involution_commutes hp2 hz₀ hz₁ p01)
    p12 hK₂ hK₂i

theorem partnerPatternBPair_two [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {z₀ z₁ : G} (hP1 : LocalOddCentral Ω {z₀}) (Λ : SpLayer p f 2 Ω z₀)
    {K₀ K₁ K₂ : Subgroup G} (hK₀ : K₀ ∈ Ω) (hK₂ : K₂ ∈ Ω) (hz₀ : IsClassicalMember p f K₀ z₀)
    (hz₁ : IsClassicalMember p f K₁ z₁) (c02 : Commutes K₀ K₂)
    (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hK₂i : locImg Ω z₀ K₂ ≤ (Λ.D.hom Λ.i₁).range) :
    PartnerPatternBPair p f 2 Ω K₀ K₁ z₁ := by
  obtain ⟨Us, hsn, hUs⟩ := omega9_shortNode hp2 hq hΩ hP1 Λ hz₀ hz₁ p01 p12
    (mem_centralizingMembers_of_commutes hK₂ hz₀.mem c02.symm) hK₂i
  exact Λ.partnerPattern_of_shortNode hq hK₀ hz₀ hK₂ c02 hsn hUs p12

theorem smallEndpoint_omega9_toral [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hconn : DeltaConnected Ω)
    {K₀ K₁ K₂ : Subgroup G} (hK₀ : K₀ ∈ Ω) (hK₁ : K₁ ∈ Ω) (hK₂ : K₂ ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K₀) {z₀ z₁ : G}
    (hz₀ : IsClassicalMember p f K₀ z₀) (hz₁ : IsClassicalMember p f K₁ z₁)
    (hP1 : LocalOddCentral Ω {z₀}) (Λ : SpLayer p f 2 Ω z₀) (c02 : Commutes K₀ K₂)
    (p01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₀ K₁)
    (p12 : ∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂)
    (hK₂i : locImg Ω z₀ K₂ ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ Ψ : spinGroup (Spin.quadOdd 4 (GaloisField p f)) →* G, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G ∧
      CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) .POmegaOdd 4 p f :=
  smallEndpoint_omega9 hp2 hq hΩ hconn hK₀ hK₁ hsingle hz₀ hz₁ hP1 Λ c02 p01 p12
    (omega9_shortNode hp2 hq hΩ hP1 Λ hz₀ hz₁ p01 p12
      (mem_centralizingMembers_of_commutes hK₂ hz₀.mem c02.symm) hK₂i)

end CFSG.ClassicalInvolution.RouteD
