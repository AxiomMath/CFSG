module

public import CFSG.ClassicalInvolution.Q3.Q3TPCtx
public import CFSG.ClassicalInvolution.Q3.Q3TCCp
public import CFSG.ClassicalInvolution.Q3.Q3TPSModel
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternB
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.Q3.Q3WAETLocal
public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL diagConj2 pair_normalize
  coe_blockSL_three_zero coe_blockSL_three_one coe_diagConj2)
open CFSG.ClassicalInvolution.Q3.Q3W (localOddThreeFree3_conj)
open CFSG.ClassicalInvolution.Q3.Q3TP (TCtxS3 exists_dictT2_of_member3S)
open CFSG.Open (classicalInvolutionOddCore)
open scoped MatrixGroups

local notation "F₃" => GaloisField 3 1

variable {G : Type} [Group G]


theorem exists_chart3 {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {z z₁ : G}
    {K₁ K₂ : Subgroup G} (hz₁ : IsClassicalMember3 K₁ z₁) (hK₂ : K₂ ≤ locLayer Ω z)
    (hzz : z₁ * z * z₁⁻¹ = z)
    (hpair : ∃ W, LinearBlockStandardPair F₃ W K₁ K₂) :
    ∃ θ : SL(2, F₃) →* locQuot Ω z, θ.range = locImg Ω z K₂ ∧
      ∀ s, Gaps.locAut hΩ hzz (θ s) = θ (diagConj2 (-1) 1 s) := by
  obtain ⟨W, hW⟩ := hpair
  obtain ⟨θ₃, -, hker, hU, hV⟩ := pair_normalize hW
  have h2 : (2 : F₃) ≠ 0 := Ring.two_ne_zero ringChar_galoisField_three_ne_two
  have hz₁mem : z₁ ∈ (blockSL F₃ 3 2 0 (by omega)).range.map θ₃ := by
    have : z₁ ∈ K₁ := hz₁.mem
    rwa [← hU] at this
  have hz₁eq : z₁ = θ₃ (blockSL F₃ 3 2 0 (by omega) (-1)) :=
    Gaps.eq_block_neg_one h2 hker (by omega) hz₁mem hz₁.orderOf_eq_two
  set φ₂ : SL(2, F₃) →* G := θ₃.comp (blockSL F₃ 3 2 1 (by omega)) with hφ₂
  have hφ₂range : φ₂.range = K₂ := by
    rw [hφ₂, MonoidHom.range_comp]
    exact hV
  have hmem : ∀ s, φ₂ s ∈ locLayer Ω z := fun s => hK₂ (hφ₂range ▸ ⟨s, rfl⟩)
  let θ : SL(2, F₃) →* locQuot Ω z :=
    (Gaps.locMk Ω z).comp (φ₂.codRestrict (locLayer Ω z) hmem)
  refine ⟨θ, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨φ₂ s, hmem s⟩, Subgroup.mem_subgroupOf.2 (hφ₂range ▸ ⟨s, rfl⟩), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hw' : (w : G) ∈ φ₂.range := by
        rw [hφ₂range]
        exact Subgroup.mem_subgroupOf.1 hw
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
      RouteD.blockSL_neg_one_conj]

namespace TCtxS3

variable {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G}
  [Finite G] (c : TCtxS3 tY nY Ω K z)

include c

theorem normal_range : c.d.ψ.range.Normal := by
  set Y := locLayer Ω z with hY
  set O := classicalInvolutionOddCore ↥Y with hOdef
  set R := c.d.ψ.range with hR
  have hnormalizer : ∀ L ∈ centralizingMembers Ω {z}, ∀ g ∈ locImg Ω z L,
      g ∈ Subgroup.normalizer (R : Set (locQuot Ω z)) := by
    intro L hL g hg
    have hfam : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
    rcases c.d.fam_cases _ hfam with h | h | ⟨R', hR', hLR⟩
    · apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (c.d.comm₀ g (h hg) r hr).symm
    · apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact (c.d.comm₁ g (h hg) r hr).symm
    · rw [hLR] at hg
      obtain ⟨x, -, rfl⟩ := hg
      exact Subgroup.le_normalizer ⟨x, rfl⟩
  let S : Subgroup ↥Y := (Subgroup.normalizer (R : Set (locQuot Ω z))).comap
    (QuotientGroup.mk' O)
  have hY' : Y ≤ S.map Y.subtype := by
    refine iSup₂_le fun L hL l hl => ?_
    have hlY : l ∈ Y := le_centralizingLayer hL hl
    exact ⟨⟨l, hlY⟩, hnormalizer L hL _ ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩, rfl⟩
  have hall : ∀ g : locQuot Ω z, g ∈ Subgroup.normalizer (R : Set (locQuot Ω z)) := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨s, hs, hsy⟩ := hY' y.2
    have : s = y := Subtype.ext hsy
    rw [← this]
    exact hs
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun g _ => hall g)

theorem exists_ctx_member (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G}
    (hβ : β ∈ Ω) {t : G} (ht : IsClassicalMember3 β t) : Nonempty (TCtxS3 tY nY Ω β t) := by
  obtain ⟨g, hg⟩ := hsingle β hβ
  have htg : t = g * z * g⁻¹ := involution_unique3 ht (hg ▸ c.hz.conj g)
  subst htg
  obtain ⟨d', hQ⟩ := exists_dictT2_of_member3S c.hY hβ ht
    (Q3TC.ShapeDictT2.conj3 c.hΩ.conjInvariant g c.d)
  exact ⟨{
    hΩ := c.hΩ
    hex := c.hex
    hK := hβ
    hz := ht
    hP1 := Gaps.localOddCentral_conj c.hΩ.conjInvariant g z c.hP1
    hO3 := localOddThreeFree3_conj c.hΩ.conjInvariant g z c.hO3
    d := d'
    hQ₀ := hQ
    hY := c.hY }⟩

end TCtxS3

end CFSG.ClassicalInvolution.Q3.Q3TPS
