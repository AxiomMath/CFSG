module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthB
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthD
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakChain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDChain
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem SpLayer.partnerPattern_of_shortNode [Finite G] (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    {z : G} (Λ : SpLayer p f 2 Ω z) {K β K₂ Us : Subgroup G} {t : G} (hK : K ∈ Ω)
    (hz : IsClassicalMember p f K z) (hK₂ : K₂ ∈ Ω) (hKK₂ : Commutes K K₂)
    (hsn : Λ.IsShortNode K₂ Us) (hUs : Us ≤ Subgroup.centralizer ({t} : Set G))
    (hβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W β K₂) :
    PartnerPatternBPair p f 2 Ω K β t := by
  obtain ⟨-, hUsperf, -, hspair, hUsc, -⟩ := hsn
  have hKUs : Commutes K Us := by
    obtain ⟨j, hj, hKj⟩ := Λ.exists_other_of_self hq hK hz
    exact hUsc K ⟨hK, le_centralizer_of_isClassicalMember hz⟩ j hj hKj
  refine ⟨![K₂, Us], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    fin_cases a
    · exact hK₂
    · simp at ha
  · intro a
    fin_cases a
    · exact hKK₂
    · exact hKUs
  · intro a ha
    fin_cases a
    · simp at ha
    · exact ⟨hUsperf, hUs⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab
  · intro a b hab hb
    fin_cases a <;> fin_cases b <;> simp at hab hb
  · intro a b ha hb
    fin_cases a <;> fin_cases b <;> simp at ha hb
    exact hspair
  · intro a ha
    fin_cases a
    · exact hβ
    · simp at ha

theorem SuLayer.partnerPatternMinus_of_shortNode [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {z : G} (Λ : SuLayer p f 2 Ω z)
    {K β K₂ Us : Subgroup G} {t : G} (hK : K ∈ Ω) (hz : IsClassicalMember p f K z) (hK₂ : K₂ ∈ Ω)
    (hKK₂ : Commutes K K₂) (hsn : Λ.IsShortNode (minusCoeffs_irr p f) K₂ Us)
    (hUs : Us ≤ Subgroup.centralizer ({t} : Set G))
    (hβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W β K₂) :
    PartnerPatternMinus p f 3 Ω K β t := by
  obtain ⟨-, hUsperf, -, hspair, hUsc, -⟩ := hsn
  have hKUs : Commutes K Us := by
    obtain ⟨j, hj, hKj⟩ := Λ.exists_other_of_self hp2 hq hK hz
    exact hUsc K ⟨hK, le_centralizer_of_isClassicalMember hz⟩ j hj hKj
  have hK₂perf : ⁅K₂, K₂⁆ = K₂ := by
    obtain ⟨z₂, hz₂⟩ := hΩ.classical K₂ hK₂
    exact commutator_eq_of_isClassicalMember hz₂
  refine ⟨![K₂, Us], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    fin_cases a
    · exact hKK₂
    · exact hKUs
  · intro a
    fin_cases a
    · exact hK₂perf
    · exact hUsperf
  · intro a ha
    fin_cases a
    · exact hK₂
    · simp at ha
  · intro a ha
    fin_cases a
    · simp at ha
    · exact hUs
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab
  · intro a b hab hb
    fin_cases a <;> fin_cases b <;> simp at hab hb
  · intro a b ha hb
    fin_cases a <;> fin_cases b <;> simp at ha hb
    exact hspair
  · intro a ha
    fin_cases a
    · exact hβ
    · simp at ha

theorem routeD_typeB4_pair [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .PSp 2 Ω z)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hpat : PartnerPatternBPair p f 2 Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = 4 := by
  obtain ⟨j, -, hjK, hjpt, -, -, hjsp, hβj0⟩ := hpat
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have h1 : (1 : Fin 2).val ≥ 1 := le_refl 1
  have hβj : Commutes β (j 1) :=
    commutes_partner_of_perfect_conj hp2 hq (Gaps.fundNoncentral p) hS3 hΩ hsingle hz hD4 hP1 hβ ht
      hKβ (hjpt 1 h1).1 (hjpt 1 h1).2 (fun y hy x hx => hjK 1 x hx y hy)
  exact omega9_lieSystem hp2 hq hΩ hconn hK hsingle hz hP1 hshape (hjK 0) (hjK 1) hβj hKβ
    (hβj0 0 rfl) (hjsp 0 1 rfl rfl)

theorem routeD_typeTwistedD5_pair [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hb : SU4SpinMinus p f (minusCoeffs_irr p f)) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω)
    {z : G} (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .PSU 4 Ω z)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hpat : PartnerPatternMinus p f 3 Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaMinus ∧ D.rank i = 5 := by
  obtain ⟨j, hjK, hjperf, -, hjt, -, -, hjtw, hβj⟩ := hpat
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have h0 : (⟨0, by norm_num⟩ : Fin (3 - 1)).val = 0 := rfl
  have hβj1 : Commutes β (j ⟨1, by norm_num⟩) :=
    commutes_partner_of_perfect_conj hp2 hq (Gaps.fundNoncentral p) hS3 hΩ hsingle hz hD4 hP1 hβ ht
      hKβ (hjperf ⟨1, by norm_num⟩) (hjt ⟨1, by norm_num⟩ (le_refl 1))
      (fun y hy x hx => hjK ⟨1, by norm_num⟩ x hx y hy)
  exact minus10_lieSystem hp2 hq hb hg6 hΩ hconn hK hsingle hz hP1 hshape (hjK ⟨0, by norm_num⟩)
    (hjK ⟨1, by norm_num⟩) hβj1 hKβ (hβj ⟨0, by norm_num⟩ rfl)
    (hjtw ⟨0, by norm_num⟩ ⟨1, by norm_num⟩ rfl rfl)

end CFSG.ClassicalInvolution.RouteD

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def PartnerPieceTwinSp2 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSp 2 (conjClass K) z →
      ∃ β ∈ conjClass K, ∃ t : G, IsClassicalMember p f β t ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
        PartnerPatternBPair p f 2 (conjClass K) K β t

@[expose] def PartnerPieceTwinSU4 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSU 4 (conjClass K) z →
      ∃ β ∈ conjClass K, ∃ t : G, IsClassicalMember p f β t ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
        PartnerPatternMinus p f 3 (conjClass K) K β t

theorem pieceTwinSp2_of_partner (h : PartnerPieceTwinSp2 p f) : PieceTwinSp2 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  obtain ⟨β, hβ, t₁, ht₁, hKβ, hpat⟩ := h G hnab K z S hS
  obtain ⟨D, -, -⟩ := routeD_typeB4_pair S.odd S.five S.inClass (mem_conjClass_self K)
    (single_class K) S.conn S.cls hS S.p1 hβ ht₁ hKβ hpat
  exact ⟨D⟩

theorem pieceTwinSU4_of_partner (hb : SU4SpinMinus p f (minusCoeffs_irr p f))
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) (h : PartnerPieceTwinSU4 p f) :
    PieceTwinSU4 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  obtain ⟨β, hβ, t₁, ht₁, hKβ, hpat⟩ := h G hnab K z S hS
  obtain ⟨D, -, -⟩ := routeD_typeTwistedD5_pair S.odd S.five hb hg6 S.inClass
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS S.p1 hβ ht₁ hKβ hpat
  exact ⟨D⟩

end CFSG.ClassicalInvolution.Generic.CoreAssembly
