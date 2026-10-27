module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Glue
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Statements

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}

theorem glueSetting_of_squareCase (hsq : SquareCaseSetting G S H z)
    {J : Subgroup (EscapingQuotient z)} (hJ : CFSG.IsComponent J) (hJH : ¬ J ≤ escapingImage H z)
    (hK : (∀ k ∈ escapingSylowImage S z, k ∈ centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
      (∃ c ∈ center J, (c : EscapingQuotient z) ≠ 1 ∧ (c : EscapingQuotient z) ≠ escapingBar z))
    (hZ : Nat.card (center J) = 2) (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) :
    GlueSetting J (escapingImage H z) (escapingBar z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : EscapingQuotientData H z :=
    escapingQuotientData hsq.core (hsq.core.sylow_le hsq.central.1) hsq.central.2.1 hsq.escape
  have hzJ : escapingBar z ∈ J := hsq.caseTwo J hJ
  have hJ9 : IsTwoANine J := ⟨hJ.1.1, hZ, ⟨e⟩⟩
  have hne : escapingBar z ≠ 1 := fun h => by
    have h2 := hq.bar_order
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hzbar := coe_zbar_eq_of_mem_center hJ9 hzJ hq.bar_mem_center hne
  have hsyl : ∀ P : Subgroup G, P ≤ centralizer ({z} : Set G) → IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((S : Subgroup G) ⊓ centralizer ({z} : Set G) : Subgroup G) := by
    intro P _ hP
    have hSle : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hsq.central.2.2 s hs)
    rw [inf_eq_left.mpr hSle]
    obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
    refine (Subgroup.card_le_of_le hPQ).trans (le_of_eq ?_)
    rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity S]
  obtain ⟨T, hT⟩ := exists_sylow_eq_escapingSylowImage hsyl
  obtain ⟨U, hUH, -⟩ := hq.sylow
  refine ⟨hq.component_normal_of_two_le_pRank hJ (two_le_pRank_of_isTwoANine hJ9), hJ9, hzJ,
    hq.bar_mem_center, hne, hq.oddCore_eq_bot, hJH, ⟨U, hUH⟩, hq.normalizer_le,
    fun hy hy2 hyz hym => hq.mem_image_of_conj_mem hy hy2 hyz hym, ⟨T, fun k hk hkc => ?_⟩⟩
  rw [hT] at hk
  rcases hK with h | ⟨c, hc, hc1, hcz⟩
  · exact h k hk hkc
  · rcases hJ9.mem_center_iff.mp hc with h | h
    · exact absurd (by rw [h]; rfl) hc1
    · exact absurd (by rw [h, hzbar]) hcz

theorem isTwoANine_escapingQuotient_of_squareCase (hsq : SquareCaseSetting G S H z)
    {J : Subgroup (EscapingQuotient z)} (hJ : CFSG.IsComponent J) (hJH : ¬ J ≤ escapingImage H z)
    (hK : (∀ k ∈ escapingSylowImage S z, k ∈ centralizer (J : Set (EscapingQuotient z)) →
        k = 1 ∨ k = escapingBar z) ∨
      (∃ c ∈ center J, (c : EscapingQuotient z) ≠ 1 ∧ (c : EscapingQuotient z) ≠ escapingBar z))
    (hZ : Nat.card (center J) = 2) (e : J ⧸ center J ≃* alternatingGroup (Fin 9)) :
    IsTwoANine (EscapingQuotient z) := by
  have hs := glueSetting_of_squareCase hsq hJ hJH hK hZ e
  exact hs.isTwoANine.of_mulEquiv ((MulEquiv.subgroupCongr hs.eq_top).trans Subgroup.topEquiv)

theorem noTwoANineQuaternionComponent_of_isolated (hT9 : TwoANineCentralizerIsolated) :
    NoTwoANineQuaternionComponent := by
  intro G _ _ S H z hsq J hJ hJH hK hZ ⟨e⟩
  have hM := isTwoANine_escapingQuotient_of_squareCase hsq hJ hJH hK hZ e
  have hwc := hT9 G S z hsq.central hM.perfect hM.card_center hM.nonempty_mulEquiv
  have hzz : z * z = 1 := by
    rw [← sq, ← hsq.central.2.1]
    exact pow_orderOf_eq_one z
  have hiso := CFSG.Adapters.isolated_of_weakClosure S
    (Subgroup.mem_centralizer_iff.mpr hsq.central.2.2) hzz hwc
  obtain ⟨g, hgc, hgne⟩ := exists_conj_commute_ne hsq.core.simple hsq.core.nonabelian
    hsq.central.2.1
  exact hgne (hiso g hgc)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
