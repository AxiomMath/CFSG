module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Assembly.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Assembly.Hom
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Assembly.KerCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Assembly.Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Assembly.ZpowersOrder
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Generation
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.LocalStatement
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Part1Out
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.StdOfHyp

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

section General

variable {Q G : Type*} [Group Q] [Group G]

theorem le_centralizer_singleton_of_map_center_eq_zpowers {L : Subgroup G} {t : G}
    (ht : (center L).map L.subtype = zpowers t) : L ≤ centralizer ({t} : Set G) := by
  intro l hl
  have htc : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 htc
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨l, hl⟩)

theorem ker_le_ker_of_le_center (Φ : Q →* G) {K : Subgroup Q} (hK : K ≤ center Q)
    {L : Subgroup G} {t : G} (hL : L ≤ centralizer ({t} : Set G))
    (hrange : centralizer ({t} : Set G) ≤ Φ.range)
    (hcent : centralizer (L : Set G) ≤ zpowers t)
    (hcop : Nat.Coprime (orderOf t) (Nat.card K)) : K ≤ Φ.ker := by
  intro k hk
  rw [MonoidHom.mem_ker]
  have hcomm : ∀ y ∈ Φ.range, y * Φ k = Φ k * y := by
    rintro _ ⟨q, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (hK hk) q]
  have hmem : Φ k ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    exact fun l hl => hcomm l (hrange (hL hl))
  have hpow : Φ k ^ Nat.card K = 1 := by
    have h1 : (⟨k, hk⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
    have h2 : k ^ Nat.card K = 1 := congrArg Subtype.val h1
    rw [← map_pow, h2, map_one]
  exact eq_one_of_mem_zpowers_of_pow_eq_one hcop (hcent hmem) hpow

end General

section Pins

variable {G : Type*} [Group G] {E : Subgroup G} {t : G}

theorem centralizer_le_range_of_pins (P : Pins G E t) {Φ : Q3 →* G}
    (hΦ : ∀ x : ↥Ze, Φ x = ((P.ψH.symm x : ↥(centralizer ({t} : Set G))) : G)) :
    centralizer ({t} : Set G) ≤ Φ.range := by
  intro x hx
  refine ⟨((P.ψH ⟨x, hx⟩ : ↥Ze) : Q3), ?_⟩
  rw [hΦ, MulEquiv.symm_apply_apply]

theorem normalizer_le_range_of_pins (P : Pins G E t) {Φ : Q3 →* G}
    (hΦ : ∀ x : ↥Zq, Φ x = ((P.ψN.symm x : ↥(normalizer (E : Set G))) : G)) :
    normalizer (E : Set G) ≤ Φ.range := by
  intro x hx
  refine ⟨((P.ψN ⟨x, hx⟩ : ↥Zq) : Q3), ?_⟩
  rw [hΦ, MulEquiv.symm_apply_apply]

theorem hom_ne_one_of_pins (P : Pins G E t) {Φ : Q3 →* G}
    (hΦ : ∀ x : ↥Ze, Φ x = ((P.ψH.symm x : ↥(centralizer ({t} : Set G))) : G)) :
    Φ ≠ 1 := by
  intro h1
  have hs : s01 ∈ Ze := mem_Ze_iff.2 (Or.inr ⟨s01_smul_x0, s01_smul_x1⟩)
  have h := hΦ ⟨s01, hs⟩
  rw [h1, MonoidHom.one_apply] at h
  have h2 : P.ψH.symm ⟨s01, hs⟩ = 1 := Subtype.ext h.symm
  have h3 : (⟨s01, hs⟩ : ↥Ze) = 1 := (MulEquiv.map_eq_one_iff _).1 h2
  have h4 : s01 = 1 := congrArg Subtype.val h3
  have h5 : s01 • x0 = x0 := by rw [h4, one_smul]
  rw [s01_smul_x0] at h5
  exact x0_ne_x1 h5.symm

end Pins

section Classes

theorem exists_mem_conj_or_exists_mem_conj_of_mulEquiv_fi24J
    {G : Type} [Group G] (M : Subgroup G)
    (θ : ↥M ≃* CFSG.Sporadic.Fi24.J) {t z : G} (htM : t ∈ M) (hzM : z ∈ M)
    (ht : orderOf t = 2) (hz : orderOf z = 2) (hnc : ¬ IsConj t z) :
    ∀ a ∈ M, orderOf a = 2 →
      (∃ m ∈ M, m * t * m⁻¹ = a) ∨ (∃ m ∈ M, m * z * m⁻¹ = a) :=
  @exists_mem_conj_or_exists_mem_conj_of_mulEquiv G CFSG.Sporadic.Fi24.J _ inferInstance M θ _ _
    (fun _ ha ha1 => CFSG.Sporadic.Fi24.isConj_tJ_or_r2 CFSG.Fischer.polarFacts
      CFSG.Sporadic.Fi23.d1_mem_localClass CFSG.Sporadic.Fi23.involution_cover ha ha1)
    t z htM hzM ht hz hnc

end Classes

theorem fi24RecognitionLocal_of_pins
    (hSch : Fi24Branch.CatalogOuterSolvable) (hB : Fi24Branch.DS81Lemma210Strong)
    (hF : Fi24Branch.FiniteFacts)
    (hpins : ∀ {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G},
      Fi24Branch.Std G L E t → L.relIndex (centralizer ({t} : Set G)) = 2 →
      Nonempty (Pins G E t)) :
    Fi24RecognitionLocal := by
  intro G _ _ L hL hc hq t ht hr E hE hM
  have h : Fi24Branch.Std G L E t := Fi24Branch.Std.of_hyp hL hc hq ht hr hE hM
  obtain ⟨P⟩ := hpins h hr
  obtain ⟨Φ, hΦN, hΦH⟩ := exists_hom_of_pins P
  obtain ⟨z, R, hz, hz2, hnc, htR, hRN, hNR, -⟩ := part1_out hSch hB hF h
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_center hc ht
  have hCt : centralizer ({t} : Set G) ≤ Φ.range := centralizer_le_range_of_pins P hΦH
  have hNE : normalizer (E : Set G) ≤ Φ.range := normalizer_le_range_of_pins P hΦN
  have hKc : toGQ.ker ≤ center Q3 :=
    ker_le_center_of_card_ker_eq_three toGQ (toG_surjective m0_eq) isSimpleGroup_G
      (by rw [card_G]; norm_num) card_ker_toG
  have hker : toGQ.ker ≤ Φ.ker :=
    ker_le_ker_of_le_center Φ hKc (le_centralizer_singleton_of_map_center_eq_zpowers ht) hCt
      h.cent.le (by rw [ht2, card_ker_toG]; decide)
  obtain ⟨e, -⟩ := exists_mulEquiv_range_of_ker_le toGQ (toG_surjective m0_eq) isSimpleGroup_G
    Φ hker (hom_ne_one_of_pins P hΦH)
  obtain ⟨eN⟩ := nonempty_native_equiv
  have htM : t ∈ Φ.range := hCt (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hzM : z ∈ Φ.range := hNE (Subgroup.le_normalizer hz.1)
  let θ : ↥Φ.range ≃* CFSG.Sporadic.Fi24.J :=
    e.symm.trans (eN.symm.trans CFSG.Sporadic.Fi24.fi24EquivJ)
  have hcls := exists_mem_conj_or_exists_mem_conj_of_mulEquiv_fi24J Φ.range θ htM hzM ht2 hz2 hnc
  have htop : Φ.range = ⊤ :=
    eq_top_of_le_normalizer h.std.simple Φ.range R ht2 hz2 hnc hCt hcls (hRN.trans hNE) htR hNR.ge
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans
    (e.symm.trans eN.symm))⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
