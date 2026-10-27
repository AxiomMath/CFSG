module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorSocle
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalSU

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.RankThree.PartTwo.Sec4
  CFSG.AGLEmbedding.KFactProofs.G28 CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers
  CFSG.RankThreeCoreUniqueness.Helpers

section Reduction


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem kfact_main_normalizer (hK : Nat.card K = 8)
    (hSU : SUStruct M) {Y : Type} [Group Y] [Finite Y] (Kn : Subgroup Y) [Kn.Normal]
    (e : Kn ≃* adjointGroup .G2 K) (hC : Subgroup.centralizer (Kn : Set Y) = ⊥)
    (T : Sylow 3 Y) (Y₀ : Subgroup Y) (h3 : 3 ≤ Open.pRank 3 (T : Subgroup Y))
    (hweak : GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀) (hne : Y₀ ≠ ⊤) :
    ∃ (zb : Y) (V₀ : Subgroup Y), G28InSitu (T : Subgroup Y) Y₀ zb V₀ ∧
      Subgroup.normalizer ((Subgroup.zpowers zb : Subgroup Y) : Set Y) ≤ Y₀ := by
  set c := actHom Kn e with hcdef
  have hinj : Function.Injective c := actHom_injective Kn e hC
  let cI : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K) := MulAut.conj
  have hcI : Function.Injective cI := conj_injective_X
  have hInn : cI.range ≤ c.range := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(e.symm g : Y), actHom_inner Kn e g⟩
  have hcases : c.range = cI.range ∨ c.range = ⊤ := by
    have h1 : Nat.card cI.range = Nat.card (adjointGroup .G2 K) :=
      Nat.card_range_of_injective hcI
    have h2 : Nat.card cI.range ∣ Nat.card c.range := Subgroup.card_dvd_of_le hInn
    have h3' : Nat.card c.range ∣ Nat.card (MulAut (adjointGroup .G2 K)) :=
      Subgroup.card_subgroup_dvd_card _
    rw [card_aut hK] at h3'
    obtain ⟨m, hm⟩ := h2
    rw [h1] at hm
    have hpos : 0 < Nat.card (adjointGroup .G2 K) := Nat.card_pos
    rw [hm, mul_comm 3] at h3'
    have hm3 : m ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hpos h3'
    have hm' : m = 1 ∨ m = 3 := (Nat.dvd_prime Nat.prime_three).mp hm3
    rcases hm' with rfl | rfl
    · left
      refine (Subgroup.eq_of_le_of_card_ge hInn ?_).symm
      rw [h1, hm, mul_one]
    · right
      apply Subgroup.eq_top_of_card_eq
      rw [hm, card_aut hK, mul_comm]
  rcases hcases with hr | hr
  ·
    exfalso
    obtain ⟨E, hET, hEe, hE27⟩ := exists_elemAbelian_27 h3
    have hEc : E.map c ≤ cI.range := hr ▸ Subgroup.map_le_range c E
    have hmap : ((E.map c).comap cI).map cI = E.map c := Subgroup.map_comap_eq_self hEc
    have hcard : Nat.card ((E.map c).comap cI) = 27 := by
      rw [← Subgroup.card_map_of_injective hcI, hmap, Subgroup.card_map_of_injective hinj, hE27]
    exact no_elemAbelian_27_X M hK
      (isElemAbelian_comap_injective cI hcI
        (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 c E hEe)) hcard
  ·
    have hsurj : Function.Surjective c := MonoidHom.range_eq_top.mp hr
    let Ψ₀ : Y ≃* MulAut (adjointGroup .G2 K) := MulEquiv.ofBijective c ⟨hinj, hsurj⟩
    have hs : Function.Surjective Ψ₀.toMonoidHom := fun x => Ψ₀.surjective x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut (adjointGroup .G2 K))
      (Sylow.mapSurjective hs T) (T0Sylow M hK)
    let Ψ : Y ≃* MulAut (adjointGroup .G2 K) := Ψ₀.trans (MulAut.conj g)
    have hT : (T : Subgroup Y).map Ψ.toMonoidHom = T0 M hK := by
      have h1 := congrArg (fun P : Sylow 3 (MulAut (adjointGroup .G2 K)) =>
        (P : Subgroup (MulAut (adjointGroup .G2 K)))) hg
      simp only [Sylow.coe_subgroup_smul, coe_T0Sylow, Sylow.coe_mapSurjective] at h1
      rw [← h1]
      show Subgroup.map Ψ.toMonoidHom (T : Subgroup Y) =
        Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map Ψ₀.toMonoidHom (T : Subgroup Y))
      rw [Subgroup.map_map]
      rfl
    have hmapsymm : ∀ A : Subgroup (MulAut (adjointGroup .G2 K)),
        (A.map Ψ.symm.toMonoidHom).map Ψ.toMonoidHom = A := fun A => by
      rw [Subgroup.map_map]
      ext x
      simp
    have hmap : ∀ A : Subgroup Y, (A.map Ψ.toMonoidHom).map Ψ.symm.toMonoidHom = A := fun A => by
      rw [Subgroup.map_map]
      ext x
      simp
    have hcore : GLBWeakCore 3 (T0 M hK) ≤ Y₀.map Ψ.toMonoidHom := by
      have h1 := map_glbWeakCore_le Nat.prime_three Ψ.symm.toMonoidHom Ψ.symm.injective
        (T0 M hK)
      rw [show (T0 M hK).map Ψ.symm.toMonoidHom = (T : Subgroup Y) by rw [← hT, hmap]] at h1
      have h2 := Subgroup.map_mono (f := Ψ.toMonoidHom) (h1.trans hweak)
      rwa [hmapsymm] at h2
    have hne' : Y₀.map Ψ.toMonoidHom ≠ ⊤ := by
      intro h
      apply hne
      have := congrArg (Subgroup.map Ψ.symm.toMonoidHom) h
      rwa [hmap, Subgroup.map_top_of_surjective _ Ψ.symm.surjective] at this
    have key := g28InSitu_aut M hK hSU hcore hne'
    have hz : Ψ.toMonoidHom (Ψ.symm (zb M)) = zb M := Ψ.apply_symm_apply _
    refine ⟨Ψ.symm (zb M), (V0 M).map Ψ.symm.toMonoidHom, G28InSitu.of_mulEquiv Ψ ?_, ?_⟩
    · rw [hT, hmapsymm, hz]
      exact key
    ·
      obtain ⟨hPS, -, -⟩ := omega_facts M hK
      have hNA := NA_le M hK hPS hcore
      have himg : (Subgroup.normalizer ((Subgroup.zpowers (Ψ.symm (zb M)) : Subgroup Y) :
          Set Y)).map Ψ.toMonoidHom = NA M := by
        rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulEquiv.apply_symm_apply]
        rfl
      intro y hy
      have h1 : Ψ y ∈ Y₀.map Ψ.toMonoidHom :=
        hNA (himg ▸ Subgroup.mem_map_of_mem Ψ.toMonoidHom hy)
      obtain ⟨y', hy', hyy'⟩ := h1
      exact (Ψ.injective hyy') ▸ hy'

end Reduction

section KFact


theorem kFactG28Local_normalizer (Y : Type) [Group Y] [Finite Y] (Kn : Subgroup Y)
    (d : TauCeti.ValidLieTypeIndex) (hd : IsGTwoEightIndex d) (hKn : Kn.Normal)
    (hKcat : Nonempty (Kn ≃* CatGroup d)) (hC : Subgroup.centralizer (Kn : Set Y) = ⊥)
    (T : Sylow 3 Y) (Y₀ : Subgroup Y) (h3 : 3 ≤ Open.pRank 3 (T : Subgroup Y))
    (hweak : GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀) (hne : Y₀ ≠ ⊤) :
    ∃ (zb : Y) (V₀ : Subgroup Y), G28InSitu (T : Subgroup Y) Y₀ zb V₀ ∧
      Subgroup.normalizer ((Subgroup.zpowers zb : Subgroup Y) : Set Y) ≤ Y₀ := by
  have : Kn.Normal := hKn
  obtain ⟨q, hq2, hq3, hdq⟩ := hd
  obtain ⟨i, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨e₀⟩ := hKcat
  have hmodel : UntwistedChevalleyModel Kn .G2 (q.p ^ q.exponent) :=
    CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq2 e₀
  obtain ⟨F, _, _, hF, ⟨e₁⟩⟩ := hmodel
  rw [hq2, hq3] at hF
  have hF8 : Nat.card F = 8 := by rw [hF]; norm_num
  have : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  obtain ⟨M⟩ := exists_model (K := F) hF8
  have hZF := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := F)
  let eC : AdjointQuotient .G2 F ≃* adjointGroup .G2 F :=
    (QuotientGroup.quotientMulEquivOfEq hZF).trans QuotientGroup.quotientBot
  exact kfact_main_normalizer M hF8 (su_struct M hF8 (suHyp M hF8)) Kn (e₁.trans eC) hC T Y₀ h3
    hweak hne

end KFact

section G28False

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
  {Y₀ : Subgroup Y} {K : Subgroup Y}


theorem g28_false (hSchur : KFactChevTwoSurvivorSchur) (hred : ReducedNongeneration p Y Rb Y₀)
    (hK : IsComponentOf K ⊤) (hKn : K.Normal)
    (hcent : ∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hkl : HasKlingenData p Rb Y₀) (hp3 : p = 3) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsGTwoEightIndex d) (e₁ : K ⧸ Subgroup.center K ≃* CatGroup d) : False := by
  subst hp3
  have hZ : Subgroup.center K = ⊥ :=
    hSchur K 3 d (Or.inr (Or.inr (Or.inl ⟨rfl, hd⟩))) hK.2.2 (isPGroup_center hred hK) ⟨e₁⟩
  have eK : K ≃* CatGroup d :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e₁
  have hC := centralizer_eq_bot hred hKn hcent hZ
  obtain ⟨zb, V₀, hG, hN⟩ := kFactG28Local_normalizer Y K d hd hKn ⟨eK⟩ hC Rb Y₀
    hred.three_le_pRank hred.weakCore_le hred.ne_top
  obtain ⟨E, D, L, hER, hEcard, hEexp, hEZ, hDE, hD, hDcard, hDC, hDN, hLC, hLY₀, e, hSL⟩ := hkl
  have hPY₀ : (Rb : Subgroup Y) ≤ Y₀ :=
    Subgroup.le_normalizer.trans
      ((normalizer_le_weakCore_of_rank 3 Nat.prime_three _ hred.three_le_pRank).trans
        hred.weakCore_le)
  obtain ⟨z, hzD, -, hzc, huniq⟩ := exists_mem_center_of_normalizer_not_le Nat.prime_three
    hred.ne_two Rb hPY₀ hred.weakCore_le hred.three_le_pRank hD hDcard (hDE.trans hER) hDN
  have hzE : z ∈ (Subgroup.center E).map E.subtype := hDC z hzD hzc
  have hzb : zb ∈ Subgroup.zpowers z := huniq zb hG.z_center hG.z_mem hG.z_order
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzb
  apply hLY₀
  intro l hl
  apply hN
  have hlz : Commute l z := (Subgroup.mem_centralizer_iff.mp (hLC hl) z hzE).symm
  have hlzb : Commute l zb := hk ▸ hlz.zpow_right k
  have hcen : l ∈ Subgroup.centralizer ((Subgroup.zpowers zb : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((hlzb.zpow_right m).symm).eq
  exact Subgroup.centralizer_le_normalizer _ hcen

end G28False

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieAux
