module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenOneGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenOneFi22
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSevenOneFi22Cent
public import CFSG.HardMathSupport.Solomon.Proving.Fi22Facts
public import CFSG.GroupTheory.ConjKerCenter
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.RankImage
public import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
public import CFSG.GroupTheory.DiagonalTwentySeven
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneKSCenter
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneCenterRankTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFive

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem commute_of_action_eq_conj {X : Type} [Group X] {L E : Subgroup X} {a : E}
    (hEN : E ≤ Subgroup.normalizer (L : Set X)) {t : ↥L}
    (h : L.normalizerMonoidHom (Subgroup.inclusion hEN a) = MulAut.conj t) {x : ↥L}
    (hx : x * t = t * x) : (a : X) * (x : X) = (x : X) * (a : X) := by
  have h1 : (L.normalizerMonoidHom (Subgroup.inclusion hEN a)) x = x := by
    rw [h]
    apply Subtype.ext
    rw [MulAut.conj_apply]
    have hxt : (x : X) * (t : X) = (t : X) * (x : X) := congrArg (fun z : ↥L => (z : X)) hx
    calc (t : X) * (x : X) * (t : X)⁻¹ = ((x : X) * (t : X)) * (t : X)⁻¹ := by rw [hxt]
      _ = (x : X) := by group
  have h2 := congrArg (fun z : ↥L => (z : X)) h1
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
    Subgroup.coe_mul, Subgroup.coe_inv] at h2
  calc (a : X) * (x : X) = ((a : X) * (x : X) * (a : X)⁻¹) * (a : X) := by group
    _ = (x : X) * (a : X) := by rw [h2]

theorem injective_normalizerMonoidHom_inclusion {X : Type} [Group X] {L E Y : Subgroup X}
    (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set X) ≤ Y) (hLY : ¬ L ≤ Y) :
    Function.Injective (L.normalizerMonoidHom.comp (Subgroup.inclusion hEN)) := by
  refine CFSG.GroupTheory.DiagonalTwentySeven.conjAction_injective hEN ?_
  intro s hs hcent
  by_contra hs1
  apply hLY
  intro l hl
  exact hC s hs hs1
    (Subgroup.mem_centralizer_singleton_iff.mpr (hcent l hl).symm)

theorem two_le_pRank_three_inf_of_starImg {G : Type} [Group G] [Finite G]
    {H M : Subgroup G} {p : ℕ}
    (h2 : 2 ≤ CFSG.Open.pRank 3 (starImg p H M)) :
    2 ≤ CFSG.Open.pRank 3 (H ⊓ M) := by
  by_contra hcon
  push Not at hcon
  have h1 : CFSG.Open.pRank 3 (H ⊓ M) ≤ 1 := by omega
  have hY : starImg p H (H ⊓ M) = starImg p H M := by
    unfold starImg
    rw [show (H ⊓ M).subgroupOf H = M.subgroupOf H from ?_]
    ext y
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  rw [← hY] at h2
  have h1' : CFSG.Open.pRank 3 ((H ⊓ M).subgroupOf H) ≤ 1 := by
    rw [CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf 3 inf_le_left]
    exact h1
  have h3 := CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.pRank_map_le_one
    Nat.prime_three (by norm_num)
    (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) h1'
  have h4 : 2 ≤ CFSG.Open.pRank 3 (((H ⊓ M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))) := h2
  omega

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem pCoreOf_two_ne_bot_of_mem_H2Fam (h : NineSettingGen G M p Q H E k)
    (hH2 : H ∈ H2Fam M Q) : pCoreOf 2 H ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hcen : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (bot_le : (⊥ : Subgroup G) ≤ Subgroup.center G)
  have hcl := hH2.2.2.2
  rw [hbot, hcen, inf_top_eq] at hcl
  exact h.not_le (hcl.trans bot_le)

theorem pRank_le_rankThreeLocalRank_of_mem_H2Fam (h : NineSettingGen G M p Q H E k)
    (hH2 : H ∈ H2Fam M Q) {q : ℕ} (hq : 1 < q) :
    CFSG.Open.pRank q H ≤ rankThreeLocalRank q H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTne : CFSG.pCore 2 ↥H ≠ ⊥ := fun hbot =>
    h.pCoreOf_two_ne_bot_of_mem_H2Fam hH2 (by rw [pCoreOf, hbot, Subgroup.map_bot])
  have htop : IsTwoLocal (⊤ : Subgroup ↥H) := by
    refine ⟨CFSG.pCore 2 ↥H, hTne, CFSG.pCore_isPGroup, ?_⟩
    exact (show ⊤ = Subgroup.normalizer ((CFSG.pCore 2 ↥H : Subgroup ↥H) : Set ↥H) from by
      rw [Subgroup.normalizer_eq_top])
  exact (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) H).le.trans
    (local_pRank_le_localRank (G := ↥H) q hq (⊤ : Subgroup ↥H) htop)

end NineSettingGen

section Fi22Certificates


theorem range_normalizerMonoidHom_inclusion_le_inner {X : Type} [Group X] {L E : Subgroup X}
    (hFi : CFSG.AGLEmbedding.IsFi22 ↥L) (hE : CFSG.Open.IsElemAbelian 5 E)
    (hEN : E ≤ Subgroup.normalizer (L : Set X)) :
    (L.normalizerMonoidHom.comp (Subgroup.inclusion hEN)).range ≤
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
  obtain ⟨φ⟩ := hFi
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  let θ : ↥L ≃* CFSG.Blueprint.NativeSporadic.Fi22 := φ.trans β.symm
  rintro _ ⟨a, rfl⟩
  have hpow : a ^ 5 = 1 := by
    apply Subtype.ext
    simpa using hE.2 (a : X) a.2
  have hφ5 : IsPGroup 5 (Subgroup.zpowers
      ((L.normalizerMonoidHom.comp (Subgroup.inclusion hEN)) a)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using
      (orderOf_map_dvd (L.normalizerMonoidHom.comp (Subgroup.inclusion hEN)) a).trans
        (orderOf_dvd_of_pow_eq_one hpow)
  obtain ⟨k, hk⟩ :=
    CFSG.HardMathSupport.Solomon.Proving.fi22_inner_of_isPGroup θ _ hφ5
  exact ⟨k, hk.symm⟩

theorem exists_sylow_five_of_fi22_action {X : Type} [Group X] [Finite X] {L E Y : Subgroup X}
    (hFi : CFSG.AGLEmbedding.IsFi22 ↥L) (hE : CFSG.Open.IsElemAbelian 5 E)
    (hEc : Nat.card E = 5 ^ 2) (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set X) ≤ Y) (hLY : ¬ L ≤ Y) :
    ∃ T : Sylow 5 ↥L, ∀ t ∈ (T : Subgroup ↥L), ∃ a : E,
      L.normalizerMonoidHom (Subgroup.inclusion hEN a) = MulAut.conj t ∧
        (t = 1 ↔ (a : X) = 1) := by
  classical
  have hFi' : CFSG.AGLEmbedding.IsFi22 ↥L := hFi
  obtain ⟨φ⟩ := hFi'
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  let θ : ↥L ≃* CFSG.Blueprint.NativeSporadic.Fi22 := φ.trans β.symm
  have hcardL : Nat.card ↥L = 64561751654400 :=
    (Nat.card_congr θ.toEquiv).trans CFSG.Sporadic.Fi22.card_Fi22
  have hcenter : Subgroup.center ↥L = ⊥ :=
    CFSG.HardMathSupport.Solomon.Proving.fi22_centre_eq_bot θ
  have hconj_inj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hcenter]
  let ψ : E →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  have hψ_inj : Function.Injective ψ := injective_normalizerMonoidHom_inclusion hEN hC hLY
  let A : Subgroup (MulAut ↥L) := ψ.range
  have hAcard : Nat.card A = 5 ^ 2 := by
    have h1 : Nat.card A = Nat.card E :=
      (Nat.card_congr (MonoidHom.ofInjective hψ_inj).toEquiv).symm
    rw [h1, hEc]
  have hAinner : A ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L :=
    range_normalizerMonoidHom_inclusion_le_inner hFi hE hEN
  let T₀ : Subgroup ↥L := A.comap (MulAut.conj : ↥L →* MulAut ↥L)
  have hTcard : Nat.card T₀ = 5 ^ 2 := by
    have h1 : Nat.card (T₀.map (MulAut.conj : ↥L →* MulAut ↥L)) = Nat.card T₀ :=
      Subgroup.card_map_of_injective hconj_inj
    rw [Subgroup.map_comap_eq_self hAinner] at h1
    rw [← h1]
    exact hAcard
  have hSylCard : Nat.card T₀ = 5 ^ (Nat.card ↥L).factorization 5 := by
    rw [hTcard, hcardL, CFSG.AGLEmbeddingD2.factorization_five_fi22]
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let T : Sylow 5 ↥L := Sylow.ofCard T₀ hSylCard
  have hTcoe : (T : Subgroup ↥L) = T₀ := Sylow.coe_ofCard T₀ hSylCard
  refine ⟨T, ?_⟩
  intro t ht
  rw [hTcoe] at ht
  obtain ⟨a, haψ⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp ht)
  refine ⟨a, haψ, ?_⟩
  constructor
  · intro h1
    have h2 : a = 1 := hψ_inj (by rw [haψ, h1, map_one, map_one])
    rw [h2]
    rfl
  · intro h1
    apply hconj_inj
    rw [← haψ]
    have h1' : a = 1 := Subtype.ext h1
    rw [h1', map_one, map_one]

theorem two_le_pRank_three_of_fi22_normalized (hK : KFactFi22CentThreeRank)
    {X : Type} [Group X] [Finite X] {L E Y : Subgroup X}
    (hFi : CFSG.AGLEmbedding.IsFi22 ↥L) (hE : CFSG.Open.IsElemAbelian 5 E)
    (hEc : Nat.card E = 5 ^ 2) (hEN : E ≤ Subgroup.normalizer (L : Set X))
    (hC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set X) ≤ Y) (hLY : ¬ L ≤ Y) :
    2 ≤ CFSG.Open.pRank 3 Y := by
  obtain ⟨T, hT⟩ := exists_sylow_five_of_fi22_action hFi hE hEc hEN hC hLY
  obtain ⟨t, htT, t', ht'T, ht1, ht'1, x, y, hxt, hyt', hxyel, hxycard⟩ := hK ↥L hFi T
  have hxY : (x : X) ∈ Y := by
    obtain ⟨a, haψ, haiff⟩ := hT t htT
    have ha1 : a ≠ 1 := fun h1 => ht1 (haiff.mpr (by rw [h1]; rfl))
    have hcomm : (a : X) * (x : X) = (x : X) * (a : X) :=
      commute_of_action_eq_conj hEN haψ hxt
    exact hC (a : X) a.2 (fun h1 => ha1 (Subtype.ext h1))
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm)
  have hyY : (y : X) ∈ Y := by
    obtain ⟨a, haψ, haiff⟩ := hT t' ht'T
    have ha1 : a ≠ 1 := fun h1 => ht'1 (haiff.mpr (by rw [h1]; rfl))
    have hcomm : (a : X) * (y : X) = (y : X) * (a : X) :=
      commute_of_action_eq_conj hEN haψ hyt'
    exact hC (a : X) a.2 (fun h1 => ha1 (Subtype.ext h1))
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm)
  let B : Subgroup ↥L := Subgroup.closure ({x, y} : Set ↥L)
  have hBY : B ≤ Y.subgroupOf L := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hxY
    · exact hyY
  refine CFSG.SectionRank.le_pRank_of_injective (G := X) (p := 3) (A := B) (H := Y) (k := 2)
    (by norm_num) (fun a b => hxyel.1.is_comm.comm a b)
    (fun a => Subtype.ext (hxyel.2 a a.2)) hxycard (L.subtype.comp B.subtype)
    (L.subtype_injective.comp B.subtype_injective) ?_
  rintro _ ⟨b, rfl⟩
  exact hBY b.2

theorem NineSevenRed.two_le_pRank_three_of_fi22 (hK : KFactFi22CentThreeRank)
    {X : Type} [Group X] [Finite X] {E Y S : Subgroup X} (h : NineSevenRed 5 X E Y S)
    {L : Subgroup X} (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hFi : CFSG.AGLEmbedding.IsFi22 ↥L) : 2 ≤ CFSG.Open.pRank 3 Y := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine two_le_pRank_three_of_fi22_normalized hK hFi h.elem_E h.card_E
    (h.le_normalizer_E hL hLY) ?_ hLY
  intro e he he1
  exact (CFSG.RankThree.PartOne.centralizer_le_of_rankThreeGamma_le (q := 5) (A := E)
    (M := rankThreeGamma 1 5 E) le_rfl he
    (orderOf_eq_prime (h.elem_E.2 e he) he1)).trans h.gamma_le

end Fi22Certificates

section KSCertificates


theorem nineSevenOneGen_of_kFacts (hB5 : KFactThreeSevenTwoGe5)
    (hK : KFactFi22CentThreeRank) : NineSevenOneGen := by
  intro G _ _ M Q H E p h hH2 hp h5
  by_contra hne
  obtain ⟨hp5, L, hLcomp, hLY, hLFi⟩ := h.fi22_of_pCoreOf_ne hB5
    kFactCenterRankFive_holds (kFactCenterRankTwo_holds
        CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
        CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds) hH2 hp h5 hne
  subst hp5
  let S : Subgroup G := pCoreOf 2 (H ⊓ M)
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 (H ⊓ M)
  have hSY : S ≤ H ⊓ M := CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)
  have hSn : H ⊓ M ≤ Subgroup.normalizer (S : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 (H ⊓ M)
  have hred := h.nineSevenRed hH2 hp hS2 hSY hSn
  have h2Y : 2 ≤ CFSG.Open.pRank 3 (starImg 5 H M) :=
    hred.two_le_pRank_three_of_fi22 hK hLcomp hLY hLFi
  have h2inf : 2 ≤ CFSG.Open.pRank 3 (H ⊓ M) := two_le_pRank_three_inf_of_starImg h2Y
  have hcore : pCoreOf 2 H ≠ ⊥ := h.pCoreOf_two_ne_bot_of_mem_H2Fam hH2
  have h3loc : 3 < rankThreeLocalRank 3 H := by
    have hle := h.pRank_le_rankThreeLocalRank_of_mem_H2Fam hH2 (q := 3) (by norm_num)
    have h5rank := five_le_pRank_three_of_fi22 kFactFi22ThreeRank_holds hLFi
    omega
  have hlt : CFSG.Open.pRank 3 (H ⊓ M) < 2 :=
    (h.nineFiveGen hp).2.2 (Or.inl hcore) h3loc
  omega

end KSCertificates

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
