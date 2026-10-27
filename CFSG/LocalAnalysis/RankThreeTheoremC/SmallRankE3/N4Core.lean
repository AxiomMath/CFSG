module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4KGPre
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGFiveMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStep1
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStep4
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGZJ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613BMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Base
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5Large

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

variable {G : Type} [Group G] [Finite G]

theorem n4_pRank_centralizer_le {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hS : Setting G) (hsit : SmallRankSituation G p P M) {x : G} (hx : SmallRankPoint P M x) :
    Open.pRank p (centralizer ({x} : Set G)) ≤ 2 := by
  have hPM := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  by_contra h
  push Not at h
  exact hsit.largeObstruction_empty x
    ⟨hPM hx.mem, hx.ne_one, hx.pow_eq_one, by omega, hx.not_centralizer_le⟩

theorem n4_x_not_mem_zpowers {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Setting G)
    (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) : x ∉ zpowers z := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  intro hxz
  have hc := hpl.card_eq
  rw [sup_eq_right.mpr (zpowers_le.mpr hxz), Nat.card_zpowers] at hc
  have hzord : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hz.pow_eq_one
  have hle := Nat.le_of_dvd hprime.pos hzord
  have : p ^ 2 ≤ p := hc ▸ hle
  nlinarith [hprime.two_le]

theorem n4_pRank_centralizer_le_of_mem_plane {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hS : Setting G) (hsit : SmallRankSituation G p P M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {y : G}
    (hyB : y ∈ zpowers x ⊔ zpowers z) (hyZ : y ∉ zpowers z) :
    Open.pRank p (centralizer ({y} : Set G)) ≤ 2 := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  obtain ⟨g, -, hconj⟩ := exists_mem_normalizer_conj_zpowers hS hsit hx hz hyB hyZ
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hC : centralizer ({y} : Set G) =
      (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
    calc centralizer ({y} : Set G)
        = centralizer ((zpowers y : Subgroup G) : Set G) := hcz _
      _ = centralizer (((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
        rw [hconj]
      _ = (centralizer ((zpowers x : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
        (centralizer_map_automorphism _ _).symm
      _ = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by rw [hcz x]
  rw [hC, pRank_map_automorphism p hprime.one_lt]
  exact n4_pRank_centralizer_le hS hsit hx

theorem n4_mem_zpowers_of_conj_mem_plane {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hS : Setting G) (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {g : G} (hg : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z) :
    g * z * g⁻¹ ∈ zpowers z := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  by_contra hgz
  have h2 := n4_pRank_centralizer_le_of_mem_plane hS hsit hx hz hg hgz
  have hPz' : (P : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({g * z * g⁻¹} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hqz : q * z = z * q := mem_centralizer_iff.mp hz.centralizes q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * q * g⁻¹ * (g * z * g⁻¹) = g * (q * z) * g⁻¹ := by group
      _ = g * (z * q) * g⁻¹ := by rw [hqz]
      _ = g * z * g⁻¹ * (g * q * g⁻¹) := by group
  have h4 := CFSG.SectionRank.pRank_mono hprime.one_lt hPz'
  rw [pRank_map_automorphism p hprime.one_lt] at h4
  have := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).2
  omega

theorem n4_exists_elemAbelian_cube_of_sylow {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hS : Setting G) (hsit : SmallRankSituation G p P M) (R : Sylow p G) :
    ∃ A : Subgroup G, A ≤ (R : Subgroup G) ∧ CFSG.IsElementaryAbelian p A ∧
      Nat.card A = p ^ 3 := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).2
  have h3 : 3 ≤ Open.pRank p (R : Subgroup G) := by
    rw [(CFSG.SectionRank.pRank_sylow R).1, ← (CFSG.SectionRank.pRank_sylow P).1]
    omega
  obtain ⟨E, hER, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hprime.one_lt (R : Subgroup G)
  have hdvd : p ^ 3 ∣ Nat.card E := hEc ▸ pow_dvd_pow p h3
  obtain ⟨A, hAc, -, hAE⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le hprime (H := ⊥) (L := E) (by simp) hdvd bot_le
  exact ⟨A, hAE.trans hER,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).2
      (CFSG.Open.IsElemAbelian.mono hE hAE), hAc⟩

theorem n4_x_not_mem_frattini {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Setting G)
    (hsit : SmallRankSituation G p P M) {x : G} (hx : SmallRankPoint P M x) {Q : Subgroup G}
    (hQ : IsPGroup p Q) : x ∉ (frattini ↥Q).map Q.subtype := by
  classical
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  rintro ⟨q, hqfr, hqx⟩
  obtain ⟨R, hQR⟩ := hQ.exists_le_sylow
  have hxR : x ∈ (R : Subgroup G) := hQR (hqx ▸ q.2)
  obtain ⟨A, hAR, hAe, hAc⟩ := n4_exists_elemAbelian_cube_of_sylow hS hsit R
  set e := (Subgroup.subgroupOfEquivOfLe hQR).symm with he
  have hxQ : ∃ h : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ∈ Q.subgroupOf (R : Subgroup G),
      (⟨⟨x, hxR⟩, h⟩ : ↥(Q.subgroupOf (R : Subgroup G))) ∈
        frattini ↥(Q.subgroupOf (R : Subgroup G)) := by
    have h1 : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ∈ Q.subgroupOf (R : Subgroup G) :=
      show x ∈ Q from hqx ▸ q.2
    refine ⟨h1, ?_⟩
    have h2 : e q ∈ frattini ↥(Q.subgroupOf (R : Subgroup G)) :=
      Subgroup.mem_comap.mp (frattini_le_comap_frattini_of_surjective (φ := e.toMonoidHom)
        e.surjective (SetLike.mem_coe.mp hqfr))
    have h3 : e q = ⟨⟨x, hxR⟩, h1⟩ := Subtype.ext (Subtype.ext hqx)
    rwa [h3] at h2
  have hA' : CFSG.IsElementaryAbelian p ↥(A.subgroupOf (R : Subgroup G)) :=
    CFSG.IsElementaryAbelian.subgroupOf hAR
  have hAc' : Nat.card ↥(A.subgroupOf (R : Subgroup G)) = p ^ 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans hAc
  have hxp : (⟨x, hxR⟩ : ↥(R : Subgroup G)) ^ p = 1 := Subtype.ext hx.pow_eq_one
  obtain ⟨E, hEC, hEe, hE3⟩ := exists_centralizer_rank_three_of_mem_frattini hp2
    R.isPGroup' hxp hxQ hA' hAc'
  have hE : IsElemAbelian p (E.map (R : Subgroup G).subtype) := by
    have h := CFSG.IsElementaryAbelian.map_subtype (p := p) (K := (R : Subgroup G)) (H := E)
    exact ⟨h.toIsMulCommutative, fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
  have hEC' : E.map (R : Subgroup G).subtype ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (hEC he)
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)
  have hEp : IsPGroup p (E.map (R : Subgroup G).subtype) :=
    fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  have hn2 : n ≤ 2 := (CFSG.SectionRank.le_pRank hprime.one_lt hEC' hE hn).trans
    (n4_pRank_centralizer_le hS hsit hx)
  have hcard : p ^ 3 ≤ Nat.card (E.map (R : Subgroup G).subtype) := by
    rw [card_map_of_injective (R : Subgroup G).subtype_injective]
    exact hE3
  rw [hn] at hcard
  have := (Nat.pow_le_pow_iff_right hprime.one_lt).mp hcard
  omega

theorem n4_core_lt {p : ℕ} {M : Subgroup G} {x z : G} {H S : Subgroup G}
    (hopt : Fail614OptimalGen p M x z H S) : pCoreOf 2 H < S := by
  refine lt_of_le_of_ne hopt.core_le fun h => ?_
  have hS1 : S ≠ ⊥ := hopt.ext.pair.ne_bot
  have hchar : (S.subgroupOf S).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hN := hopt.char_le S le_rfl hS1 hchar
  have hH : H ≤ M :=
    calc H = normalizer (pCoreOf 2 H : Set G) := hopt.eq_normalizer
      _ = normalizer (S : Set G) := by rw [h]
      _ ≤ M := hN
  exact hopt.ext.pair.not_le hH

theorem n4_isPGroup_two_primeCore {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Setting G)
    (hsit : SmallRankSituation G p P M) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {H S : Subgroup G} (hopt : Fail614OptimalGen p M x z H S)
    (hO : rankThreePrimeCore p H ≤ M)
    (h65 : ∀ F : Subgroup G, F ≠ ⊥ → F ≤ rankThreePrimeCore p H → Odd (Nat.card F) →
      zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M) :
    IsPGroup 2 (rankThreePrimeCore p H) := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  obtain ⟨f, hf, hfdvd, hf2⟩ : ∃ f : ℕ, f.Prime ∧ f ∣ Nat.card (rankThreePrimeCore p H) ∧ f ≠ 2 := by
    by_contra hcon
    push Not at hcon
    apply hnot
    rw [IsPGroup.iff_card]
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdn => hcon d hd hdn)⟩
  haveI : Fact f.Prime := ⟨hf⟩
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hHO : H ≤ normalizer (rankThreePrimeCore p H : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H
  have hOp : ¬ p ∣ Nat.card (rankThreePrimeCore p H) :=
    (Nat.Prime.coprime_iff_not_dvd hprime).mp (CFSG.AGLEmbedding.glbPrimeCore_coprime p H)
  have hbotf : IsPGroup f (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hBbot : zpowers x ⊔ zpowers z ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨F, hFsyl, -, hBF⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hprime hf
    hB3 hOp (hBH.trans hHO) bot_le hbotf hBbot
  have hF1 : F ≠ ⊥ := by
    obtain ⟨P2, hP2⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hFsyl
    intro hF
    have h1 := P2.not_dvd_index
    have hP2bot : (P2 : Subgroup ↥(rankThreePrimeCore p H)) = ⊥ := by
      rw [hF] at hP2
      exact (Subgroup.map_eq_bot_iff_of_injective _
        (rankThreePrimeCore p H).subtype_injective).mp hP2
    rw [hP2bot, Subgroup.index_bot] at h1
    exact h1 hfdvd
  have hodd : Odd (Nat.card F) := by
    obtain ⟨k, hk⟩ := hFsyl.2.1.exists_card_eq
    rw [hk]
    exact Odd.pow (hf.odd_of_ne_two hf2)
  have hN := h65 F hF1 hFsyl.1 hodd hBF
  exact hopt.ext.pair.not_le (p65_le_of_normalizer_le hprime hf hOp hHO hO hFsyl hN)

theorem n4_exists_kgData3Pre (hKF : KFact64iiL) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hS : Setting G) (hsit : SmallRankSituation G p P M) (hp5 : 5 ≤ p) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H S : Subgroup G}
    (hopt : Fail614OptimalGen p M x z H S) (hO : rankThreePrimeCore p H ≤ M)
    (hΩ : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z)
    (h2 : IsPGroup 2 (rankThreePrimeCore p H)) :
    ∃ L : Subgroup G,
      KGData3Pre p H (rankThreePrimeCore p H) S (zpowers x ⊔ zpowers z) L M z := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hHtop : H ≠ ⊤ := n4_isTwoLocal_ne_top hS hopt.ext.pair.isTwoLocal
  have hcat : ∀ X : Subgroup G, X ≤ H → CFSG.AGLEmbedding.CatalogSimpleSections ↥X := fun X hXH =>
    CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper X
      (fun h => hHtop (top_le_iff.mp (h ▸ hXH)))
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp (hcat H le_rfl)
  have hzo : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have hxo : orderOf x = p := orderOf_eq_prime hx.pow_eq_one hx.ne_one
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hx.mem
  have hxnz : x ∉ zpowers z := n4_x_not_mem_zpowers hS hsit hx hz
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hB3' : IsPGroup p ↥((zpowers x ⊔ zpowers z).subgroupOf H) :=
    hB3.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨Q', hQ'⟩ := hB3'.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup H).map H.subtype with hQ
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Q H := ⟨Q', rfl⟩
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := by
    intro b hb
    have hbH : (⟨b, hBH hb⟩ : H) ∈ (zpowers x ⊔ zpowers z).subgroupOf H := hb
    exact ⟨⟨b, hBH hb⟩, hQ' hbH, rfl⟩
  have hQM : Q ≤ M := hopt.sylow_le Q hQsyl.isPGroup hQsyl.le hBQ
  have hΩQ := hΩ Q hQsyl.le hQsyl.isPGroup hBQ
  have hfr : x ∉ (frattini ↥Q).map Q.subtype := n4_x_not_mem_frattini hS hsit hx hQsyl.isPGroup
  have hwc : ∀ g ∈ H, g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z → g * z * g⁻¹ ∈ zpowers z :=
    fun g _ hg => n4_mem_zpowers_of_conj_mem_plane hS hsit hx hz hg
  have hNZ : normalizer (zpowers z : Set G) ⊓ H ≤ M ⊓ H :=
    fun g hg => ⟨n4_normalizer_zpowers_le_of_central hS hsit hz hg.1, hg.2⟩
  have hcover : ¬ H ≤ (M ⊓ H) ⊔ rankThreePrimeCore p H := by
    intro hle
    exact hopt.ext.pair.not_le (hle.trans (sup_le inf_le_left hO))
  obtain ⟨L, hsec, hLH, hzL, hrk, hLnot, hMN⟩ := hKF G p H Q (M ⊓ H) x z hprime hp5 hKH
    hxo hzo hxz hxnz hQsyl hBQ hΩQ hfr hwc (le_inf hQM hQsyl.le) inf_le_right hNZ hcover
  refine ⟨L, ?_⟩
  have hDeq : rankThreePrimeCore p H = pCoreOf 2 H := KGC.glbPrimeCore_eq_pCoreOf hprime hp2 H h2
  obtain ⟨⟨-, hS2, hBS⟩, hSmax⟩ := hopt.maxInv
  have hSHM : S ≤ H ⊓ M := hopt.ext.pair.isMax.1.1
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  refine ⟨hprime, hp5, CFSG.AGLEmbedding.glbPrimeCore_le p H,
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H, h2, hO, ?_, hSHM.trans inf_le_left,
    hSHM.trans inf_le_right, hS2, hBH,
    hBP.trans hPM, hpl.isElemAbelian, hpl.card_eq, Subgroup.mem_sup_right
      (mem_zpowers z), hzo, hBS, ?_, ?_, n4_normalizer_zpowers_le_of_central hS hsit hz, hsec,
      hLH, hzL, hrk, ?_, hMN, ?_, hopt.pRank_le, hcat, hopt.char_le⟩
  · rw [hDeq]
    exact n4_core_lt hopt
  · exact fun S' hS'H hS'2 hBS' hSS' => hSmax S' ⟨hS'H, hS'2, hBS'⟩ hSS'
  · intro S₀ hS₀ hS₀S hSB
    rw [hDeq] at hS₀
    exact hopt.norm_le S₀ hS₀ hS₀S hSB
  · intro hLM
    exact hLnot (fun l hl => Subgroup.mem_sup_left ⟨⟨hLM hl, hLH hl⟩, hl⟩)
  · intro g hg
    have := hS.charTwo H hopt.ext.pair.isTwoLocal
    rw [← hDeq] at this
    exact this hg

theorem n4_exists_kgData3 (hKF : KFact64iiL) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hS : Setting G) (hsit : SmallRankSituation G p P M) (hp5 : 5 ≤ p) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H S : Subgroup G}
    (hopt : Fail614OptimalGen p M x z H S) (hO : rankThreePrimeCore p H ≤ M)
    (hΩ : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z)
    (h2 : IsPGroup 2 (rankThreePrimeCore p H)) :
    ∃ L : Subgroup G,
      KGC.KGData3 p H (rankThreePrimeCore p H) S (zpowers x ⊔ zpowers z) L M z := by
  obtain ⟨L, d⟩ := n4_exists_kgData3Pre hKF hS hsit hp5 hx hz hopt hO hΩ h2
  exact ⟨L, d.toKGData3⟩

theorem n4_strong_of_alpha {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Setting G)
    (hsit : SmallRankSituation G p P M) {z : G} (hz : SmallRankCentral P z)
    (hα : HasPrimeConstraint (G := M) p) : KGC.KGStrongEmb p M z := by
  intro f hf hf2 hfp Y hYM hzY hsec hrel
  exfalso
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hPM : (P : Subgroup G) ≤ M :=
    (sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal).1
  have hzc : ∀ g ∈ (P : Subgroup G), g * z = z * g := fun g hg =>
    mem_centralizer_iff.mp hz.centralizes g hg
  have hzord : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  exact not_isPConstrained_of_section P hPM hz.mem hzc hz.pow_eq_one hYM hsec hzY
    (L613B.not_mem_rankThreePrimeCore hzord)
    (CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_of_hasPrimeConstraint hα)

theorem n4_false_of_kgData3 (hzj : CFSG.LocalAnalysis.RankFourTheoremC.KFactZJFactorizationGe)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix) (h2715 : KFact2715) (h131 : KFact131)
    (hpc : KFactParabolicCover) (h282 : KFact282) (h6n : KGStep6Noncyc) (hT : KGTransvCent)
    (h241 : KFact2401ThreeOmega) {A : Type} [Group A] [Finite A] {p : ℕ}
    {H D S B L M : Subgroup A} {z : A} (d3 : KGC.KGData3 p H D S B L M z)
    (hG : KGC.KGStrongEmb p M z) : False := by
  haveI : (D.subgroupOf H).Normal := d3.toData.normal_subgroupOf
  have hchev := d3.chev_or_alt hzj
  have hc := KGQ.kgroup_step4 d3.toData.cfg (d3.toData.strong_img hG) hAutO hAutE h2024 h2401
    hAlt6 hchev
  by_cases hbot : KGC.img H D S ⊓ KGC.img H D L = ⊥
  · by_cases hcyc : IsCyclic ↥(KGC.img H D S)
    · haveI := hcyc
      exact KGSix.false_of_data hT h241 d3 hG hc hbot
    · exact h6n _ p _ _ _ _ _ d3.toData.cfg hc hbot hcyc
  · by_cases hsyl : CFSG.ABGLocalTools.IsSylowOf 2
        (KGC.img H D S ⊓ KGC.img H D L) (KGC.img H D L)
    · by_cases hB : fusionIsBenderGroup ↥(KGC.img H D L)
      · exact KGQ.false_of_bender_sylow d3.toData.cfg h2715 hsyl hB
      · exact KGFive.false_of_sylow h282 d3 hc hsyl hB
    · exact kgStep5Para_of_inputs h131 hpc _ p _ _ _ _ _ d3.toData.cfg (d3.toData.strongEmb_img hG)
        hc hbot hsyl

theorem n4_false_of_alpha (hKF : KFact64iiL)
    (hzj : CFSG.LocalAnalysis.RankFourTheoremC.KFactZJFactorizationGe)
    (hAutO : KFactAutAltOrder) (hAutE : KFactAutAltEmbed) (h2024 : KG2024)
    (h2401 : KFact2401Three) (hAlt6 : KGAltSix) (h2715 : KFact2715) (h131 : KFact131)
    (hpc : KFactParabolicCover) (h282 : KFact282) (h6n : KGStep6Noncyc) (hT : KGTransvCent)
    (h241 : KFact2401ThreeOmega) {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Setting G)
    (hsit : SmallRankSituation G p P M) (hp5 : 5 ≤ p) {x z : G} (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {H S : Subgroup G} (hopt : Fail614OptimalGen p M x z H S)
    (hO : rankThreePrimeCore p H ≤ M)
    (hΩ : ∀ Q : Subgroup G, Q ≤ H → IsPGroup p Q → zpowers x ⊔ zpowers z ≤ Q →
      ∀ q ∈ Q, q ^ p = 1 → q ∈ zpowers x ⊔ zpowers z)
    (h2 : IsPGroup 2 (rankThreePrimeCore p H)) (hα : HasPrimeConstraint (G := M) p) : False := by
  obtain ⟨L, d3⟩ := n4_exists_kgData3 hKF hS hsit hp5 hx hz hopt hO hΩ h2
  exact n4_false_of_kgData3 hzj hAutO hAutE h2024 h2401 hAlt6 h2715 h131 hpc h282 h6n hT h241 d3
    (n4_strong_of_alpha hS hsit hz hα)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
