module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MsideReduction
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Unique
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUCons
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Competitor

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem threePrimeResidual_le (H : Subgroup G) : threePrimeResidual H ≤ H := by
  rw [threePrimeResidual, Subgroup.closure_le]
  rintro x ⟨hx, -⟩
  exact hx

theorem le_normalizer_threePrimeResidual (H : Subgroup G) :
    H ≤ Subgroup.normalizer (threePrimeResidual H : Set G) := by
  intro h hh
  have hsub : (threePrimeResidual H).map (MulAut.conj h).toMonoidHom ≤ threePrimeResidual H := by
    rw [threePrimeResidual, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hx, k, hk⟩, rfl⟩
    refine Subgroup.subset_closure ⟨?_, k, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hk, mul_one, mul_inv_cancel]
  have hcard : Nat.card (threePrimeResidual H) ≤
      Nat.card ((threePrimeResidual H).map (MulAut.conj h).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr (Subgroup.eq_of_le_of_card_ge hsub hcard)

omit [Finite G] in
theorem le_threePrimeResidual {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 3 A) :
    A ≤ threePrimeResidual H := by
  intro a ha
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  refine Subgroup.subset_closure ⟨hAH ha, k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

omit [Finite G] in
theorem threePrimeResidual_le_threePrimeResidual_self (H : Subgroup G) :
    threePrimeResidual H ≤ threePrimeResidual (threePrimeResidual H) := by
  intro x hx
  have h : Subgroup.closure {x | x ∈ H ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} ≤
      threePrimeResidual (threePrimeResidual H) := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyH, k, hk⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hyH, k, hk⟩, k, hk⟩
  exact h hx

theorem isPGroup_zpowers_of_pow_eq_one {X : Type*} [Group X] {p k : ℕ} {g : X}
    (hg : g ^ p ^ k = 1) : IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨k, Subtype.ext ?_⟩
  change (g ^ n) ^ p ^ k = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem D2AlmostSimple.eq_bot_of_le_normalizer {p : ℕ} {X : Type*} [Group X] [Finite X]
    {R : Sylow p X} {A X₀ K : Subgroup X} (hK : D2AlmostSimple p X R A X₀ K) {Y : Subgroup X}
    (hYK : K ≤ Subgroup.normalizer (Y : Set X)) (hKY : ¬ K ≤ Y) : Y = ⊥ := by
  have : IsSimpleGroup K := by
    have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.component.2.2.2
    exact ((QuotientGroup.quotientMulEquivOfEq hK.center_eq_bot).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hKn : K.Normal := hK.normal
  have hn : (Y.subgroupOf K).Normal := by
    constructor
    intro y hy k
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hYK k.2) y).mp hy
  rcases hn.eq_bot_or_eq_top with hb | ht
  ·
    rw [eq_bot_iff, ← hK.centralizer_eq_bot]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hc : y * k * y⁻¹ * k⁻¹ = 1 := by
      have hcY : y * k * y⁻¹ * k⁻¹ ∈ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (hYK hk) y⁻¹).mp (Y.inv_mem hy)
        have h2 := Y.mul_mem hy this
        simpa [mul_assoc] using h2
      have hcK : y * k * y⁻¹ * k⁻¹ ∈ K :=
        K.mul_mem (hKn.conj_mem k hk y) (K.inv_mem hk)
      have : (⟨_, hcK⟩ : K) ∈ Y.subgroupOf K := Subgroup.mem_subgroupOf.mpr hcY
      rw [hb, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have : y * k = k * y := by
      calc y * k = y * k * y⁻¹ * k⁻¹ * (k * y) := by group
        _ = k * y := by rw [hc, one_mul]
    exact this.symm
  · exact absurd (fun k hk => by
      have : (⟨k, hk⟩ : K) ∈ Y.subgroupOf K := ht ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this) hKY

theorem mem_normalizer_inf {X : Type*} [Group X] {A B : Subgroup X} {g : X}
    (hA : g ∈ Subgroup.normalizer (A : Set X)) (hB : g ∈ Subgroup.normalizer (B : Set X)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩, fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]

theorem D2L34BetaConf3.twoCore_inf_glbPrimeCore_ne_bot {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    pCoreOf 2 M ⊓ GLBPrimeCore 3 H ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 M with hQdef
  set W := GLBPrimeCore 3 H with hWdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  intro hQW
  have hNU : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H :=
    hc.normalizer_eq.le.trans inf_le_left
  have hQU : Q ≤ pCoreOf 2 (H ⊓ M) := pCoreOf_two_le_of_normalizer_le hNU
  have hQHM : Q ≤ H ⊓ M := hQU.trans (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M))
  have hQp : IsPGroup 2 Q := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAM : A ≤ M := hc.esc.A_le.trans hc.esc.le_M
  have hX₀ := hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hAbar : Nat.card ((A.subgroupOf H).map π) = 3 ^ 2 := hc.almostSimple.card_A
  have hQbarp : IsPGroup 2 ((Q.subgroupOf H).map π) := by
    have hQH : IsPGroup 2 (Q.subgroupOf H) :=
      hQp.of_equiv (Subgroup.subgroupOfEquivOfLe (hQHM.trans inf_le_left)).symm
    exact hQH.map π
  obtain ⟨m, hm⟩ := hQbarp.exists_card_eq
  have hdisj : (A.subgroupOf H).map π ⊓ (Q.subgroupOf H).map π = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by
      rw [hAbar, hm]; exact Nat.Coprime.pow 2 m (by norm_num))).eq_bot
  have hcomm : ∀ a ∈ A, ∀ q ∈ Q, q * a = a * q := by
    intro a ha q hq
    have hqH : q ∈ H := (hQHM hq).1
    have haH : a ∈ H := hAH ha
    set c := q * a * q⁻¹ * a⁻¹ with hc_def
    have hcQ : c ∈ Q := by
      have h1 : a * q⁻¹ * a⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hMQ (hAM ha)) q⁻¹).mp (Q.inv_mem hq)
      have := Q.mul_mem hq h1
      simpa [hc_def, mul_assoc] using this
    have hcH : c ∈ H := H.mul_mem (H.mul_mem (H.mul_mem hqH haH) (H.inv_mem hqH)) (H.inv_mem haH)
    have hqX₀ : π ⟨q, hqH⟩ ∈ Subgroup.normalizer
        (((A.subgroupOf H).map π : Subgroup _) : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      rw [← hX₀]
      exact ⟨⟨q, hqH⟩, Subgroup.mem_subgroupOf.mpr (hQHM hq), rfl⟩
    have haA : π ⟨a, haH⟩ ∈ (A.subgroupOf H).map π :=
      ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hcA : π ⟨c, hcH⟩ ∈ (A.subgroupOf H).map π := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hqX₀ _).mp haA
      have h2 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ haA)
      have he : π ⟨c, hcH⟩ = π ⟨q, hqH⟩ * π ⟨a, haH⟩ * (π ⟨q, hqH⟩)⁻¹ * (π ⟨a, haH⟩)⁻¹ := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      rw [he]
      exact h2
    have hcQb : π ⟨c, hcH⟩ ∈ (Q.subgroupOf H).map π :=
      ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hcQ, rfl⟩
    have hc1 : π ⟨c, hcH⟩ = 1 := by
      have : π ⟨c, hcH⟩ ∈ (A.subgroupOf H).map π ⊓ (Q.subgroupOf H).map π := ⟨hcA, hcQb⟩
      rw [hdisj, Subgroup.mem_bot] at this
      exact this
    have hcW : c ∈ W := (mk'_primeComplementCore_eq_one_iff 3 ⟨c, hcH⟩).mp hc1
    have hcb : c ∈ Q ⊓ W := ⟨hcQ, hcW⟩
    rw [hQW, Subgroup.mem_bot] at hcb
    calc q * a = c * (a * q) := by rw [hc_def]; group
      _ = a * q := by rw [hcb, one_mul]
  have hAC : A ≤ M ⊓ Subgroup.centralizer (Q : Set G) := fun a ha =>
    ⟨hAM ha, Subgroup.mem_centralizer_iff.mpr fun q hq => hcomm a ha q hq⟩
  have hloc : IsTwoLocal M := hc.esc.maxTwoLocal_M.1
  have hAQ : A ≤ Q := hAC.trans ((D2Amb3.glob (G := G)).charTwo M hloc)
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card Q := Subgroup.card_dvd_of_le hAQ
  rw [hc.esc.card_A, hn] at hdvd
  have h3 : 3 ∣ 2 ^ n := (dvd_pow_self 3 (by norm_num : (2 : ℕ) ≠ 0)).trans hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem D2L34BetaConf3.eq_of_maxTwoLocal_of_cover_of_facts {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hOnly : D2OnlyL34At P M) {J : Subgroup G} (hJH : J ≤ H) (hJgen : J ≤ threePrimeResidual J)
    {E : Subgroup G} (hEJ : E ≤ J) (hEel : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2) (hup : ∀ E₀ : Subgroup G, IsPGroup 3 E₀ → E ≤ E₀ → E₀ ≤ M)
    (hEcore : GLBCore 3 1 E ≤ M)
    (hKJ : K ≤ (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hJN : J ≤ N) : N = H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set πN := QuotientGroup.mk' (primeComplementCore (G := N) 3) with hπN
  set WH := GLBPrimeCore 3 H with hWH
  set WN := GLBPrimeCore 3 N with hWN
  have hAR : A = R := Subgroup.eq_of_le_of_card_ge hc.esc.A_le
    (by rw [hR9, hc.esc.card_A]; norm_num)
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) hEc
  have hErank : 2 ≤ Open.pRank 3 E := le_pRank_of_isElemAbelian Nat.prime_three hEel hEc
  have hX₀H := hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hRbK : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ K := by
    rw [hc.rbar, ← hAR]
    exact hc.le_K
  have := hc.almostSimple.normal
  have htopH := Sylow.normalizer_sup_eq_top' (N := K) Rbar hRbK
  have hfrH : ∀ h ∈ H, ∃ a ∈ J, ∃ b ∈ H ⊓ M, h = a * b := by
    intro h hh
    have hmem := htopH.symm ▸ Subgroup.mem_top (π ⟨h, hh⟩)
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
    obtain ⟨k, hk, y, hy, hky⟩ := hmem
    obtain ⟨j, hj, rfl⟩ := hKJ hk
    have hy' : y ∈ ((H ⊓ M).subgroupOf H).map π := by
      rw [hX₀H, hAR, ← hc.rbar]
      exact hy
    obtain ⟨m, hm, rfl⟩ := hy'
    set w : H := (j * m)⁻¹ * ⟨h, hh⟩ with hw_def
    have hw1 : π w = 1 := by
      rw [hw_def, map_mul, map_inv, map_mul, hky, inv_mul_cancel]
    have hwM : (w : G) ∈ M :=
      hc.esc.primeCore_le ((mk'_primeComplementCore_eq_one_iff 3 w).mp hw1)
    have hmHM : (m : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hm
    refine ⟨j, Subgroup.mem_subgroupOf.mp hj, (m : G) * w,
      ⟨H.mul_mem m.2 w.2, M.mul_mem hmHM.2 hwM⟩, ?_⟩
    have he : (⟨h, hh⟩ : H) = j * (m * w) := by rw [hw_def]; group
    have := congrArg Subtype.val he
    simpa using this
  have hNM : ¬ N ≤ M := by
    intro hle
    apply hc.esc.not_le
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrH h hh
    exact M.mul_mem (hle (hJN ha)) hb.2
  have hEN : E ≤ N := hEJ.trans hJN
  have hEpN : IsPGroup 3 (E.subgroupOf N) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEN).symm
  obtain ⟨T, hET⟩ := hEpN.exists_le_sylow
  set E₀ : Subgroup G := (T : Subgroup N).map N.subtype with hE₀
  have hEE₀ : E ≤ E₀ := fun a ha => ⟨⟨a, hEN ha⟩, hET (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hE₀p : IsPGroup 3 E₀ := T.isPGroup'.map N.subtype
  have hE₀M : E₀ ≤ M := hup E₀ hE₀p hEE₀
  have hE₀N : E₀ ≤ N := Subgroup.map_subtype_le _
  have hrank₀ : Open.pRank 3 (N ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hNM (D2Amb3.d1 (G := G) P M hc.esc.maxTwoLocal_M
      ((weakCore_le_fullCore 3 (P : Subgroup G)).trans hc.esc.core_le) N hN.1 (by omega))
  have hesc₀ : D2Escape 3 P M E N E₀ :=
    { prime := Nat.prime_three
      ne_two := by norm_num
      sylow_le := hc.esc.sylow_le
      core_le := hc.esc.core_le
      maxTwoLocal_M := hc.esc.maxTwoLocal_M
      maxTwoLocal_H := hN
      elem := hEel
      card_A := hEc
      core_A := hEcore
      A_le := hEE₀
      le_H := hE₀N
      le_M := hE₀M
      isSylow := ⟨T, rfl⟩
      pRank_eq := le_antisymm
        ((pRank_mono 3 Nat.prime_three (le_inf hE₀N hE₀M)).trans hrank₀)
        (hErank.trans (pRank_mono 3 Nat.prime_three hEE₀))
      not_le := hNM }
  have hE₀9 : Nat.card E₀ = 9 := le_antisymm (hR9 ▸ hc.max E N E₀ hesc₀) (by
    have := Subgroup.card_le_of_le hEE₀
    rw [hEc] at this
    omega)
  have hAE : E = E₀ := Subgroup.eq_of_le_of_card_ge hEE₀ (by rw [hE₀9, hEc]; norm_num)
  have hmax₀ : D2EscapeMax 3 P M E₀ := fun A' H' R' h' =>
    (hc.max A' H' R' h').trans (by rw [hR9, hE₀9])
  obtain ⟨Rbar₀, K₀, hRbar₀, hK₀⟩ := hesc₀.almostSimple (D2Amb3.glob (G := G))
  obtain ⟨d₀, hd₀, hi⟩ := hOnly E N E₀ hesc₀ hmax₀ Rbar₀ K₀ hRbar₀ hK₀
  have := hK₀.normal
  have hK₀c : Nat.card K₀ = 20160 :=
    (kFactSmallThreeOrders K₀).2.1 (isLinThreeFour_of_l34Index hd₀ hi)
  have hE₀p' : IsPGroup 3 (E₀.subgroupOf N) :=
    hE₀p.of_equiv (Subgroup.subgroupOfEquivOfLe hE₀N).symm
  have hRb : Nat.card (Rbar₀ : Subgroup (N ⧸ primeComplementCore (G := N) 3)) = 3 ^ 2 := by
    rw [hRbar₀, card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3)
      hE₀p', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀N).toEquiv, hE₀9]
    norm_num
  have hfac : (Nat.card (N ⧸ primeComplementCore (G := N) 3)).factorization 3 = 2 := by
    have h1 := Rbar₀.card_eq_multiplicity
    rw [hRb] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  have hidx3 : ¬ 3 ∣ K₀.index := by
    intro h3
    have hmul := K₀.index_mul_card
    rw [hK₀c] at hmul
    have hidx0 : K₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 : (K₀.index * 20160).factorization 3 = 2 := by rw [hmul, hfac]
    rw [Nat.factorization_mul hidx0 (by norm_num), Finsupp.add_apply,
      factorization_20160_three] at h2
    have h1 := (Nat.prime_three.dvd_iff_one_le_factorization hidx0).mp h3
    omega
  have hRbK : (Rbar₀ : Subgroup (N ⧸ primeComplementCore (G := N) 3)) ≤ K₀ :=
    le_of_isPGroup_of_not_dvd_index Nat.prime_three hidx3 Rbar₀.isPGroup'
  have hAK₀ : (E.subgroupOf N).map πN ≤ K₀ := by
    rw [hAE, ← hRbar₀]
    exact hRbK
  have hX₀N := hK₀.eq_normalizer_of_l34 kFactL34Inner hd₀ hi hAK₀
  have hJK₀ : (J.subgroupOf N).map πN ≤ K₀ := by
    have hJle : J ≤ (K₀.comap πN).map N.subtype := by
      refine hJgen.trans ?_
      rw [threePrimeResidual, Subgroup.closure_le]
      rintro x ⟨hxJ, k, hk⟩
      have hxN : x ∈ N := hJN hxJ
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      change πN ⟨x, hxN⟩ ∈ K₀
      have hpow : (πN ⟨x, hxN⟩) ^ 3 ^ k = 1 := by
        rw [← map_pow]
        have : (⟨x, hxN⟩ : N) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
        rw [this, map_one]
      exact le_of_isPGroup_of_not_dvd_index Nat.prime_three hidx3
        (MsidePrelim.isPGroup_zpowers_of_pow_eq_one hpow) (Subgroup.mem_zpowers _)
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hJle (Subgroup.mem_subgroupOf.mp hx)
    have : y = ⟨x, hxN⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have hKc : Nat.card K = 20160 :=
    (kFactSmallThreeOrders K).2.1 (isLinThreeFour_of_l34Index hc.l34 hc.iso)
  have hYbot : ((WN ⊓ J).subgroupOf H).map π = ⊥ := by
    apply D2AlmostSimple.eq_bot_of_le_normalizer hc.almostSimple
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := hKJ hk
      apply Subgroup.le_normalizer_map π
      refine ⟨j, ?_, rfl⟩
      rw [← Subgroup.subgroupOf_normalizer_eq (inf_le_right.trans hJH), SetLike.mem_coe,
        Subgroup.mem_subgroupOf]
      have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
      exact mem_normalizer_inf (le_normalizer_glbPrimeCore 3 N (hJN hjJ))
        (Subgroup.le_normalizer hjJ)
    · intro hle
      have h1 : Nat.card K ∣ Nat.card (((WN ⊓ J).subgroupOf H).map π) :=
        Subgroup.card_dvd_of_le hle
      have h2 : Nat.card (((WN ⊓ J).subgroupOf H).map π) ∣
          Nat.card ((WN ⊓ J).subgroupOf H) := Subgroup.card_map_dvd _ _
      have h3 : Nat.card ((WN ⊓ J).subgroupOf H) = Nat.card (WN ⊓ J : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hJH)).toEquiv
      have h4 : Nat.card (WN ⊓ J : Subgroup G) ∣ Nat.card WN := Subgroup.card_dvd_of_le inf_le_left
      have h3K : 3 ∣ Nat.card K := by rw [hKc]; norm_num
      have h3W : 3 ∣ Nat.card WN := h3K.trans (h1.trans (h2.trans (h3 ▸ h4)))
      exact absurd (Nat.Coprime.coprime_dvd_right h3W (glbPrimeCore_coprime 3 N)) (by norm_num)
  have hWNJ : WN ⊓ J ≤ WH := by
    intro x hx
    have hxH : x ∈ H := hJH hx.2
    have hmem : π ⟨x, hxH⟩ ∈ ((WN ⊓ J).subgroupOf H).map π :=
      ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hYbot, Subgroup.mem_bot] at hmem
    exact (mk'_primeComplementCore_eq_one_iff 3 ⟨x, hxH⟩).mp hmem
  have hcardH : Nat.card ((J.subgroupOf H).map π) = WH.relIndex J := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← glbPrimeCore_subgroupOf 3 H,
      Subgroup.relIndex_subgroupOf hJH]
  have hcardN : Nat.card ((J.subgroupOf N).map πN) = WN.relIndex J := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← glbPrimeCore_subgroupOf 3 N,
      Subgroup.relIndex_subgroupOf hJN]
  have hrel : WH.relIndex J ≤ WN.relIndex J := by
    rw [← Subgroup.inf_relIndex_right WH J, ← Subgroup.inf_relIndex_right WN J]
    exact Subgroup.relIndex_le_of_le_left (le_inf hWNJ inf_le_right)
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have hge : 20160 ≤ Nat.card ((J.subgroupOf N).map πN) := by
    rw [hcardN]
    calc 20160 = Nat.card K := hKc.symm
      _ ≤ Nat.card ((J.subgroupOf H).map π) := Subgroup.card_le_of_le hKJ
      _ = WH.relIndex J := hcardH
      _ ≤ WN.relIndex J := hrel
  have hJbN : (J.subgroupOf N).map πN = K₀ :=
    Subgroup.eq_of_le_of_card_ge hJK₀ (by rw [hK₀c]; exact hge)
  have htopN := Sylow.normalizer_sup_eq_top' (N := K₀) Rbar₀ hRbK
  have hβ : ∀ n ∈ N, ∃ a ∈ H ⊓ N, ∃ b ∈ N ⊓ M, n = a * b := by
    intro n hn
    have hmem := htopN.symm ▸ Subgroup.mem_top (πN ⟨n, hn⟩)
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
    obtain ⟨k, hk, y, hy, hky⟩ := hmem
    rw [← hJbN] at hk
    obtain ⟨j, hj, rfl⟩ := hk
    have hy' : y ∈ ((N ⊓ M).subgroupOf N).map πN := by
      rw [hX₀N, hAE, ← hRbar₀]
      exact hy
    obtain ⟨m, hm, rfl⟩ := hy'
    set w : N := (j * m)⁻¹ * ⟨n, hn⟩ with hw_def
    have hw1 : πN w = 1 := by
      rw [hw_def, map_mul, map_inv, map_mul, hky, inv_mul_cancel]
    have hwM : (w : G) ∈ M :=
      hesc₀.primeCore_le ((mk'_primeComplementCore_eq_one_iff 3 w).mp hw1)
    have hmNM : (m : G) ∈ N ⊓ M := Subgroup.mem_subgroupOf.mp hm
    refine ⟨j, ⟨hJH (Subgroup.mem_subgroupOf.mp hj), j.2⟩, (m : G) * w,
      ⟨N.mul_mem m.2 w.2, M.mul_mem hmNM.2 hwM⟩, ?_⟩
    have he : (⟨n, hn⟩ : N) = j * (m * w) := by rw [hw_def]; group
    have := congrArg Subtype.val he
    simpa using this
  have hα : ∀ h ∈ H, ∃ a ∈ H ⊓ N, ∃ b ∈ H ⊓ M, h = a * b := by
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrH h hh
    exact ⟨a, ⟨hJH ha, hJN ha⟩, b, hb, rfl⟩
  exact L34Squeeze.eq_of_factorizations hc.esc.maxTwoLocal_H hN
    (le_normalizer_glbPrimeCore 3 H) hc.esc.primeCore_le
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    (D2L34BetaConf3.twoCore_inf_glbPrimeCore_ne_bot hc) hα hβ

theorem D2L34BetaConf3.eq_of_maxTwoLocal_of_cover {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {J : Subgroup G} (hJH : J ≤ H) (hJgen : J ≤ threePrimeResidual J)
    {E : Subgroup G} (hEJ : E ≤ J) (hEM : E ≤ M) (hEel : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2)
    (hKJ : K ≤ (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hJN : J ≤ N) : N = H := by
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) hEc
  have hEne : E ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hEc; norm_num at hEc
  exact hc.eq_of_maxTwoLocal_of_cover_of_facts (hc.card_R_eq_nine hstr) hOnly hJH hJgen hEJ
    hEel hEc (fun E₀ hE₀p hEE₀ => le_of_stronglyEmbedded_of_inf_ne_bot Nat.prime_three hstr hE₀p
      fun h => hEne (le_bot_iff.mp (h ▸ le_inf hEE₀ hEM)))
    (glbCore_one_le_of_stronglyEmbedded Nat.prime_three hstr hEp hEM) hKJ hN hJN

theorem D2L34BetaConf3.d2L34Kmax {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) : D2L34Kmax H := by
  intro N hN hJN
  set J := threePrimeResidual H with hJdef
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) hc.esc.card_A
  have hAJ : A ≤ J := le_threePrimeResidual hAH hAp
  have hJH : J ≤ H := threePrimeResidual_le H
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) := le_normalizer_threePrimeResidual H
  have hJbn : ((J.subgroupOf H).map π).Normal := by
    have : (J.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mpr hHJ
    exact this.map π (QuotientGroup.mk'_surjective _)
  have hJb1 : (J.subgroupOf H).map π ≠ ⊥ := by
    intro h
    have hle : (A.subgroupOf H).map π ≤ (J.subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.comap_mono hAJ)
    rw [h, le_bot_iff] at hle
    have := hc.almostSimple.card_A
    rw [hle, Subgroup.card_bot] at this
    norm_num at this
  exact D2L34BetaConf3.eq_of_maxTwoLocal_of_cover hc hstr hOnly hJH
    (threePrimeResidual_le_threePrimeResidual_self H) hAJ (hc.esc.A_le.trans hc.esc.le_M)
    hc.esc.elem hc.esc.card_A (hc.almostSimple.le_of_normal hJbn hJb1) hN hJN

theorem D2L34BetaConf3.normalizer_le_of_cover {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {C : Subgroup G} (hC1 : C ≠ ⊥) (hCp : IsPGroup 2 C)
    (hAC : A ≤ Subgroup.normalizer (C : Set G))
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (C : Set G) ≤ H := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set Y := H ⊓ Subgroup.normalizer (C : Set G) with hY
  set J := threePrimeResidual Y with hJdef
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC1, hCp, rfl⟩
  obtain ⟨N, hNC, hN⟩ := exists_maximal_twoLocal hloc
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) hc.esc.card_A
  have hJY : J ≤ Y := threePrimeResidual_le Y
  have hJH : J ≤ H := hJY.trans inf_le_left
  have hJN : J ≤ N := (hJY.trans inf_le_right).trans hNC
  have hAJ : A ≤ J := le_threePrimeResidual (le_inf hAH hAC) hAp
  have hKJ : K ≤ (J.subgroupOf H).map π := by
    by_contra hKJ
    have hbot := D2AlmostSimple.eq_bot_of_le_normalizer hc.almostSimple
      (Y := (J.subgroupOf H).map π)
      (fun k hk => by
        obtain ⟨a, haY, haH, rfl⟩ := hcov k hk
        apply Subgroup.le_normalizer_map π
        refine ⟨⟨a, haH⟩, ?_, rfl⟩
        rw [← Subgroup.subgroupOf_normalizer_eq hJH, SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact le_normalizer_threePrimeResidual Y haY) hKJ
    have hle : (A.subgroupOf H).map π ≤ (J.subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.comap_mono hAJ)
    rw [hbot, le_bot_iff] at hle
    have := hc.almostSimple.card_A
    rw [hle, Subgroup.card_bot] at this
    norm_num at this
  have hNH := D2L34BetaConf3.eq_of_maxTwoLocal_of_cover hc hstr hOnly hJH
    (threePrimeResidual_le_threePrimeResidual_self Y) hAJ (hc.esc.A_le.trans hc.esc.le_M)
    hc.esc.elem hc.esc.card_A hKJ hN hJN
  exact hNC.trans hNH.le

omit [D2Amb3 G] in
theorem D2L34BetaConf3.eq_of_maxTwoLocal_of_normalizer_cover_of_cover
    {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hcover : ∀ {J E : Subgroup G}, J ≤ H → J ≤ threePrimeResidual J → E ≤ J → E ≤ M →
      E ≤ A ⊔ GLBPrimeCore 3 H → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      K ≤ (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) →
      ∀ {N : Subgroup G}, GLBIsMaxTwoLocal N → J ≤ N → N = H)
    {C : Subgroup G}
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k)
    {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hNC : Subgroup.normalizer (C : Set G) ≤ N) :
    N = H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set Y := H ⊓ Subgroup.normalizer (C : Set G) with hY
  set J := threePrimeResidual Y with hJdef
  set W := GLBPrimeCore 3 H with hW
  set D := Y ⊓ (A ⊔ W) with hD
  set Abar := (A.subgroupOf H).map π with hAbar
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAM : A ≤ M := hc.esc.A_le.trans hc.esc.le_M
  have hWH : W ≤ H := glbPrimeCore_le 3 H
  have hWM : W ≤ M := hc.esc.primeCore_le
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := le_normalizer_glbPrimeCore 3 H
  have hDH : D ≤ H := inf_le_left.trans inf_le_left
  have hJY : J ≤ Y := threePrimeResidual_le Y
  have hJH : J ≤ H := hJY.trans inf_le_left
  have hJN : J ≤ N := (hJY.trans inf_le_right).trans hNC
  have hAbar9 : Nat.card Abar = 3 ^ 2 := hc.almostSimple.card_A
  have hAbarE : IsElemAbelian 3 Abar := hc.almostSimple.elem
  have hAWmap : ∀ x (hx : x ∈ A ⊔ W), π ⟨x, (sup_le hAH hWH) hx⟩ ∈ Abar := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A W (hAH.trans hHW),
      Set.mem_mul] at hx
    obtain ⟨a, ha, w, hw, rfl⟩ := hx
    have e : (⟨a * w, (sup_le hAH hWH) (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right hw))⟩ : H) = ⟨a, hAH ha⟩ * ⟨w, hWH hw⟩ := rfl
    rw [e, map_mul, (mk'_primeComplementCore_eq_one_iff 3 ⟨w, hWH hw⟩).mpr hw, mul_one]
    exact ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hAbarD : Abar ≤ (D.subgroupOf H).map π := by
    rintro _ ⟨⟨a', ha'H⟩, ha', rfl⟩
    obtain ⟨a, haY, haH, hae⟩ := hcov _ (hc.le_K ⟨⟨a', ha'H⟩, ha', rfl⟩)
    refine ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ⟨haY, ?_⟩, hae⟩
    have hw : π ((⟨a', ha'H⟩ : H)⁻¹ * ⟨a, haH⟩) = 1 := by
      rw [map_mul, map_inv, hae, inv_mul_cancel]
    have hwW := (mk'_primeComplementCore_eq_one_iff 3 _).mp hw
    have e : a = a' * (a'⁻¹ * a) := by group
    show a ∈ A ⊔ W
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha'))
      (Subgroup.mem_sup_right hwW)
  have h9 : 3 ^ 2 ∣ Nat.card D := by
    have h1 : Nat.card Abar ∣ Nat.card ((D.subgroupOf H).map π) := Subgroup.card_dvd_of_le hAbarD
    have h2 : Nat.card ((D.subgroupOf H).map π) ∣ Nat.card (D.subgroupOf H) :=
      Subgroup.card_map_dvd _ _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv] at h2
    rw [← hAbar9]
    exact h1.trans h2
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set E := E'.map D.subtype with hE
  have hEc : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective D.subtype_injective, hE']
  have hED : E ≤ D := Subgroup.map_subtype_le _
  have hEp : IsPGroup 3 E := IsPGroup.of_card hEc
  have hEW : ∀ x ∈ E, x ∈ W → x = 1 := by
    intro x hxE hxW
    have h1 : orderOf x ∣ 3 ^ 2 := hEc ▸ Subgroup.orderOf_dvd_natCard E hxE
    have h2 : orderOf x ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hxW
    have hcop : Nat.Coprime (orderOf x) (Nat.card W) :=
      Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left 2 (glbPrimeCore_coprime 3 H))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2)
  have hEAW : ∀ x ∈ E, x ∈ A ⊔ W := fun x hx => (hED hx).2
  have hEH : ∀ x ∈ E, x ∈ H := fun x hx => hDH (hED hx)
  have hEel : IsElemAbelian 3 E := by
    have hAc : ∀ u ∈ Abar, ∀ v ∈ Abar, u * v = v * u := fun u hu v hv =>
      congrArg Subtype.val (hAbarE.1.is_comm.comm (⟨u, hu⟩ : Abar) ⟨v, hv⟩)
    refine ⟨isMulCommutative_iff.mpr fun x y => Subtype.ext ?_, fun x hx => ?_⟩
    · have hxE := x.2
      have hyE := y.2
      have hc1 : π ⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹,
          hEH _ (E.mul_mem (E.mul_mem (E.mul_mem hxE hyE) (E.inv_mem hxE))
            (E.inv_mem hyE))⟩ = 1 := by
        have e : (⟨(x : G) * y * (x : G)⁻¹ * (y : G)⁻¹,
            hEH _ (E.mul_mem (E.mul_mem (E.mul_mem hxE hyE) (E.inv_mem hxE)) (E.inv_mem hyE))⟩ : H)
            = ⟨x, hEH _ hxE⟩ * ⟨y, hEH _ hyE⟩ * (⟨x, hEH _ hxE⟩ : H)⁻¹ *
              (⟨y, hEH _ hyE⟩ : H)⁻¹ := rfl
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv,
          hAc _ (hAWmap _ (hEAW _ hxE)) _ (hAWmap _ (hEAW _ hyE)), mul_inv_cancel_right,
          mul_inv_cancel]
      have h1 := hEW _ (E.mul_mem (E.mul_mem (E.mul_mem hxE hyE) (E.inv_mem hxE)) (E.inv_mem hyE))
        ((mk'_primeComplementCore_eq_one_iff 3 _).mp hc1)
      change (x : G) * y = y * x
      calc (x : G) * y = ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) * (y * x) := by group
        _ = y * x := by rw [h1, one_mul]
    · have hx3 : π ⟨x ^ 3, hEH _ (E.pow_mem hx 3)⟩ = 1 := by
        have e : (⟨x ^ 3, hEH _ (E.pow_mem hx 3)⟩ : H) = (⟨x, hEH _ hx⟩ : H) ^ 3 := rfl
        rw [e, map_pow]
        exact hAbarE.2 _ (hAWmap _ (hEAW _ hx))
      exact hEW _ (E.pow_mem hx 3) ((mk'_primeComplementCore_eq_one_iff 3 _).mp hx3)
  have hEJ : E ≤ J := le_threePrimeResidual (fun x hx => (hED hx).1) hEp
  have hEM : E ≤ M := fun x hx => (sup_le hAM hWM) (hEAW x hx)
  have hKJ : K ≤ (J.subgroupOf H).map π := by
    by_contra hKJ
    have hbot := D2AlmostSimple.eq_bot_of_le_normalizer hc.almostSimple
      (Y := (J.subgroupOf H).map π)
      (fun k hk => by
        obtain ⟨a, haY, haH, rfl⟩ := hcov k hk
        apply Subgroup.le_normalizer_map π
        refine ⟨⟨a, haH⟩, ?_, rfl⟩
        rw [← Subgroup.subgroupOf_normalizer_eq hJH, SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact le_normalizer_threePrimeResidual Y haY) hKJ
    apply (show E ≠ ⊥ from fun h => by rw [h, Subgroup.card_bot] at hEc; norm_num at hEc)
    rw [eq_bot_iff]
    intro x hx
    have hmem : π ⟨x, hEH x hx⟩ ∈ (J.subgroupOf H).map π :=
      ⟨⟨x, hEH x hx⟩, Subgroup.mem_subgroupOf.mpr (hEJ hx), rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hEW x hx ((mk'_primeComplementCore_eq_one_iff 3 _).mp hmem)
  exact hcover hJH (threePrimeResidual_le_threePrimeResidual_self Y) hEJ hEM
    (fun x hx => hEAW x hx) hEel hEc hKJ hN hJN

theorem D2L34BetaConf3.eq_of_maxTwoLocal_of_normalizer_cover {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {C : Subgroup G}
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k)
    {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hNC : Subgroup.normalizer (C : Set G) ≤ N) :
    N = H :=
  hc.eq_of_maxTwoLocal_of_normalizer_cover_of_cover
    (fun hJH hJgen hEJ hEM _ hEel hEc hKJ _ hN hJN =>
      hc.eq_of_maxTwoLocal_of_cover hstr hOnly hJH hJgen hEJ hEM hEel hEc hKJ hN hJN) hcov hN hNC

theorem D2L34BetaConf3.normalizer_le_of_cover' {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {C : Subgroup G} (hC1 : C ≠ ⊥) (hCp : IsPGroup 2 C)
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (C : Set G) ≤ H := by
  obtain ⟨N, hNC, hN⟩ := exists_maximal_twoLocal
    (⟨C, hC1, hCp, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C : Set G)))
  exact hNC.trans (D2L34BetaConf3.eq_of_maxTwoLocal_of_normalizer_cover hc hstr hOnly hcov hN
    hNC).le

theorem D2L34BetaConf3.normalizer_le_of_char_cover {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {V C : Subgroup G} (hV : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hCV : C ≤ V) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf V).Characteristic)
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (V : Set G) ≤ H := by
  have hVC : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := V) (C.subgroupOf V)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCV] at h1
  exact hVC.trans (D2L34BetaConf3.normalizer_le_of_cover hc hstr hOnly hC1 (hV.to_le hCV)
    (hAV.trans hVC) hcov)

theorem D2L34BetaConf3.normalizer_le_of_char_cover' {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {V C : Subgroup G} (hV : IsPGroup 2 V) (hCV : C ≤ V)
    (hC1 : C ≠ ⊥) (hchar : (C.subgroupOf V).Characteristic)
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (V : Set G) ≤ H := by
  have hVC : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := V) (C.subgroupOf V)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCV] at h1
  exact hVC.trans (D2L34BetaConf3.normalizer_le_of_cover' hc hstr hOnly hC1 (hV.to_le hCV) hcov)

end CFSG.LocalAnalysis.RankThreeTheoremC

namespace CFSG.AGLEmbeddingD2.Tits.MsidePrelim

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G]

theorem D2L34BetaConf.d2L34Kmax {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) : D2L34Kmax H := by
  have := hc.amb3
  exact hc.toConf3.d2L34Kmax hstr hOnly

theorem D2L34BetaConf.normalizer_le_of_char_cover {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {V C : Subgroup G} (hV : IsPGroup 2 V)
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hCV : C ≤ V) (hC1 : C ≠ ⊥)
    (hchar : (C.subgroupOf V).Characteristic)
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (V : Set G) ≤ H := by
  have := hc.amb3
  exact hc.toConf3.normalizer_le_of_char_cover hstr hOnly hV hAV hCV hC1 hchar hcov

theorem D2L34BetaConf.normalizer_le_of_char_cover' {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {V C : Subgroup G} (hV : IsPGroup 2 V) (hCV : C ≤ V)
    (hC1 : C ≠ ⊥) (hchar : (C.subgroupOf V).Characteristic)
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (V : Set G) ≤ H := by
  have := hc.amb3
  exact hc.toConf3.normalizer_le_of_char_cover' hstr hOnly hV hCV hC1 hchar hcov

end CFSG.AGLEmbeddingD2.Tits.MsidePrelim
