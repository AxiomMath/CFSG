module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27AutL34
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WEscape
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycSquare

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

private theorem isSimpleGroup_of_almostSimple {X : Type*} [Group X] [Finite X] {p : ℕ}
    {Rb : Sylow p X} {B X₀ L : Subgroup X} (hK : D2AlmostSimple p X Rb B X₀ L) :
    IsSimpleGroup L := by
  have hq : IsSimpleGroup (L ⧸ Subgroup.center L) := hK.component.2.2.2
  exact ((QuotientGroup.quotientMulEquivOfEq hK.center_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem le_of_relIndex_le_three {X : Type*} [Group X] [Finite X] {K L Y : Subgroup X}
    (hKn : K.Normal) (hKs : IsSimpleGroup K) (h6 : ¬ Nat.card K ∣ 6) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hrel : K.relIndex L ≤ 3) (hcard : Nat.card K ≤ Nat.card Y) : K ≤ Y := by
  have h1 := Subgroup.relIndex_mul_card Y K
  have h2 := Subgroup.relIndex_mul_card K Y
  have hKL0 : K.relIndex L ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have h3 : K.relIndex Y ≤ 3 := by
    rw [← Subgroup.relIndex_sup_right Y K]
    exact (Subgroup.relIndex_le_of_le_right (sup_le hYL hKL) hKL0).trans hrel
  have hpos : 0 < Nat.card (Y ⊓ K : Subgroup X) := Nat.card_pos
  have hYK : Nat.card (K ⊓ Y : Subgroup X) = Nat.card (Y ⊓ K : Subgroup X) := by
    rw [inf_comm]
  have h4 : Y.relIndex K ≤ 3 := by
    have : Y.relIndex K * Nat.card (Y ⊓ K : Subgroup X) ≤
        3 * Nat.card (Y ⊓ K : Subgroup X) := by
      rw [h1]
      calc Nat.card K ≤ Nat.card Y := hcard
        _ = K.relIndex Y * Nat.card (K ⊓ Y : Subgroup X) := h2.symm
        _ ≤ 3 * Nat.card (Y ⊓ K : Subgroup X) := by
          rw [hYK]
          exact Nat.mul_le_mul_right _ h3
    exact Nat.le_of_mul_le_mul_right this hpos
  set D := Y.subgroupOf K
  have hDi : D.index ≤ 3 := h4
  rcases Subgroup.Normal.eq_bot_or_eq_top D.normalCore with hb | ht
  · exfalso
    have hdvd := D.index_normalCore_dvd_factorial_index
    rw [hb, Subgroup.index_bot] at hdvd
    exact h6 (hdvd.trans (Nat.factorial_dvd_factorial hDi))
  · have hDt : D = ⊤ := top_le_iff.mp (ht ▸ D.normalCore_le)
    exact Subgroup.subgroupOf_eq_top.mp hDt

private theorem exists_mul_of_l34
    {d₀ : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d₀)
    {Y B J : Subgroup G} {Rb : Sylow 3 (Y ⧸ primeComplementCore (G := Y) 3)}
    {L : Subgroup (Y ⧸ primeComplementCore (G := Y) 3)}
    (hK : D2AlmostSimple 3 (Y ⧸ primeComplementCore (G := Y) 3) Rb
      ((B.subgroupOf Y).map (QuotientGroup.mk' (primeComplementCore 3)))
      (((Y ⊓ M).subgroupOf Y).map (QuotientGroup.mk' (primeComplementCore 3))) L)
    (he : Nonempty (L ≃* (TauCeti.CFSGIndex.lie d₀).Group))
    (hBL : (B.subgroupOf Y).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ L)
    (hWM : GLBPrimeCore 3 Y ≤ M)
    (hLJ : L ≤ (J.subgroupOf Y).map (QuotientGroup.mk' (primeComplementCore (G := Y) 3))) :
    ∀ y ∈ Y, ∃ a ∈ J, ∃ b ∈ Y ⊓ M, y = a * b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := Y) 3)
  set Bb := (B.subgroupOf Y).map π
  have hX₀ := hK.eq_normalizer_of_l34 kFactL34Inner hd he hBL
  have := hK.normal
  have hLc : Nat.card L = 20160 :=
    (kFactSmallThreeOrders L).2.1 (isLinThreeFour_of_l34Index hd he)
  have hcard : Nat.card (Bb.subgroupOf L) = 3 ^ (Nat.card L).factorization 3 := by
    rw [hLc, factorization_20160_three,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hK.card_A]
  have htop := Sylow.normalizer_sup_eq_top (Sylow.ofCard (Bb.subgroupOf L) hcard)
  rw [Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, inf_of_le_left hBL] at htop
  intro y hy
  have hmem := htop.symm ▸ Subgroup.mem_top (π ⟨y, hy⟩)
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
  obtain ⟨k, hk, z, hz, hkz⟩ := hmem
  obtain ⟨j, hj, rfl⟩ := hLJ hk
  have hz' : z ∈ ((Y ⊓ M).subgroupOf Y).map π := by
    rw [hX₀]
    exact hz
  obtain ⟨m, hm, rfl⟩ := hz'
  set w : Y := (j * m)⁻¹ * ⟨y, hy⟩ with hw_def
  have hw1 : π w = 1 := by
    rw [hw_def, map_mul, map_inv, map_mul, hkz, inv_mul_cancel]
  have hwM : (w : G) ∈ M := hWM ((mk'_primeComplementCore_eq_one_iff 3 w).mp hw1)
  have hmYM : (m : G) ∈ Y ⊓ M := Subgroup.mem_subgroupOf.mp hm
  refine ⟨j, Subgroup.mem_subgroupOf.mp hj, (m : G) * w,
    ⟨Y.mul_mem m.2 w.2, M.mul_mem hmYM.2 hwM⟩, ?_⟩
  have he : (⟨y, hy⟩ : Y) = j * (m * w) := by rw [hw_def]; group
  have := congrArg Subtype.val he
  simpa using this

private theorem D2L34WeakConf3.twoCore_inf_glbPrimeCore_ne_bot' [D2Amb3 G]
    (hw : D2L34WeakConf3 d P M A H R Rbar K) (hO2 : pCoreOf 2 M ≤ H) :
    pCoreOf 2 M ⊓ GLBPrimeCore 3 H ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 M
  set W := GLBPrimeCore 3 H
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  intro hQW
  have hQHM : Q ≤ H ⊓ M := le_inf hO2 (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M)
  have hQp : IsPGroup 2 Q := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hAH : A ≤ H := hw.esc.A_le.trans hw.esc.le_H
  have hAM : A ≤ M := hw.esc.A_le.trans hw.esc.le_M
  have hX₀ := hw.almostSimple.eq_normalizer_of_l34 kFactL34Inner hw.l34 hw.iso hw.le_K
  have hAbar : Nat.card ((A.subgroupOf H).map π) = 3 ^ 2 := hw.almostSimple.card_A
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
  have hloc : IsTwoLocal M := hw.esc.maxTwoLocal_M.1
  have hAQ : A ≤ Q := hAC.trans ((D2Amb3.glob (G := G)).charTwo M hloc)
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hdvd : Nat.card A ∣ Nat.card Q := Subgroup.card_dvd_of_le hAQ
  rw [hw.esc.card_A, hn] at hdvd
  have h3 : 3 ∣ 2 ^ n := (dvd_pow_self 3 (by norm_num : (2 : ℕ) ≠ 0)).trans hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

private theorem core_one_le_of_le_sup_of_escape (hesc : D2Escape 3 P M A H R)
    {E : Subgroup G} (hE : E ≤ A ⊔ GLBPrimeCore 3 H) (hEp : IsPGroup 3 E)
    (hE9 : Nat.card E = 3 ^ 2) : GLBCore 3 1 E ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := GLBPrimeCore 3 H
  have hAH : A ≤ H := hesc.A_le.trans hesc.le_H
  have hAM : A ≤ M := hesc.A_le.trans hesc.le_M
  have hWM : W ≤ M := hesc.primeCore_le
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := hAH.trans (le_normalizer_glbPrimeCore 3 H)
  have hSM : A ⊔ W ≤ M := sup_le hAM hWM
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) hesc.card_A
  have hWcop : Nat.Coprime 3 (Nat.card W) := glbPrimeCore_coprime 3 H
  have hW3 : ¬ 3 ∣ Nat.card W := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hWcop
  have hAWbot : A ⊓ W = ⊥ := (Subgroup.disjoint_of_coprime_natCard
    (by rw [hesc.card_A]; exact Nat.Coprime.pow_left 2 hWcop)).eq_bot
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hAW
  rw [sup_comm, inf_comm, hAWbot, Subgroup.card_bot, mul_one, hesc.card_A] at hcard
  have hAidx : ¬ 3 ∣ (A.subgroupOf (A ⊔ W)).index := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf (A ⊔ W))
    have h2 : Nat.card (A.subgroupOf (A ⊔ W)) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [h2, hesc.card_A, hcard] at h1
    have h3 : (A.subgroupOf (A ⊔ W)).index = Nat.card W := by
      rw [mul_comm (Nat.card W)] at h1
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3 ^ 2) h1
    rw [h3]
    exact hW3
  obtain ⟨g, hgS, hgE⟩ := exists_conj_map_le_of_isPGroup (le_sup_left : A ≤ A ⊔ W) hAp hAidx hE
    hEp
  have hEA : E.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hgE (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE9, hesc.card_A])
  have hE' : E = A.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hEA, Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  rw [hE']
  exact glbCore_one_map_conj_le (M.inv_mem (hSM hgS)) hesc.core_A

theorem D2L34WeakConf3.eq_of_maxTwoLocal_of_cover27 [D2Amb3 G]
    (hw : D2L34WeakConf3 d P M A H R Rbar K) (hrk : D2NormRankTwo G M)
    (hAll : D2L34AllResidue3 P M)
    (hmax : ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' → Nat.card R' ≤ 27)
    (hO2 : pCoreOf 2 M ≤ H) {T : Subgroup G} (hNE : D2NonExtremalL34At P M T)
    {J : Subgroup G} (hJH : J ≤ H) (hJgen : J ≤ threePrimeResidual J) {E : Subgroup G}
    (hEJ : E ≤ J) (hEM : E ≤ M) (hEcore : GLBCore 3 1 E ≤ M) (hEel : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2)
    (hKJ : K ≤ (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hJN : J ≤ N)
    (hTN : Subgroup.normalizer (T : Set G) ≤ N) : N = H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  set πN := QuotientGroup.mk' (primeComplementCore (G := N) 3)
  set WH := GLBPrimeCore 3 H
  set WN := GLBPrimeCore 3 N
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) hEc
  have hErank : 2 ≤ Open.pRank 3 E := le_pRank_of_isElemAbelian Nat.prime_three hEel hEc
  have hfrH : ∀ h ∈ H, ∃ a ∈ J, ∃ b ∈ H ⊓ M, h = a * b :=
    exists_mul_of_l34 hw.l34 hw.almostSimple hw.iso hw.le_K hw.esc.primeCore_le hKJ
  have hNM : ¬ N ≤ M := by
    intro hle
    apply hw.esc.not_le
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrH h hh
    exact M.mul_mem (hle (hJN ha)) hb.2
  have hEN : E ≤ N := hEJ.trans hJN
  have hEpN : IsPGroup 3 (E.subgroupOf N) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEN).symm
  obtain ⟨T₀, hET⟩ := hEpN.exists_le_sylow
  set E₀ : Subgroup G := (T₀ : Subgroup N).map N.subtype
  have hEE₀ : E ≤ E₀ := fun a ha => ⟨⟨a, hEN ha⟩, hET (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hE₀p : IsPGroup 3 E₀ := T₀.isPGroup'.map N.subtype
  have hE₀M : E₀ ≤ M := le_of_pGroup_of_normRankTwo hrk hE₀p hEE₀ hEM hErank
  have hE₀N : E₀ ≤ N := Subgroup.map_subtype_le _
  have hrank₀ : Open.pRank 3 (N ⊓ M) ≤ 2 := by
    by_contra hlt
    exact hNM (D2Amb3.d1 (G := G) P M hw.esc.maxTwoLocal_M
      ((weakCore_le_fullCore 3 (P : Subgroup G)).trans hw.esc.core_le) N hN.1 (by omega))
  have hesc₀ : D2Escape 3 P M E N E₀ :=
    { prime := Nat.prime_three
      ne_two := by norm_num
      sylow_le := hw.esc.sylow_le
      core_le := hw.esc.core_le
      maxTwoLocal_M := hw.esc.maxTwoLocal_M
      maxTwoLocal_H := hN
      elem := hEel
      card_A := hEc
      core_A := hEcore
      A_le := hEE₀
      le_H := hE₀N
      le_M := hE₀M
      isSylow := ⟨T₀, rfl⟩
      pRank_eq := le_antisymm
        ((pRank_mono 3 Nat.prime_three (le_inf hE₀N hE₀M)).trans hrank₀)
        (hErank.trans (pRank_mono 3 Nat.prime_three hEE₀))
      not_le := hNM }
  obtain ⟨d₀, Rb₀, K₀, hd₀, hK₀, hi, hEK₀⟩ : ∃ (d₀ : TauCeti.ValidLieTypeIndex)
      (Rb₀ : Sylow 3 (N ⧸ primeComplementCore (G := N) 3))
      (K₀ : Subgroup (N ⧸ primeComplementCore (G := N) 3)), IsL34Index d₀ ∧
      D2AlmostSimple 3 (N ⧸ primeComplementCore (G := N) 3) Rb₀ ((E.subgroupOf N).map πN)
        (((N ⊓ M).subgroupOf N).map πN) K₀ ∧
      Nonempty (K₀ ≃* (TauCeti.CFSGIndex.lie d₀).Group) ∧ (E.subgroupOf N).map πN ≤ K₀ := by
    obtain ⟨n, hn⟩ := hE₀p.exists_card_eq
    have h9 : 3 ^ 2 ≤ 3 ^ n := by
      rw [← hn, ← hEc]
      exact Subgroup.card_le_of_le hEE₀
    have h27 : 3 ^ n ≤ 27 := by
      rw [← hn]
      exact hmax E N E₀ hesc₀
    have hn4 : n < 4 := by
      by_contra hlt
      have h81 : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hlt)
      norm_num at h81
      omega
    interval_cases n
    · norm_num at h9
    · norm_num at h9
    ·
      have hEeq : E = E₀ := Subgroup.eq_of_le_of_card_ge hEE₀ (by rw [hn, hEc])
      have hesc : D2Escape 3 P M E N E := by
        rw [← hEeq] at hesc₀
        exact hesc₀
      obtain ⟨Rb₀, K₀, hRb₀, hK₀⟩ := hesc.almostSimple (D2Amb3.glob (G := G))
      obtain ⟨d₀, hd₀, hi⟩ := hNE E N hesc hTN Rb₀ K₀ hRb₀ hK₀
      exact ⟨d₀, Rb₀, K₀, hd₀, hK₀, hi, hK₀.le_of_l34 kFactL34Outer hd₀ hi⟩
    ·
      have hmax₀ : D2EscapeMax 3 P M E₀ := fun A' H' R' h' =>
        (hmax A' H' R' h').trans (by rw [hn]; norm_num)
      obtain ⟨d₀, Rb₀, K₀, hc₀⟩ := hAll E N E₀ hesc₀ hmax₀
      exact ⟨d₀, Rb₀, K₀, hc₀.l34, hc₀.almostSimple, hc₀.iso, hc₀.le_K⟩
  have hK₀c : Nat.card K₀ = 20160 :=
    (kFactSmallThreeOrders K₀).2.1 (isLinThreeFour_of_l34Index hd₀ hi)
  have hKc : Nat.card K = 20160 :=
    (kFactSmallThreeOrders K).2.1 (isLinThreeFour_of_l34Index hw.l34 hw.iso)
  obtain ⟨L, hK₀L, hrelL, hL3⟩ :=
    l34_exists_le_of_pow_eq_one hd₀ hK₀.normal hK₀.centralizer_eq_bot hi
  have hJL : (J.subgroupOf N).map πN ≤ L := by
    have hJle : J ≤ (L.comap πN).map N.subtype := by
      refine hJgen.trans ?_
      rw [threePrimeResidual, Subgroup.closure_le]
      rintro x ⟨hxJ, k, hk⟩
      have hxN : x ∈ N := hJN hxJ
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      change πN ⟨x, hxN⟩ ∈ L
      have hpow : (πN ⟨x, hxN⟩) ^ 3 ^ k = 1 := by
        rw [← map_pow]
        have : (⟨x, hxN⟩ : N) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
        rw [this, map_one]
      exact hL3 _ k hpow
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hJle (Subgroup.mem_subgroupOf.mp hx)
    have : y = ⟨x, hxN⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  have hYbot : ((WN ⊓ J).subgroupOf H).map π = ⊥ := by
    apply D2AlmostSimple.eq_bot_of_le_normalizer hw.almostSimple
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
      have h4 : Nat.card (WN ⊓ J : Subgroup G) ∣ Nat.card WN :=
        Subgroup.card_dvd_of_le inf_le_left
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
  have hge : Nat.card K₀ ≤ Nat.card ((J.subgroupOf N).map πN) := by
    rw [hcardN, hK₀c]
    calc 20160 = Nat.card K := hKc.symm
      _ ≤ Nat.card ((J.subgroupOf H).map π) := Subgroup.card_le_of_le hKJ
      _ = WH.relIndex J := hcardH
      _ ≤ WN.relIndex J := hrel
  have hK₀J : K₀ ≤ (J.subgroupOf N).map πN :=
    le_of_relIndex_le_three hK₀.normal (isSimpleGroup_of_almostSimple hK₀)
      (by rw [hK₀c]; norm_num) hK₀L hJL hrelL hge
  have hfrN : ∀ n ∈ N, ∃ a ∈ J, ∃ b ∈ N ⊓ M, n = a * b :=
    exists_mul_of_l34 hd₀ hK₀ hi hEK₀ hesc₀.primeCore_le hK₀J
  have hα : ∀ h ∈ H, ∃ a ∈ H ⊓ N, ∃ b ∈ H ⊓ M, h = a * b := by
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrH h hh
    exact ⟨a, ⟨hJH ha, hJN ha⟩, b, hb, rfl⟩
  have hβ : ∀ n ∈ N, ∃ a ∈ H ⊓ N, ∃ b ∈ N ⊓ M, n = a * b := by
    intro n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := hfrN n hn
    exact ⟨a, ⟨hJH ha, hJN ha⟩, b, hb, rfl⟩
  exact L34Squeeze.eq_of_factorizations hw.esc.maxTwoLocal_H hN
    (le_normalizer_glbPrimeCore 3 H) hw.esc.primeCore_le
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    (hw.twoCore_inf_glbPrimeCore_ne_bot' hO2) hα hβ

theorem D2L34WeakConf3.eq_of_maxTwoLocal_of_normalizer_cover27 [D2Amb3 G]
    (hw : D2L34WeakConf3 d P M A H R Rbar K) (hrk : D2NormRankTwo G M)
    (hAll : D2L34AllResidue3 P M)
    (hmax : ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' → Nat.card R' ≤ 27)
    (hO2 : pCoreOf 2 M ≤ H) {T : Subgroup G} (hNE : D2NonExtremalL34At P M T) {C : Subgroup G}
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k)
    {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hNC : Subgroup.normalizer (C : Set G) ≤ N)
    (hTN : Subgroup.normalizer (T : Set G) ≤ N) : N = H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  set Y := H ⊓ Subgroup.normalizer (C : Set G)
  set J := threePrimeResidual Y
  set W := GLBPrimeCore 3 H
  set D := Y ⊓ (A ⊔ W)
  set Abar := (A.subgroupOf H).map π
  have hAH : A ≤ H := hw.esc.A_le.trans hw.esc.le_H
  have hAM : A ≤ M := hw.esc.A_le.trans hw.esc.le_M
  have hWH : W ≤ H := glbPrimeCore_le 3 H
  have hWM : W ≤ M := hw.esc.primeCore_le
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := le_normalizer_glbPrimeCore 3 H
  have hDH : D ≤ H := inf_le_left.trans inf_le_left
  have hJY : J ≤ Y := threePrimeResidual_le Y
  have hJH : J ≤ H := hJY.trans inf_le_left
  have hJN : J ≤ N := (hJY.trans inf_le_right).trans hNC
  have hAbar9 : Nat.card Abar = 3 ^ 2 := hw.almostSimple.card_A
  have hAbarE : IsElemAbelian 3 Abar := hw.almostSimple.elem
  have hAWmap : ∀ x (hx : x ∈ A ⊔ W), π ⟨x, (sup_le hAH hWH) hx⟩ ∈ Abar := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A W (hAH.trans hHW),
      Set.mem_mul] at hx
    obtain ⟨a, ha, w, hw', rfl⟩ := hx
    have e : (⟨a * w, (sup_le hAH hWH) (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right hw'))⟩ : H) = ⟨a, hAH ha⟩ * ⟨w, hWH hw'⟩ := rfl
    rw [e, map_mul, (mk'_primeComplementCore_eq_one_iff 3 ⟨w, hWH hw'⟩).mpr hw', mul_one]
    exact ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hAbarD : Abar ≤ (D.subgroupOf H).map π := by
    rintro _ ⟨⟨a', ha'H⟩, ha', rfl⟩
    obtain ⟨a, haY, haH, hae⟩ := hcov _ (hw.le_K ⟨⟨a', ha'H⟩, ha', rfl⟩)
    refine ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ⟨haY, ?_⟩, hae⟩
    have hw1 : π ((⟨a', ha'H⟩ : H)⁻¹ * ⟨a, haH⟩) = 1 := by
      rw [map_mul, map_inv, hae, inv_mul_cancel]
    have hwW := (mk'_primeComplementCore_eq_one_iff 3 _).mp hw1
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
            hEH _ (E.mul_mem (E.mul_mem (E.mul_mem hxE hyE) (E.inv_mem hxE)) (E.inv_mem hyE))⟩ :
              H) = ⟨x, hEH _ hxE⟩ * ⟨y, hEH _ hyE⟩ * (⟨x, hEH _ hxE⟩ : H)⁻¹ *
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
    have hbot := D2AlmostSimple.eq_bot_of_le_normalizer hw.almostSimple
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
  exact hw.eq_of_maxTwoLocal_of_cover27 hrk hAll hmax hO2 hNE hJH
    (threePrimeResidual_le_threePrimeResidual_self Y) hEJ hEM
    (core_one_le_of_le_sup_of_escape hw.esc (fun x hx => hEAW x hx) hEp hEc) hEel hEc hKJ hN hJN
    hTN

theorem D2L34WeakConf3.normalizer_le_of_cover27 [D2Amb3 G]
    (hw : D2L34WeakConf3 d P M A H R Rbar K) (hrk : D2NormRankTwo G M)
    (hAll : D2L34AllResidue3 P M)
    (hmax : ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' → Nat.card R' ≤ 27)
    (hO2 : pCoreOf 2 M ≤ H) {T : Subgroup G} (hNE : D2NonExtremalL34At P M T) {C : Subgroup G}
    (hC1 : C ≠ ⊥) (hCp : IsPGroup 2 C)
    (hTC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G))
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (C : Set G) ≤ H := by
  obtain ⟨N, hNC, hN⟩ := exists_maximal_twoLocal
    (⟨C, hC1, hCp, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C : Set G)))
  exact hNC.trans (hw.eq_of_maxTwoLocal_of_normalizer_cover27 hrk hAll hmax hO2 hNE hcov hN hNC
    (hTC.trans hNC)).le

theorem D2L34BetaConf3.pCoreOf_two_le (hc : D2L34BetaConf3 d P M A H R Rbar K) :
    pCoreOf 2 M ≤ H :=
  (pCoreOf_two_le_of_normalizer_le (hc.normalizer_eq.le.trans inf_le_left)).trans
    ((RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left)

theorem D2L34BetaConf3.not_normalizer_le_of_isSylowTwoOf'
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {T : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) : ¬ Subgroup.normalizer (T : Set G) ≤ M := by
  intro hNM
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAM : A ≤ M := hc.esc.A_le.trans hc.esc.le_M
  have hcov := hc.cover_of_isSylowTwoOf_of_map_eq hT (B := A) (Y := H ⊓ M) rfl hT.1
    (le_inf hAH hAM) (inf_le_inf_left H hNM)
  apply hc.almostSimple.not_le
  intro k hk
  obtain ⟨a, ha, haH, rfl⟩ := hcov k hk
  exact ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩

theorem D2L34SideCtx3.isSylowTwoOf_of_card27
    (hFF : CitedFFL34BestOffender) (ctx : D2L34SideCtx3 G d P M A H R Rbar K)
    (h27 : Nat.card R = 27) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M))
    (hNE : D2NonExtremalL34At P M T) :
    IsSylowTwoOf T M ∧ Subgroup.normalizer (T : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := ctx.amb
  obtain ⟨C, hCT, hC1, hchar, hcovC⟩ := ctx.conf.exists_char_cover_syl' hFF hT
  have hTC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := T) (C.subgroupOf T)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCT] at h1
  have hNT : Subgroup.normalizer (T : Set G) ≤ H :=
    hTC.trans (ctx.conf.toWeak.normalizer_le_of_cover27 ctx.normRankTwo ctx.allResidue
      (ctx.conf.card_le_27 h27) ctx.conf.pCoreOf_two_le hNE hC1 (hT.2.1.to_le hCT) hTC hcovC)
  refine ⟨?_, hNT⟩
  have hTM : T ≤ M := hT.1.trans inf_le_right
  obtain ⟨S, hTS, hS⟩ := exists_isSylowTwoOf_of_le hTM hT.2.1
  have hST : S ≤ T := by
    refine CFSG.AGLEmbeddingD2.le_of_normalizer_inf_le hS.2.1 ?_
    rw [inf_of_le_right hTS]
    have hle : S ⊓ Subgroup.normalizer (T : Set G) ≤ H ⊓ M :=
      le_inf (inf_le_right.trans hNT) (inf_le_left.trans hS.1)
    exact (hT.eq_of_le (le_inf hTS Subgroup.le_normalizer) hle (hS.2.1.to_le inf_le_left)).le
  rwa [le_antisymm hST hTS] at hS

end CFSG.LocalAnalysis.RankThreeTheoremC
