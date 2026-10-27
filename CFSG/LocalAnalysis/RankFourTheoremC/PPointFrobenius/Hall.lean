module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CentC
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Borel
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Solvable0
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.LocalAnalysis.RankThreeTheoremC.FPFSolvableProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5OddSolv

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_primeCore_solvable [Fact p.Prime] (hEv :
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactCoprimeAutEvenCentralizer)
    (hG : FrobGlobal G) (hl : FrobLocal p P M x) :
    Group.IsSolvable ↥(CFSG.Open.GLBPrimeCore p M) := by
  have hp2 : p ≠ 2 := by have := hl.p5; omega
  have hxM : x ∈ M := hl.point.elem.1
  refine CFSG.LocalAnalysis.RankThreeTheoremC.oddCentralizerSolvable_holds hEv hp2
    (X := CFSG.Open.GLBPrimeCore p M) (x := x)
    (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M hxM) ?_
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp (CFSG.AGLEmbedding.glbPrimeCore_coprime p M))
    (Nat.odd_iff.mpr (by have := fr_primeCore_inf_centralizer_odd hG hl; omega)) ?_
  · have := hl.point.elem.2.1
    rw [← this]
    exact pow_orderOf_eq_one x
  · exact CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hG.kProper _
      (ne_top_of_le_ne_top (fr_M_ne_top hl) (CFSG.AGLEmbedding.glbPrimeCore_le p M))


theorem fr_primeCore_eq_sup [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    (hsolv : Group.IsSolvable ↥(CFSG.Open.GLBPrimeCore p M)) :
    CFSG.Open.GLBPrimeCore p M =
      CFSG.Open.pCoreOf 2 M ⊔ (CFSG.Open.GLBPrimeCore p M ⊓ centralizer ({x} : Set G)) := by
  have hp2 : p ≠ 2 := by have := hl.p5; omega
  have hM2 : CFSG.Open.IsTwoLocal M := hl.loc.maxLocal.1
  have hxM : x ∈ M := hl.point.elem.1
  have hxo : orderOf x = p := hl.point.elem.2.1
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    have := hl.p5
    omega
  have hNM : CFSG.Open.GLBPrimeCore p M ≤ M := CFSG.AGLEmbedding.glbPrimeCore_le p M
  have hMN : M ≤ normalizer ((CFSG.Open.GLBPrimeCore p M : Subgroup G) : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M
  have hNcop : Nat.Coprime p (Nat.card ↥(CFSG.Open.GLBPrimeCore p M)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p M
  have hT2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hTN : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.GLBPrimeCore p M :=
    CFSG.LocalAnalysis.RankThreeTheoremC.pCoreOf_two_le_rankThreePrimeCore Fact.out hp2 M
  have hMT : M ≤ normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hNT : CFSG.Open.GLBPrimeCore p M ≤ normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) :=
    hNM.trans hMT
  have hC : CFSG.Open.GLBPrimeCore p M ⊓ centralizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G)
      ≤ CFSG.Open.pCoreOf 2 M :=
    fun n hn => hG.charTwo M hM2 ⟨hNM hn.1, hn.2⟩
  have hO2 : ∀ W : Subgroup G, W ≤ CFSG.Open.GLBPrimeCore p M → IsPGroup 2 W →
      CFSG.Open.GLBPrimeCore p M ≤ normalizer (W : Set G) → W ≤ CFSG.Open.pCoreOf 2 M := by
    intro W hWN hW2 hNW
    have h1 : W ≤ CFSG.Open.pCoreOf 2 (CFSG.Open.GLBPrimeCore p M) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWN hNW hW2
    have h2 : CFSG.Open.pCoreOf 2 (CFSG.Open.GLBPrimeCore p M) ≤ CFSG.Open.pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hNM)
        (hMN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact h1.trans h2
  have hfpf : ∀ t ∈ CFSG.Open.pCoreOf 2 M, x * t = t * x → t = 1 := by
    intro t ht htx
    have : t ∈ CFSG.Open.pCoreOf 2 M ⊓ centralizer ({x} : Set G) :=
      ⟨ht, Subgroup.mem_centralizer_singleton_iff.mpr htx.symm⟩
    rw [fr_pCore_inf_centralizer_eq_bot hG hl] at this
    exact Subgroup.mem_bot.mp this
  have hcomm := CFSG.LocalAnalysis.RankThreeTheoremC.fpfSolvable G p (CFSG.Open.pCoreOf 2 M)
    (CFSG.Open.GLBPrimeCore p M) x hT2 hTN hsolv hNT hC hO2
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hNcop) hxp hx1 (hMN hxM) (hMT hxM) hfpf
  apply le_antisymm
  · intro n hn
    obtain ⟨s, hsT, hsn⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_mul_mem_inf_centralizer_of_fpf
      hTN (hMT hxM) hfpf hcomm hn
    have hn' : n = s⁻¹ * (s * n) := by group
    rw [hn']
    exact Subgroup.mul_mem_sup ((CFSG.Open.pCoreOf 2 M).inv_mem hsT) hsn
  · exact sup_le hTN inf_le_left


open CFSG.RankThreeCoreUniqueness.Helpers in
theorem fr_M_solvable [Fact p.Prime]
    (hEv : CFSG.LocalAnalysis.RankThreeTheoremC.KFactCoprimeAutEvenCentralizer)
    (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    (hlayer : CFSG.layer (M ⧸ primeComplementCore (G := M) p) = ⊥) : Group.IsSolvable M := by
  have hPM : (P : Subgroup G) ≤ M := CFSG.LocalAnalysis.RankFourTheoremC.sylow_le_of_core hl.loc
  have hO : Group.IsSolvable (CFSG.Open.GLBPrimeCore p M) := fr_primeCore_solvable hEv hG hl
  have hO' : Group.IsSolvable (primeComplementCore (G := M) p) := by
    have hO2 : Group.IsSolvable (CFSG.Open.rankThreePrimeCore p M) := hO
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.rankThreePrimeCore_eq_map_primeComplementCore] at hO2
    exact Group.isSolvable_of_isSolvable_injective
      (f := ((primeComplementCore (G := M) p).equivMapOfInjective M.subtype
        M.subtype_injective).toMonoidHom) (MulEquiv.injective _)
  refine CFSG.LocalAnalysis.RankThreeTheoremC.isSolvable_of_layer_quotient_eq_bot hO' hlayer
    (CFSG.LocalAnalysis.RankThreeTheoremC.isMulCommutative_sylow_quotient (fr_pGroup_abelian hl))
    (P.subtype hPM) ?_
  have hmap : (normalizer (((P.subtype hPM : Sylow p M) : Subgroup M) : Set M)).map M.subtype ≤
      M ⊓ normalizer ((layerOf x : Subgroup G) : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n.2, fr_normalizer_sylow_le hG hl ?_⟩
    have h := Subgroup.le_normalizer_map M.subtype ⟨n, hn, rfl⟩
    rwa [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPM] at h
  have hN := fr_solvable_inf_normalizer hG hl
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.inclusion hmap).comp
      ((normalizer _).equivMapOfInjective M.subtype M.subtype_injective).toMonoidHom)
    ((Subgroup.inclusion_injective hmap).comp (MulEquiv.injective _))

open CFSG.Open in
theorem frobConclusion_of_pieces [Fact p.Prime] (hp5 : 5 ≤ p) {M : Subgroup G} {x : G}
    (hM2 : IsTwoLocal M) (hxM : x ∈ M) (hxo : orderOf x = p)
    (hsolv : Group.IsSolvable M)
    (hF : GLBPrimeCore p M = pCoreOf 2 M ⊔ GLBPrimeCore p (centralizer ({x} : Set G)))
    (hodd : ¬ 2 ∣ Nat.card ↥(GLBPrimeCore p (centralizer ({x} : Set G))))
    (hCx : pCoreOf 2 M ⊓ centralizer ({x} : Set G) = ⊥)
    (hfpf : ∀ f ∈ GLBPrimeCore p (centralizer ({x} : Set G)), f ≠ 1 →
      ∀ t ∈ pCoreOf 2 M, t * f = f * t → t = 1) :
    FrobConclusion p M x := by
  have hzC : centralizer ((zpowers x : Subgroup G) : Set G) = centralizer ({x} : Set G) := by
    rw [zpowers_eq_closure, Subgroup.centralizer_closure]
  refine ⟨hsolv, ?_⟩
  rw [hzC]
  set C : Subgroup G := centralizer ({x} : Set G) with hCdef
  set T : Subgroup G := pCoreOf 2 M with hTdef
  set F₀ : Subgroup G := GLBPrimeCore p C with hF₀def
  set F : Subgroup G := GLBPrimeCore p M with hFdef
  have hp2 : p ≠ 2 := by omega
  have hpodd : ¬ 2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h).symm
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    omega
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hF₀C : F₀ ≤ C := CFSG.AGLEmbedding.glbPrimeCore_le p C
  have hCN : C ≤ normalizer (F₀ : Set G) := CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p C
  have hF₀cop : p.Coprime (Nat.card ↥F₀) := CFSG.AGLEmbedding.glbPrimeCore_coprime p C
  have hFM : F ≤ M := CFSG.AGLEmbedding.glbPrimeCore_le p M
  have hTF : T ≤ F :=
    CFSG.LocalAnalysis.RankThreeTheoremC.pCoreOf_two_le_rankThreePrimeCore Fact.out hp2 M
  have hTM : M ≤ normalizer (T : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hT2 : IsPGroup 2 T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hF₀F : F₀ ≤ F := hF ▸ le_sup_right
  have hcomm : ∀ f ∈ F₀, ∀ i : ℤ, f * x ^ i = x ^ i * f := fun f hf i =>
    (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hF₀C hf)) i)
  have hprod : ∀ v ∈ F₀ ⊔ zpowers x, ∃ f ∈ F₀, ∃ i : ℤ, v = f * x ^ i := by
    intro v hv
    have hx_le : zpowers x ≤ normalizer (F₀ : Set G) := zpowers_le.mpr (hCN hxC)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left F₀ (zpowers x) hx_le] at hv
    obtain ⟨f, hf, z, hz, rfl⟩ := hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hz
    exact ⟨f, hf, i, rfl⟩
  have hfN : ∀ f ∈ F₀, f ^ Nat.card ↥F₀ = 1 := fun f hf =>
    orderOf_dvd_iff_pow_eq_one.mp (by simpa using Subgroup.orderOf_dvd_natCard F₀ hf)
  have hxip : ∀ i : ℤ, (x ^ i) ^ p = 1 := fun i => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hN2 : ¬ 2 ∣ Nat.card ↥F₀ * p := fun h => by
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    · exact hodd h
    · exact hpodd h
  have hKV : T ⊓ (F₀ ⊔ zpowers x) = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨htT, htV⟩
    obtain ⟨f, hf, i, rfl⟩ := hprod t htV
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨f * x ^ i, htT⟩
    have hk' : orderOf (f * x ^ i) = 2 ^ k := by simpa using hk
    have hc : Commute f (x ^ i) := hcomm f hf i
    have hpow : (f * x ^ i) ^ (Nat.card ↥F₀ * p) = 1 := by
      rw [hc.mul_pow, pow_mul, hfN f hf, one_pow, pow_mul', hxip i, one_pow, mul_one]
    have hdvd : 2 ^ k ∣ Nat.card ↥F₀ * p := hk' ▸ orderOf_dvd_of_pow_eq_one hpow
    have hk0 : k = 0 := by
      by_contra hne
      exact hN2 (dvd_trans (dvd_pow_self 2 hne) hdvd)
    rw [hk0, pow_zero] at hk'
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hk')
  have hfpfV : ∀ v ∈ F₀ ⊔ zpowers x, v ≠ 1 → ∀ k ∈ T, k * v = v * k → k = 1 := by
    intro v hv hv1 k hkT hkv
    obtain ⟨f, hf, i, rfl⟩ := hprod v hv
    by_cases hxi : x ^ i = 1
    · have hf1 : f ≠ 1 := by
        intro h
        apply hv1
        rw [h, hxi, mul_one]
      rw [hxi, mul_one] at hkv
      exact hfpf f hf hf1 k hkT hkv
    · have hc : Commute f (x ^ i) := hcomm f hf i
      have hvN : (f * x ^ i) ^ Nat.card ↥F₀ = (x ^ i) ^ Nat.card ↥F₀ := by
        rw [hc.mul_pow, hfN f hf, one_mul]
      have hkvN : k * (x ^ i) ^ Nat.card ↥F₀ = (x ^ i) ^ Nat.card ↥F₀ * k := by
        have h1 : Commute k (f * x ^ i) := hkv
        rw [← hvN]
        exact h1.pow_right _
      set y : G := (x ^ i) ^ Nat.card ↥F₀ with hy
      have hy_mem : y ∈ zpowers x := Subgroup.pow_mem _ (zpow_mem (mem_zpowers x) i) _
      have hy1 : y ≠ 1 := by
        intro h
        apply hxi
        have h1 : x ^ (i * (Nat.card ↥F₀ : ℤ)) = 1 := by
          rw [zpow_mul, zpow_natCast]; exact h
        have h2 : (p : ℤ) ∣ i * (Nat.card ↥F₀ : ℤ) := by
          have := orderOf_dvd_iff_zpow_eq_one.mpr h1
          rwa [hxo] at this
        have hcop : IsCoprime (p : ℤ) (Nat.card ↥F₀ : ℤ) := Nat.isCoprime_iff_coprime.mpr hF₀cop
        exact orderOf_dvd_iff_zpow_eq_one.mp (by rw [hxo]; exact hcop.dvd_of_dvd_mul_right h2)
      have hyp : y ^ p = 1 := by
        rw [hy, ← pow_mul, mul_comm, pow_mul, hxip i, one_pow]
      have hyo : orderOf y = p := orderOf_eq_prime hyp hy1
      have hzy : zpowers y = zpowers x :=
        Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hy_mem)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hxo])
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hzy ▸ mem_zpowers x : x ∈ zpowers y)
      have hkx : k * x = x * k := by
        have h1 : Commute k y := hkvN
        have := h1.zpow_right j
        rw [hj] at this
        exact this
      have hkT' : k ∈ T ⊓ C := ⟨hkT, mem_centralizer_singleton_iff.mpr hkx⟩
      rw [hCx] at hkT'
      exact Subgroup.mem_bot.mp hkT'
  have hTne : T ≠ ⊥ := CFSG.LocalAnalysis.RankThreeTheoremC.pCoreOf_two_ne_bot hM2
  have hVne : F₀ ⊔ zpowers x ≠ ⊥ := by
    intro h
    have : x ∈ F₀ ⊔ zpowers x := Subgroup.mem_sup_right (mem_zpowers x)
    rw [h] at this
    exact hx1 (Subgroup.mem_bot.mp this)
  have hTR : T ≤ F ⊔ zpowers x := hTF.trans le_sup_left
  refine ⟨hTne, hVne, hTR, ?_, sup_le_sup_right hF₀F _, ?_, hKV, hfpfV⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTR]
    exact sup_le (hFM.trans hTM) (zpowers_le.mpr (hTM hxM))
  · rw [hF, sup_assoc]

theorem fr_primeCore_centralizer_le_M [Fact p.Prime] (hl : FrobLocal p P M x) :
    CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G)) ≤ M :=
  CFSG.PreuniquenessRankFour.Helpers.intersecting_local_primeCore_le p hl.loc.beta.1 P
    (CFSG.LocalAnalysis.RankFourTheoremC.sylow_le_of_core hl.loc) hl.loc.core
    (by rw [inf_comm]; exact hl.point.elem.2.2.1)

open CFSG.RankThreeCoreUniqueness.Helpers in
theorem fr_F0_le_F [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    (hlayer : CFSG.layer (M ⧸ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := M) p) = ⊥) :
    CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G)) ≤ CFSG.Open.GLBPrimeCore p M := by
  set R : Subgroup G := CFSG.Open.GLBPrimeCore p (centralizer ({x} : Set G)) with hRdef
  have hRM : R ≤ M := fr_primeCore_centralizer_le_M hl
  have hPM : (P : Subgroup G) ≤ M := CFSG.LocalAnalysis.RankFourTheoremC.sylow_le_of_core hl.loc
  have hPC : (P : Subgroup G) ≤ normalizer (R : Set G) :=
    (fr_P_le_centralizer hl).trans
      (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p (centralizer ({x} : Set G)))
  have hRp : Nat.Coprime p (Nat.card R) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p (centralizer ({x} : Set G))
  set O := primeComplementCore (G := M) p with hOdef
  have hcore : primeComplementCore (G := M ⧸ O) p = ⊥ := primeComplementCore_quotient_eq_bot p
  have hchar : centralizer (CFSG.pCore p (M ⧸ O) : Set (M ⧸ O)) ≤ CFSG.pCore p (M ⧸ O) :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot (M ⧸ O) p hcore hlayer
  have hQS : CFSG.pCore p (M ⧸ O) ≤ ((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' O) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal
      ((P.subtype hPM).mapSurjective (QuotientGroup.mk'_surjective O))
  set Rbar : Subgroup (M ⧸ O) := (R.subgroupOf M).map (QuotientGroup.mk' O) with hRbar
  have hnorm : ((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' O) ≤
      normalizer ((Rbar : Subgroup (M ⧸ O)) : Set (M ⧸ O)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.map_subgroupOf_le_normalizer_map (N := M) hPC
      (QuotientGroup.mk' O)
  have hQnorm : ∀ q ∈ CFSG.pCore p (M ⧸ O), ∀ r ∈ Rbar, q * r * q⁻¹ ∈ Rbar := by
    intro q hq r hr
    have hqN : q ∈ normalizer ((Rbar : Subgroup (M ⧸ O)) : Set (M ⧸ O)) := hnorm (hQS hq)
    exact (Subgroup.mem_normalizer_iff.mp hqN r).mp hr
  have hRbar_dvd : Nat.card Rbar ∣ Nat.card R := by
    have h1 : Nat.card Rbar ∣ Nat.card (R.subgroupOf M) :=
      Subgroup.card_map_dvd (H := R.subgroupOf M) (f := QuotientGroup.mk' O)
    have h2 : Nat.card (R.subgroupOf M) = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv
    rw [← h2]
    exact h1
  have hRbar_cop : Nat.Coprime p (Nat.card Rbar) := hRp.coprime_dvd_right hRbar_dvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := p) (G := M ⧸ O))
  have hcopQ : Nat.Coprime (Nat.card Rbar) (Nat.card (CFSG.pCore p (M ⧸ O) : Subgroup (M ⧸ O))) := by
    rw [hn]
    exact Nat.Coprime.pow_right n hRbar_cop.symm
  have hdisj : Disjoint Rbar (CFSG.pCore p (M ⧸ O)) := Subgroup.disjoint_of_coprime_natCard hcopQ
  have hinf : Rbar ⊓ CFSG.pCore p (M ⧸ O) = ⊥ := disjoint_iff.mp hdisj
  have hcomm : ∀ q ∈ CFSG.pCore p (M ⧸ O), ∀ r ∈ Rbar, q * r = r * q := by
    intro q hq r hr
    have hc1 : q * r * q⁻¹ * r⁻¹ ∈ Rbar := Rbar.mul_mem (hQnorm q hq r hr) (Rbar.inv_mem hr)
    have hc2 : q * r * q⁻¹ * r⁻¹ ∈ CFSG.pCore p (M ⧸ O) := by
      have hconj : r * q⁻¹ * r⁻¹ ∈ CFSG.pCore p (M ⧸ O) :=
        (CFSG.pCore_normal (p := p) (G := M ⧸ O)).conj_mem q⁻¹
          ((CFSG.pCore p (M ⧸ O)).inv_mem hq) r
      have e : q * r * q⁻¹ * r⁻¹ = q * (r * q⁻¹ * r⁻¹) := by group
      rw [e]
      exact (CFSG.pCore p (M ⧸ O)).mul_mem hq hconj
    have h1 : q * r * q⁻¹ * r⁻¹ = 1 := by
      have hmem : q * r * q⁻¹ * r⁻¹ ∈ Rbar ⊓ CFSG.pCore p (M ⧸ O) := ⟨hc1, hc2⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    calc q * r = q * r * q⁻¹ * r⁻¹ * (r * q) := by group
      _ = r * q := by rw [h1, one_mul]
  have hRQ : Rbar ≤ CFSG.pCore p (M ⧸ O) := by
    intro r hr
    refine hchar ?_
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hcomm q hq r hr
  have hRbot : Rbar = ⊥ := by
    have h := hinf
    rwa [inf_eq_left.mpr hRQ] at h
  exact CFSG.LocalAnalysis.RankThreeTheoremC.le_rankThreePrimeCore_of_map_mk_eq_bot (p := p)
    hRM hRbot

open CFSG.Open in
theorem frobConclusion_of_parts [Fact p.Prime]
    (hEv : CFSG.LocalAnalysis.RankThreeTheoremC.KFactCoprimeAutEvenCentralizer)
    (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    (hlayer : CFSG.layer (M ⧸ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := M) p) = ⊥)
    (hfpf : ∀ f ∈ GLBPrimeCore p (centralizer ({x} : Set G)), f ≠ 1 →
      ∀ t ∈ pCoreOf 2 M, t * f = f * t → t = 1) :
    FrobConclusion p M x := by
  have hsolv : Group.IsSolvable M := fr_M_solvable hEv hG hl hlayer
  have hFsolv : Group.IsSolvable ↥(GLBPrimeCore p M) := fr_primeCore_solvable hEv hG hl
  have h1 := fr_primeCore_eq_sup hG hl hFsolv
  have h2 : GLBPrimeCore p M ⊓ centralizer ({x} : Set G) =
      GLBPrimeCore p (centralizer ({x} : Set G)) :=
    le_antisymm (fr_primeCore_inf_centralizer_le hG hl)
      (le_inf (fr_F0_le_F hG hl hlayer) (CFSG.AGLEmbedding.glbPrimeCore_le p _))
  rw [h2] at h1
  exact frobConclusion_of_pieces hl.p5 hl.loc.maxLocal.1 hl.point.elem.1 hl.point.elem.2.1 hsolv h1
    (fr_primeCore_centralizer_odd hG hl) (fr_pCore_inf_centralizer_eq_bot hG hl) hfpf

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
