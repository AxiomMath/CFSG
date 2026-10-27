module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGStep5
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Sylow
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ

open CFSG.Open CFSG.GH74.Uniqueness.SU CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGB Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LocalAnalysis.RankThreeTheoremC (IsMaxTwoInvariantIn)

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem exists_mem_normalizer_not_mem_of_lt {r : ℕ} [Fact r.Prime] {X T : Subgroup A}
    (hT : IsPGroup r T) (hXT : X < T) :
    ∃ x ∈ T, x ∈ normalizer (X : Set A) ∧ x ∉ X := by
  have hne : X.subgroupOf T ≠ ⊤ := fun htop =>
    absurd (fun x hxT => (Subgroup.mem_subgroupOf.mp (htop ▸ trivial : (⟨x, hxT⟩ : T) ∈
      X.subgroupOf T))) (not_le_of_gt hXT)
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  have hlt : X.subgroupOf T < Subgroup.normalizer ((X.subgroupOf T : Subgroup T) : Set T) :=
    hnc _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, ?_, fun hxA => hxnot (Subgroup.mem_subgroupOf.mpr hxA)⟩
  have hxsub : x ∈ (Subgroup.normalizer (X : Set A)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hXT.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem normalizer_le_normalizer_primeCore (r : ℕ) (K : Subgroup A) :
    normalizer (K : Set A) ≤ normalizer (rankThreePrimeCore r K : Set A) := by
  have : (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := K) r).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_characteristic r
  show normalizer (K : Set A) ≤ normalizer (GLBPrimeCore r K : Set A)
  rw [CFSG.AGLEmbedding.glbPrimeCore_eq_primeComplementCoreOf]
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem S_le_normalizer_inf (c : KQCfg A p Kb Sb Bb Mb z) :
    Sb ≤ normalizer ((Sb ⊓ Kb : Subgroup A) : Set A) :=
  fun s hs => mem_normalizer_inf' (Subgroup.le_normalizer hs) (c.S_le_K hs)

theorem B_le_normalizer_inf (c : KQCfg A p Kb Sb Bb Mb z) :
    Bb ≤ normalizer ((Sb ⊓ Kb : Subgroup A) : Set A) :=
  fun b hb => mem_normalizer_inf' (c.B_le_S hb) (c.B_le_K hb)

theorem normalizer_inf_le (c : KQCfg A p Kb Sb Bb Mb z) (hne : Sb ⊓ Kb ≠ ⊥) :
    normalizer ((Sb ⊓ Kb : Subgroup A) : Set A) ≤ Mb :=
  c.cover (Sb ⊓ Kb) inf_le_left hne (S_le_normalizer_inf c) (B_le_normalizer_inf c)

theorem pCoreOf_le_inf (c : KQCfg A p Kb Sb Bb Mb z) :
    pCoreOf 2 (normalizer ((Sb ⊓ Kb : Subgroup A) : Set A) ⊓ Kb) ≤ Sb ⊓ Kb := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K0 : Subgroup A := normalizer ((Sb ⊓ Kb : Subgroup A) : Set A) ⊓ Kb with hK0
  set R : Subgroup A := pCoreOf 2 K0 with hR
  have hSK0 : Sb ≤ normalizer (K0 : Set A) := fun s hs =>
    mem_normalizer_inf' (Subgroup.le_normalizer (S_le_normalizer_inf c hs)) (c.S_le_K hs)
  have hBK0 : Bb ≤ normalizer (K0 : Set A) := fun b hb =>
    mem_normalizer_inf' (Subgroup.le_normalizer (B_le_normalizer_inf c hb)) (c.B_le_K hb)
  have hSR : Sb ≤ normalizer (R : Set A) := fun s hs =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K0 (hSK0 hs)
  have hBR : Bb ≤ normalizer (R : Set A) := fun b hb =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K0 (hBK0 hb)
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K0
  have hRS2 : IsPGroup 2 ↥(R ⊔ Sb) := hR2.to_sup_of_normal_left' c.S_two hSR
  have hBRS : Bb ≤ normalizer ((R ⊔ Sb : Subgroup A) : Set A) := fun b hb =>
    mem_normalizer_sup' (hBR hb) (c.B_le_S hb)
  have hRSeq : R ⊔ Sb = Sb := c.max_S (R ⊔ Sb) hRS2 hBRS le_sup_right
  have hRS : R ≤ Sb := hRSeq ▸ le_sup_left
  exact le_inf hRS ((CFSG.LieType.BorelTits.pCoreOf_le 2 K0).trans inf_le_right)

theorem isParabolicTwo_inf (c : KQCfg A p Kb Sb Bb Mb z) (hchev : IsChevSimple 2 ↥Kb)
    (h131 : KFact131) (hne : Sb ⊓ Kb ≠ ⊥) : IsParabolicTwo A Kb (Kb ⊓ Mb) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup A := Sb ⊓ Kb with hT
  set K0 : Subgroup A := normalizer (T : Set A) ⊓ Kb with hK0
  have hT2 : IsPGroup 2 T := c.S_two.to_le inf_le_left
  obtain ⟨P, hpar, hTO, hNP⟩ := h131 A Kb T hchev inf_le_right hT2 hne
  set O : Subgroup A := pCoreOf 2 P with hO
  have hPK : P ≤ Kb := hpar.1
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hOP : O ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hPO : P ≤ normalizer (O : Set A) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hOT : O = T := by
    by_contra hne'
    have hlt : T < O := lt_of_le_of_ne hTO (Ne.symm hne')
    obtain ⟨x, hxO, hxN, hxT⟩ := exists_mem_normalizer_not_mem_of_lt hO2 hlt
    have hxK0 : x ∈ K0 := ⟨hxN, hPK (hOP hxO)⟩
    have hOK0 : O ⊓ K0 ≤ pCoreOf 2 K0 := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
        (hO2.to_le inf_le_left)
      intro k hk
      exact mem_normalizer_inf' (hPO (hNP hk)) (Subgroup.le_normalizer hk)
    exact hxT (pCoreOf_le_inf c (hOK0 ⟨hxO, hxK0⟩))
  have hPN : P ≤ normalizer (T : Set A) := hOT ▸ hPO
  have hNT : normalizer (T : Set A) ≤ Mb := normalizer_inf_le c hne
  obtain ⟨U, hU, hUP⟩ := hpar.2
  exact ⟨inf_le_left, U, hU, fun u hu => ⟨hu.2, hNT (hPN (hUP hu))⟩⟩

theorem isSylowOf_inf_primeCore (c : KQCfg A p Kb Sb Bb Mb z) :
    CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ rankThreePrimeCore p (Kb ⊓ Mb))
      (rankThreePrimeCore p (Kb ⊓ Mb)) := by
  have hp := c.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := c.five_le; omega
  set K₀ : Subgroup A := Kb ⊓ Mb with hK₀
  set D : Subgroup A := rankThreePrimeCore p K₀ with hD
  obtain ⟨-, -, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p K₀
  have hpD : ¬ p ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have hSK₀ : Sb ≤ normalizer (K₀ : Set A) := fun s hs =>
    mem_normalizer_inf' (c.S_le_K hs) (Subgroup.le_normalizer (S_le_M c hs))
  have hBK₀ : Bb ≤ normalizer (K₀ : Set A) := fun b hb =>
    mem_normalizer_inf' (c.B_le_K hb) (Subgroup.le_normalizer (B_le_M c hb))
  have hSD : Sb ≤ normalizer (D : Set A) := hSK₀.trans (normalizer_le_normalizer_primeCore p K₀)
  have hBD : Bb ≤ normalizer (D : Set A) := hBK₀.trans (normalizer_le_normalizer_primeCore p K₀)
  have hDH : D ≤ normalizer (D : Set A) := Subgroup.le_normalizer
  have hDn : (D.subgroupOf (normalizer (D : Set A))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDH).mpr le_rfl
  have hmax : IsMaxTwoInvariantIn Bb (normalizer (D : Set A)) Sb := by
    refine ⟨⟨hSD, c.S_two, c.B_le_S⟩, fun S' hS' hSS' => ?_⟩
    exact c.max_S S' hS'.2.1 hS'.2.2 hSS'
  exact s622_isSylowOf_inf hp hp2 (CFSG.Open.IsElemAbelian.isPGroup c.B_elem) hDH hDn hpD hBD hmax

theorem not_le_primeCore_of_not_sylow (c : KQCfg A p Kb Sb Bb Mb z) (hchev : IsChevSimple 2 ↥Kb)
    (h131 : KFact131) (hne : Sb ⊓ Kb ≠ ⊥)
    (hns : ¬ CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ Kb) Kb) :
    ∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U (Kb ⊓ Mb) →
      ¬ U ≤ rankThreePrimeCore p (Kb ⊓ Mb) := by
  haveI : Fact p.Prime := ⟨c.prime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro U hU hUD
  set K₀ : Subgroup A := Kb ⊓ Mb with hK₀
  obtain ⟨hDK₀, -, -⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p K₀
  have hW1 := isSylowOf_inf_primeCore c
  have hUD' := hU.of_le hUD hDK₀
  have hcardW1 : Nat.card ↥(Sb ⊓ rankThreePrimeCore p K₀) = Nat.card U := by
    rw [hW1.card_eq, hUD'.card_eq]
  obtain ⟨U₁, hU₁, hU₁N⟩ := (isParabolicTwo_inf c hchev h131 hne).2
  have hU₁K₀ : U₁ ≤ K₀ := fun u hu => hU₁N ⟨Subgroup.le_normalizer hu, hU₁.le hu⟩
  have hU₁K₀syl := hU₁.of_le hU₁K₀ inf_le_left
  have hcardU₁ : Nat.card U₁ = Nat.card U := by rw [hU₁K₀syl.card_eq, hU.card_eq]
  have hSDK : CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ rankThreePrimeCore p K₀) Kb :=
    CFSG.ABGLocalTools.isSylowOf_of_card (inf_le_right.trans (hDK₀.trans inf_le_left))
      (by rw [hcardW1, ← hcardU₁, hU₁.card_eq])
  have hSDW : Sb ⊓ rankThreePrimeCore p K₀ ≤ Sb ⊓ Kb :=
    le_inf inf_le_left (inf_le_right.trans (hDK₀.trans inf_le_left))
  have hWeq : Sb ⊓ Kb = Sb ⊓ rankThreePrimeCore p K₀ :=
    hSDK.eq_of_le hSDW inf_le_right (c.S_two.to_le inf_le_left)
  exact hns (by rw [hWeq]; exact hSDK)

theorem mem_of_pow_mem' {K S : Subgroup A} (hS : S ≤ normalizer (K : Set A)) {y : A}
    (hy : y ∈ K ⊔ S) {q : ℕ} (hq : q.Prime) (hcop : ∀ s ∈ S, Nat.Coprime (orderOf s) q)
    (hyq : y ^ q = 1) : y ∈ K := by
  obtain ⟨s, hsS, k, hkK, rfl⟩ := exists_mul_of_le_normalizer hS hy
  obtain ⟨k', hk', hm⟩ := pow_mul_mem (hS hsS) hkK (orderOf s)
  rw [pow_orderOf_eq_one, one_mul] at hm
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime (hcop s hsS) hq.one_lt
  have hpow : (s * k) ^ (orderOf s * r) = s * k := by
    have h1 : (s * k) ^ (orderOf s * r) = (s * k) ^ ((orderOf s * r) % q) := by
      conv_lhs => rw [← Nat.div_add_mod (orderOf s * r) q, pow_add, pow_mul, hyq, one_pow, one_mul]
    rw [h1, hr, pow_one]
  rw [← hpow, pow_mul, hm]
  exact K.pow_mem hk' r

theorem exists_commuting_of_dvd_card {p : ℕ} (hp : p.Prime) {N : Subgroup A} {z : A}
    (hzo : orderOf z = p) (hz : z ∈ normalizer (N : Set A)) (hdvd : p ∣ Nat.card N) :
    ∃ w ∈ N, orderOf w = p ∧ w * z = z * w := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZN : zpowers z ≤ normalizer (N : Set A) := Subgroup.zpowers_le.mpr hz
  letI : MulDistribMulAction (zpowers z) ↥N :=
    { smul := fun g n => ⟨(g : A) * n * (g : A)⁻¹, (mem_normalizer_iff.mp (hZN g.2) n).mp n.2⟩
      one_smul := fun n => Subtype.ext (by change (1 : A) * n * 1⁻¹ = n; group)
      mul_smul := fun a b n => Subtype.ext (by
        change ((a * b : zpowers z) : A) * n * ((a * b : zpowers z) : A)⁻¹ =
          (a : A) * ((b : A) * n * (b : A)⁻¹) * (a : A)⁻¹
        simp only [Subgroup.coe_mul]
        group)
      smul_mul := fun a n m => Subtype.ext (by
        change (a : A) * (n * m) * (a : A)⁻¹ =
          ((a : A) * n * (a : A)⁻¹) * ((a : A) * m * (a : A)⁻¹)
        group)
      smul_one := fun a => Subtype.ext (by change (a : A) * 1 * (a : A)⁻¹ = 1; group) }
  have hG : IsPGroup p (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hmod := hG.card_modEq_card_fixedPoints ↥N
  have hfix : p ∣ Nat.card ↥(FixedPoints.subgroup (zpowers z) ↥N) := by
    have h1 : p ∣ Nat.card (MulAction.fixedPoints (zpowers z) ↥N) := (hmod.dvd_iff dvd_rfl).mp hdvd
    exact h1
  obtain ⟨w', hw'⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(FixedPoints.subgroup (zpowers z) ↥N)) p hfix
  refine ⟨((w' : ↥N) : A), (w' : ↥N).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hw'
  · have h1 : ∀ m : zpowers z, m • (w' : ↥N) = (w' : ↥N) := w'.2
    have h2 := congrArg Subtype.val (h1 ⟨z, Subgroup.mem_zpowers z⟩)
    have h3 : z * ((w' : ↥N) : A) * z⁻¹ = ((w' : ↥N) : A) := h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm

theorem not_dvd_card_of_section {p : ℕ} (hp : p.Prime) {X H N : Subgroup A}
    (hrk : CFSG.Open.pRank p X ≤ 1) (hHX : H ≤ X) (hs : S622IsSimpleSection H N) {z : A}
    (hzH : z ∈ H) (hzN : z ∉ N) (hzo : orderOf z = p) : ¬ p ∣ Nat.card N := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  have hNH : N ≤ H := hs.1
  have hzNorm : z ∈ normalizer (N : Set A) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hs.2.1 hzH
  obtain ⟨w, hwN, hwo, hwz⟩ := exists_commuting_of_dvd_card hp hzo hzNorm hdvd
  have hwp : w ^ p = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo] at this
  have hzp : z ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo] at this
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hwo
    exact hp.one_lt.ne hwo
  have hzw : z ∉ zpowers w := fun h => hzN (Subgroup.zpowers_le.mpr hwN h)
  obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers hp hwp hzp hw1 hzw hwz
  have hEX : zpowers w ⊔ zpowers z ≤ X :=
    sup_le (Subgroup.zpowers_le.mpr (hHX (hNH hwN))) (Subgroup.zpowers_le.mpr (hHX hzH))
  have := SU1.le_pRank hp.one_lt hEX hel hcard
  omega

theorem eq_primeCore_of_section {p : ℕ} (hp : p.Prime) {X H N : Subgroup A}
    (hrk : CFSG.Open.pRank p X ≤ 1) (hHX : H ≤ X) (hs : S622IsSimpleSection H N) {z : A}
    (hzH : z ∈ H) (hzN : z ∉ N) (hzo : orderOf z = p) : N = rankThreePrimeCore p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpN := not_dvd_card_of_section hp hrk hHX hs hzH hzN hzo
  obtain ⟨hNH, hNn, hne, hmin, hnab⟩ := hs
  obtain ⟨hCH, hHC, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p H
  apply le_antisymm
  · exact le_sSup ⟨hNH, hNn, (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN⟩
  · have hCn : (rankThreePrimeCore p H |>.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mpr hHC
    have hsupn : ((N ⊔ rankThreePrimeCore p H).subgroupOf H).Normal := by
      rw [Subgroup.subgroupOf_sup hNH hCH]
      haveI := hNn
      haveI := hCn
      exact Subgroup.sup_normal _ _
    rcases hmin (N ⊔ rankThreePrimeCore p H) le_sup_left (sup_le hNH hCH) hsupn with h | h
    · exact h ▸ le_sup_right
    · exfalso
      apply hzN
      have hzS : z ∈ N ⊔ rankThreePrimeCore p H := by rw [h]; exact hzH
      have hHN : H ≤ normalizer (N : Set A) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNn
      have hzp : z ^ p = 1 := by
        have := pow_orderOf_eq_one z
        rwa [hzo] at this
      refine mem_of_pow_mem' (hCH.trans hHN) hzS hp (fun s hs => ?_) hzp
      have hdvd : orderOf s ∣ Nat.card (rankThreePrimeCore p H) := by
        have h1 := orderOf_dvd_natCard (⟨s, hs⟩ : rankThreePrimeCore p H)
        rwa [Subgroup.orderOf_mk] at h1
      exact (Nat.Coprime.coprime_dvd_left hdvd hcop.symm)

theorem false_of_not_sylow (c : KQCfg A p Kb Sb Bb Mb z) (hse : KQStrongEmb A p Mb z)
    (hchev : IsChevSimple 2 ↥Kb) (h131 : KFact131) (hpc : KFactParabolicCover)
    (hne : Sb ⊓ Kb ≠ ⊥) (hns : ¬ CFSG.ABGLocalTools.IsSylowOf 2 (Sb ⊓ Kb) Kb) : False := by
  have hp := c.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hK₀par := isParabolicTwo_inf c hchev h131 hne
  have hzM : z ∈ Mb := c.cover_Z (Subgroup.le_normalizer (Subgroup.mem_zpowers z))
  have hzK₀ : z ∈ Kb ⊓ Mb := ⟨c.z_mem_K, hzM⟩
  have hK₀ne : Kb ⊓ Mb ≠ Kb := fun h => c.not_le (h.symm.le.trans inf_le_right)
  have hSyl := not_le_primeCore_of_not_sylow c hchev h131 hne hns
  obtain ⟨f, hf, hf2, hfp, ⟨H, N, hH, hs, hzH, hzN, hfd⟩, g, hgK, hgK₀, hgf⟩ :=
    hpc A Kb (Kb ⊓ Mb) z p hchev hp c.five_le c.rank c.z_order hzK₀ hK₀par hK₀ne hSyl
  have hNC : N = rankThreePrimeCore p H :=
    eq_primeCore_of_section hp c.rank (hH.trans inf_le_left) hs hzH hzN c.z_order
  rw [hNC] at hs hfd
  have hgM : g ∉ Mb := fun hgM => hgK₀ ⟨hgK, hgM⟩
  refine hse f hf hf2 hfp H (hH.trans inf_le_right) hzH hs hfd g hgM
    (hgf.trans (Subgroup.card_dvd_of_le ?_))
  exact inf_le_inf (inf_le_right : Kb ⊓ Mb ≤ Mb) (Subgroup.map_mono (inf_le_right : Kb ⊓ Mb ≤ Mb))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGQ
