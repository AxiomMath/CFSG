module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBig
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineMemberDefLocal
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporHull
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.AGLEmbeddingD2 (d2SporadicOrder)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement)

structure SporOvergroupData (L : Type) [Group L] [Finite L] (p d : ℕ) (Y : Subgroup L) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  kgroup : CFSG.SectionRank.IsKGroupCat L
  rank_le : CFSG.Open.pRank p (⊤ : Subgroup L) ≤ 3
  ne_top : Y ≠ ⊤
  d_prime : d.Prime
  d_ne_two : d ≠ 2
  d_ne : d ≠ p
  barE : ∃ Eb : Subgroup L, CFSG.Open.IsElemAbelian p Eb ∧ Nat.card Eb = p ^ 2 ∧
    (∀ e ∈ Eb, e ≠ 1 → Subgroup.centralizer {e} ≤ Y) ∧
    ∀ R : Subgroup L, IsPGroup p R → Eb ≤ R → Subgroup.normalizer (R : Set L) ≤ Y
  sylowD : ∃ D : Subgroup L, CFSG.ABGLocalTools.IsSylowOf d D ⊤ ∧ D ≠ ⊥ ∧
    ∀ F : Subgroup L, F ≤ D → F ≠ ⊥ → Subgroup.normalizer (F : Set L) ≤ Y

@[expose] def SporBigNone (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* Carrier s) →
    ∀ (d : ℕ) (Y : Subgroup L), ¬ SporOvergroupData L p d Y

@[expose] def SporBigLy : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* Carrier .Ly) →
    ∀ (d : ℕ) (Y : Subgroup L), SporOvergroupData L 5 d Y →
      d = 31 ∧ CFSG.RankThreeEvenClassification.Helpers.primeComplementCore ↥Y d = ⊥ ∧
        ChevalleyExceptionalModel (oPrimeModPrimeComplement d Y) .G2 5 1

@[expose] def SporBigOvergroup : Prop :=
  SporBigNone .Co1 5 ∧ SporBigNone .HN 5 ∧ SporBigNone .B 5 ∧ SporBigNone .M 7 ∧ SporBigLy

private theorem exists_sylow_subgroupOf_of_hyp {X : Type} [Group X] [Finite X]
    {K E D X₁ : Subgroup X} {p d : ℕ} (h : ThreeNineHyp K E D X₁ p d)
    (hZ : Subgroup.center ↥K = ⊥) (hout : ¬ d ∣ Nat.card (Outer ↥K)) :
    ∃ D' : Subgroup ↥K, CFSG.ABGLocalTools.IsSylowOf d D' ⊤ ∧ D' ≠ ⊥ ∧
      ∀ F : Subgroup ↥K, F ≤ D' → F ≠ ⊥ →
        Subgroup.normalizer (F : Set ↥K) ≤ X₁.subgroupOf K := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hout
  have hDsylK : CFSG.ABGLocalTools.IsSylowOf d D K := by
    have h1 := h.sylow.inf_of_le_normalizer le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
    rwa [inf_eq_left.mpr hDK] at h1
  have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← Subgroup.subgroupOf_self K, Subgroup.map_subgroupOf_eq_of_le (le_rfl : K ≤ K)]
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf d (D.subgroupOf K) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := d) K).mp ?_
    rwa [Subgroup.map_subgroupOf_eq_of_le hDK, htop]
  have hne : D.subgroupOf K ≠ ⊥ := by
    intro hbot
    apply h.D_ne_bot
    have h1 := congrArg (fun F : Subgroup ↥K => F.map K.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hDK, Subgroup.map_bot] at h1
  refine ⟨D.subgroupOf K, hDsyl, hne, fun F hF hF1 n hn => ?_⟩
  have hFD : F.map K.subtype ≤ D := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    exact hF hy
  have hsub : (F.map K.subtype).subgroupOf K = F := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_subtype_le F)]
  have hF1' : F.map K.subtype ≠ ⊥ := by
    intro hbot
    apply hF1
    have h1 := congrArg (fun H : Subgroup X => H.subgroupOf K) hbot
    rwa [hsub, Subgroup.bot_subgroupOf] at h1
  have hn' : (n : X) ∈ Subgroup.normalizer ((F.map K.subtype) : Set X) := by
    have hmem : n ∈ (Subgroup.normalizer ((F.map K.subtype) : Set X)).subgroupOf K := by
      rw [Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le F), hsub]
      exact hn
    exact hmem
  exact h.normalizer_inf_le_of_le_D hFD hF1' ⟨hn', le_sup_left (a := K) n.2⟩

theorem sporOvergroupData_of_hyp {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    {p d : ℕ} (h : ThreeNineHyp K E D X₁ p d) (hZ : Subgroup.center ↥K = ⊥)
    (hO : Nat.card (Outer ↥K) ≤ 2) :
    SporOvergroupData ↥K p d (X₁.subgroupOf K) := by
  have hO0 : Nat.card (Outer ↥K) ≠ 0 := Nat.card_pos.ne'
  have hp : ¬ p ∣ Nat.card (Outer ↥K) := not_dvd_of_le_two h.prime h.ne_two hO0 hO
  have hd : ¬ d ∣ Nat.card (Outer ↥K) := not_dvd_of_le_two h.d_prime h.d_ne_two hO0 hO
  have hrk : CFSG.Open.pRank p (K ⊔ E) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono h.prime.one_lt (le_top : K ⊔ E ≤ ⊤)).trans h.rank_le
  refine ⟨h.prime, h.ne_two, h.kgroup, pRank_top_le_three_of_sup h.prime hrk,
    (h.index_facts hZ hp hd).1, h.d_prime, h.d_ne_two, h.d_ne, h.exists_barE hZ hp, ?_⟩
  exact exists_sylow_subgroupOf_of_hyp h hZ hd

theorem coreOfData {L : Type} [Group L] [Finite L] {p d : ℕ} {Y : Subgroup L}
    (h : SporOvergroupData L p d Y) :
    ∃ M : Subgroup L, IsCoatom M ∧ Y ≤ M ∧
      p ^ (Nat.card L).factorization p ∣ Nat.card Y ∧
      d ∣ Nat.card Y ∧ d ^ (Nat.card L).factorization d ∣ Nat.card Y ∧
      ∃ D : Subgroup L, CFSG.ABGLocalTools.IsSylowOf d D ⊤ ∧ D ≠ ⊥ ∧
        Subgroup.normalizer (D : Set L) ≤ M := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact d.Prime := ⟨h.d_prime⟩
  obtain ⟨M, hM, hYM⟩ := (eq_top_or_exists_le_coatom Y).resolve_left h.ne_top
  obtain ⟨Eb, hEb, -, -, hN⟩ := h.barE
  have hpc : p ^ (Nat.card L).factorization p ∣ Nat.card Y := by
    obtain ⟨T, hET⟩ := (CFSG.Open.IsElemAbelian.isPGroup hEb).exists_le_sylow
    rw [← Sylow.card_eq_multiplicity T]
    exact Subgroup.card_dvd_of_le
      (Subgroup.le_normalizer.trans (hN T T.isPGroup' hET))
  obtain ⟨D, hDsyl, hDne, hND⟩ := h.sylowD
  have hDY : D ≤ Y := Subgroup.le_normalizer.trans (hND D le_rfl hDne)
  have hDcard : Nat.card D = d ^ (Nat.card L).factorization d := by
    have h1 := hDsyl.card_eq
    rwa [Subgroup.card_top] at h1
  have hDpow : d ^ (Nat.card L).factorization d ∣ Nat.card Y :=
    hDcard ▸ Subgroup.card_dvd_of_le hDY
  have hdY : d ∣ Nat.card Y := by
    have hk0 : (Nat.card L).factorization d ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hDcard
      exact hDne (Subgroup.eq_bot_of_card_eq D hDcard)
    exact (hDcard.symm ▸ dvd_pow_self d hk0).trans (Subgroup.card_dvd_of_le hDY)
  exact ⟨M, hM, hYM, hpc, hdY, hDpow, D, hDsyl, hDne, (hND D le_rfl hDne).trans hYM⟩

private theorem card_eq_of_not_sq_dvd {L : Type} [Group L] [Finite L] {d : ℕ} (hd : d.Prime)
    {D : Subgroup L} (hDsyl : CFSG.ABGLocalTools.IsSylowOf d D ⊤) (hDne : D ≠ ⊥)
    (hsq : ¬ d ^ 2 ∣ Nat.card L) : Nat.card D = d := by
  have : Fact d.Prime := ⟨hd⟩
  have hc : Nat.card D = d ^ (Nat.card L).factorization d := by
    have h1 := hDsyl.card_eq
    rwa [Subgroup.card_top] at h1
  have hk0 : (Nat.card L).factorization d ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hc
    exact hDne (Subgroup.eq_bot_of_card_eq D hc)
  have hk1 : (Nat.card L).factorization d ≤ 1 := by
    by_contra h1
    apply hsq
    have h2 : d ^ 2 ∣ Nat.card D := hc.symm ▸ pow_dvd_pow d (by omega : 2 ≤ _)
    exact h2.trans (Subgroup.card_subgroup_dvd_card D)
  rw [hc, show (Nat.card L).factorization d = 1 by omega, pow_one]

private theorem false_B_of_data (hloc : SporBigLocal)
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = d2SporadicOrder s)
    {L : Type} [Group L] [Finite L] (e : L ≃* Carrier .B)
    {d : ℕ} {Y : Subgroup L} (h : SporOvergroupData L 5 d Y) : False := by
  obtain ⟨hmax, hn11M, hn19M, hn31M, hn11, hn19, hn31⟩ := (hloc L).2.2.2.2 ⟨e⟩
  obtain ⟨M, hM, hYM, h5, hd, hd2, D, hDsyl, hDne, hnorm⟩ := coreOfData h
  have hL : Nat.card L = d2SporadicOrder .B :=
    (Nat.card_congr e.toEquiv).trans (hcard .B (by decide))
  have h56 : 5 ^ 6 ∣ Nat.card L := by rw [hL]; norm_num [d2SporadicOrder]
  have h5' : 5 ^ 6 ∣ Nat.card Y :=
    pow_dvd_of_factorization Nat.prime_five (Nat.card_pos.ne') h56 h5
  have hYMd := Subgroup.card_dvd_of_le hYM
  have hMc := hmax M hM (h5'.trans hYMd)
  have hdM := hd.trans hYMd
  have hd2M := hd2.trans hYMd
  have hDc : ¬ d ^ 2 ∣ Nat.card L → Nat.card D = d := fun hsq =>
    card_eq_of_not_sq_dvd h.d_prime hDsyl hDne hsq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMc
  rcases hMc with hMc | hMc | hMc <;> rw [hMc] at hdM hd2M
  · have hmem := mem_of_prime_dvd h.d_prime
      (qs := [(2, 15), (3, 6), (5, 6), (7, 1), (11, 1), (19, 1)]) (by norm_num)
      (by norm_num; exact hdM)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.d_ne_two rfl
    · exact not_pow_dvd_of_factorization (e := 13) Nat.prime_three (Nat.card_pos.ne')
        (by rw [hL]; norm_num [d2SporadicOrder]) (by norm_num) hd2M
    · exact h.d_ne rfl
    · exact not_pow_dvd_of_factorization (e := 2) Nat.prime_seven (Nat.card_pos.ne')
        (by rw [hL]; norm_num [d2SporadicOrder]) (by norm_num) hd2M
    · exact false_of_normOrder hM hMc
        (hDc (by rw [hL]; norm_num [d2SporadicOrder])) hnorm hn11M hn11 (by norm_num)
    · exact false_of_normOrder hM hMc
        (hDc (by rw [hL]; norm_num [d2SporadicOrder])) hnorm hn19M hn19 (by norm_num)
  · have hmem := mem_of_prime_dvd h.d_prime (qs := [(2, 5), (3, 1), (5, 6), (31, 1)])
      (by norm_num) (by norm_num; exact hdM)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact h.d_ne_two rfl
    · exact not_pow_dvd_of_factorization (e := 13) Nat.prime_three (Nat.card_pos.ne')
        (by rw [hL]; norm_num [d2SporadicOrder]) (by norm_num) hd2M
    · exact h.d_ne rfl
    · exact false_of_normOrder hM hMc
        (hDc (by rw [hL]; norm_num [d2SporadicOrder])) hnorm hn31M hn31 (by norm_num)
  · have hmem := mem_of_prime_dvd h.d_prime (qs := [(2, 9), (3, 1), (5, 6)]) (by norm_num)
      (by norm_num; exact hdM)
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact h.d_ne_two rfl
    · exact not_pow_dvd_of_factorization (e := 13) Nat.prime_three (Nat.card_pos.ne')
        (by rw [hL]; norm_num [d2SporadicOrder]) (by norm_num) hd2M
    · exact h.d_ne rfl

private theorem primeComplementCore_eq_bot_of_isSimpleGroup {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] {d : ℕ} (hd : d.Prime) (hdvd : d ∣ Nat.card S) :
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore S d = ⊥ := by
  obtain ⟨hN, hnd⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore_properties S d hd
  rcases hN.eq_bot_or_eq_top with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hnd
    exact absurd hdvd hnd

private theorem ly_g2_case {L : Type} [Group L] [Finite L] {d : ℕ} {Y M : Subgroup L}
    (hM : IsCoatom M) (hYM : Y ≤ M) (hMc : Nat.card M = 5859000000)
    (h56 : 5 ^ 6 ∣ Nat.card Y) (hd : d ∣ Nat.card Y) (hG2 : LyG2Five L)
    (hd31 : d = 31) :
    CFSG.RankThreeEvenClassification.Helpers.primeComplementCore ↥Y d = ⊥ ∧
      ChevalleyExceptionalModel (oPrimeModPrimeComplement d Y) .G2 5 1 := by
  subst d
  obtain ⟨hsM, hmodM, hsub⟩ := hG2 M hM hMc
  haveI := hsM
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hY : Y = M := by
    by_contra hne
    exact hsub Y (lt_of_le_of_ne hYM hne)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h56 hd)
  have : IsSimpleGroup ↥(⊤ : Subgroup ↥M) :=
    MulEquiv.isSimpleGroup Subgroup.topEquiv
  obtain ⟨e1⟩ := SporCent.nonempty_oPrimeModPrimeComplement_mulEquiv (d := 31)
    (by norm_num) (Y := M) (⊤ : Subgroup ↥M) (by rw [Subgroup.card_top, hMc]; norm_num)
    (by rw [Subgroup.index_top]; norm_num)
  have hdM : 31 ∣ Nat.card ↥M := hY ▸ hd
  rw [hY]
  exact ⟨primeComplementCore_eq_bot_of_isSimpleGroup (by norm_num) hdM,
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv (e1.trans Subgroup.topEquiv) hmodM⟩

theorem threeNineFiveSporBig_of_overgroup_facts (hob : SporBigOvergroup)
    (hsimp : ∀ s : TauCeti.SporadicName, IsSimpleGroup (Carrier s))
    (hcard : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = d2SporadicOrder s)
    (hcardM : Nat.card (Carrier .M) = CFSG.Open.monsterOrder)
    (hout : ∀ s : TauCeti.SporadicName, Nat.card (Outer (Carrier s)) ≤ 2) :
    ThreeNineFiveSporBig := by
  intro X _ _ K E D X₁ p d s h hsb hs
  obtain ⟨e⟩ := hs
  haveI : IsSimpleGroup (Carrier s) := hsimp s
  haveI : IsSimpleGroup ↥K := MulEquiv.isSimpleGroup e
  have hcK : Nat.card ↥K = Nat.card (Carrier s) := Nat.card_congr e.toEquiv
  have hNp : ¬ (Nat.card (Carrier s)).Prime := by
    by_cases hsM : s = .M
    · subst hsM
      rw [hcardM]
      norm_num [CFSG.Open.monsterOrder]
    · rw [hcard s hsM]
      cases s <;> first | exact absurd rfl hsM | norm_num [d2SporadicOrder]
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; exact hNp)
  have hOK : Nat.card (Outer ↥K) = Nat.card (Outer (Carrier s)) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
  have hO : Nat.card (Outer ↥K) ≤ 2 := hOK.trans_le (hout s)
  have hdata : SporOvergroupData ↥K p d (X₁.subgroupOf K) :=
    sporOvergroupData_of_hyp h hZ hO
  rcases hsb with ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact (hob.1 ↥K ⟨e⟩ d (X₁.subgroupOf K) hdata).elim
  · obtain ⟨hd31, -, hmod⟩ := hob.2.2.2.2 ↥K ⟨e⟩ d (X₁.subgroupOf K) hdata
    have hd : ¬ d ∣ Nat.card (Outer ↥K) := not_dvd_of_le_two h.d_prime h.d_ne_two
      (Nat.card_pos.ne') hO
    have hDK : D ≤ K := h.D_le_K_of_not_dvd hZ hd
    have hd2K : ¬ d ^ 2 ∣ Nat.card ↥K := by
      rw [hd31, hcK, hcard .Ly (by decide)]
      norm_num [d2SporadicOrder]
    have hDc : Nat.card D = d := card_D_eq h hDK hd2K
    have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    have hcyc : IsCyclic ↥D := isCyclic_of_prime_card (hDc.trans hd31)
    have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
    obtain ⟨eX⟩ := oPrimeModPrimeComplement_congr d (Subgroup.subgroupOfEquivOfLe hX₁K)
    exact ⟨hcyc, hDK, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hd31, ⟨e⟩,
      CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eX.symm hmod⟩)))⟩
  · exact (hob.2.2.1 ↥K ⟨e⟩ d (X₁.subgroupOf K) hdata).elim
  · exact (hob.2.1 ↥K ⟨e⟩ d (X₁.subgroupOf K) hdata).elim
  · exact (hob.2.2.2.1 ↥K ⟨e⟩ d (X₁.subgroupOf K) hdata).elim

section Producer

theorem threeNineFiveSporBig_of_overgroup (hob : SporBigOvergroup) : ThreeNineFiveSporBig := by
  have hMfacts := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_M
    CFSG.Milestones.fam_m_finiteness CFSG.Milestones.fam_m_simplicity
  have hMcard : Nat.card (Carrier .M) = CFSG.Open.monsterOrder :=
    (Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans
      CFSG.Milestones.fam_m_finiteness
  have : Finite (Carrier .M) := hMfacts.1
  have hMout : Nat.card (Outer (Carrier .M)) ≤ 2 :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds _ hMfacts.2.1 hMfacts.2.2.2 .M
      (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .M)
  have hfacts : ∀ s, CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CarrierFacts s :=
    fun s => if hs : s = .M then hs ▸ hMfacts else
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M s hs
  exact threeNineFiveSporBig_of_overgroup_facts hob (fun s => (hfacts s).2.1)
    CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder hMcard
    (fun s => if hs : s = .M then hs ▸ hMout else
      CFSG.AGLEmbeddingD2.card_outer_carrier_le_two_of_ne_M s hs)

end Producer

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
