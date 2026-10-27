module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Facts2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Lift
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Norm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem catalogIs_transport_H1420 {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs A Q) : catalogIs B Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem mulEquiv_quot_center_of_card_one {Y : Type} [Group Y] (h : Nat.card (Subgroup.center Y) = 1) :
    Nonempty (Y ≃* Y ⧸ Subgroup.center Y) := by
  have hbot : Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ h
  exact ⟨QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)⟩

theorem inf_eq_bot_of_pGroup_of_not_dvd {G : Type} [Group G] [Finite G] {A O : Subgroup G}
    (hA : IsPGroup 3 A) (hO : ¬ 3 ∣ Nat.card O) : A ⊓ O = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hA
  have hdvd : Nat.card (A ⊓ O : Subgroup G) ∣ 3 ^ k := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    apply hO
    have h3 : 3 ∣ Nat.card (A ⊓ O : Subgroup G) := by
      rw [hj]
      exact dvd_pow_self 3 hne
    exact h3.trans (Subgroup.card_dvd_of_le inf_le_right)
  rw [hj0, pow_zero] at hj
  exact Subgroup.eq_bot_of_card_eq _ hj

theorem pQuot_commute_of_commutator_mem {G : Type} [Group G] {K : Subgroup G} {k a : G} (hk : k ∈ K)
    (ha : a ∈ K) (hc : ⁅k, a⁆ ∈ GLAPPrimeCoreOf 3 K) :
    (QuotientGroup.mk ⟨k, hk⟩ : PQuot 3 K) * QuotientGroup.mk ⟨a, ha⟩ =
      QuotientGroup.mk ⟨a, ha⟩ * QuotientGroup.mk ⟨k, hk⟩ := by
  set x : ↥K := ⟨k, hk⟩ with hx
  set y : ↥K := ⟨a, ha⟩ with hy
  have hw : ⁅y, x⁆ ∈ GLAPPrimeCore 3 ↥K := by
    have h1 : ⁅a, k⁆ ∈ GLAPPrimeCoreOf 3 K := by
      rw [← commutatorElement_inv]
      exact (GLAPPrimeCoreOf 3 K).inv_mem hc
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 h1
    have hzy : z = ⁅y, x⁆ := Subtype.ext (by simpa [commutatorElement_def, hx, hy] using hzeq)
    rw [← hzy]
    exact hz
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have key : (x * y)⁻¹ * (y * x) = (x * y)⁻¹ * ⁅y, x⁆ * (x * y) := by
    simp only [commutatorElement_def]
    group
  rw [key]
  have h := (GLAPPrimeCore.normal 3 ↥K).conj_mem _ hw (x * y)⁻¹
  rwa [inv_inv] at h

theorem inf_eq_bot_of_centre {G : Type} [Group G] [Finite G] {K A : Subgroup G}
    (hcent : Nat.card (Subgroup.center (PQuot 3 K)) = 1) (hA : IsPGroup 3 A)
    (hAc : ∀ a ∈ A, ∀ k ∈ K, ⁅k, a⁆ ∈ GLAPPrimeCoreOf 3 K) : A ⊓ K = ⊥ := by
  have hO : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K : Subgroup G) :=
    not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
  apply eq_bot_iff.2
  intro a ha
  obtain ⟨haA, haK⟩ := ha
  have hcen : (QuotientGroup.mk ⟨a, haK⟩ : PQuot 3 K) ∈ Subgroup.center (PQuot 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    exact pQuot_commute_of_commutator_mem k.2 haK (hAc a haA k k.2)
  have hbot : Subgroup.center (PQuot 3 K) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcent
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  have haO : a ∈ GLAPPrimeCoreOf 3 K := Subgroup.mem_map.2 ⟨⟨a, haK⟩, hcen, rfl⟩
  have hAO := inf_eq_bot_of_pGroup_of_not_dvd hA hO
  have hmem : a ∈ A ⊓ GLAPPrimeCoreOf 3 K := ⟨haA, haO⟩
  rw [hAO] at hmem
  exact hmem

theorem not_dvd_card_core {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
  have h := not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
  unfold GLAPPrimeCoreOf at h
  rwa [Subgroup.card_map_of_injective K.subtype_injective] at h

theorem isElemAbelian_zpowers_three {G : Type} [Group G] {b : G} (hb : b ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers b) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem isElemAbelian_bot' {G : Type} [Group G] (p : ℕ) : CFSG.Open.IsElemAbelian p (⊥ : Subgroup G) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    simp [Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2]
  · rw [Subgroup.mem_bot.1 hx, one_pow]

theorem le_twoLocalRank_of_witness {G : Type} [Group G] [Finite G] {K A : Subgroup G} {s r : ℕ}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hAK : A ⊓ K = ⊥)
    (hAc : ∀ a ∈ A, ∀ k ∈ K, ⁅k, a⁆ ∈ GLAPPrimeCoreOf 3 K) (hAr : Nat.card A = 3 ^ r)
    (V E : Subgroup (PQuot 3 K)) (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hEV : E ≤ Subgroup.normalizer (V : Set (PQuot 3 K))) (hEc : Nat.card E = 3 ^ s) :
    s + r ≤ GLATwoLocalRank 3 G := by
  obtain ⟨P, W, hP, hP2, hWN, hW, hWc⟩ := twoLocal_of_witness hA hAN hAK hAc V E hV hV2 hE hEV hEc
  have hk : Nat.card W = 3 ^ (s + r) := by
    rw [hWc, hAr, pow_add]
  have h1 := CFSG.LocalAnalysis.GLTheoremA.S8.L84.le_pRank_of_isElemAbelian Nat.prime_three hWN hW hk
  have h2 := CFSG.LocalAnalysis.GLTheoremA.S8.L84.pRank_normalizer_le_glaTwoLocalRank Nat.prime_three hP hP2
  exact h1.trans h2

end CFSG.LocalAnalysis.GLTheoremA.H1420

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L89

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.H1420
open scoped commutatorElement

theorem in8910_i1432_of_facts (G : Type) [Group G] [Finite G] (hI112 : I112NormAt G 3)
    (hD4 : I1432ClsD4) (hG2 : I1432ClsG2) (hWD4 : I1432WitD4) (hWG2 : I1432WitG2)
    (hWFi : I1432WitFi24) (hCent : I1432Cent) (hBD4 : I1432BD4) : I1432At G := by
  intro X K B I U b y hX hK hB hBX hUX hU hU2 hBU hb hb1 hbC hyB hI hnot
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hBel : CFSG.Open.IsElemAbelian 3 B := hB.1
  have hBcard : Nat.card B = 3 ^ GLATwoLocalRank 3 G := hB.2.1
  have hyX : y ∈ X := hBX hyB
  have hIK : I ≤ K := hI.1.trans inf_le_left
  have hIy : I ≤ Subgroup.centralizer ({y} : Set G) := fun i hi => (hI.1 hi).2
  have hIperf : ⁅I, I⁆ = I := glaPComponent_perfect hI
  have hIn : ¬ I ≤ GLAPPrimeCoreOf 3 K := not_le_glaPPrimeCoreOf_of_component hp hI inf_le_left
  have hyK : y ∈ Subgroup.normalizer (K : Set G) :=
    normalizer_of_centralized hp hK (Subgroup.le_normalizer hyX) hIK hIy hIperf hIn
  have hKX : CFSG.Open.IsKGroup ↥K := CFSG.Open.IsKGroup.of_le hX hK.1
  have hKq : CFSG.Open.IsKGroup (PQuot 3 K) := CFSG.Open.IsKGroup.quotient hKX _
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hcat : IsCatalogGroup (PSimple 3 K) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' hKq hQ
  have hcen3 := CFSG.LocalAnalysis.GLTheoremA.I106TGroup.center_pQuot_three_pow K
  have hmodel : I1432Model K I y := ⟨hQ, hcat, hyK, hBel.2 y hyB, hI, hnot⟩
  have hPQ : ∀ (Q : TauCeti.CFSGIndex → Prop), Nat.card (Subgroup.center (PQuot 3 K)) = 1 →
      catalogIs (PSimple 3 K) Q → catalogIs (PQuot 3 K) Q := by
    intro Q hc h
    obtain ⟨e⟩ := mulEquiv_quot_center_of_card_one hc
    exact catalogIs_transport_H1420 e.symm h
  refine ⟨fun hIt => ?_, fun hIt hm => ?_⟩
  ·
    rcases hD4 G K I y hmodel hIt with hFi | hD27
    · exact hFi
    · exfalso
      have hcenter : Nat.card (Subgroup.center (PQuot 3 K)) = 1 :=
        hCent (PQuot 3 K) hQ hcen3 (Or.inl hD27)
      obtain ⟨V, E0, hV, hV2, hEV, hE0, hE0c⟩ := hWD4 (PQuot 3 K) (hPQ _ hcenter hD27)
      obtain ⟨S, -, hSel, hScard⟩ :=
        CFSG.RankThree.Classical2.exists_elemAbelian_lift (GLAPPrimeCore 3 ↥K) (not_dvd_card_core K) hE0
      have hEK : ∃ E : Subgroup G, E ≤ K ∧ CFSG.Open.IsElemAbelian 3 E ∧ 3 ^ 3 ≤ Nat.card E := by
        refine ⟨S.map K.subtype, Subgroup.map_subtype_le S,
          isElemAbelian_map_of_injOn K.subtype S hSel, ?_⟩
        rw [Subgroup.card_map_of_injective K.subtype_injective, hScard, hE0c]
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
      have hBN : B ≤ Subgroup.normalizer (K : Set G) :=
        hI112 hp (by norm_num) X B K hX hB hBX hK hEK
      have hB0el : CFSG.Open.IsElemAbelian 3 (B ⊓ centModSubgroup 3 K) :=
        isElemAbelian_mono hBel inf_le_left
      have hB0N : (B ⊓ centModSubgroup 3 K) ≤ Subgroup.normalizer (K : Set G) := fun x hx => hx.2.1
      have hB0c : ∀ a ∈ B ⊓ centModSubgroup 3 K, ∀ k ∈ K, ⁅k, a⁆ ∈ GLAPPrimeCoreOf 3 K :=
        fun a ha k hk => ha.2.2 k hk
      have hB0K : (B ⊓ centModSubgroup 3 K) ⊓ K = ⊥ :=
        inf_eq_bot_of_centre hcenter (isPGroup_of_isElemAbelian hB0el) hB0c
      obtain ⟨r, hr⟩ := CFSG.LocalAnalysis.GLTheoremA.S8.L84.exists_card_eq_pow_of_isElemAbelian hB0el
      have hrank := le_twoLocalRank_of_witness hB0el hB0N hB0K hB0c hr V E0 hV hV2 hE0 hEV hE0c
      have hBrk := hBD4 G K I B y hmodel hIt hD27 hBel hBN hyB
      rw [hBcard, hr] at hBrk
      have h2 : 3 ^ GLATwoLocalRank 3 G ≤ 3 ^ (9 + r) := by
        rw [pow_add]
        exact hBrk
      have h3 : GLATwoLocalRank 3 G ≤ 9 + r := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
      omega
  ·
    have hb3 : b ^ 3 = 1 := hBel.2 b hb
    have hbrank : ∀ s : ℕ, HasTwoLocalWitness (PQuot 3 K) s →
        Nat.card (Subgroup.center (PQuot 3 K)) = 1 → s + 1 ≤ GLATwoLocalRank 3 G := by
      intro s hw hc
      obtain ⟨V, E0, hV, hV2, hEV, hE0, hE0c⟩ := hw
      have hAc : ∀ a ∈ Subgroup.zpowers b, ∀ k ∈ K, ⁅k, a⁆ ∈ GLAPPrimeCoreOf 3 K :=
        fun a ha k hk => hbC.2 (Subgroup.commutator_mem_commutator hk ha)
      have hcard : Nat.card (Subgroup.zpowers b) = 3 ^ 1 := by
        rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1, pow_one]
      exact le_twoLocalRank_of_witness (isElemAbelian_zpowers_three hb3) (Subgroup.zpowers_le.2 hbC.1)
        (inf_eq_bot_of_centre hc (isPGroup_of_isElemAbelian (isElemAbelian_zpowers_three hb3)) hAc)
        hAc hcard V E0 hV hV2 hE0 hEV hE0c
    rcases hG2 G K I y hmodel hIt with hTh | hFi | hG227 | hD43 | hTD43 | hD427
    · exact hTh
    · exfalso
      obtain ⟨V, E0, hV, hV2, hEV, hE0, hE0c⟩ := hWFi (PQuot 3 K) hQ hFi
      have hrank := le_twoLocalRank_of_witness (A := ⊥) (r := 0) (isElemAbelian_bot' 3) bot_le
        (bot_inf_eq _) (fun a ha k _ => by
          rw [Subgroup.mem_bot.1 ha, commutatorElement_one_right]
          exact Subgroup.one_mem _) (by simp) V E0 hV hV2 hE0 hEV hE0c
      omega
    · exfalso
      have hc : Nat.card (Subgroup.center (PQuot 3 K)) = 1 :=
        hCent (PQuot 3 K) hQ hcen3 (Or.inr (Or.inl hG227))
      have h1 := hbrank 4 (hWG2 (PQuot 3 K) (Or.inl (hPQ _ hc hG227))) hc
      omega
    · exfalso
      have hc : Nat.card (Subgroup.center (PQuot 3 K)) = 1 :=
        hCent (PQuot 3 K) hQ hcen3 (Or.inr (Or.inr (Or.inl hD43)))
      have h1 := hbrank 4 (hWG2 (PQuot 3 K) (Or.inr (Or.inl (hPQ _ hc hD43)))) hc
      omega
    · exfalso
      have hc : Nat.card (Subgroup.center (PQuot 3 K)) = 1 :=
        hCent (PQuot 3 K) hQ hcen3 (Or.inr (Or.inr (Or.inr hTD43)))
      have h1 := hbrank 4 (hWG2 (PQuot 3 K) (Or.inr (Or.inr (hPQ _ hc hTD43)))) hc
      omega
    · exfalso
      have hc : Nat.card (Subgroup.center (PQuot 3 K)) = 1 :=
        hCent (PQuot 3 K) hQ hcen3 (Or.inl hD427)
      have h1 := hbrank 12 (hWD4 (PQuot 3 K) (hPQ _ hc hD427)) hc
      omega

end CFSG.LocalAnalysis.GLTheoremA.S8.L89

end
