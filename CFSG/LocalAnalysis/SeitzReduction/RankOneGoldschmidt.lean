module

public import CFSG.CGT.Timmesfeld75.GoldschmidtMilestone
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3FourEightTypes
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.Blueprint
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 odd_card_goldschmidtOddCore
  goldschmidt1974_of_milestone)
open CFSG.QuasithinUnique.Lin2 (exists_fusionBenderBorel_of_fusionIsBenderGroup
  false_of_benderBorel)
open scoped MatrixGroups

theorem false_of_goldschmidtSimpleType {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.goldschmidtSimpleType X) (h16 : 16 ∣ Nat.card X) {U Y : Subgroup X}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hY : Y ≤ Subgroup.normalizer (U : Set X))
    (hYns : ¬ Group.IsSolvable Y) : False := by
  have hbender : CFSG.Open.fusionIsBenderGroup X → False := fun hB => by
    obtain ⟨q, k, hq⟩ := exists_fusionBenderBorel_of_fusionIsBenderGroup hB
    exact false_of_benderBorel hq hU hU2 hY hYns
  unfold CFSG.Open.goldschmidtSimpleType at hX
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ |
      ⟨p, f, hp, hodd, hf, -, h8, ⟨e⟩⟩ | ⟨m, -, hcard⟩ | ⟨⟨e⟩⟩
  · exact hbender (Or.inl ⟨f, by omega, ⟨e⟩⟩)
  · exact hbender (Or.inr (Or.inr ⟨a, ha, ⟨e⟩⟩))
  · exact hbender (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩))
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    obtain ⟨k, hk, hkeq⟩ :=
      CFSG.ComponentClassification.AschbacherTheorem3.FourEight.psl2_card_two_part h8
    have h1 := CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (p := p) (m := f) hp2
      (by omega)
    have hcardX : Nat.card X = 4 * k := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p f)) = _
      rw [h1, mul_comm 2 f, pow_mul, hkeq]
    have hk2 := Nat.odd_iff.mp hk
    omega
  ·
    obtain ⟨k, hk, hkeq⟩ :=
      CFSG.ComponentClassification.AschbacherTheorem3.FourEight.ordRee_two_part m
    have hk2 := Nat.odd_iff.mp hk
    rw [hcard, hkeq] at h16
    omega
  ·
    rw [Nat.card_congr e.toEquiv,
      CFSG.ComponentClassification.AschbacherTheorem3.FourEight.card_goldschmidtJ1] at h16
    omega

theorem isQuasisimple_and_center_eq_bot_of_isSimpleGroup {B : Type*} [Group B] [IsSimpleGroup B]
    (hna : ∃ a b : B, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple B ∧ Subgroup.center B = ⊥ := by
  obtain ⟨a, b, hab⟩ := hna
  have hZ : Subgroup.center B = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center B) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a) hab
  have hP : commutator B = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator B) with h | h
    · refine absurd ?_ hab
      rw [← commutatorElement_eq_one_iff_mul_comm, ← Subgroup.mem_bot, ← h, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    · exact h
  let e : B ⧸ Subgroup.center B ≃* B :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨⟨hP, e.isSimpleGroup⟩, hZ⟩

theorem goldschmidtSimpleType_of_isSimpleGroup (hGold : Goldschmidt1974) {X : Type} [Group X]
    [Finite X] [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (S : Sylow 2 X)
    {A : Subgroup X} (hAS : A ≤ (S : Subgroup X)) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    (hA1 : A ≠ ⊥) : CFSG.Open.goldschmidtSimpleType X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hc⟩ := hGold X S A hAS hAab hcl
  set M : Subgroup X := Subgroup.normalClosure (A : Set X)
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  have hMtop : M = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h0 | h0
    · exact absurd (le_bot_iff.1 (h0 ▸ hAM)) hA1
    · exact h0
  let eM : ↥M ≃* X := (MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥M := eM.isSimpleGroup
  have hcardM : Nat.card ↥M = Nat.card X := Nat.card_congr eM.toEquiv
  have hO : CFSG.Open.goldschmidtOddCore ↥M = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.goldschmidtOddCore ↥M) with
      h0 | h0
    · exact h0
    · exfalso
      have hodd := odd_card_goldschmidtOddCore ↥M
      rw [h0, Subgroup.card_top, hcardM] at hodd
      have hAp : IsPGroup 2 ↥A := S.isPGroup'.to_le hAS
      have hne : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
      obtain ⟨m, hm, hcard⟩ := hAp.nontrivial_iff_card.mp hne
      have h2 : 2 ∣ Nat.card X :=
        (dvd_pow_self 2 hm.ne').trans (hcard ▸ Subgroup.card_subgroup_dvd_card A)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  let eH : (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M) ≃* X :=
    ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans eM
  let eT : ↥(⊤ : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)) ≃* X :=
    Subgroup.topEquiv.trans eH
  have : IsSimpleGroup ↥(⊤ : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)) :=
    eT.isSimpleGroup
  have hnabT : ∃ a b : ↥(⊤ : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨eT.symm a, eT.symm b, fun h1 => hab ?_⟩
    apply eT.symm.injective
    rw [map_mul, map_mul, h1]
  obtain ⟨hq, hZ⟩ := isQuasisimple_and_center_eq_bot_of_isSimpleGroup hnabT
  have hcomp : CFSG.Open.IsComponentOf
      (⊤ : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)) ⊤ :=
    ⟨le_rfl, CFSG.Open.IsSubnormal.refl _, hq⟩
  let eZ : (↥(⊤ : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M)) ⧸
      Subgroup.center ↥(⊤ : Subgroup (↥M ⧸ CFSG.Open.goldschmidtOddCore ↥M))) ≃* X :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eT
  exact CFSG.ComponentClassification.AschbacherTheorem3.goldschmidtSimpleType_of_mulEquiv eZ.symm
    (hc ⊤ hcomp)

theorem exists_fusionBenderBorel_of_seitzRankOne {X : Type} [Group X] [Finite X]
    (h : SeitzRankOne X) : ∃ q k : ℕ, 8 ≤ q ^ k ∧ CFSG.Open.fusionBenderBorel X q k := by
  rcases h with ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hm⟩
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let e' : X ≃* PSL(2, GaloisField 2 f) :=
      e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f (by omega) hK)
    have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e'.toEquiv
    refine ⟨2 ^ f, 1, ?_,
      (CFSG.Open.bender_psl2_borel_full f (by omega)).map_mulEquiv e'.symm⟩
    rw [pow_one]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
    have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
    let e'' : X ≃* CFSG.Open.PSU3 2 f :=
      e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)
    have : Finite (CFSG.Open.PSU3 2 f) := Finite.of_equiv _ e''.toEquiv
    refine ⟨2 ^ f, 3, ?_, (CFSG.Open.bender_psu3_borel_full f hf).map_mulEquiv e''.symm⟩
    calc 8 = (2 ^ 1) ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) 3
  ·
    have hs : SuzukiModel X 2 f := by
      rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hs⟩
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact absurd ht (by decide)
      · exact hs
    obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := hs
    let e' : X ≃* CFSG.Open.Sz a :=
      e.trans ((MulEquiv.subgroupCongr
        (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
          (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
    have : Finite (CFSG.Open.Sz a) := Finite.of_equiv _ e'.toEquiv
    refine ⟨2 ^ (2 * a + 1), 2, ?_,
      (CFSG.Open.bender_suzuki_borel_full a ha).map_mulEquiv e'.symm⟩
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _

theorem eight_le_card_sylow_of_seitzRankOne {X : Type} [Group X] [Finite X] (h : SeitzRankOne X)
    (T : Sylow 2 X) : 8 ≤ Nat.card T := by
  obtain ⟨q, k, hqk, hB⟩ := exists_fusionBenderBorel_of_seitzRankOne h
  rw [(hB T).2.2.2.2]
  exact hqk

theorem eight_dvd_card_of_seitzRankOne {X : Type} [Group X] [Finite X] (h : SeitzRankOne X) :
    8 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp T.isPGroup'
  have h8 := eight_le_card_sylow_of_seitzRankOne h T
  rw [hn] at h8
  have hn3 : 3 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h8)
  have hT : 8 ∣ Nat.card T := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hn3
  exact hT.trans (Subgroup.card_subgroup_dvd_card _)

theorem exists_involution_centralizer_of_even {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (heven : Even (Nat.card (Subgroup.centralizer (L : Set G))))
    (hZ : Subgroup.center L = ⊥) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ Subgroup.centralizer (L : Set G) ∧ t ∉ L := by
  obtain ⟨c, hcC, hc⟩ := StandardSubgroupAPI.exists_mem_orderOf_eq_two_of_even heven
  refine ⟨c, hc, hcC, fun hcL => ?_⟩
  have hmem : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC l l.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  have hc1 : c = 1 := congrArg Subtype.val hmem
  have h1 : orderOf c = 1 := by rw [hc1, orderOf_one]
  rw [hc] at h1
  exact absurd h1 (by norm_num)

theorem exists_involution_centralizer_of_seitzSetting {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : SeitzSetting G L) :
    ∃ t : G, orderOf t = 2 ∧ t ∈ Subgroup.centralizer (L : Set G) ∧ t ∉ L := by
  obtain ⟨-, -, -, ⟨-, heven, -⟩, -, -, -, -, hZ⟩ := h
  exact exists_involution_centralizer_of_even heven hZ

theorem sixteen_dvd_card_of_involution {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (h8 : 8 ∣ Nat.card L) {t : X} (ht : orderOf t = 2) (htL : t ∉ L)
    (htC : t ∈ Subgroup.centralizer (L : Set X)) : 16 ∣ Nat.card X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 L) := inferInstance
  have h8T : 2 ^ 3 ∣ Nat.card T₁ := T₁.pow_dvd_card_of_pow_dvd_card (by simpa using h8)
  set T : Subgroup X := (T₁ : Subgroup L).map L.subtype
  have hcardT : Nat.card T = Nat.card T₁ := Subgroup.card_map_of_injective L.subtype_injective
  have hTL : T ≤ L := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := T₁.isPGroup'.map L.subtype
  have hz2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have htT : t ∈ Subgroup.centralizer (T : Set X) := Subgroup.centralizer_le hTL htC
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (T : Set X) :=
    (Subgroup.zpowers_le.mpr htT).trans (Subgroup.centralizer_le_normalizer _)
  set H : Subgroup X := T ⊔ Subgroup.zpowers t
  have hH2 : IsPGroup 2 H := hT2.to_sup_of_normal_left' hz2 hnorm
  have hTH : T ≤ H := le_sup_left
  have htH : t ∈ H := (le_sup_right : Subgroup.zpowers t ≤ H) (Subgroup.mem_zpowers t)
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hH2
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT2
  have hb3 : 3 ≤ b := by
    have h3 : 2 ^ 3 ∣ 2 ^ b := by rw [← hb, hcardT]; exact h8T
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3
  have hba : b < a := by
    have hdvd : 2 ^ b ∣ 2 ^ a := by rw [← hb, ← ha]; exact Subgroup.card_dvd_of_le hTH
    rcases ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hTeq : T = H := Subgroup.eq_of_le_of_card_ge hTH (by rw [ha, hb, heq])
      exact htL (hTL (hTeq ▸ htH))
  have h16H : 16 ∣ Nat.card H := by
    rw [ha]
    exact Dvd.dvd.trans (by norm_num : (16 : ℕ) ∣ 2 ^ 4) (pow_dvd_pow 2 (by omega))
  exact h16H.trans (Subgroup.card_subgroup_dvd_card H)

theorem false_of_stronglyClosed_abelian_of_involution (hGold : Goldschmidt1974) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hLns : ¬ Group.IsSolvable L) (h8 : 8 ∣ Nat.card L) {t : G} (ht : orderOf t = 2)
    (htL : t ∉ L) (htC : t ∈ Subgroup.centralizer (L : Set G)) (P : Sylow 2 G)
    {A : Subgroup G} (hAP : A ≤ (P : Subgroup G)) (hAab : IsMulCommutative A) (hA1 : A ≠ ⊥)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (P : Subgroup G) → g⁻¹ * a * g ∈ A) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := goldschmidtSimpleType_of_isSimpleGroup hGold hnab P hAP hAab hcl hA1
  have h16 := sixteen_dvd_card_of_involution h8 ht htL htC
  have hz2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hz1 : Subgroup.zpowers t ≠ ⊥ := by
    intro h0
    have ht1 : t ∈ (⊥ : Subgroup G) := h0 ▸ Subgroup.mem_zpowers t
    rw [Subgroup.mem_bot] at ht1
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hLC : L ≤ Subgroup.centralizer (Subgroup.zpowers t : Set G) :=
    Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr htC)
  exact false_of_goldschmidtSimpleType hG h16 hz1 hz2
    (hLC.trans (Subgroup.centralizer_le_normalizer _)) hLns

theorem false_of_stronglyClosed_abelian_of_goldschmidt (hGold : Goldschmidt1974) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (h : SeitzSetting G L) (h1 : SeitzRankOne L)
    (P : Sylow 2 G) {A : Subgroup G} (hAP : A ≤ (P : Subgroup G)) (hAab : IsMulCommutative A)
    (hA1 : A ≠ ⊥) (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (P : Subgroup G) → g⁻¹ * a * g ∈ A) :
    False := by
  obtain ⟨t, ht, htC, htL⟩ := exists_involution_centralizer_of_seitzSetting h
  obtain ⟨hsimple, hnab, -, ⟨hq, -⟩, -⟩ := h
  have hLns : ¬ Group.IsSolvable L := by
    intro hs
    have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
    have : Nontrivial ↥L := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L
    rw [hq.1] at hlt
    exact lt_irrefl _ hlt
  exact false_of_stronglyClosed_abelian_of_involution hGold hnab hLns
    (eight_dvd_card_of_seitzRankOne h1) ht htL htC P hAP hAab hA1 hcl

theorem false_of_stronglyClosed_abelian
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : SeitzSetting G L) (h1 : SeitzRankOne L)
    (P : Sylow 2 G) {A : Subgroup G} (hAP : A ≤ (P : Subgroup G)) (hAab : IsMulCommutative A)
    (hA1 : A ≠ ⊥) (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (P : Subgroup G) → g⁻¹ * a * g ∈ A) :
    False :=
  false_of_stronglyClosed_abelian_of_goldschmidt goldschmidt1974_of_milestone h h1 P hAP hAab hA1
    hcl

end CFSG.SeitzReduction.RankOne
