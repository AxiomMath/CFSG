module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Assembly
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21L2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem twoElements_le_of_layer_eq_bot' {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRc : IsMulCommutative R) (hL : CFSG.layer (K ⧸ CFSG.Assembly.oddCore K) = ⊥) :
    ∀ k ∈ K, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ oddCoreIn K ⊔ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Assembly.oddCore K with hN
  obtain ⟨S, hS⟩ := exists_sylow_map hR
  have hchar : centralizer (CFSG.pCore 2 (K ⧸ N) : Set (K ⧸ N)) ≤ CFSG.pCore 2 (K ⧸ N) :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2
      (pPrimeCore_quotient_assemblyOddCore_eq_bot K) hL
  have : (CFSG.pCore 2 (K ⧸ N)).Normal := CFSG.pCore_normal (p := 2)
  have hPS : CFSG.pCore 2 (K ⧸ N) ≤ S := (CFSG.pCore_isPGroup (p := 2)).le_sylow_of_normal S
  have hScomm : ∀ x ∈ (S : Subgroup (K ⧸ N)), ∀ y ∈ (S : Subgroup (K ⧸ N)), x * y = y * x := by
    rw [hS]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have h := congrArg Subtype.val (hRc.is_comm.comm ⟨a, mem_subgroupOf.mp ha⟩
      ⟨b, mem_subgroupOf.mp hb⟩)
    simp only [coe_mul] at h
    exact Subtype.ext (by simpa using h)
  have hSP : (S : Subgroup (K ⧸ N)) ≤ CFSG.pCore 2 (K ⧸ N) := by
    refine le_trans (fun x hx => ?_) hchar
    rw [mem_centralizer_iff]
    intro y hy
    exact hScomm y (hPS hy) x hx
  have hSn : (S : Subgroup (K ⧸ N)).Normal := by
    rw [le_antisymm hSP hPS]
    infer_instance
  intro k hk n hkn
  apply mem_sup_of_mk_mem hk
  rw [← hS]
  have hz := isPGroup_zpowers_of_pow_eq_one
    (x := QuotientGroup.mk' N (⟨k, hk⟩ : K)) (n := n) (by
      rw [← map_pow]
      have : (⟨k, hk⟩ : K) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hkn)
      rw [this, map_one])
  have heq := S.is_maximal' (hz.to_sup_of_normal_right S.isPGroup') le_sup_right
  rw [← heq]
  exact mem_sup_left (mem_zpowers _)

theorem not_isCyclic_of_isPerfect {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    [Group.IsPerfect Q] (P : Sylow 2 Q) : ¬ IsCyclic P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hPcyc
  have h2 : 2 ∣ Nat.card Q := by
    have h4 := four_dvd_card_of_isPerfect (Q := Q)
    exact (show 2 ∣ 4 by norm_num).trans h4
  have hmin : (Nat.card Q).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hcomp := IsCyclic.isComplement' hmin hPcyc
  have : Group.IsSolvable (P : Subgroup Q) := by
    have := P.isPGroup'.isNilpotent
    infer_instance
  rw [CFSG.ComponentClassification.SolvableKernelContainment.hom_eq_one
    (MonoidHom.transferSylow P (hPcyc.normalizer_le_centralizer hmin)), MonoidHom.ker_one]
    at hcomp
  have h := hcomp.card_mul_card
  rw [card_top] at h
  have hP1 : Nat.card (P : Subgroup Q) = 1 := by
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have : Nat.card Q * Nat.card (P : Subgroup Q) = Nat.card Q * 1 := by rw [h, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  exact Sylow.ne_bot_of_dvd_card P h2 (card_eq_one.mp hP1)

theorem false_of_pRank_twoPrimeLayerIn_eq_one' {K R : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRc : IsMulCommutative R) (hne : twoPrimeLayerIn K ≠ oddCoreIn K)
    (h1 : Open.pRank 2 (twoPrimeLayerIn K) = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Assembly.oddCore K with hN
  set E := CFSG.layer (K ⧸ N) with hE
  set L₀ := twoPrimeLayerIn K with hL₀
  have hE1 : E ≠ ⊥ := fun h => hne ((twoPrimeLayerIn_eq_oddCoreIn_iff K).mpr h)
  have : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hE1
  have : Group.IsPerfect E := CFSG.LocalCores.layer_isPerfect
  have hR₀ : IsSylowOf 2 (R ⊓ L₀) L₀ :=
    hR.inf_of_le_normalizer (twoPrimeLayerIn_le K) (le_normalizer_twoPrimeLayerIn K)
  have hR₀c : IsCyclic (R ⊓ L₀ : Subgroup G) := by
    refine AschbacherTheorem3.isCyclic_of_pRank_le_one hR₀.isPGroup
      (AschbacherTheorem3.isMulCommutative_of_le inf_le_left hRc) ?_
    have := CFSG.SectionRank.pRank_mono one_lt_two (inf_le_right : R ⊓ L₀ ≤ L₀)
    omega
  set φ : K →* K ⧸ N := QuotientGroup.mk' N with hφ
  have hR₀K : R ⊓ L₀ ≤ K := inf_le_left.trans hR.le
  set R₀' := (R ⊓ L₀).subgroupOf K with hR₀'
  have hinj : Function.Injective (φ.comp R₀'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro x hxk
    have hxN : (x : K) ∈ N := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hφ,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hxk
      exact hxk
    have hx' : ((x : K) : G) ∈ oddCoreIn K ⊓ R := ⟨⟨x, hxN, rfl⟩, (mem_subgroupOf.mp x.2).1⟩
    rw [oddCoreIn_inf_eq_bot hR.isPGroup, mem_bot] at hx'
    rw [mem_bot]
    exact Subtype.ext (Subtype.ext hx')
  set S₀ := (φ.comp R₀'.subtype).range with hS₀
  have hS₀E : S₀ ≤ E := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (mem_subgroupOf.mp x.2).2
    have hyx' : y = (x : K) := Subtype.ext hyx
    change φ (x : K) ∈ E
    rw [← hyx']
    exact hy
  have hcardS₀ : Nat.card S₀ = Nat.card (R ⊓ L₀ : Subgroup G) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hR₀K).toEquiv
  have hcardE : (Nat.card E).factorization 2 = (Nat.card L₀).factorization 2 := by
    have hL : Nat.card L₀ = Nat.card N * Nat.card E := card_twoPrimeLayerIn K
    have hNodd : Nat.card N % 2 = 1 := Nat.odd_iff.mp (odd_card_assemblyOddCore K)
    have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
    have hE0 : Nat.card E ≠ 0 := Nat.card_pos.ne'
    have hnd : ¬ 2 ∣ Nat.card N := by omega
    rw [hL, Nat.factorization_mul hN0 hE0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, zero_add]
  have hS₀syl : IsSylowOf 2 S₀ E := by
    refine isSylowOf_of_card hS₀E ?_
    rw [hcardS₀, hR₀.card_eq, hcardE]
  obtain ⟨P, hP⟩ := hS₀syl.exists_sylow_eq_subgroupOf
  apply not_isCyclic_of_isPerfect P
  rw [hP]
  have e : ↥(R ⊓ L₀ : Subgroup G) ≃* ↥(S₀.subgroupOf E) :=
    (subgroupOfEquivOfLe hR₀K).symm.trans
      ((MonoidHom.ofInjective hinj).trans (subgroupOfEquivOfLe hS₀E).symm)
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem isElemAbelian_of_caseD {K R T Y : Subgroup G} {g : G} (hK : TightlyEmbedded K)
    (hR : IsSylowOf 2 R K) (hRc : IsMulCommutative R) (hg : g ∉ normalizer (K : Set G))
    (hT : IsSylowOf 2 T (rightConjugate K g)) (hTN : T ≤ normalizer (K : Set G))
    (hY : Y = oUpperTwoPrime (K ⊔ T)) {n : ℕ} (hn : 2 ≤ n)
    (φ : Y →* Multiplicative (Fin n → ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (hφ : Function.Surjective φ) (hker : φ.ker = (oddCoreIn K).subgroupOf Y) :
    IsElemAbelian 2 R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn0 : n ≠ 0 := by omega
  set K₂ := oUpperTwoPrime K with hK₂
  set a := (Nat.card K).factorization 2 with ha
  have han : a ≤ n := factorization_le_of_caseD hK hg hT hTN hY hn0 φ hφ hker
  have hRa : Nat.card R = 2 ^ a := hR.card_eq
  have hK₂K : K₂ ≤ K := oUpperTwoPrime_le K
  have hK₂Y : K₂ ≤ Y := by
    rw [hY]
    exact closure_mono fun x ⟨hx, k, hk⟩ => ⟨mem_sup_left hx, k, hk⟩
  have hRK₂ : R ≤ K₂ := fun r hr => by
    obtain ⟨m, hm⟩ := hR.isPGroup ⟨r, hr⟩
    exact mem_oUpperTwoPrime (hR.le hr) (n := m) (by simpa using congrArg Subtype.val hm)
  have hφO : ∀ y : Y, φ y = 1 ↔ (y : G) ∈ oddCoreIn K := fun y => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  have hRO : ∀ r ∈ R, r ∈ oddCoreIn K → r = 1 := fun r hr hrO => by
    have h : r ∈ oddCoreIn K ⊓ R := ⟨hrO, hr⟩
    rwa [oddCoreIn_inf_eq_bot hR.isPGroup, mem_bot] at h
  let ψ : Y →* PSL(2, GaloisField 2 n) :=
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm.toMonoidHom.comp
      ((MonoidHom.snd _ _).comp φ)
  have hψ : Function.Surjective ψ := by
    intro x
    obtain ⟨y, hy⟩ := hφ (1, CFSG.Walter.psl2MulEquivSL2OfCharTwo x)
    refine ⟨y, ?_⟩
    change (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm (φ y).2 = x
    rw [hy]
    exact MulEquiv.symm_apply_apply _ _
  have hψφ : ∀ y : Y, ψ y = 1 → φ y ^ 2 = 1 := by
    intro y hy
    have h2 : (φ y).2 = 1 := by simpa [ψ] using hy
    ext1
    · exact sq_eq_one_multiplicative _
    · simp [h2]
  have hL : IsSimpleGroup PSL(2, GaloisField 2 n) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 n hn0]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  have hcardL : Nat.card PSL(2, GaloisField 2 n) = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    CFSG.Walter.psl2_even_card hn0
  have hK₂n : (K₂.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hK₂Y).mpr ((hY.le.trans (oUpperTwoPrime_le _)).trans
      ((sup_le le_normalizer hTN).trans (normalizer_le_normalizer_oUpperTwoPrime K)))
  have hJn : ((K₂.subgroupOf Y).map ψ).Normal := hK₂n.map ψ hψ
  refine ⟨hRc, fun r hr => ?_⟩
  have hrY : r ∈ Y := hK₂Y (hRK₂ hr)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K₂.subgroupOf Y).map ψ) with hJ | hJ
  · have hk1 : ψ ⟨r, hrY⟩ = 1 := by
      have : ψ ⟨r, hrY⟩ ∈ (K₂.subgroupOf Y).map ψ := ⟨⟨r, hrY⟩, hRK₂ hr, rfl⟩
      rwa [hJ, mem_bot] at this
    have h2 := (hφO (⟨r, hrY⟩ ^ 2)).mp (by rw [map_pow]; exact hψφ _ hk1)
    exact hRO _ (R.pow_mem hr 2) (by simpa using h2)
  let ψ₂ : K₂.subgroupOf Y →* PSL(2, GaloisField 2 n) := ψ.comp (K₂.subgroupOf Y).subtype
  have hψ₂r : ψ₂.range = ⊤ := by rw [MonoidHom.range_comp, range_subtype, hJ]
  have hcardK₂ : Nat.card ψ₂.ker * Nat.card PSL(2, GaloisField 2 n) = Nat.card K₂ := by
    have h := Subgroup.card_ker_mul_card_range ψ₂
    rw [hψ₂r, card_top, Nat.card_congr (subgroupOfEquivOfLe hK₂Y).toEquiv] at h
    exact h
  have hRK₂s : IsSylowOf 2 R K₂ := hR.of_le hRK₂ hK₂K
  have hdvdK₂ : ∀ j, 2 ^ j ∣ Nat.card K₂ → j ≤ a := fun j hj => by
    have := pow_dvd_card_of_isSylowOf hRK₂s hj
    rw [hRa] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  have hkerodd : Odd (Nat.card ψ₂.ker) := by
    refine Nat.not_even_iff_odd.mp fun he => ?_
    obtain ⟨m, hm⟩ := even_iff_two_dvd.mp he
    have h := hdvdK₂ (n + 1) (by
      rw [← hcardK₂, hcardL, hm, pow_succ]
      exact ⟨m * ((2 ^ n) ^ 2 - 1), by ring⟩)
    omega
  have hkey : ∀ y : Y, (y : G) ∈ K₂ → ψ y = 1 → (y : G) ∈ oddCoreIn K := by
    intro y hyK hy
    have hx : (⟨y, hyK⟩ : K₂.subgroupOf Y) ∈ ψ₂.ker := hy
    have hdvd1 : orderOf (φ y) ∣ 2 := orderOf_dvd_of_pow_eq_one (hψφ y hy)
    have hdvd2 : orderOf (φ y) ∣ Nat.card ψ₂.ker := by
      let χ := φ.comp ((K₂.subgroupOf Y).subtype.comp ψ₂.ker.subtype)
      have h1 : χ ⟨_, hx⟩ = φ y := rfl
      rw [← h1]
      exact (orderOf_map_dvd χ _).trans (orderOf_dvd_natCard _)
    have h1 : orderOf (φ y) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hkerodd) hdvd1 hdvd2
    exact (hφO y).mp (orderOf_eq_one_iff.mp h1)
  have hRinj : ∀ ρ ∈ R, ∀ hρ : ρ ∈ Y, ψ ⟨ρ, hρ⟩ = 1 → ρ = 1 := fun ρ hρR hρ h =>
    hRO ρ hρR (hkey ⟨ρ, hρ⟩ (hRK₂ hρR) h)
  by_cases hR1 : R = ⊥
  · rw [hR1] at hr
    rw [mem_bot.mp hr, one_pow]
  have h2R : 2 ∣ Nat.card R := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR.isPGroup
    rcases m with _ | m
    · exact absurd (card_eq_one.mp (by simpa using hm)) hR1
    · rw [hm, pow_succ]
      exact dvd_mul_left _ _
  obtain ⟨⟨r₀, hr₀⟩, hr₀2⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2R
  rw [Subgroup.orderOf_mk] at hr₀2
  have hr₀Y : r₀ ∈ Y := hK₂Y (hRK₂ hr₀)
  have ht : orderOf (ψ ⟨r₀, hr₀Y⟩) = 2 := by
    refine orderOf_eq_prime ?_ fun h => ?_
    · rw [← map_pow]
      have : (⟨r₀, hr₀Y⟩ : Y) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, ← hr₀2]
        exact pow_orderOf_eq_one r₀)
      rw [this, map_one]
    · have := hRinj r₀ hr₀ hr₀Y h
      rw [this, orderOf_one] at hr₀2
      norm_num at hr₀2
  have hc : ψ ⟨r, hrY⟩ ∈ centralizer ({ψ ⟨r₀, hr₀Y⟩} : Set PSL(2, GaloisField 2 n)) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h := congrArg Subtype.val (hRc.is_comm.comm ⟨r, hr⟩ ⟨r₀, hr₀⟩)
    simpa using h
  have hsq := CFSG.Walter.psl2_sq_eq_one_of_mem_centralizer_of_charTwo ht hc
  have hr2Y : r ^ 2 ∈ Y := Y.pow_mem hrY 2
  have hψr2 : ψ ⟨r ^ 2, hr2Y⟩ = 1 := by
    have : (⟨r ^ 2, hr2Y⟩ : Y) = ⟨r, hrY⟩ ^ 2 := rfl
    rw [this, map_pow, hsq]
  exact hRinj _ (R.pow_mem hr 2) hr2Y hψr2

end CFSG.ComponentClassification.Asc76.Sec5
