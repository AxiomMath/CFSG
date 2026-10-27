module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeAltSix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNormalizesNoSU
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35K6bA
import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143Card
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSolvDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_conj_of_pow_three_pow {K : Type*} [Group K] (hK : ¬ 3 ∣ Nat.card (Outer K))
    {α : MulAut K} {k : ℕ} (hα : α ^ 3 ^ k = 1) : ∃ g : K, α = MulAut.conj g := by
  set q := QuotientGroup.mk' (inner K) α with hq
  have hq3 : q ^ 3 ^ k = 1 := by rw [hq, ← map_pow, hα, map_one]
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Outer K)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK)
  have hd : orderOf q ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hq3) (orderOf_dvd_natCard q)
  rw [Nat.dvd_one, orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hd
  obtain ⟨g, hg⟩ := hd
  exact ⟨g, hg.symm⟩

theorem exists_mul_of_pow_three_pow {K : Subgroup Y} [K.Normal]
    (hX : ∀ α : MulAut K, ∀ k : ℕ, α ^ 3 ^ k = 1 → ∃ g : K, α = MulAut.conj g)
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥) {y : Y} {n : ℕ} (hy : y ^ 3 ^ n = 1) :
    ∃ k ∈ K, ∃ c ∈ centralizer (K : Set Y), y = k * c ∧ k ^ 3 ^ n = 1 ∧ c ^ 3 ^ n = 1 := by
  set θ : Y →* MulAut K := MulAut.conjNormal with hθ
  have hθ3 : θ y ^ 3 ^ n = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨g, hg⟩ := hX _ n hθ3
  have hc : (g : Y)⁻¹ * y ∈ centralizer (K : Set Y) := by
    refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
    have h1 := congrArg (fun a : MulAut K => ((a ⟨m, hm⟩ : K) : Y)) hg
    simp only [hθ, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc m * ((g : Y)⁻¹ * y) = (g : Y)⁻¹ * ((g : Y) * m * (g : Y)⁻¹) * y := by group
      _ = (g : Y)⁻¹ * (y * m * y⁻¹) * y := by rw [h1]
      _ = (g : Y)⁻¹ * y * m := by group
  have hkc : (g : Y) * ((g : Y)⁻¹ * y) = ((g : Y)⁻¹ * y) * g :=
    Subgroup.mem_centralizer_iff.mp hc g g.2
  have h1 : (g : Y) ^ 3 ^ n * ((g : Y)⁻¹ * y) ^ 3 ^ n = 1 := by
    rw [← Commute.mul_pow hkc, mul_inv_cancel_left, hy]
  have hc3 : ((g : Y)⁻¹ * y) ^ 3 ^ n = 1 := by
    have h2 : ((g : Y)⁻¹ * y) ^ 3 ^ n ∈ K ⊓ centralizer (K : Set Y) := by
      refine ⟨?_, Subgroup.pow_mem _ hc _⟩
      rw [eq_inv_of_mul_eq_one_right h1]
      exact K.inv_mem (K.pow_mem g.2 _)
    rwa [hKC, Subgroup.mem_bot] at h2
  refine ⟨g, g.2, (g : Y)⁻¹ * y, hc, by group, ?_, hc3⟩
  rwa [hc3, mul_one] at h1

theorem three_le_pRank_of_sup_zpowers {H F : Subgroup Y} {c : Y} (hFH : F ≤ H) (hcH : c ∈ H)
    (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 3 ^ 2) (hc3 : c ^ 3 = 1) (hcF : c ∉ F)
    (hcomm : ∀ a ∈ F, a * c = c * a) : 3 ≤ CFSG.Open.pRank 3 H := by
  have hcomm' : ∀ a ∈ F, ∀ b ∈ zpowers c, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a c from hcomm a ha) k).eq
  have hel := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hF
    (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hc3) hcomm'
  obtain ⟨k, hk⟩ := CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_three hel
  have hlt : F < F ⊔ zpowers c := by
    refine lt_of_le_of_ne le_sup_left fun h => hcF ?_
    rw [h]
    exact mem_sup_right (mem_zpowers c)
  have hcard := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
  rw [hFc, hk] at hcard
  have hk3 : 3 ≤ k := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp hcard
    omega
  have hle : k ≤ CFSG.Open.pRank 3 H :=
    CFSG.GH74.Uniqueness.SU.SU1.le_pRank (by norm_num) (sup_le hFH (zpowers_le.mpr hcH)) hel hk
  omega

theorem eq_one_of_inf_eq_bot_of_pow {N : Subgroup Y} [N.Normal] {R : Sylow 3 Y}
    (hRN : (R : Subgroup Y) ⊓ N = ⊥) {c : Y} (hc : c ∈ N) {n : ℕ} (hcn : c ^ 3 ^ n = 1) :
    c = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R N
  have hPbot : (P : Subgroup N) = ⊥ := by
    rw [hRN] at hP
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hP
  have hzp : IsPGroup 3 (zpowers (⟨c, hc⟩ : N)) := by
    rintro ⟨w, hw⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have : (⟨c, hc⟩ : N) ^ 3 ^ n = 1 := Subtype.ext (by simpa using hcn)
    rw [this, one_zpow]
  obtain ⟨P', hP'⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N P P'
  have hP'bot : (P' : Subgroup N) = ⊥ := by
    rw [← hg, Sylow.coe_subgroup_smul, hPbot, Subgroup.smul_bot]
  have h1 : (⟨c, hc⟩ : N) ∈ (P' : Subgroup N) := hP' (mem_zpowers _)
  rw [hP'bot, Subgroup.mem_bot] at h1
  simpa using congrArg Subtype.val h1

theorem le_normalizer_of_borel {K Y₀ E : Subgroup Y} [K.Normal] {R : Sylow 3 Y}
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hX : ∀ α : MulAut K, ∀ k : ℕ, α ^ 3 ^ k = 1 → ∃ g : K, α = MulAut.conj g)
    (hrkK : CFSG.Open.pRank 3 K ≤ 2)
    (T : Sylow 3 K) (hT : (T : Subgroup K).map K.subtype = (R : Subgroup Y) ⊓ K)
    (hF : ∃ F : Subgroup Y, F ≤ (R : Subgroup Y) ⊓ K ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 2)
    (hmax : ∀ H : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ H →
      H = normalizer ((T : Subgroup K) : Set K) ∨ H = ⊤)
    (hKnle : ¬ K ≤ Y₀)
    (hER : E ≤ R) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 2)
    (hcore : (if 3 ≤ CFSG.pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀) :
    (R : Subgroup Y) ⊓ K ≤ Y₀ ∧ Y₀ ≤ normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  set U : Subgroup Y := (R : Subgroup Y) ⊓ K with hU
  obtain ⟨F, hFU, hFel, hFc⟩ := hF
  have hrk3 : (R : Subgroup Y) ⊓ C ≠ ⊥ →
      3 ≤ CFSG.Open.pRank 3 (U ⊔ ((R : Subgroup Y) ⊓ centralizer (U : Set Y))) := by
    intro hne
    have hRp : IsPGroup 3 ↥((R : Subgroup Y) ⊓ C) := R.isPGroup'.to_le inf_le_left
    have hcard : 3 ∣ Nat.card ↥((R : Subgroup Y) ⊓ C) := by
      haveI : Nontrivial ↥((R : Subgroup Y) ⊓ C) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      obtain ⟨k, hk⟩ := hRp.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        have := Finite.one_lt_card (α := ↥((R : Subgroup Y) ⊓ C))
        rw [hk] at this
        simp at this
      rw [hk]
      exact dvd_pow_self 3 hk0
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hcard
    have hzR : (z : Y) ∈ (R : Subgroup Y) := z.2.1
    have hzC : (z : Y) ∈ C := z.2.2
    have hzo : orderOf (z : Y) = 3 := by rw [Subgroup.orderOf_coe, hz]
    have hz3 : (z : Y) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hzo)
    have hz1 : (z : Y) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzo
      omega
    have hzF : (z : Y) ∉ F := by
      intro h
      have : (z : Y) ∈ K ⊓ C := ⟨(hFU h).2, hzC⟩
      rw [hKC, Subgroup.mem_bot] at this
      exact hz1 this
    refine three_le_pRank_of_sup_zpowers (hFU.trans le_sup_left)
      (mem_sup_right ⟨hzR, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩) hFel hFc hz3 hzF
      fun a ha => (Subgroup.mem_centralizer_iff.mp hzC a (hFU ha).2)
    exact Subgroup.mem_centralizer_iff.mp hzC u hu.2
  have hRK : (R : Subgroup Y) ⊓ C = ⊥ → (R : Subgroup Y) ≤ K := by
    intro hRC r hr
    obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
    have hrn : r ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨k, hk, c, hc, rfl, -, hcn⟩ := exists_mul_of_pow_three_pow hX hKC hrn
    rw [eq_one_of_inf_eq_bot_of_pow hRC hc hcn, mul_one]
    exact hk
  have hNU : normalizer (U : Set Y) ≤ Y₀ := by
    have hU2 : 2 ≤ CFSG.Open.pRank 3 U := CFSG.SectionRank.le_pRank (by norm_num) hFU hFel hFc
    by_cases h3 : 3 ≤ CFSG.pRank 3 (R : Subgroup Y)
    · rw [if_pos h3] at hcore
      have hne : (R : Subgroup Y) ⊓ C ≠ ⊥ := by
        intro hRC
        have hRU : (R : Subgroup Y) ≤ K := hRK hRC
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
        have := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hRU
        omega
      exact (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3 inf_le_left hU2
        (hrk3 hne)).trans hcore
    · have hRC : (R : Subgroup Y) ⊓ C = ⊥ := by
        by_contra hne
        apply h3
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
        exact (hrk3 hne).trans (CFSG.SectionRank.pRank_mono (by norm_num)
          (sup_le inf_le_left inf_le_left))
      have hUR : U = (R : Subgroup Y) := inf_eq_left.mpr (hRK hRC)
      rw [hUR]
      exact (normalizer_sylow_le_threeFourCore Nat.prime_three R hER hE hEc).trans hcore
  have hmemU : ∀ v : Y, ∀ hv : v ∈ K, v ∈ U ↔ (⟨v, hv⟩ : K) ∈ (T : Subgroup K) := by
    intro v hv
    rw [← hT]
    constructor
    · rintro ⟨w, hw, hwv⟩
      have hwv' : w = ⟨v, hv⟩ := Subtype.ext hwv
      rwa [hwv'] at hw
    · intro h
      exact ⟨_, h, rfl⟩
  have hle : normalizer ((T : Subgroup K) : Set K) ≤ Y₀.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hNU
    rw [Subgroup.mem_normalizer_iff]
    intro v
    by_cases hv : v ∈ K
    · have hconj : (x : Y) * v * (x : Y)⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem v hv x
      rw [hmemU v hv, hmemU _ hconj]
      have h1 : (⟨(x : Y) * v * (x : Y)⁻¹, hconj⟩ : K) = x * ⟨v, hv⟩ * x⁻¹ :=
        Subtype.ext (by simp)
      rw [h1]
      exact Subgroup.mem_normalizer_iff.mp hx _
    · have hconj : ¬ (x : Y) * v * (x : Y)⁻¹ ∈ K := by
        intro h
        apply hv
        have h1 := (inferInstance : K.Normal).conj_mem _ h (x : Y)⁻¹
        simpa [mul_assoc] using h1
      exact ⟨fun h => absurd (Subgroup.mem_inf.mp h).2 hv,
        fun h => absurd (Subgroup.mem_inf.mp h).2 hconj⟩
  have hEq : Y₀.subgroupOf K = normalizer ((T : Subgroup K) : Set K) := by
    rcases hmax _ hle with h | h
    · exact h
    · exact absurd (fun k hk => by
        have := h ▸ Subgroup.mem_top (⟨k, hk⟩ : K)
        exact Subgroup.mem_subgroupOf.mp this) hKnle
  have hUY₀ : U ≤ Y₀ := Subgroup.le_normalizer.trans hNU
  have hY₀U : ∀ g ∈ Y₀, ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    have hvK : g * u * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem u hu.2 g
    have hvY : g * u * g⁻¹ ∈ Y₀ := Y₀.mul_mem (Y₀.mul_mem hg (hUY₀ hu)) (Y₀.inv_mem hg)
    have hvN : (⟨g * u * g⁻¹, hvK⟩ : K) ∈ normalizer ((T : Subgroup K) : Set K) := by
      rw [← hEq]
      exact Subgroup.mem_subgroupOf.mpr hvY
    obtain ⟨n, hn⟩ := R.isPGroup' ⟨u, hu.1⟩
    have hun : u ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hzp : IsPGroup 3 (zpowers (⟨g * u * g⁻¹, hvK⟩ : K)) := by
      rintro ⟨w, hw⟩
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
      refine ⟨n, Subtype.ext ?_⟩
      have h1 : (⟨g * u * g⁻¹, hvK⟩ : K) ^ 3 ^ n = 1 := Subtype.ext (by
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [conj_pow, hun, mul_one, mul_inv_cancel])
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
    have hsup := T.isPGroup'.to_sup_of_normal_left' hzp (zpowers_le.mpr hvN)
    have hmaxT := T.is_maximal' hsup le_sup_left
    have hmem : (⟨g * u * g⁻¹, hvK⟩ : K) ∈ (T : Subgroup K) := by
      rw [← hmaxT]
      exact mem_sup_right (mem_zpowers _)
    exact (hmemU _ hvK).mpr hmem
  refine ⟨hUY₀, fun g hg => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hY₀U g hg x hx, fun hx => ?_⟩
  have h1 := hY₀U g⁻¹ (Y₀.inv_mem hg) _ hx
  simpa [mul_assoc] using h1

theorem perm_three_exists_inv_sq : ∀ a : Equiv.Perm (Fin 3), a ^ 3 = 1 →
    ∃ τ : Equiv.Perm (Fin 3), τ * a * τ⁻¹ = a⁻¹ ∧ τ ^ 2 = 1 := by decide

theorem exists_card_nine_le_centralizer {U : Subgroup Y} {t : Y} (hU27 : Nat.card U = 27)
    (htU : t ∈ normalizer (U : Set Y)) {m : ℕ} (htm : t ^ 2 ^ m = 1)
    (hcomm : Nat.card ↥⁅U, zpowers t⁆ ≤ 3) :
    ∃ F : Subgroup Y, F ≤ U ∧ F ≤ centralizer ({t} : Set Y) ∧ Nat.card F = 3 ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAU : zpowers t ≤ normalizer (U : Set Y) := zpowers_le.mpr htU
  have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 3) (by rw [hU27]; norm_num)
  have hcop : Nat.Coprime (Nat.card (zpowers t)) (Nat.card U) := by
    rw [Nat.card_zpowers, hU27]
    have hdvd : orderOf t ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one htm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj]
    exact Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 27)
  haveI : Group.IsNilpotent U := hUp.isNilpotent
  have hfact := CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite
    hAU hcop inferInstance
  set H : Subgroup Y := U ⊓ centralizer ((zpowers t : Subgroup Y) : Set Y) with hH
  have hHN : H ≤ normalizer ((⁅U, zpowers t⁆ : Subgroup Y) : Set Y) :=
    inf_le_left.trans (Subgroup.normalizer_commutator_ge_left U (zpowers t))
  have hcard := CFSG.ComponentClassification.AS76b.card_sup_le_mul hHN
  have h27 : 27 ≤ Nat.card ↥⁅U, zpowers t⁆ * Nat.card H := by
    rw [← hU27]
    exact (Subgroup.card_le_of_le hfact).trans hcard
  have hH9 : 9 ≤ Nat.card H := by nlinarith
  have hHp : IsPGroup 3 H := hUp.to_le inf_le_left
  obtain ⟨r, hr⟩ := hHp.exists_card_eq
  have hr2 : 2 ≤ r := by
    by_contra h
    push Not at h
    interval_cases r <;> simp_all
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime 3
    ((pow_dvd_pow 3 hr2).trans (dvd_of_eq hr.symm) : 3 ^ 2 ∣ Nat.card H)
  refine ⟨F'.map H.subtype, (Subgroup.map_subtype_le _).trans inf_le_left, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.mp x.2.2 t (mem_zpowers t)
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hF']

omit [Finite Y] in
theorem isPGroup_zpowers_of_pow_eq_one {p n : ℕ} {g : Y} (h : g ^ p ^ n = 1) :
    IsPGroup p (zpowers g) := by
  rintro ⟨w, hw⟩
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
  refine ⟨n, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

omit [Finite Y] in
theorem conjNormal_eq_one_iff {K : Subgroup Y} [K.Normal] {a : Y} :
    (MulAut.conjNormal a : MulAut K) = 1 ↔ a ∈ centralizer (K : Set Y) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
    have h1 := congrArg (fun φ : MulAut K => ((φ ⟨m, hm⟩ : K) : Y)) h
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc m * a = (a * m * a⁻¹) * a := by rw [h1]
      _ = a * m := by group
  · intro h
    refine MulEquiv.ext fun m => Subtype.ext ?_
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [← Subgroup.mem_centralizer_iff.mp h m m.2]
    group

theorem card_map_of_forall_eq_one {G H : Type*} [Group G] [Group H] (f : G →* H)
    {U : Subgroup G} (hU : ∀ u ∈ U, f u = 1 → u = 1) : Nat.card (U.map f) = Nat.card U := by
  have hinj : Function.Injective (f.subgroupMap U) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (hU u u.2 (congrArg Subtype.val hu))
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, f.subgroupMap_surjective U⟩)).symm

theorem eq_of_le_of_not_comm {G : Type*} [Group G] {H L : Subgroup G} (hHL : H ≤ L)
    (hL : Nat.card L = 27) (hH : ¬ ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : H = L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have hdvd : Nat.card H ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le hHL
    rwa [hL] at this
  obtain ⟨n, hn3, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  refine Subgroup.eq_of_le_of_card_ge hHL ?_
  rw [hL, hn]
  by_contra hlt
  apply hH
  have hn2 : n ≤ 2 := by
    by_contra h
    have h3 : n = 3 := by omega
    rw [h3] at hlt
    exact hlt (by norm_num)
  intro x hx y hy
  interval_cases n
  · have hbot : H = ⊥ := Subgroup.eq_bot_of_card_eq H (by simpa using hn)
    rw [hbot, Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  · haveI : IsCyclic H := isCyclic_of_prime_card (p := 3) (by simpa using hn)
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := H)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · exact congrArg Subtype.val (IsPGroup.commutative_of_card_eq_prime_sq hn ⟨x, hx⟩ ⟨y, hy⟩)

omit [Finite Y] in
theorem commutator_le_of_isSubnormal {S Y₀ U A : Subgroup Y} (hS : IsSubnormal S Y₀)
    (hUY : U ≤ Y₀) (hAS : A ≤ S) (hAU : A ≤ normalizer (U : Set Y))
    (hcomm : ⁅⁅U, A⁆, A⁆ = ⁅U, A⁆) : ⁅U, A⁆ ≤ S := by
  obtain ⟨d, hd⟩ := exists_iterate_commutator_le_of_isSubnormal hS hUY
  have h1 : ∀ n : ℕ, ⁅U, A⁆ ≤ (fun X : Subgroup Y => ⁅X, A⁆)^[n] U := by
    intro n
    induction n with
    | zero => exact Subgroup.le_normalizer_iff_commutator_le_left.mp hAU
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc ⁅U, A⁆ = ⁅⁅U, A⁆, A⁆ := hcomm.symm
        _ ≤ ⁅(fun X : Subgroup Y => ⁅X, A⁆)^[n] U, A⁆ := Subgroup.commutator_mono ih le_rfl
  have h2 : ∀ n : ℕ, (fun X : Subgroup Y => ⁅X, A⁆)^[n] U ≤
      (fun X : Subgroup Y => ⁅X, S⁆)^[n] U := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Subgroup.commutator_mono ih hAS
  exact (h1 d).trans ((h2 d).trans hd)

theorem commute_of_commutator_mem {K P : Subgroup Y} [K.Normal]
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hrkC : CFSG.Open.pRank 3 (centralizer (K : Set Y)) ≤ 1)
    (hP3 : ∀ x ∈ P, x ^ 3 = 1) (hPKC : P ≤ K ⊔ centralizer (K : Set Y))
    (hPC : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ centralizer (K : Set Y)) :
    ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  have hcube : ∀ k ∈ K, ∀ c ∈ C, (k * c) ^ 3 = 1 → c ^ 3 = 1 := by
    intro k hk c hc h
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.mp hc k hk
    have h1 : k ^ 3 * c ^ 3 = 1 := by rw [← Commute.mul_pow hkc 3]; exact h
    have h2 : c ^ 3 ∈ K ⊓ C := by
      refine ⟨?_, Subgroup.pow_mem _ hc 3⟩
      rw [eq_inv_of_mul_eq_one_right h1]
      exact K.inv_mem (K.pow_mem hk 3)
    rwa [hKC, Subgroup.mem_bot] at h2
  set PC : Subgroup Y := (P ⊔ K) ⊓ C with hPC'
  have hPC3 : ∀ w ∈ PC, w ^ 3 = 1 := by
    intro w hw
    obtain ⟨hwPK, hwC⟩ := Subgroup.mem_inf.mp hw
    rw [sup_comm, ← SetLike.mem_coe, Subgroup.normal_mul K P] at hwPK
    obtain ⟨k, hk, p, hp, rfl⟩ := Set.mem_mul.mp hwPK
    have hpe : p = k⁻¹ * (k * p) := by group
    have hp3 := hP3 p hp
    rw [hpe] at hp3
    exact hcube _ (K.inv_mem hk) _ hwC hp3
  have hPCc := commute_of_pow_three_of_pRank_le_one inf_le_right hrkC hPC3
  have hdec : ∀ x ∈ P, ∃ k ∈ K, ∃ c ∈ PC, x = k * c ∧ ∀ k' ∈ K, c * k' = k' * c := by
    intro x hx
    have hx' := hPKC hx
    rw [← SetLike.mem_coe, Subgroup.normal_mul K C] at hx'
    obtain ⟨k, hk, c, hc, rfl⟩ := Set.mem_mul.mp hx'
    refine ⟨k, hk, c, ⟨?_, hc⟩, rfl, fun k' hk' =>
      (Subgroup.mem_centralizer_iff.mp hc k' hk').symm⟩
    have : c = k⁻¹ * (k * c) := by group
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_right (K.inv_mem hk)) (mem_sup_left hx)
  intro x hx y hy
  obtain ⟨k₁, hk₁, c₁, hc₁, rfl, hc₁K⟩ := hdec x hx
  obtain ⟨k₂, hk₂, c₂, hc₂, rfl, hc₂K⟩ := hdec y hy
  have e2 := hPCc c₁ hc₁ c₂ hc₂
  have e3 := hc₁K k₂ hk₂
  have e4 := hc₂K k₁ hk₁
  have hxy : k₁ * c₁ * (k₂ * c₂) = k₁ * k₂ * (c₁ * c₂) := by
    calc k₁ * c₁ * (k₂ * c₂) = k₁ * (c₁ * k₂) * c₂ := by group
      _ = k₁ * (k₂ * c₁) * c₂ := by rw [e3]
      _ = k₁ * k₂ * (c₁ * c₂) := by group
  have hyx : k₂ * c₂ * (k₁ * c₁) = k₂ * k₁ * (c₁ * c₂) := by
    calc k₂ * c₂ * (k₁ * c₁) = k₂ * (c₂ * k₁) * c₁ := by group
      _ = k₂ * (k₁ * c₂) * c₁ := by rw [e4]
      _ = k₂ * k₁ * (c₂ * c₁) := by group
      _ = k₂ * k₁ * (c₁ * c₂) := by rw [e2]
  have hw : k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ K ⊓ C := by
    refine ⟨K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂), ?_⟩
    have h := hPC _ hx _ hy
    have he : k₁ * c₁ * (k₂ * c₂) * (k₁ * c₁)⁻¹ * (k₂ * c₂)⁻¹ =
        (k₁ * c₁ * (k₂ * c₂)) * (k₂ * c₂ * (k₁ * c₁))⁻¹ := by group
    rw [he, hxy, hyx] at h
    have he' : k₁ * k₂ * (c₁ * c₂) * (k₂ * k₁ * (c₁ * c₂))⁻¹ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by
      group
    rwa [he'] at h
  rw [hKC, Subgroup.mem_bot] at hw
  have hk : k₁ * k₂ = k₂ * k₁ := by
    calc k₁ * k₂ = (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) * (k₂ * k₁) := by group
      _ = k₂ * k₁ := by rw [hw, one_mul]
  rw [hxy, hyx, hk]

theorem mulAut_eq_one_of_two_pow_of_forall {K : Type*} [Group K] (R : Subgroup (MulAut K))
    (hcent : ∀ ψ : MulAut K, ψ ^ 2 = 1 → (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1)
    {α : MulAut K} {m : ℕ} (hα : α ^ 2 ^ m = 1) (hc : ∀ r ∈ R, α * r = r * α) : α = 1 := by
  induction m with
  | zero => simpa using hα
  | succ m ih =>
    refine ih ?_
    have h2 : (α ^ 2 ^ m) ^ 2 = 1 := by rw [← pow_mul, ← pow_succ]; exact hα
    exact hcent _ h2 fun r hr => (Commute.pow_left (hc r hr) _).eq

theorem mem_centralizer_of_two_pow_of_forall {K : Subgroup Y} [K.Normal]
    (hcent : ∀ R : Subgroup (MulAut K), CFSG.GH74.KGroups.ElemAb 3 R → Nat.card R = 9 →
      ∀ ψ : MulAut K, ψ ^ 2 = 1 → (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1)
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥) {t : Y} {m : ℕ} (ht : t ^ 2 ^ m = 1)
    {F : Subgroup Y} (hFK : F ≤ K) (hFt : F ≤ centralizer ({t} : Set Y))
    (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 3 ^ 2) : t ∈ centralizer (K : Set Y) := by
  obtain ⟨θ, hθ⟩ : ∃ θ : Y →* MulAut K, θ = MulAut.conjNormal := ⟨_, rfl⟩
  have hθ1 : ∀ a : Y, θ a = 1 ↔ a ∈ centralizer (K : Set Y) := fun a => by
    rw [hθ]; exact conjNormal_eq_one_iff
  have hθF : ∀ u ∈ F, θ u = 1 → u = 1 := fun u hu h1 => by
    have : u ∈ K ⊓ centralizer (K : Set Y) := ⟨hFK hu, (hθ1 u).mp h1⟩
    rwa [hKC, Subgroup.mem_bot] at this
  have hRc : Nat.card (F.map θ) = 9 := by rw [card_map_of_forall_eq_one θ hθF, hFc]; norm_num
  have hR : CFSG.GH74.KGroups.ElemAb 3 (F.map θ) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hab : a * b = b * a := congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      rw [← map_mul, ← map_mul, hab]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hF.2 a ha, map_one]
  refine (hθ1 t).mp (mulAut_eq_one_of_two_pow_of_forall (F.map θ) (hcent _ hR hRc)
    (by rw [← map_pow, ht, map_one]) ?_)
  rintro _ ⟨a, ha, rfl⟩
  have hta : t * a = a * t :=
    Subgroup.mem_centralizer_iff.mp (hFt ha) t (Set.mem_singleton t)
  rw [← map_mul, ← map_mul, hta]


end Generic

section Solvable

variable {Y I₀ : Type} [Group Y] [Finite Y] [Group I₀] [Finite I₀]

theorem card_dvd_card_quotient_of_isPGroup (σ : I₀ →* Y) {Q : Subgroup Y} (hQ : IsPGroup 3 Q)
    (hQS : Q ≤ σ.range) : Nat.card Q ∣ Nat.card (I₀ ⧸ CFSG.pCore 2 I₀) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup (p := 2) (G := I₀)).exists_card_eq
  have hcardI : Nat.card I₀ = Nat.card (I₀ ⧸ CFSG.pCore 2 I₀) * 2 ^ e := by
    rw [← he]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  have h1 : Nat.card Q ∣ Nat.card I₀ :=
    (Subgroup.card_dvd_of_le hQS).trans (Subgroup.card_range_dvd σ)
  rw [hcardI] at h1
  have hcop : Nat.Coprime (Nat.card Q) (2 ^ e) := by
    rw [ha]
    exact Nat.Coprime.pow a e (by norm_num)
  exact hcop.dvd_of_dvd_mul_right h1

omit [Finite I₀] in
theorem card_quotient_pCore_of_not_symThree
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀))
    (hs3 : ¬ Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3))) :
    Nat.card (I₀ ⧸ CFSG.pCore 2 I₀) = 216 := by
  rcases hb with hf | ⟨F, _, _, hF, ⟨f⟩⟩
  · exact absurd hf hs3
  · rw [Nat.card_congr f.toEquiv,
      CFSG.HardMathSupport.Solomon.Coordinator.card_statedSU_three_of' (q := 2)
        (by rw [hF]; norm_num)]
    norm_num

theorem not_comm_map_sylow (σ : I₀ →* Y) (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀))
    (hs3 : ¬ Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)))
    (hker : Nat.Coprime 3 (Nat.card σ.ker)) (P₀ : Sylow 3 I₀) :
    ¬ ∀ x ∈ (P₀ : Subgroup I₀).map σ, ∀ y ∈ (P₀ : Subgroup I₀).map σ, x * y = y * x := by
  intro hcomm'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, ha, hb3, hab⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNoSU.exists_cube_not_comm hb
      (not_nonempty_iff.mp hs3)
  have hH : IsPGroup 3
      (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀))) := by
    intro x
    exact ⟨1, Subtype.ext (by
      simpa using IsSymThreeOrSUThreeTwo.cube kFactSUThreeTwoShape_holds hb x x.2)⟩
  have hmemH : ∀ z : I₀ ⧸ CFSG.pCore 2 I₀, z ^ 3 = 1 →
      z ∈ CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) :=
    fun z hz => Subgroup.subset_closure
      ⟨Subgroup.mem_top z, Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hz)⟩
  set Pbar := P₀.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 I₀)) with hPbar
  have hHP : CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) ≤
      (Pbar : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀)) := by
    haveI := (normal_oUpperTwo_top :
      (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup (I₀ ⧸ CFSG.pCore 2 I₀))).Normal)
    have hsup := hH.to_sup_of_normal_left Pbar.isPGroup'
    have := Pbar.is_maximal' hsup le_sup_right
    rw [← this]
    exact le_sup_left
  have hlift : ∀ z : I₀ ⧸ CFSG.pCore 2 I₀, z ^ 3 = 1 →
      ∃ x ∈ (P₀ : Subgroup I₀), QuotientGroup.mk' (CFSG.pCore 2 I₀) x = z := by
    intro z hz
    have h1 := hHP (hmemH z hz)
    rw [hPbar, Sylow.coe_mapSurjective] at h1
    obtain ⟨x, hx, hxz⟩ := h1
    exact ⟨x, hx, hxz⟩
  obtain ⟨x, hx, hxa⟩ := hlift a ha
  obtain ⟨y, hy, hyb⟩ := hlift b hb3
  have hcomm := hcomm' (σ x) (Subgroup.mem_map_of_mem σ hx) (σ y) (Subgroup.mem_map_of_mem σ hy)
  set z := x * y * x⁻¹ * y⁻¹ with hz
  have hzP : z ∈ (P₀ : Subgroup I₀) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx))
      (Subgroup.inv_mem _ hy)
  have hzk : z ∈ σ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hz1 : z = 1 := by
    obtain ⟨m, hm⟩ := P₀.isPGroup' ⟨z, hzP⟩
    have hm' : z ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 : orderOf z ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
    have h2 : orderOf z ∣ Nat.card σ.ker := by
      have := orderOf_dvd_natCard (⟨z, hzk⟩ : σ.ker)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (3 ^ m) (Nat.card σ.ker) := Nat.Coprime.pow_left m hker
    have h3 : orderOf z ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd h1 h2
    rwa [Nat.dvd_one, orderOf_eq_one_iff] at h3
  apply hab
  rw [← hxa, ← hyb, ← map_mul, ← map_mul]
  congr 1
  calc x * y = z * (y * x) := by rw [hz]; group
    _ = y * x := by rw [hz1, one_mul]

namespace SolvNone

theorem le_pCore_two_of_not_three_dvd (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀))
    {M : Subgroup I₀} [M.Normal] (h : ¬ 3 ∣ Nat.card M) : M ≤ CFSG.pCore 2 I₀ := by
  haveI : (M.map (QuotientGroup.mk' (CFSG.pCore 2 I₀))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hMbar : M.map (QuotientGroup.mk' (CFSG.pCore 2 I₀)) = ⊥ :=
    SevenFourL34.normal_eq_bot_of_not_three_dvd
      SevenFourL34.kFactSUThreeTwoNoNormalThreePrime_holds hb _
      fun h3 => h (h3.trans (Subgroup.card_map_dvd M _))
  intro g hg
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 I₀) g ∈
      M.map (QuotientGroup.mk' (CFSG.pCore 2 I₀)) := Subgroup.mem_map_of_mem _ hg
  rw [hMbar, Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff g).mp h1

theorem comap_le_pCore_two_of_coprime {C : Subgroup Y} [C.Normal] (σ : I₀ →* Y)
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀)) (hC : Nat.Coprime 3 (Nat.card C))
    (hker : Nat.Coprime 3 (Nat.card σ.ker)) : C.comap σ ≤ CFSG.pCore 2 I₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (C.comap σ).Normal := Subgroup.Normal.comap inferInstance σ
  refine le_pCore_two_of_not_three_dvd hb fun h3 => ?_
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := C.comap σ) 3 h3
  have hgo : orderOf (g : I₀) = 3 := by rw [Subgroup.orderOf_coe, hg]
  have hσg : σ g = 1 := by
    have h1 : orderOf (σ g) ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C g.2
    have h2 : orderOf (σ g) ∣ 3 := (orderOf_map_dvd σ (g : I₀)).trans (dvd_of_eq hgo)
    have h3' : orderOf (σ g) ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hC]
      exact Nat.dvd_gcd h2 h1
    rwa [Nat.dvd_one, orderOf_eq_one_iff] at h3'
  have hdvd : orderOf (⟨g, MonoidHom.mem_ker.mpr hσg⟩ : σ.ker) ∣ Nat.card σ.ker :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hgo] at hdvd
  exact absurd (Nat.Coprime.eq_one_of_dvd hker hdvd) (by norm_num)

end SolvNone

theorem exists_two_pow_inv_of_symThree (σ : I₀ →* Y)
    (f : I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)) {C : Subgroup Y}
    (hσC : (CFSG.pCore 2 I₀).map σ ≤ C) {y : Y} (hy : y ∈ σ.range) (hodd : Odd (orderOf y)) :
    ∃ t ∈ σ.range, (∃ m : ℕ, t ^ 2 ^ m = 1) ∧ t * y * t⁻¹ * y ∈ C := by
  have hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) := Or.inl ⟨f⟩
  obtain ⟨g, hg, hgy⟩ := exists_oUpperTwo_of_odd σ hy hodd
  have ha3 : f (g : I₀ ⧸ CFSG.pCore 2 I₀) ^ 3 = 1 := by
    rw [← map_pow, ← QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff _).mpr (cube_mem_pCore_two hb g hg), map_one]
  obtain ⟨τ, hτ, hτ2⟩ := perm_three_exists_inv_sq _ ha3
  obtain ⟨q, hq⟩ := f.surjective τ
  obtain ⟨t₀, rfl⟩ := QuotientGroup.mk_surjective q
  have hw : t₀ * g * t₀⁻¹ * g ∈ CFSG.pCore 2 I₀ := by
    rw [← QuotientGroup.eq_one_iff]
    apply f.injective
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      map_mul, map_mul, map_mul, map_inv, hq, hτ, map_one, inv_mul_cancel]
  have ht2 : t₀ ^ 2 ∈ CFSG.pCore 2 I₀ := by
    rw [← QuotientGroup.eq_one_iff]
    apply f.injective
    rw [QuotientGroup.mk_pow, map_pow, hq, hτ2, map_one]
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := I₀)) ⟨t₀ ^ 2, ht2⟩
  have hm' : t₀ ^ 2 ^ (m + 1) = 1 := by
    have h1 : (t₀ ^ 2) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [pow_succ', pow_mul, h1]
  refine ⟨σ t₀, ⟨t₀, rfl⟩, ⟨m + 1, by rw [← map_pow, hm', map_one]⟩, ?_⟩
  have h1 := hσC (Subgroup.mem_map_of_mem σ hw)
  rwa [map_mul, map_mul, map_mul, map_inv, hgy] at h1

theorem mem_centralizer_of_symThree_of_forall (σ : I₀ →* Y)
    (f : I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)) {K Y₀ U : Subgroup Y} [K.Normal]
    (hcent : ∀ R : Subgroup (MulAut K), CFSG.GH74.KGroups.ElemAb 3 R → Nat.card R = 9 →
      ∀ ψ : MulAut K, ψ ^ 2 = 1 → (∀ r ∈ R, ψ * r = r * ψ) → ψ = 1)
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥) (hσs : IsSubnormal σ.range Y₀)
    (hUK : U ≤ K) (hU27 : Nat.card U = 27) (hU3 : ∀ u ∈ U, u ^ 3 = 1) (hUY : U ≤ Y₀)
    {t : Y} (htS : t ∈ σ.range) (htU : t ∈ normalizer (U : Set Y)) {m : ℕ}
    (htm : t ^ 2 ^ m = 1) : t ∈ centralizer (K : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h6 : Nat.card (I₀ ⧸ CFSG.pCore 2 I₀) = 6 := by
    rw [Nat.card_congr f.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hAU : zpowers t ≤ normalizer (U : Set Y) := zpowers_le.mpr htU
  have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 3) (by rw [hU27]; norm_num)
  have hcop : Nat.Coprime (Nat.card (zpowers t)) (Nat.card U) := by
    rw [Nat.card_zpowers, hU27]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one htm)
    rw [hj]
    exact Nat.Coprime.pow_left j (by norm_num : Nat.Coprime 2 27)
  haveI : Group.IsNilpotent U := hUp.isNilpotent
  have hcc := CFSG.Quasithin.F53.Stellmacher.S35.K6b.comm_comm_eq_of_coprime (zpowers t) U hAU
    hcop inferInstance
  have hcS : ⁅U, zpowers t⁆ ≤ σ.range :=
    commutator_le_of_isSubnormal hσs hUY (zpowers_le.mpr htS) hAU hcc
  have hcp : IsPGroup 3 ↥⁅U, zpowers t⁆ :=
    hUp.to_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hAU)
  have hc3 : Nat.card ↥⁅U, zpowers t⁆ ≤ 3 := by
    have hdvd := card_dvd_card_quotient_of_isPGroup σ hcp hcS
    rw [h6] at hdvd
    obtain ⟨a, ha⟩ := hcp.exists_card_eq
    rw [ha] at hdvd ⊢
    have ha1 : a ≤ 1 := by
      by_contra h
      have h9 : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at h9
    calc 3 ^ a ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) ha1
      _ = 3 := by norm_num
  obtain ⟨F, hFU, hFt, hFc⟩ := exists_card_nine_le_centralizer hU27 htU htm hc3
  have hFel : IsElemAbelian 3 F :=
    ⟨⟨⟨fun a b => IsPGroup.commutative_of_card_eq_prime_sq hFc a b⟩⟩,
      fun a ha => hU3 a (hFU ha)⟩
  exact mem_centralizer_of_two_pow_of_forall hcent hKC htm (hFU.trans hUK) hFt hFel hFc

theorem false_of_not_symThree_of_card_le (σ : I₀ →* Y)
    (hb : IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀))
    (hs3 : ¬ Nonempty (I₀ ⧸ CFSG.pCore 2 I₀ ≃* Equiv.Perm (Fin 3)))
    (hker : Nat.Coprime 3 (Nat.card σ.ker)) {K Y₀ : Subgroup Y} [K.Normal]
    (hKC : K ⊓ centralizer (K : Set Y) = ⊥)
    (hrkC : CFSG.Open.pRank 3 (centralizer (K : Set Y)) ≤ 1)
    (hinner : ∀ y ∈ σ.range, y ^ 3 = 1 → ∃ k ∈ K, ∃ c ∈ centralizer (K : Set Y), y = k * c)
    (hA : ∀ Q : Subgroup (MulAut K), IsPGroup 3 Q → Nat.card Q ≤ 27)
    (hcond : SolvThreeAutCond Y₀ σ) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  obtain ⟨θ, hθ⟩ : ∃ θ : Y →* MulAut K, θ = MulAut.conjNormal := ⟨_, rfl⟩
  have hθ1 : ∀ a : Y, θ a = 1 ↔ a ∈ C := fun a => by
    rw [hθ]; exact conjNormal_eq_one_iff
  have h216 := card_quotient_pCore_of_not_symThree hb hs3
  have hsyl : ∀ P₀ : Sylow 3 I₀, Nat.card ((P₀ : Subgroup I₀).map σ) = 27 ∧
      (∀ x ∈ (P₀ : Subgroup I₀).map σ, x ^ 3 = 1) ∧
      ∀ z ∈ (P₀ : Subgroup I₀).map σ, θ z = 1 → z = 1 := by
    intro P₀
    set P : Subgroup Y := (P₀ : Subgroup I₀).map σ with hP
    have hPS : P ≤ σ.range := Subgroup.map_le_range σ _
    have hPp : IsPGroup 3 P := P₀.isPGroup'.map σ
    have hP3 : ∀ x ∈ P, x ^ 3 = 1 := by
      intro x hx
      obtain ⟨n, hn⟩ := hPp ⟨x, hx⟩
      have hxn : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
      exact pow_three_eq_one_of_mem_range_of_odd σ hb (hPS hx)
        (Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hxn))
    have hPKC : P ≤ K ⊔ C := fun x hx => by
      obtain ⟨k, hk, c, hc, rfl⟩ := hinner x (hPS hx) (hP3 x hx)
      exact mul_mem_sup hk hc
    have hPnc := not_comm_map_sylow σ hb hs3 hker P₀
    have hPdvd : Nat.card P ∣ 27 := by
      have hdvd := card_dvd_card_quotient_of_isPGroup σ hPp hPS
      rw [h216] at hdvd
      obtain ⟨a, ha⟩ := hPp.exists_card_eq
      rw [ha] at hdvd ⊢
      have ha3 : a ≤ 3 := by
        by_contra h
        have h81 : 3 ^ 4 ∣ 216 := (pow_dvd_pow 3 (by omega)).trans hdvd
        norm_num at h81
      exact (pow_dvd_pow 3 ha3).trans (by norm_num)
    have hP27 : Nat.card P = 27 := by
      have h27 : 27 ∣ Nat.card P := by
        by_contra h
        exact hPnc (commute_of_le_of_not_dvd le_rfl h hP3)
      exact Nat.dvd_antisymm hPdvd h27
    have hθP : Nat.card (P.map θ) = 27 := by
      have hdvd : Nat.card (P.map θ) ∣ 27 := hP27 ▸ Subgroup.card_map_dvd P θ
      by_contra hne
      have h27 : ¬ 27 ∣ Nat.card (P.map θ) := fun h => hne (Nat.dvd_antisymm hdvd h)
      have hθ3 : ∀ x ∈ P.map θ, x ^ 3 = 1 := by
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_pow, hP3 x hx, map_one]
      have hcomm := commute_of_le_of_not_dvd le_rfl h27 hθ3
      apply hPnc
      refine commute_of_commutator_mem hKC hrkC hP3 hPKC fun x hx y hy => (hθ1 _).mp ?_
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        hcomm _ (Subgroup.mem_map_of_mem θ hx) _ (Subgroup.mem_map_of_mem θ hy)]
      group
    refine ⟨hP27, hP3, fun z hz hz1 => ?_⟩
    have hbij := (θ.subgroupMap_surjective P).bijective_of_nat_card_le (by rw [hθP, hP27])
    have h1 : θ.subgroupMap P ⟨z, hz⟩ = 1 := Subtype.ext hz1
    exact congrArg Subtype.val ((injective_iff_map_eq_one _).mp hbij.1 _ h1)
  set M : Subgroup I₀ := C.comap σ with hM
  haveI : M.Normal := Subgroup.Normal.comap inferInstance σ
  have hM3 : ¬ 3 ∣ Nat.card M := by
    intro h3
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := M) 3 h3
    have hgo : orderOf (g : I₀) = 3 := by rw [Subgroup.orderOf_coe, hg]
    have hg3 : (g : I₀) ^ 3 ^ 1 = 1 := by rw [pow_one, ← hgo, pow_orderOf_eq_one]
    obtain ⟨P', hP'⟩ := (isPGroup_zpowers_of_pow_eq_one hg3).exists_le_sylow
    have hσg : σ g = 1 :=
      (hsyl P').2.2 _ (Subgroup.mem_map_of_mem σ (hP' (mem_zpowers _))) ((hθ1 _).mpr g.2)
    have hdvd : orderOf (⟨g, MonoidHom.mem_ker.mpr hσg⟩ : σ.ker) ∣ Nat.card σ.ker :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hgo] at hdvd
    exact absurd (Nat.Coprime.eq_one_of_dvd hker hdvd) (by norm_num)
  have hMO : ∀ g ∈ M, g ∈ CFSG.pCore 2 I₀ := SolvNone.le_pCore_two_of_not_three_dvd hb hM3
  rcases hcond with hf | ⟨y₀, -, ⟨n₀, hy₀3⟩, α, hα, g₁, hg₁⟩
  · exact hs3 hf
  apply hg₁
  have hy₀N : y₀ ∈ normalizer (σ.range : Set Y) :=
    Subgroup.mem_normalizer_fintype fun s hs => by
      obtain ⟨g, rfl⟩ := hs
      exact ⟨α g, hα g⟩
  set G' : Subgroup Y := σ.range ⊔ zpowers y₀ with hG'
  have hG'N : G' ≤ normalizer (σ.range : Set Y) := sup_le le_normalizer (zpowers_le.mpr hy₀N)
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 I₀) := inferInstance
  obtain ⟨hP27, hP3, hPθ⟩ := hsyl P₀
  set P : Subgroup Y := (P₀ : Subgroup I₀).map σ with hP
  have hPS : P ≤ σ.range := Subgroup.map_le_range σ _
  have hPG : P ≤ G' := hPS.trans le_sup_left
  obtain ⟨Q₁, hQ₁⟩ :=
    ((P₀.isPGroup'.map σ).comap_of_injective G'.subtype G'.subtype_injective).exists_le_sylow
  have hy₀G : y₀ ∈ G' := mem_sup_right (mem_zpowers y₀)
  obtain ⟨Q₂, hQ₂⟩ := ((isPGroup_zpowers_of_pow_eq_one hy₀3).comap_of_injective G'.subtype
    G'.subtype_injective).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (↥G') Q₁ Q₂
  have hy₀Q₂ : (⟨y₀, hy₀G⟩ : ↥G') ∈ (Q₂ : Subgroup ↥G') :=
    hQ₂ (Subgroup.mem_comap.mpr (mem_zpowers y₀))
  have hw : x⁻¹ * ⟨y₀, hy₀G⟩ * x ∈ (Q₁ : Subgroup ↥G') := by
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy₀Q₂
    simpa [MulAut.smul_def, MulAut.conj_inv_apply, mul_assoc] using hy₀Q₂
  set θ' : ↥G' →* MulAut K := θ.comp G'.subtype with hθ'
  have hPQ : P.map θ ≤ (Q₁ : Subgroup ↥G').map θ' := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨p, hPG hp⟩, hQ₁ (Subgroup.mem_comap.mpr hp), rfl⟩
  have hPθc : Nat.card (P.map θ) = 27 := by rw [card_map_of_forall_eq_one θ hPθ, hP27]
  haveI : Finite ↥((Q₁ : Subgroup ↥G').map θ') :=
    Finite.of_surjective _ (θ'.subgroupMap_surjective (Q₁ : Subgroup ↥G'))
  have hPQe : P.map θ = (Q₁ : Subgroup ↥G').map θ' :=
    Subgroup.eq_of_le_of_card_ge hPQ (by rw [hPθc]; exact hA _ (Q₁.isPGroup'.map θ'))
  have hwθ : θ' (x⁻¹ * ⟨y₀, hy₀G⟩ * x) ∈ P.map θ := by
    rw [hPQe]
    exact Subgroup.mem_map_of_mem θ' hw
  obtain ⟨p, hp, hpw⟩ := hwθ
  have hpw' : θ p = θ ((x : Y)⁻¹ * y₀ * x) := by
    rw [hpw, hθ', MonoidHom.comp_apply]
    rfl
  have hc : p⁻¹ * ((x : Y)⁻¹ * y₀ * x) ∈ C := by
    rw [← hθ1, map_mul, map_inv, hpw', inv_mul_cancel]
  have hqS : (x : Y) * p * (x : Y)⁻¹ ∈ σ.range :=
    (mem_normalizer_iff.mp (hG'N x.2) p).mp (hPS hp)
  have hq3 : ((x : Y) * p * (x : Y)⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hP3 p hp, mul_one, mul_inv_cancel]
  have hqodd : Odd (orderOf ((x : Y) * p * (x : Y)⁻¹)) :=
    Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hq3)
  obtain ⟨x₀, hx₀O, hx₀q⟩ := exists_oUpperTwo_of_odd σ hqS hqodd
  set c' : Y := (x : Y) * (p⁻¹ * ((x : Y)⁻¹ * y₀ * x)) * (x : Y)⁻¹ with hc'
  have hc'C : c' ∈ C := (inferInstance : C.Normal).conj_mem _ hc _
  have hy₀e : y₀ = σ x₀ * c' := by
    rw [hx₀q, hc']
    group
  clear_value c'
  haveI := (normal_oUpperTwo_top :
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).Normal)
  have hM' : x₀⁻¹ * α g₁ * x₀ * g₁⁻¹ ∈ M := by
    show σ (x₀⁻¹ * α g₁ * x₀ * g₁⁻¹) ∈ C
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hα, hy₀e]
    have he : (σ x₀)⁻¹ * (σ x₀ * c' * σ g₁ * (σ x₀ * c')⁻¹) * σ x₀ * (σ g₁)⁻¹ =
        c' * (σ g₁ * c'⁻¹ * (σ g₁)⁻¹) := by group
    rw [he]
    exact C.mul_mem hc'C ((inferInstance : C.Normal).conj_mem _ (C.inv_mem hc'C) _)
  have hO := hMO _ hM'
  have he : α g₁ * g₁⁻¹ =
      (x₀ * (x₀⁻¹ * α g₁ * x₀ * g₁⁻¹) * x₀⁻¹) * (x₀ * (g₁ * x₀⁻¹ * g₁⁻¹)) := by group
  rw [he]
  refine Subgroup.mul_mem _ (mem_sup_right ?_) (mem_sup_left ?_)
  · exact (inferInstance : (CFSG.pCore 2 I₀).Normal).conj_mem _ hO x₀
  · exact Subgroup.mul_mem _ hx₀O
      ((inferInstance : (CFSG.ComponentClassification.AS76b.oUpperTwo
        (⊤ : Subgroup I₀)).Normal).conj_mem _ (Subgroup.inv_mem _ hx₀O) g₁)

end Solvable

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
