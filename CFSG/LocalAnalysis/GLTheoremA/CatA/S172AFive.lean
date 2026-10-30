module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem iterate_apply_eq_pow {Y : Type} [Group Y] (φ : MulAut Y) (n : ℕ) (y : Y) :
    φ^[n] y = (φ ^ n) y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ih]

theorem five_false (hb : CatDistinct.OrderBridge) {Ω : Type} [Group Ω] [Finite Ω]
    {S B D K : Subgroup Ω} {x : Ω} (hcfg : Cfg172 3 S B D K x)
    (hK : catalogIs (PSimple 3 K) (isLnA 2 4)) : False := by
  classical
  have hKq : CFSG.Open.IsQuasisimple ↥K := hcfg.std.2.2.2.2.2.1.2.2
  haveI : Group.IsPerfect ↥K := ⟨hKq.1⟩
  have hBN : B ≤ Subgroup.normalizer (K : Set Ω) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.B_norm_K hcfg.elem
      (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hcfg.idiag) hcfg.std
  have hDB : D ≤ B := hcfg.std.1
  have hcard : Nat.card (PSimple 3 K) = 60 := card_of_isLnA_two_four hb hK
  have hOne : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PSimple 3 K) := by
      have h1 : Subsingleton (↥K ⧸ GLAPPrimeCore 3 ↥K) := by
        rw [htop]
        exact QuotientGroup.subsingleton_quotient_top
      exact (QuotientGroup.mk'_surjective (Subgroup.center (↥K ⧸ GLAPPrimeCore 3 ↥K))).subsingleton
    have h2 := (Finite.card_le_one_iff_subsingleton).2 hsub
    rw [hcard] at h2
    omega
  have hOZ : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K :=
    CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hKq inferInstance hOne
  let Φ : (↥K ⧸ Subgroup.center ↥K) ≃* PSimple 3 K := pSimpleEquivCenterQuot 3 hOZ
  have hcardQ : Nat.card (↥K ⧸ Subgroup.center ↥K) = 60 := (Nat.card_congr Φ.toEquiv).trans hcard
  have h3 : (Nat.card (↥K ⧸ Subgroup.center ↥K)).factorization 3 = 1 := by
    rw [hcardQ]
    exact factorization_three_sixty
  have hcatQ : catalogIs (↥K ⧸ Subgroup.center ↥K) (isLnA 2 4) := by
    obtain ⟨i, hi, ⟨e⟩⟩ := hK
    exact ⟨i, hi, ⟨Φ.trans e⟩⟩
  have hAut := autThreePowInner_of_isLnA_two_four hcatQ h3
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2
  have hZQ : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ := center_quotient_center_eq_bot
  let ψ : ↥B →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
    (centerQuotientHom ↥K).comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hBN))
  have hkerD : ψ.ker ≤ D.subgroupOf B := by
    intro g hg
    have hg1 : ψ g = 1 := MonoidHom.mem_ker.1 hg
    have hg1' : centerQuotientHom ↥K (K.normalizerMonoidHom (Subgroup.inclusion hBN g)) = 1 :=
      hg1
    have hc : (g : Ω) ∈ Subgroup.centralizer (K : Set Ω) :=
      (normalizer_action_eq_one_iff (K := K) (Subgroup.inclusion hBN g)).1 hg1'
    rw [Subgroup.mem_subgroupOf, hcfg.std.2.2.2.2.2.2]
    exact ⟨g.2, hc⟩
  have hcardD : Nat.card ↥D = 9 := by
    rw [hcfg.std.2.2.1]
    norm_num
  have hkerle : Nat.card ↥ψ.ker ≤ 9 := by
    have h1 := Subgroup.card_le_of_le hkerD
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv, hcardD] at h1
    exact h1
  have hconj_inj := conj_injective_of_center_eq_bot hZQ
  have hrangeLe : ψ.range ≤
      (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →* MulAut (↥K ⧸ Subgroup.center ↥K)).range := by
    rintro φ ⟨g, rfl⟩
    have hg3 : g ^ 3 = (1 : ↥B) := Subtype.ext (by simpa using hcfg.elem.2 (g : Ω) g.2)
    have hp3 : ψ g ^ 3 = 1 := by
      rw [← map_pow, hg3, map_one]
    obtain ⟨a, ha⟩ := hAut (ψ g) 1 (by
      intro y
      rw [pow_one, iterate_apply_eq_pow, hp3]
      rfl)
    refine ⟨a, ?_⟩
    ext y
    rw [MulAut.conj_apply]
    exact (ha y).symm
  have hcardInn : Nat.card ↥(MulAut.conj :
      (↥K ⧸ Subgroup.center ↥K) →* MulAut (↥K ⧸ Subgroup.center ↥K)).range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hconj_inj).toEquiv]
    exact hcardQ
  have hdvdInn : Nat.card ↥ψ.range ∣ 60 := by
    rw [← hcardInn]
    exact Subgroup.card_dvd_of_le hrangeLe
  obtain ⟨m, hm⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_card_eq_pow_of_isElemAbelian
    Nat.prime_three hcfg.elem
  have hdvdB : Nat.card ↥ψ.range ∣ 3 ^ m := by
    rw [← hm, ← Subgroup.card_ker_mul_card_range ψ]
    exact Dvd.intro_left _ rfl
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvdB
  have he1 : e ≤ 1 := by
    by_contra hc
    push Not at hc
    have h9 : 3 ^ 2 ∣ 3 ^ e := pow_dvd_pow 3 hc
    rw [← he] at h9
    have h60 := dvd_trans h9 hdvdInn
    norm_num at h60
  have hrange3 : Nat.card ↥ψ.range ≤ 3 := by
    rw [he]
    calc 3 ^ e ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) he1
      _ = 3 := by norm_num
  have hcardB : Nat.card ↥B = Nat.card ↥ψ.ker * Nat.card ↥ψ.range :=
    (Subgroup.card_ker_mul_card_range ψ).symm
  have hle : Nat.card ↥B ≤ 9 * 3 := by
    rw [hcardB]
    exact Nat.mul_le_mul hkerle hrange3
  have hfour := hcfg.four
  norm_num at hfour
  omega

end CFSG.LocalAnalysis.GLTheoremA.S172A

end
