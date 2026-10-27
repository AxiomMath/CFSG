module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Setup
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Arith
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26PGLCalc
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26PGLPow
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26FieldAut
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.Sporadic.J4.QT2LocProof

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.GorensteinWalter CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open scoped MatrixGroups commutatorElement

theorem l2_package {r : ℕ} (hr : 4 ≤ r) {A : Type} [Group A] [Finite A] (T : Subgroup A) [T.Normal]
    (hT : CFSG.ClassicalInvolution.Q3.TA3.SmallL2 ↥T) (hC : Subgroup.centralizer (T : Set A) = ⊥)
    {x b z : A} (hxo : orderOf x = 2 ^ (r - 1)) (hbx : b * x * b⁻¹ = x⁻¹)
    (hbb : b * b = x ^ 2 ^ (r - 2)) (hz : x ^ 2 ^ (r - 2) = z) :
    b ∉ T ∧
    (∃ (p f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), p.Prime ∧ p ≠ 2 ∧ Nat.card K = p ^ f ∧
        p ^ f % 4 = 1 ∧ 13 ≤ p ^ f ∧ Nonempty (↥T ≃* GorensteinWalter.PSL2 K)) ∧
    ∃ N : ℕ, r ≤ N ∧
      (∃ w ∈ T, w * z = z * w ∧ ∃ m : ℕ, Odd m ∧ orderOf (⁅b, w⁆ ^ m) = 2 ^ (N - 1) ∧
        (N = r → Subgroup.zpowers (⁅b, w⁆ ^ m) = Subgroup.zpowers x)) ∧
      (N = r → ∀ B : MulAut ↥T, B * MulAut.conjNormal x = MulAut.conjNormal x * B →
        B ^ 2 ^ (r - 1) = 1 → B ^ 2 ^ (r - 2) = 1 ∨ B ^ 2 ^ (r - 2) = MulAut.conjNormal z) := by
  classical
  obtain ⟨p, f, K, _, _, Ψ, α, hp, hp2, hf, hKcard, h2, hPSL, hΨz, hΨx, hα, hΨbb, hΨbα, hΨb1,
    hmem, a₀, ha₀T, ha₀z, hΨa₀⟩ := l2_setup_iff hr T hT hC hxo hbx hbb hz
  haveI : Fact p.Prime := ⟨hp⟩
  have hθinj : Function.Injective
      ((Ψ.toMonoidHom : MulAut ↥T →* PGammaL2 K).comp (MulAut.conjNormal : A →* MulAut ↥T)) :=
    Ψ.injective.comp (conjNormal_injective hC)
  have hB'Z : Ψ (MulAut.conjNormal b) * tor (-1) = tor (-1) * Ψ (MulAut.conjNormal b) := by
    rw [← hΨbb, ← mul_assoc]
  obtain ⟨γ, ε, σ, hε, hBe⟩ := exists_decomp h2 hB'Z
  have hσr : (Ψ (MulAut.conjNormal b)).right = σ := by
    have h := congrArg (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) hBe
    rw [map_mul, map_mul, map_pow, rightHom_tor, rightHom_wref, SemidirectProduct.rightHom_inr,
      one_pow, one_mul, one_mul] at h
    exact h
  have hσ1 : σ ≠ 1 := fun h => hΨb1 (hσr.trans h)
  have hσ2 : σ * σ = 1 := by
    have h := congrArg (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) hΨbb
    rw [map_mul, rightHom_tor] at h
    exact hσr ▸ h
  obtain ⟨q, hqq, hq⟩ := fieldAut_invol_eq_pow hσ2 hσ1
  have hBB : (tor γ * wref ^ ε * SemidirectProduct.inr σ : PGammaL2 K) *
      (tor γ * wref ^ ε * SemidirectProduct.inr σ) = tor (-1) := by
    rw [← hBe]; exact hΨbb
  have hBα : (tor γ * wref ^ ε * SemidirectProduct.inr σ : PGammaL2 K) * tor α *
      (tor γ * wref ^ ε * SemidirectProduct.inr σ)⁻¹ = tor α⁻¹ := by
    rw [← hBe]; exact hΨbα
  obtain ⟨h0, h1⟩ := l2_alpha_facts hr hα hε hq hσ2 hBB hBα
  have hNodd : Odd (Nat.card K) := by rw [hKcard]; exact (hp.odd_of_ne_two hp2).pow
  have hqodd : Odd q := by
    rw [← hqq] at hNodd
    exact (Nat.odd_mul.mp hNodd).1
  obtain ⟨hrN, hγN, δ, hδ⟩ := l2_nu_facts hr hα hε hqq hqodd h0 h1
  set N := padicValNat 2 (Nat.card K - 1) with hNdef
  have hN2 : 2 ^ r ∣ Nat.card K - 1 :=
    (pow_dvd_pow 2 hrN).trans (pow_padicValNat_dvd (p := 2) (n := Nat.card K - 1))
  have hNpos : 0 < Nat.card K - 1 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have h2r : 2 ^ r ≤ Nat.card K - 1 := Nat.le_of_dvd hNpos hN2
  have h16 : 16 ≤ 2 ^ r := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  set θ : A →* PGammaL2 K :=
    (Ψ.toMonoidHom : MulAut ↥T →* PGammaL2 K).comp (MulAut.conjNormal : A →* MulAut ↥T) with hθ
  have hθb : θ b = tor γ * wref ^ ε * SemidirectProduct.inr σ := hBe
  have hθa : θ a₀ = tor (-1) * wref := hΨa₀
  have hθc : θ ⁅b, a₀⁆ = tor (γ ^ 2) := by
    rw [map_commutatorElement, hθb, hθa]
    exact l2_commutator γ ε hε σ
  refine ⟨?_, ?_, N, hrN, ?_, ?_⟩
  ·
    intro hbT
    obtain ⟨y, hy⟩ := (hmem b).mp hbT
    apply hΨb1
    rw [← hy]
    simp
  ·
    refine ⟨p, f, K, inferInstance, inferInstance, hp, hp2, hKcard, ?_, ?_, hPSL⟩
    · rw [← hKcard, ← hqq]
      have := odd_mul_self_mod_eight hqodd
      omega
    · rw [← hKcard]
      omega
  ·
    have hγne : orderOf γ ≠ 0 := (orderOf_pos γ).ne'
    obtain ⟨k, m₀, hm₀, ho⟩ := Nat.exists_eq_two_pow_mul_odd hγne
    have hk : k = N := by
      have h1 : padicValNat 2 (orderOf γ) = k := by
        rw [ho, padicValNat.mul (by positivity) (hm₀.pos.ne'), padicValNat.prime_pow,
          padicValNat.eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hm₀.not_two_dvd_nat)]
        simp
      rw [← h1, hγN]
    have hN1 : 1 ≤ N := by omega
    have hord : orderOf (γ ^ (2 * m₀)) = 2 ^ (N - 1) := by
      rw [orderOf_pow' _ (by have := hm₀.pos; omega), ho, hk]
      have hg : Nat.gcd (2 ^ N * m₀) (2 * m₀) = 2 * m₀ := by
        apply Nat.gcd_eq_right
        refine ⟨2 ^ (N - 1), ?_⟩
        calc 2 ^ N * m₀ = 2 * 2 ^ (N - 1) * m₀ := by
              rw [← pow_succ']; congr 2; omega
          _ = 2 * m₀ * 2 ^ (N - 1) := by ring
      rw [hg]
      have h2 : 2 ^ N * m₀ = 2 * m₀ * 2 ^ (N - 1) := by
        calc 2 ^ N * m₀ = 2 * 2 ^ (N - 1) * m₀ := by
              rw [← pow_succ']; congr 2; omega
          _ = 2 * m₀ * 2 ^ (N - 1) := by ring
      rw [h2]
      exact Nat.mul_div_cancel_left _ (by have := hm₀.pos; omega)
    have hθcm : θ (⁅b, a₀⁆ ^ m₀) = tor (γ ^ (2 * m₀)) := by
      rw [map_pow, hθc, ← map_pow, ← pow_mul]
    refine ⟨a₀, ha₀T, ha₀z, m₀, hm₀, ?_, fun hNr => ?_⟩
    · rw [← orderOf_injective θ hθinj, hθcm, orderOf_injective (tor : Kˣ →* PGammaL2 K)
        tor_injective, hord]
    ·
      have hxθ : θ x = tor α := hΨx
      have hcard1 : Nat.card (Subgroup.zpowers (γ ^ (2 * m₀))) =
          Nat.card (Subgroup.zpowers α) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord, hα, hNr]
      have hKU : Subgroup.zpowers (γ ^ (2 * m₀)) = Subgroup.zpowers α :=
        IsCyclic.subgroup_eq_iff_card_eq.mpr hcard1
      apply Subgroup.map_injective hθinj
      rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers, hθcm, hxθ, ← MonoidHom.map_zpowers,
        ← MonoidHom.map_zpowers, hKU]
  ·
    intro hNr B hBx hB2
    have hCα : Ψ B * tor α = tor α * Ψ B := by
      rw [← hΨx]
      have := congrArg Ψ hBx
      rw [map_mul, map_mul] at this
      exact this
    have hC2 : Ψ B ^ 2 ^ (r - 1) = 1 := by rw [← map_pow, hB2, map_one]
    have hNr' : padicValNat 2 (Nat.card K - 1) = r := hNr
    rcases l2_pow_dichotomy h2 hr hNr' hα hCα hC2 with h | h
    · left
      apply Ψ.injective
      rw [map_pow, h, map_one]
    · right
      apply Ψ.injective
      rw [map_pow, h, hΨz]

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
