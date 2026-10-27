module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCompTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwDecSplit

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (rootSpan_commute_of_orth)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

variable
  {K : Type} [Field K] {σ : K ≃+* K} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  {g₀ : ModGL Tag.E6 (AlgebraicClosure K)} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K}

theorem twCompHat_mem_iff {τ : ModGL TwistTag.E6.tag K} :
    τ ∈ twTorusHat K σ g₀ ↔ τ ∈ twistedE6InndiagGL K σ ∧
      twLinePsi K g₀ τ ∈ torusGroup Tag.E6 (AlgebraicClosure K) :=
  Iff.rfl

theorem twCompHat_psi_fixed {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (pic : TwE6ThreeA2Picture K σ (ℓ ^ f) Fr g₀ h₀ L T n) {ĝ : ModGL TwistTag.E6.tag K}
    (hĝ : ĝ ∈ twistedE6InndiagGL K σ) :
    tw6Theta (AlgebraicClosure K) Fr (twLinePsi K g₀ ĝ) = twLinePsi K g₀ ĝ := by
  have hmem := map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf pic.card_eq σ pic.σ_apply Fr
    pic.Fr_apply (Subgroup.mem_map_of_mem _ hĝ)
  obtain ⟨-, hfix⟩ :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).1 hmem
  have hfix' : twistE6 (AlgebraicClosure K) Fr
      (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) ĝ) =
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) ĝ := hfix
  rw [twLinePsi_apply, tw6Theta_apply, map_mul, map_mul, map_inv, pic.g₀_lang, hfix']
  group

theorem twCompHat_finite {Ω : Type} [Field Ω] (P : ModGL Tag.E6 Ω → Prop) :
    Finite {d : ModGL Tag.E6 Ω // d ∈ torusGroup Tag.E6 Ω ∧ P d ∧ d ^ 3 = 1} := by
  have hex : ∀ d : {d : ModGL Tag.E6 Ω // d ∈ torusGroup Tag.E6 Ω ∧ P d ∧ d ^ 3 = 1},
      ∃ b : Fin Tag.E6.rank → rootsOfUnity 3 Ω,
        rootDiagUnit Tag.E6 (fun i => (b i : Ωˣ)) = d.1 := by
    rintro ⟨d, hd, -, hd3⟩
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hd
    exact ⟨fun i => ⟨b i, (mem_rootsOfUnity 3 _).2 (twCompTor_pow_eq_one_of hd3 i)⟩, rfl⟩
  choose g hg using hex
  exact Finite.of_injective g fun d₁ d₂ h => Subtype.ext (by rw [← hg d₁, ← hg d₂, h])

theorem TwE6ThreeA2Picture.conj_mem_T {q : ℕ} (pic : TwE6ThreeA2Picture K σ q Fr g₀ h₀ L T n)
    (hn : n ∈ twistedE6RootGroup K σ) (τ : ModGL TwistTag.E6.tag K) :
    τ ∈ T ↔ n * τ * n⁻¹ ∈ T := by
  obtain ⟨t, ht, hψn⟩ := pic.n_image
  have hN : twLinePsi K g₀ n ∈ Subgroup.normalizer
      (torusGroup Tag.E6 (AlgebraicClosure K) : Set (ModGL Tag.E6 (AlgebraicClosure K))) := by
    rw [hψn]
    exact mul_mem (canonicalRep_mem_normalizer _) (Subgroup.le_normalizer ht)
  rw [pic.mem_T, pic.mem_T, map_mul, map_mul, map_inv]
  refine and_congr ⟨fun h => mul_mem (mul_mem hn h) (inv_mem hn), fun h => ?_⟩
    (Subgroup.mem_normalizer_iff.1 hN _)
  have e : τ = n⁻¹ * (n * τ * n⁻¹) * n := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hn) h) hn

theorem twTorusHat_pow_three_mem {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (pic : TwE6ThreeA2Picture K σ (ℓ ^ f) Fr g₀ h₀ L T n) {τ : ModGL TwistTag.E6.tag K}
    (hτ : τ ∈ twTorusHat K σ g₀) : τ ^ 3 ∈ T := by
  obtain ⟨hτC, hτH⟩ := twCompHat_mem_iff.1 hτ
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [pic.card_eq]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, hcube, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K pic.card_eq σ
      pic.σ_apply
  set g : ↥(twistedE6InndiagGL K σ) := ⟨τ, hτC⟩ with hgdef
  have hg : twistedE6InndiagConj K σ g ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rw [← range_twistedE6InndiagConj]
    exact ⟨g, rfl⟩
  have h1 := hcube (QuotientGroup.mk ⟨_, hg⟩)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  have hc' : twistedE6InndiagConj K σ ⟨c, Subgroup.mem_sup_left c.2⟩ =
      twistedE6InndiagConj K σ (g ^ 3) := by
    have e : twistedE6InndiagConj K σ ⟨c, Subgroup.mem_sup_left c.2⟩ = MulAut.conj c :=
      MulEquiv.ext fun _ => Subtype.ext rfl
    rw [e, hc, map_pow, Subgroup.coe_pow]
  have h2 := congrArg Subtype.val
    (twistedE6InndiagConj_injective hℓ hf pic.card_eq σ pic.σ_apply hc')
  have hτ3 : τ ^ 3 = (c : ModGL TwistTag.E6.tag K) := by
    rw [h2, Subgroup.coe_pow]
  rw [pic.mem_T, hτ3]
  refine ⟨c.2, ?_⟩
  rw [← hτ3, map_pow]
  exact pow_mem hτH 3

theorem twTorusHat_card_three_le {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (pic : TwE6ThreeA2Picture K σ (ℓ ^ f) Fr g₀ h₀ L T n) (h3 : 3 ∣ ℓ ^ f + 1) :
    Nat.card {τ : ModGL TwistTag.E6.tag K // τ ∈ twTorusHat K σ g₀ ∧ τ ^ 3 = 1} ≤ 27 := by
  let φ : {τ : ModGL TwistTag.E6.tag K // τ ∈ twTorusHat K σ g₀ ∧ τ ^ 3 = 1} →
      {d : ModGL Tag.E6 (AlgebraicClosure K) // d ∈ torusGroup Tag.E6 (AlgebraicClosure K) ∧
        tw6Theta (AlgebraicClosure K) Fr d = d ∧ d ^ 3 = 1} := fun τ =>
    ⟨twLinePsi K g₀ τ.1, (twCompHat_mem_iff.1 τ.2.1).2,
      twCompHat_psi_fixed hℓ hf pic (twCompHat_mem_iff.1 τ.2.1).1,
      by rw [← map_pow, τ.2.2, map_one]⟩
  have hφ : Function.Injective φ := fun a b h =>
    Subtype.ext (twLinePsi_injective K g₀ (congrArg Subtype.val h))
  haveI := twCompHat_finite (Ω := AlgebraicClosure K)
    fun d => tw6Theta (AlgebraicClosure K) Fr d = d
  exact (Nat.card_le_card_of_injective φ hφ).trans (twTheta_torus_card_three_le pic.Fr_apply h3)

theorem twTorusHat_pow_three_of_pow_nine {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (pic : TwE6ThreeA2Picture K σ (ℓ ^ f) Fr g₀ h₀ L T n) (h3 : 3 ∣ ℓ ^ f + 1)
    {τ : ModGL TwistTag.E6.tag K} (hτ : τ ∈ twTorusHat K σ g₀) (h9 : τ ^ 9 = 1) : τ ^ 3 = 1 := by
  obtain ⟨hτC, hτH⟩ := twCompHat_mem_iff.1 hτ
  have h := twTheta_torus_pow_three_of_pow_nine pic.Fr_apply h3 hτH
    (twCompHat_psi_fixed hℓ hf pic hτC) (by rw [← map_pow, h9, map_one])
  apply twLinePsi_injective K g₀
  rw [map_pow, h, map_one]

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
