module

public import CFSG.HardMathSupport.Seitz.TrialityEven.FrameConjPm
public import CFSG.HardMathSupport.Seitz.TrialityEven.FrameCentPm
public import CFSG.HardMathSupport.Seitz.TrialityEven.PhiPlanePm
public import CFSG.HardMathSupport.Seitz.TrialityEven.PhiPrimePm

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open Subgroup TauCeti CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KEXC CFSG.GH74.GLS.Stage2.Bender.Thm1


theorem phiThreeLiftEven {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {f : ℕ} (hf : 2 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hd : (3 : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * ((2 ^ f : ℕ) : ℤ) + 1)
    (E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hE : CFSG.IsElementaryAbelian 3 E) (hEcard : Nat.card E = 3 ^ 2)
    (hF : ∃ F : D4PhiFrame K σ (2 ^ f) ε, F.Contains E) :
    ∃ r' : ℕ, r'.Prime ∧ 5 ≤ r' ∧
      (r' : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * ((2 ^ f : ℕ) : ℤ) + 1 ∧
      ∃ E' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        CFSG.IsElementaryAbelian r' E' ∧ Nat.card E' = r' ^ 2 ∧
        {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom | ∃ y ∈ E', y ≠ 1 ∧ k * y = y * k} ⊆
          Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
            ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨r', hr', hr'5, hr'd, hr'q⟩ := exists_prime_ge_five_dvd_phi_pm hq4 hε hd
  have : Fact r'.Prime := ⟨hr'⟩
  refine ⟨r', hr', hr'5, hr'd, ?_⟩
  obtain ⟨F, c₁, hc₁⟩ := hF
  obtain ⟨P, hPexp, hPcard⟩ := exists_plane_of_dvd_phi_pm (ℓ := 2) (by omega) K hK σ hσ hε hr'
    (by omega) hr'd
  have hPp : IsPGroup r' P := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hPexp g g.2)⟩
  obtain ⟨c₂, hc₂⟩ := exists_conj_into_frame_torus_pm (ℓ := 2) (by omega) K hK σ hσ hε hr'
    (by omega) hr'd F P hPp
  have : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hPcard
  have hPea : CFSG.IsElementaryAbelian r' P := by
    refine { exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hPexp g g.2
  set c := c₁⁻¹ * c₂ with hc
  refine ⟨P.map (MulAut.conj c).toMonoidHom, CFSG.IsElementaryAbelian.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective,
      hPcard]
  have hK3 : Nat.card K = 2 ^ (f * 3) := by rw [hK, pow_mul]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hΩ : ringChar (AlgebraicClosure K) = 2 := ringChar.eq _ 2
  have hι : Function.Injective
      ((triEmb K σ (AlgebraicClosure K)).comp (MulAut.conj c₁).toMonoidHom) :=
    triEmb_injective.comp (MulAut.conj c₁).injective
  have hT := twistedTorus_D4_eq_map_of_weylImage F.Fr F.hn F.w F.hnw (d4T36M ε) F.hw
  have htup : ∀ z, F.g0⁻¹ * triEmb K σ (AlgebraicClosure K) (c₁ * z * c₁⁻¹) * F.g0 ∈
      twistedTorusOf F.n (twistHom TwistTag.D4 (AlgebraicClosure K) F.Fr) →
      ∃ b ∈ fixedCharTuples (d4T36M ε) F.Fr, rootDiagUnit TwistTag.D4.tag b =
        F.g0⁻¹ * ((triEmb K σ (AlgebraicClosure K)).comp (MulAut.conj c₁).toMonoidHom) z *
          F.g0 := by
    intro z hz
    rw [hT] at hz
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.1 hz
    exact ⟨b, hb, hbz⟩
  rintro k ⟨y, hy, hy1, hky⟩
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.1 hy
  have hconj : c₁ * ((MulAut.conj c).toMonoidHom y₀) * c₁⁻¹ = c₂ * y₀ * c₂⁻¹ := by
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨by', hbyF, hby⟩ := htup ((MulAut.conj c).toMonoidHom y₀) (by
    rw [hconj]
    exact hc₂ y₀ hy₀)
  have hyr : ((MulAut.conj c).toMonoidHom y₀) ^ r' = 1 := by
    rw [← map_pow, hPexp y₀ hy₀, map_one]
  obtain ⟨x, hxE, hx1, hle⟩ := exists_centralizer_le_of_frameTuples_pm hε hι
    (fun g => triEmb_mem_adjointGroup _) F.hg0C (by rw [hΩ]; norm_num) hE hEcard
    (fun x hx => htup x (hc₁ x hx)) hr' hr'5 (by rw [hΩ]; omega) hy1 hyr hbyF hby
  exact Subgroup.subset_closure ⟨x, hxE, hx1, Subgroup.mem_centralizer_singleton_iff.1
    (hle (Subgroup.mem_centralizer_singleton_iff.2 hky))⟩

end CFSG.HardMathSupport.Seitz.TrialityEven
