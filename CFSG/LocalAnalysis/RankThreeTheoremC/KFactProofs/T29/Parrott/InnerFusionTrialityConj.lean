module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionTrialityJ
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion

open CFSG.Open Subgroup TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof (d4S0 d4S0_mem d4S0_eq d4T0 d4T0_mem d4HT
  orbitRankOneHom_middle_sl2Three baseChangeGL_rankOneHom)

section Reps


variable {K : Type} [Field K] [Finite K]

theorem units_map_entrywiseHom_orbitN_one (σ : K ≃+* K) (a : Fin TwistTag.D4.foldedTag.rank) :
    Units.map (entrywiseHom σ.toRingHom)
        (orbitN TwistTag.D4 K σ.toRingHom a 1 : ModGL TwistTag.D4.tag K) =
      orbitN TwistTag.D4 K σ.toRingHom a 1 := by
  have hδ : ∀ c, σ (σ.toRingHom c) = σ.toRingHom (σ c) := fun _ => rfl
  rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul,
    units_map_entrywiseHom_orbitX hδ, units_map_entrywiseHom_orbitY hδ]
  have h1 : (⟨σ (((1 : (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) :
      orbitField TwistTag.D4 K σ.toRingHom a) : K), map_mem_orbitField hδ
        (((1 : (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) :
          orbitField TwistTag.D4 K σ.toRingHom a)).2⟩ :
      orbitField TwistTag.D4 K σ.toRingHom a) = ((1 : (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) :
        orbitField TwistTag.D4 K σ.toRingHom a) :=
    Subtype.ext (by simp)
  have h2 : (⟨σ ((-(((1 : (orbitField TwistTag.D4 K σ.toRingHom a)ˣ)⁻¹ :
      (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) : orbitField TwistTag.D4 K σ.toRingHom a) :
        orbitField TwistTag.D4 K σ.toRingHom a) : K), map_mem_orbitField hδ
          (-(((1 : (orbitField TwistTag.D4 K σ.toRingHom a)ˣ)⁻¹ :
            (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) :
              orbitField TwistTag.D4 K σ.toRingHom a)).2⟩ :
      orbitField TwistTag.D4 K σ.toRingHom a) =
        -(((1 : (orbitField TwistTag.D4 K σ.toRingHom a)ˣ)⁻¹ :
          (orbitField TwistTag.D4 K σ.toRingHom a)ˣ) : orbitField TwistTag.D4 K σ.toRingHom a) :=
    Subtype.ext (by
      rw [inv_one, Units.val_one]
      show σ ((-1 : orbitField TwistTag.D4 K σ.toRingHom a) : K) =
        ((-1 : orbitField TwistTag.D4 K σ.toRingHom a) : K)
      rw [show ((-1 : orbitField TwistTag.D4 K σ.toRingHom a) : K) = -1 from rfl, map_neg,
        map_one])
  rw [h1, h2]

theorem units_map_entrywiseHom_d4HT (σ : K ≃+* K) :
    Units.map (entrywiseHom σ.toRingHom) (d4HT σ) = d4HT σ := by
  rw [d4HT, map_list_prod, List.map_reverse, List.map_map]
  congr 2
  refine List.map_congr_left fun a _ => ?_
  exact units_map_entrywiseHom_orbitN_one σ a

theorem fieldActor_d4S0 (σ : K ≃+* K) :
    fieldActor (t := TwistTag.D4) σ σ ⟨d4S0 σ, d4S0_mem σ⟩ = ⟨d4S0 σ, d4S0_mem σ⟩ := by
  apply Subtype.ext
  rw [coe_fieldActor]
  show Units.map (entrywiseHom σ.toRingHom) (d4S0 σ) = d4S0 σ
  rw [d4S0_eq, map_mul, map_mul]
  simp only [units_map_entrywiseHom_eq_baseChangeGL_self, baseChangeGL_rankOneHom,
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.map_sl2Three]

theorem fieldActor_d4T0 (σ : K ≃+* K) :
    fieldActor (t := TwistTag.D4) σ σ ⟨d4T0 σ, d4T0_mem σ⟩ = ⟨d4T0 σ, d4T0_mem σ⟩ := by
  apply Subtype.ext
  rw [coe_fieldActor]
  show Units.map (entrywiseHom σ.toRingHom) (d4T0 σ) = d4T0 σ
  rw [d4T0, orbitRankOneHom_middle_sl2Three, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_d4HT,
    units_map_entrywiseHom_eq_baseChangeGL_self (g := rankOneHom _ _ _ _), baseChangeGL_rankOneHom,
    CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.map_sl2Three]

end Reps

section Conj


variable {K : Type} [Field K] [Finite K]

theorem exists_conj_eq_d4S0_or_d4T0 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz : orderOf z = 3) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      g * z * g⁻¹ = ⟨d4S0 σ, d4S0_mem σ⟩ ∨ g * z * g⁻¹ = ⟨d4T0 σ, d4T0_mem σ⟩ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := f * 3) (by omega) (by rw [hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hz3' : (z : ModGL TwistTag.D4.tag K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, pow_three_eq_one_of_orderOf hz, Subgroup.coe_one]
  have hz1' : (z : ModGL TwistTag.D4.tag K) ≠ 1 := fun h =>
    ne_one_of_orderOf_three hz (Subtype.ext h)
  obtain ⟨ζ, x, hζ, hx, hcase⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_conj_dA_or_dB hf hℓ3 hK hσ
      (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) ℓ f)
      (fun c => iterateFrobenius_def ℓ f c) z.2 hz3' hz1'
  rcases hcase with hA | hB
  · obtain ⟨k, hk, hkeq⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.exists_conj_d4S0
      (algebraMap K (AlgebraicClosure K)) σ hζ
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_conj_of_triEmb_conj hf hK
      hσ (CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.isPointIrreducible_gA hζ) (z := z)
      (s := ⟨d4S0 σ, d4S0_mem σ⟩) hx hk hA hkeq
    exact ⟨g, Or.inl hg⟩
  · obtain ⟨k, hk, hkeq⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.exists_conj_d4T0
      (algebraMap K (AlgebraicClosure K)) σ hζ
    obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_conj_of_triEmb_conj hf hK
      hσ (CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof.isPointIrreducible_gB hζ) (z := z)
      (s := ⟨d4T0 σ, d4T0_mem σ⟩) hx hk hB hkeq
    exact ⟨g, Or.inr hg⟩

theorem exists_conj_mem_d4SubfieldJ {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz : orderOf z = 3) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, g * z * g⁻¹ ∈ d4SubfieldJ σ := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  obtain ⟨g, hg | hg⟩ := exists_conj_eq_d4S0_or_d4T0 hℓ hℓ3 hf hK hσ hz
  · exact ⟨g, (mem_d4SubfieldJ hσ3).2 (by rw [hg]; exact fieldActor_d4S0 σ)⟩
  · exact ⟨g, (mem_d4SubfieldJ hσ3).2 (by rw [hg]; exact fieldActor_d4T0 σ)⟩

end Conj

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion
