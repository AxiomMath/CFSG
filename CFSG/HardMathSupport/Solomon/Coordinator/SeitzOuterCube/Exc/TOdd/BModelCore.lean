module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.RankThree.PartOne.KLR.SL2Gen
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof Subgroup
open CFSG.RankThree.PartTwo.Sec11

section Theta


theorem bModel_entrywise_rankOneHom {L : Type} [Field L] (Fr : L →+* L)
    (i : Fin TwistTag.D4.tag.rank) (A : SL2 L) :
    Units.map (entrywiseHom Fr) (rankOneHom TwistTag.D4 L i A) =
      rankOneHom TwistTag.D4 L i (Matrix.SpecialLinearGroup.map Fr A) := by
  have h := CFSG.RankThree.PartOne.KLR.hom_eq_of_uSL_vSL
    ((Units.map (entrywiseHom Fr)).comp (rankOneHom TwistTag.D4 L i))
    ((rankOneHom TwistTag.D4 L i).comp (Matrix.SpecialLinearGroup.map Fr))
    (fun s => by
      simp only [MonoidHom.comp_apply, rankOneHom_uSL, CFSG.RankThree.PartOne.KLR.map_uSL,
        units_map_entrywiseHom_xUnit])
    (fun s => by
      simp only [MonoidHom.comp_apply, rankOneHom_vSL, CFSG.RankThree.PartOne.KLR.map_vSL,
        units_map_entrywiseHom_yUnit])
  exact DFunLike.congr_fun h A

theorem bModel_entrywise_thetaHom {L : Type} [Field L] (Fr : L →+* L) (A : SL2 L) :
    Units.map (entrywiseHom Fr) (thetaHom L A) =
      thetaHom L (Matrix.SpecialLinearGroup.map Fr A) := by
  have key : ∀ w, Units.map (entrywiseHom Fr)
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L w) =
        canonicalRep (coxeterSystem TwistTag.D4.tag) L w := fun w =>
    baseChangeGL_canonicalRep Fr w
  have hh : Units.map (entrywiseHom Fr) (thetaConj L) = thetaConj L := by
    rw [thetaConj, map_mul, key, key]
  rw [thetaHom_apply, thetaHom_apply, map_mul, map_mul, map_inv, hh, bModel_entrywise_rankOneHom]

end Theta

section SL2

variable {L : Type} [Field L] [IsAlgClosed L]

theorem bModel_sl2_mem_zpowers {ζ : Lˣ} (hζ : orderOf ζ = 3) {Z B : SL2 L} (hZ3 : Z ^ 3 = 1)
    (hZ1 : Z ≠ 1) (hB3 : B ^ 3 = 1) (hBZ : B * Z = Z * B) : B ∈ Subgroup.zpowers Z := by
  obtain ⟨P, m, hm, hPZ⟩ := exists_conj_HSL_of_pow_three hζ hZ3 hZ1
  have hζ3 : ζ ^ 3 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hne : (ζ ^ m : Lˣ) ≠ (ζ ^ m)⁻¹ := by
    intro h
    have h2 : (ζ ^ m) ^ 2 = 1 := by
      rw [pow_two]
      exact mul_eq_one_iff_eq_inv.mpr h
    have h3 : (ζ ^ m) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
    have h4 : ζ ^ m = 1 := by
      calc ζ ^ m = (ζ ^ m) ^ 3 * ((ζ ^ m) ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, h2]; simp
    have h5 : 3 ∣ m := hζ ▸ orderOf_dvd_of_pow_eq_one h4
    omega
  obtain ⟨B', hB'⟩ : ∃ B' : SL2 L, B' = P⁻¹ * B * P := ⟨_, rfl⟩
  have hcomm : B' * HSL (ζ ^ m) = HSL (ζ ^ m) * B' := by
    have h1 : B * (P * HSL (ζ ^ m) * P⁻¹) = (P * HSL (ζ ^ m) * P⁻¹) * B := by
      rw [← hPZ]
      exact hBZ
    rw [hB']
    calc P⁻¹ * B * P * HSL (ζ ^ m) = P⁻¹ * (B * (P * HSL (ζ ^ m) * P⁻¹)) * P := by group
      _ = P⁻¹ * ((P * HSL (ζ ^ m) * P⁻¹) * B) * P := by rw [h1]
      _ = HSL (ζ ^ m) * (P⁻¹ * B * P) := by group
  have hne' : (((ζ ^ m)⁻¹ : Lˣ) : L) - ((ζ ^ m : Lˣ) : L) ≠ 0 := fun h =>
    hne (Units.ext (sub_eq_zero.mp h).symm)
  have hoff : ∀ i j : Fin 2, i ≠ j → (B' : Matrix (Fin 2) (Fin 2) L) i j = 0 := by
    intro i j hij
    have h01 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 0 1) hcomm
    have h10 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 1 0) hcomm
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add] at h01 h10
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact (mul_eq_zero.mp (show (B' : Matrix (Fin 2) (Fin 2) L) 0 1 *
        ((((ζ ^ m)⁻¹ : Lˣ) : L) - ((ζ ^ m : Lˣ) : L)) = 0 by linear_combination h01)).resolve_right
          hne'
    · exact (mul_eq_zero.mp (show (B' : Matrix (Fin 2) (Fin 2) L) 1 0 *
        (((ζ ^ m : Lˣ) : L) - (((ζ ^ m)⁻¹ : Lˣ) : L)) = 0 by linear_combination h10)).resolve_right
          (fun h => hne' (by linear_combination -h))
    · exact absurd rfl hij
  obtain ⟨t, ht⟩ := eq_HSL_of_diag hoff
  have h3 : B' ^ 3 = 1 := by
    have := conj_pow (a := P⁻¹) (b := B) (i := 3)
    rw [inv_inv] at this
    rw [hB', this, hB3]
    group
  have ht3 : t ^ 3 = 1 := by
    apply CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_injective (K := L)
    rw [map_pow, CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply, ← ht, h3, map_one]
  obtain ⟨j, hj, rfl⟩ := eq_pow_of_pow_three hζ ht3
  refine Subgroup.mem_zpowers_iff.mpr ⟨((j * m : ℕ) : ℤ), ?_⟩
  have h4 : (ζ ^ m) ^ (j * m) = ζ ^ j := by
    rw [← pow_mul, show m * (j * m) = j * (m * m) by ring]
    have : ζ ^ (m * m) = ζ := by
      rcases hm with rfl | rfl
      · simp
      · rw [show 2 * 2 = 3 + 1 by norm_num, pow_add, hζ3, one_mul, pow_one]
    rw [pow_mul', this]
  have h5 : HSL (ζ ^ m) ^ (j * m) = HSL (ζ ^ j) := by
    rw [← h4]
    exact (map_pow (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom L) (ζ ^ m) (j * m)).symm
  rw [zpow_natCast, hPZ, conj_pow, h5, ← ht, hB']
  group

end SL2

section Centralizer


variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem bModel_triEmb_fieldActor {L : Type} [Field L] [Algebra K L] {Fr : L →+* L}
    (hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c))
    (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    triEmb K σ L (fieldActor σ σ x) = Units.map (entrywiseHom Fr) (triEmb K σ L x) := by
  have e : Fr.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom :=
    RingHom.ext fun c => (hcomm c).symm
  have h1 : Units.map (entrywiseHom σ.toRingHom) (x : ModGL TwistTag.D4.tag K) =
      baseChangeGL σ.toRingHom (x : ModGL TwistTag.D4.tag K) := Units.ext rfl
  have h2 : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L)
      (x : ModGL TwistTag.D4.tag K)) =
      baseChangeGL Fr (baseChangeGL (algebraMap K L) (x : ModGL TwistTag.D4.tag K)) := Units.ext rfl
  rw [triEmb_apply, triEmb_apply, coe_fieldActor, h1, h2, baseChangeGL_baseChangeGL,
    baseChangeGL_baseChangeGL, e]

theorem bModel_fieldActor_eq_self_of_mem_centralizer (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hc : c ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) :
    fieldActor σ σ c = c := by
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hcomm : ∀ c, algebraMap K L (σ c) = Fr (algebraMap K L c) := fun c => by
    rw [hσ, hFr, map_pow]
  have hfixθ := twistHom_thetaConj σ Fr (RingHom.ext hcomm)
  obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hc
  have hFZ : Matrix.SpecialLinearGroup.map Fr Z = Z := thetaHom_injective (by
    rw [← twistHom_thetaHom Fr hfixθ, hZ]
    exact triEmb_fixed Fr (RingHom.ext hcomm) c)
  apply triEmb_injective (L := L)
  rw [bModel_triEmb_fieldActor hcomm, ← hZ, bModel_entrywise_thetaHom, hFZ]

theorem bModel_mem_zpowers_of_mem_centralizer (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {z b : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hzS : z ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hbS : b ∈ centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
      Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hb3 : b ^ 3 = 1) (hbz : b * z = z * b) : b ∈ Subgroup.zpowers z := by
  have hℓ : ℓ.Prime := Fact.out
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  set L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨Z, hZ⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hzS
  obtain ⟨B, hB⟩ := exists_thetaHom_of_mem_centralizer hf hℓ3 hK hσ L hFr hbS
  have hZ3 : Z ^ 3 = 1 := thetaHom_injective (by
    rw [map_pow, hZ, ← map_pow, hz3, map_one, map_one])
  have hZ1 : Z ≠ 1 := fun h => hz1 (triEmb_injective (L := L) (by rw [← hZ, h, map_one, map_one]))
  have hB3 : B ^ 3 = 1 := thetaHom_injective (by
    rw [map_pow, hB, ← map_pow, hb3, map_one, map_one])
  have hBZ : B * Z = Z * B := thetaHom_injective (by
    rw [map_mul, map_mul, hB, hZ, ← map_mul, ← map_mul, hbz])
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨μ, hμ⟩ := exists_units_orderOf_nine L h3L
  have hζ : orderOf (μ ^ 3) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hμ]; norm_num), hμ]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (bModel_sl2_mem_zpowers hζ hZ3 hZ1 hB3 hBZ)
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, triEmb_injective (L := L) ?_⟩
  rw [map_zpow, ← hZ, ← map_zpow, hk, hB]

end Centralizer

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
