module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitaryRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairBasic
public import CFSG.StronglyEmbedded.BenderUnitaryBorel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped Matrix LinearAlgebra.Projectivization

universe u

theorem unitary_natural_action_whole_point_parameter
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    let P := ℙ K (Fin 3 → K)
    let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let Omega := {x : P // x ∈ A}
    let G := ProjectiveSpecialUnitaryMatrixGroup J
    Nat.card Omega = (2 ^ f) ^ 3 + 1 ∧
    ∃ (rho : G →* Equiv.Perm Omega) (b : Omega) (B : Subgroup G) (S : Sylow 2 G),
      Function.Injective rho ∧
      (∀ (g : G) (z : Omega) (M : J.specialSubgroup),
        Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) K) =
            (g : Matrix.ProjGenLinGroup (Fin 3) K) →
          ((rho g z : Omega) : P) =
            (Matrix.GeneralLinearGroup.toLin (M : GL (Fin 3) K)).toLinearEquiv •
              (z : P)) ∧
      letI : MulAction G Omega := MulAction.compHom Omega rho
      B = MulAction.stabilizer G b ∧
      Subgroup.normalizer ((S : Subgroup G) : Set G) = B ∧
      TwoRankAtLeastTwo G ∧ fusionStronglyEmbedded B ∧
      MulAction.IsMultiplyPretransitive G Omega 2 ∧
      Nat.card {x : G // x ∈ B ∧ IsInvolution x} = 2 ^ f - 1 ∧
      Nat.card (S : Subgroup G) = (2 ^ f) ^ 3 ∧
      Nat.card (Subgroup.center (S : Subgroup G)) = 2 ^ f ∧
      (∀ z ∈ Subgroup.center (S : Subgroup G), z ^ 2 = 1) ∧
      (∀ x : (S : Subgroup G), x ^ 2 = 1 →
        x ∈ Subgroup.center (S : Subgroup G)) ∧
      ∀ a c : Omega, a ≠ b → c ≠ b →
        ∃! s : S, (s : G) • a = c := by
  classical
  let q := 2 ^ f
  have hqpos : 0 < q := by positivity
  have hqeven : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := ringChar.of_eq (FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hKcard]
    exact Nat.mod_eq_zero_of_dvd
      (even_iff_two_dvd.mp (hqeven.pow_of_ne_zero (by norm_num)))))
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite G := Finite.of_injective
    (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  obtain ⟨hdegree, rho, b, hinj, hnatural, _hBcard,
    ⟨R, D, hRle, hDle, hN, hinf, hsup, _hcyc, hRcard,
      hcomm, hcommcard, hDcard, hreg, ⟨coord, hcoord⟩, _hDcoord, _hDsurj⟩,
    htwo, _hGcard, _hthree⟩ := External.huppert_II_10_12 J q hKcard hfixed hJ
  let : MulAction G Omega := MulAction.compHom Omega rho
  have hstab : (MulAction.stabilizer (Equiv.Perm Omega) b).comap rho =
      MulAction.stabilizer G b := by
    ext g
    rfl
  have hRle' : R ≤ MulAction.stabilizer G b := hstab ▸ hRle
  have hDle' : D ≤ MulAction.stabilizer G b := hstab ▸ hDle
  have hN' : MulAction.stabilizer G b ≤ Subgroup.normalizer (R : Set G) :=
    hstab ▸ hN
  have hsup' : R ⊔ D = MulAction.stabilizer G b := hsup.trans hstab
  have hRne : R ≠ ⊥ := by
    intro h
    have hcard : Nat.card R = 1 := by rw [h]; simp
    have heven : Even (Nat.card R) := hRcard ▸ hqeven.pow_of_ne_zero (by norm_num)
    rw [hcard] at heven
    exact (by decide : ¬ Even (1 : ℕ)) heven
  have hnormalizer : Subgroup.normalizer (R : Set G) = MulAction.stabilizer G b :=
    normalizer_eq_stabilizer_of_regular_compl R b hRle' hRne hreg hN'
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    have hdiv : Nat.gcd (q + 1) 3 ∣ q ^ 2 - 1 := by
      rw [show q ^ 2 - 1 = (q - 1) * (q + 1) by
        simpa [mul_comm] using Nat.sq_sub_sq q 1]
      exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left (q + 1) 3) _
    exact Odd.of_dvd_nat
      (Nat.Even.sub_odd (pow_pos hqpos 2)
        (hqeven.pow_of_ne_zero (by norm_num)) odd_one)
      (Nat.div_dvd_of_dvd hdiv)
  have hRp : IsPGroup 2 R :=
    IsPGroup.of_card (n := f * 3) (by simpa only [q, ← pow_mul] using hRcard)
  obtain ⟨Q, hQ⟩ := exists_sylow_map_eq_of_normal_complement
    hRle' hDle' hN' hinf hsup' hRp hDodd.not_two_dvd_nat
  obtain ⟨S, hS⟩ := exists_sylow_map_eq_of_normalizer_le Q (by
    rw [hQ, hnormalizer])
  have hSR : (S : Subgroup G) = R := hS.trans hQ
  have hNS : Subgroup.normalizer ((S : Subgroup G) : Set G) =
      MulAction.stabilizer G b := by rw [hSR]; exact hnormalizer
  have hsquareR : ∀ z ∈ Subgroup.center R, z ^ 2 = 1 :=
    External.hermitianRoot_center_pow_two_of_coordinates J hJ R hcomm coord hcoord
  have hcentralR : ∀ x : R, x ^ 2 = 1 → x ∈ Subgroup.center R :=
    hermitian_root_square_one_mem_center_of_coordinates J hJ R coord hcoord
  have hsquareS : ∀ z ∈ Subgroup.center (S : Subgroup G), z ^ 2 = 1 := by
    rw [hSR]
    exact hsquareR
  have hcentralS : ∀ x : (S : Subgroup G), x ^ 2 = 1 →
      x ∈ Subgroup.center (S : Subgroup G) := by
    rw [hSR]
    exact hcentralR
  have hZcard : Nat.card (Subgroup.center (S : Subgroup G)) = q := by
    rw [hSR, ← hcomm]
    exact hcommcard
  have hrank : TwoRankAtLeastTwo G :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair.rank_two_of_sylow_center S
      (by
        rw [hZcard]
        simpa only [show 2 ^ 2 = 4 from rfl] using
          Nat.pow_le_pow_right (n := 2) (by omega) hf) hsquareS
  have hSE : fusionStronglyEmbedded (MulAction.stabilizer G b) := by
    rw [← hNS]
    exact (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ S).1
  have hcount : Nat.card {x : G // x ∈ MulAction.stabilizer G b ∧ IsInvolution x} =
      q - 1 := by
    rw [CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair.point_involution_card_of_sylow_center
      S b hNS (fun x hx => hcentralS x hx.sq_eq_one) hsquareS, hZcard]
  have hregS : ∀ a c : Omega, a ≠ b → c ≠ b →
      ∃! s : S, (s : G) • a = c := by
    intro a c ha hc
    let e : (S : Subgroup G) ≃* R := MulEquiv.subgroupCongr hSR
    obtain ⟨r, hr, huniq⟩ := hreg a c ha hc
    refine ⟨e.symm r, ?_, ?_⟩
    · change (e.symm r : G) • a = c
      simp only [e, MulEquiv.subgroupCongr_symm_apply]
      exact hr
    · intro s hs
      apply e.injective
      have he : e s = r := huniq (e s) (by
        change (e s : G) • a = c
        simp only [e, MulEquiv.subgroupCongr_apply]
        exact hs)
      simpa using he
  have htwo' : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a c d e hac hde
    exact htwo a c d e hac hde
  exact ⟨hdegree, rho, b, MulAction.stabilizer G b, S, hinj, hnatural,
    rfl, hNS, hrank, hSE, htwo', hcount, by simpa only [hSR] using hRcard,
    hZcard, hsquareS, hcentralS, hregS⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
