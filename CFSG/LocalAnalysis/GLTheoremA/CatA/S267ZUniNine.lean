module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniAut
import CFSG.LieType.SeitzGeneration.OuterLinearDescent
import CFSG.GH74.Uniqueness.SU.SU7Gen3
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCArith
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_cube_of_fixed {σ : K ≃+* K} {Q₀ : ℕ} (hK : Nat.card K = (Q₀ ^ 3) ^ 2)
    (hK0 : Nat.card (semilinearFixedSubfield σ) = Q₀ ^ 2) (h3 : 3 ∣ Q₀ + 1) {d : K} (hd0 : d ≠ 0)
    (hσd : σ d = d) : ∃ w : K, w ^ 3 = d := by
  set K₀ := semilinearFixedSubfield σ
  have hQ : 2 ≤ Q₀ := by omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (Q₀ ^ 3) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  let b : K₀ := ⟨d, hσd⟩
  have hb0 : b ≠ 0 := fun hb => hd0 (congrArg Subtype.val hb)
  have hcard : Nat.card K₀ˣ = Q₀ ^ 2 - 1 := by rw [Nat.card_units, hK0]
  have hbpow : (Units.mk0 b hb0) ^ (Q₀ ^ 2 - 1) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hdpow : (Units.mk0 d hd0) ^ (Q₀ ^ 2 - 1) = 1 := by
    apply Units.ext
    have := congrArg (fun u : K₀ˣ => ((u : K₀) : K)) hbpow
    simpa [b] using this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, g ^ m = Units.mk0 d hd0 :=
    mem_powers_iff_mem_zpowers.mpr (hg _)
  have hdvd : orderOf g ∣ m * (Q₀ ^ 2 - 1) :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul, hm, hdpow])
  have h1 : 1 ≤ Q₀ ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hfac : (Q₀ ^ 3) ^ 2 - 1 = (Q₀ ^ 2 - 1) * (Q₀ ^ 4 + Q₀ ^ 2 + 1) := by
    have h6 : 1 ≤ (Q₀ ^ 3) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    zify [h1, h6]
    ring
  rw [hord, hfac, mul_comm m] at hdvd
  have hpos : 0 < Q₀ ^ 2 - 1 := by
    have : 4 ≤ Q₀ ^ 2 := by nlinarith
    omega
  have hm' : Q₀ ^ 4 + Q₀ ^ 2 + 1 ∣ m := Nat.dvd_of_mul_dvd_mul_left hpos hdvd
  have h3' : 3 ∣ Q₀ ^ 4 + Q₀ ^ 2 + 1 := by
    have h2 : Q₀ % 3 = 2 := by omega
    apply Nat.dvd_of_mod_eq_zero
    simp [Nat.add_mod, Nat.pow_mod, h2]
  obtain ⟨m', rfl⟩ := h3'.trans hm'
  refine ⟨((g ^ m' : Kˣ) : K), ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, hm, Units.val_mk0]

theorem norm_one_of_pow_three_eq (h : UnitaryFieldData ℓ f K) (h3 : 3 ∣ ℓ ^ f + 1) {v δ : K}
    (hv : v ^ 3 = δ) (hδ : h.bar δ * δ = 1) : h.bar v * v = 1 := by
  set q := ℓ ^ f with hqdef
  have hK : Nat.card K = q ^ 2 := by rw [h.card, hqdef, ← pow_mul, mul_comm]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ h.prime.ne_zero)
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hv
    rw [← hv, mul_zero] at hδ
    exact zero_ne_one hδ
  have hε3 : (h.bar v * v) ^ 3 = 1 := by rw [mul_pow, ← map_pow, hv, hδ]
  have hε1 : (h.bar v * v) ^ (q - 1) = 1 := by
    have hunit : (Units.mk0 v hv0) ^ (q ^ 2 - 1) = 1 := by
      rw [← hK, ← Nat.card_units]
      exact pow_card_eq_one'
    have hv' : v ^ (q ^ 2 - 1) = 1 := by
      have := congrArg Units.val hunit
      simpa using this
    have hfac : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      zify [h2, hq1]
      ring
    rw [UnitaryFieldData.bar_apply, ← hqdef, ← pow_succ, ← pow_mul, ← hfac, hv']
  have hcop : Nat.Coprime 3 (q - 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  have := (pow_gcd_eq_one (a := h.bar v * v)).2 ⟨hε3, hε1⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem fieldFactor_fieldAut (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) (τ : K ≃+* K) :
    fieldFactor h hℓ (fieldAut h τ) = τ := by
  have := primeFormFieldFactor_apply h (isPrimeFormGram_one (n := 3)) (le_refl 3)
    (not_three_two_of_ne_two h.prime hℓ) 1 τ
  rwa [map_one, one_mul] at this

private theorem finite_ringEquiv' : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) fun _ _ hσ =>
    RingEquiv.ext (congrFun hσ)

section NineThree

variable (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = 3) {Q₀ : ℕ}
  (hK0 : Nat.card (semilinearFixedSubfield σ) = Q₀ ^ 2) (hq : ℓ ^ f = Q₀ ^ 3) (h3 : 3 ∣ Q₀ + 1)
include hℓ hσ hK0 hq h3

theorem exists_conj_eq_conjUHom (A : UG h)
    (hA : fieldUHom h σ * conjUHom h A = conjUHom h A * fieldUHom h σ) :
    ∃ s : SG h, MulAut.conj s = conjUHom h A := by
  set q := ℓ ^ f with hqdef
  have hK : Nat.card K = (Q₀ ^ 3) ^ 2 := by rw [h.card, ← hq, ← pow_mul, mul_comm]
  have h3q : 3 ∣ q + 1 := by
    rw [hq]
    exact (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.OFRC.dvd_pow_prime_add_one_iff
      (p := 3)).2 h3
  set Aσ := primeFormFieldU h (isPrimeFormGram_one (n := 3)) σ A
  have hc : conjUHom h Aσ = conjUHom h A := by
    rw [← fieldUHom_conj, hA, mul_inv_cancel_right]
  have hc' : primeFormConjHom h _ (A⁻¹ * Aσ) = 1 := by
    rw [map_mul, map_inv, ← quotU_conjUHom hℓ, ← quotU_conjUHom hℓ, hc, inv_mul_cancel]
  have hker : A⁻¹ * Aσ ∈ (primeFormConjHom h ((1 : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)).ker := hc'
  rw [ker_primeFormConjHom, Subgroup.mem_subgroupOf] at hker
  obtain ⟨c, hcA⟩ := hker
  have hAσ : (Aσ : GL (Fin 3) K) = (A : GL (Fin 3) K) * Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    have e : ((A⁻¹ * Aσ : UG h) : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c :=
      hcA.symm
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at e
    rw [← e, mul_inv_cancel_left]
  have hmat : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
      (c : K) • ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have e := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hAσ
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at e
    rw [← coe_glAut]
    change ((Aσ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [e, scalar_apply, ← smul_eq_mul_diagonal]
  have hA0 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 0 := Units.ne_zero _
  obtain ⟨μ, hμ0, hμ⟩ := CFSG.LieType.SeitzGeneration.exists_rational_smul (p := 3)
    Nat.prime_three h.prime (by have := h.one_le; omega) h.card σ hσ hA0 hmat
  set M := μ • ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hσd : σ M.det = M.det := by
    have e := RingHom.map_det (σ : K →+* K) M
    rw [RingHom.mapMatrix_apply] at e
    exact e.trans (congrArg Matrix.det hμ)
  have hdetA0 : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hdA : M.det = μ ^ 3 * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
    rw [hM, Matrix.det_smul, Fintype.card_fin]
  have hd0 : M.det ≠ 0 := by
    rw [hdA]
    exact mul_ne_zero (pow_ne_zero 3 hμ0) hdetA0
  obtain ⟨w, hw⟩ := exists_cube_of_fixed hK hK0 h3 hd0 hσd
  set v := w / μ with hvdef
  have hv : v ^ 3 = ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
    rw [hvdef, div_pow, hw, hdA]
    field_simp
  have hvn : h.bar v * v = 1 := by
    refine norm_one_of_pow_three_eq h h3q hv ?_
    have := norm_det_eq_one h 1 A.2
    rwa [UnitaryFieldData.norm, mul_comm] at this
  have hv0 : v ≠ 0 := ne_zero_of_norm hvn
  set u : Kˣ := Units.mk0 v hv0 with hu
  have hsU : Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ ∈ UG h := by
    rw [mem_primeFormUnitary]
    have hb : h.bar ((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) = 1 := by
      rw [Units.val_inv_eq_inv_val, hu, Units.val_mk0, map_inv₀, ← mul_inv, hvn, inv_one]
    rw [Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_map (map_zero h.bar),
      diagonal_transpose, Units.val_one, Matrix.mul_one, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact hb
  set B : GL (Fin 3) K := Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A with hB
  have hBdet : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [hB, Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hv,
      Units.val_inv_eq_inv_val, hu, Units.val_mk0, ← mul_pow, inv_mul_cancel₀ hv0, one_pow]
  have hBS : B ∈ SG h := (mem_gramSU_iff_unitary h).2 ⟨mul_mem hsU A.2, hBdet⟩
  refine ⟨⟨B, hBS⟩, ?_⟩
  rw [← conjUHom_of_mem]
  exact conjUHom_scalar_mul u⁻¹ rfl

variable (hperf : commutator (SG h) = ⊤) {E : Subgroup (MulAut (SG h))} (hE : IsElemAbelian 3 E)
  (hσE : fieldUHom h σ ∈ E)
include hperf hE hσE

theorem mem_range_conj_of_quotU_mem {γ : MulAut (SG h)} (hγ : γ ∈ E)
    (hγD : quotU h hℓ γ ∈ innDiag h) : ∃ s : SG h, MulAut.conj s = γ := by
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hγD
  have hγA : conjUHom h A = γ := quotU_injective hℓ hperf (by rw [quotU_conjUHom]; exact hA)
  have hcomm : fieldUHom h σ * conjUHom h A = conjUHom h A * fieldUHom h σ := by
    rw [hγA]
    exact congrArg (Subtype.val : E → MulAut (SG h)) (hE.1.is_comm.comm ⟨_, hσE⟩ ⟨_, hγ⟩)
  obtain ⟨s, hs⟩ := exists_conj_eq_conjUHom h hℓ hσ hK0 hq h3 A hcomm
  exact ⟨s, hs.trans hγA⟩

theorem exists_eq_zpow_mul_conj {γ : MulAut (SG h)} (hγ : γ ∈ E) :
    ∃ k : ℤ, ∃ s : SG h, MulAut.conj s ∈ E ∧ γ = fieldUHom h σ ^ k * MulAut.conj s := by
  haveI : Finite (K ≃+* K) := finite_ringEquiv'
  have hinj := quotU_injective hℓ hperf
  have hE' : IsElemAbelian 3 (E.map (quotU h hℓ)) :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff hinj 3 E).2 hE
  have hF := card_map_fieldFactor_le h hℓ Nat.prime_three hE'
  have hσF : σ ∈ (E.map (quotU h hℓ)).map (fieldFactor h hℓ) :=
    ⟨fieldAut h σ, ⟨fieldUHom h σ, hσE, quotU_fieldUHom hℓ σ⟩, fieldFactor_fieldAut h hℓ σ⟩
  have hFeq : Subgroup.zpowers σ = (E.map (quotU h hℓ)).map (fieldFactor h hℓ) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hσF)
      (by rw [Nat.card_zpowers, hσ]; exact hF)
  have hγF : fieldFactor h hℓ (quotU h hℓ γ) ∈ Subgroup.zpowers σ := by
    rw [hFeq]
    exact ⟨quotU h hℓ γ, ⟨γ, hγ, rfl⟩, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hγF
  have hγ₀E : (fieldUHom h σ ^ k)⁻¹ * γ ∈ E := mul_mem (inv_mem (zpow_mem hσE k)) hγ
  have hγ₀D : quotU h hℓ ((fieldUHom h σ ^ k)⁻¹ * γ) ∈ innDiag h := by
    rw [← ker_fieldFactor h hℓ, MonoidHom.mem_ker, map_mul, map_inv, map_zpow,
      quotU_fieldUHom, map_mul, map_inv, map_zpow, fieldFactor_fieldAut, hk, inv_mul_cancel]
  obtain ⟨s, hs⟩ := mem_range_conj_of_quotU_mem h hℓ hσ hK0 hq h3 hperf hE hσE hγ₀E hγ₀D
  refine ⟨k, s, hs ▸ hγ₀E, ?_⟩
  rw [hs, mul_inv_cancel_left]

theorem nine_le_card_inf_range (hcard : Nat.card E = 27) :
    9 ≤ Nat.card ↥(E ⊓ (MulAut.conj : SG h →* MulAut (SG h)).range) := by
  have hinj := quotU_injective hℓ hperf
  have hE' : IsElemAbelian 3 (E.map (quotU h hℓ)) :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff hinj 3 E).2 hE
  set φ := (fieldFactor h hℓ).comp (quotU h hℓ)
  have h1 := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker φ E
  have hmap : Nat.card (E.map φ) ≤ 3 := by
    rw [← Subgroup.map_map]
    exact card_map_fieldFactor_le h hℓ Nat.prime_three hE'
  have hle : E ⊓ φ.ker ≤ E ⊓ (MulAut.conj : SG h →* MulAut (SG h)).range := by
    rintro γ ⟨hγ, hγk⟩
    refine ⟨hγ, ?_⟩
    have hγD : quotU h hℓ γ ∈ innDiag h := by
      rw [← ker_fieldFactor h hℓ]
      exact hγk
    obtain ⟨s, hs⟩ := mem_range_conj_of_quotU_mem h hℓ hσ hK0 hq h3 hperf hE hσE hγ hγD
    exact ⟨s, hs⟩
  have h2 := Subgroup.card_le_of_le hle
  rw [hcard] at h1
  have : 27 ≤ 3 * Nat.card ↥(E ⊓ φ.ker) := by
    rw [← h1]
    exact Nat.mul_le_mul_right _ hmap
  omega

end NineThree

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end
