module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangU64
public import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LieType.SemisimpleCentralizers.OrderThree

open Matrix CFSG.Open CFSG.Assembly
open CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.ClassicalGroups.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

private theorem three_dvd_two_pow_add_two {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n + 2 := by
  have hmod : (2 ^ n + 2) % 3 = 0 := by
    rw [Nat.add_mod, CFSG.two_pow_mod_three_of_even hn]
  exact Nat.dvd_of_mod_eq_zero hmod

private theorem not_three_dvd_two_pow_add_one_of_even {n : ℕ} (hn : Even n) : ¬ 3 ∣ 2 ^ n + 1 := by
  have hmod : (2 ^ n + 1) % 3 = 2 := by
    rw [Nat.add_mod, CFSG.two_pow_mod_three_of_even hn]
  intro hdvd
  rw [Nat.dvd_iff_mod_eq_zero] at hdvd
  omega

theorem exists_cube_eq_of_pow_succ_eq_one {M : Type*} [CommMonoid M] {n : ℕ} (hn : Even n) {ν : M}
    (hν : ν ^ (2 ^ n + 1) = 1) : ∃ ρ : M, ρ ^ (2 ^ n + 1) = 1 ∧ ρ ^ 3 = ν := by
  obtain ⟨m, hm⟩ := three_dvd_two_pow_add_two hn
  refine ⟨ν ^ m, ?_, ?_⟩
  · rw [← pow_mul]
    rw [pow_mul', hν, one_pow]
  · rw [← pow_mul, Nat.mul_comm m 3, ← hm]
    rw [show 2 ^ n + 2 = (2 ^ n + 1) + 1 by omega, pow_succ, hν, one_mul]

theorem exists_mem_statedSU_pow_three_eq_one {K : Type} [Field K] [Finite K] {n d : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : Even n) (hn0 : n ≠ 0) (hd : 3 ≤ d)
    {β : MulAut (StatedProj (StatedSU d (2 ^ n) K))} {A : GL (Fin d) K}
    (hA : A ∈ LargeEvenGUSet (Fin d) K (2 ^ n))
    (hβA : ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = A * g * A⁻¹ →
      β (QuotientGroup.mk g) = QuotientGroup.mk g')
    (hβ3 : β ^ 3 = 1) :
    ∃ B : GL (Fin d) K, B ∈ StatedSU d (2 ^ n) K ∧ B ^ 3 = 1 ∧
      ∀ g g' : ↥(StatedSU d (2 ^ n) K), (g' : GL (Fin d) K) = B * g * B⁻¹ →
        β (QuotientGroup.mk g) = QuotientGroup.mk g' := by
  have hn1 : 1 ≤ n := by omega
  have hd1 : 1 ≤ d := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn1, by rw [hK, ← pow_mul, Nat.mul_comm]⟩
  haveI : CharP K 2 := h.charP
  let bar : K ≃+* K := unitaryInvolution K 2 n
  have hbar : IsUnitaryInvolution bar := isUnitaryInvolution_unitaryInvolution hK
  have hbarapp : ∀ x, bar x = x ^ (2 ^ n) := fun x => unitaryInvolution_apply K 2 n x
  have hbarh : ∀ x, h.bar x = bar x := fun x => by rw [hbarapp]; rfl
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  have hμ : bar μ = μ := by rw [hbarapp]; exact hμq
  have hAconj : conjTr bar (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) =
      μ • (1 : Matrix (Fin d) (Fin d) K) := by
    have hmap : (A : Matrix (Fin d) (Fin d) K).map bar =
        (A : Matrix (Fin d) (Fin d) K).map (· ^ (2 ^ n)) := by
      ext i j
      simp [hbarapp]
    unfold conjTr
    rw [hmap]
    exact hAμ
  obtain ⟨A', l, hA'iso, hAA'⟩ := exists_isometry_rep hbar A hμ0 hμ hAconj
  have hA'uU : A' ∈ uU h d := by
    rw [mem_uU]
    have hmap : ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar =
        ((A' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map bar := by
      ext i j
      simp [hbarh]
    rw [hmap]
    simpa [IsIso, conjTr] using hA'iso
  let Au : uU h d := ⟨A', hA'uU⟩
  have hβeq : β = uConjAut h hd1 Au := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    let x' : StatedSU d (2 ^ n) K :=
      ⟨A' * (g : GL (Fin d) K) * A'⁻¹, uConjSU_mem h Au g⟩
    have hx' : (x' : GL (Fin d) K) = A * (g : GL (Fin d) K) * A⁻¹ := by
      dsimp [x']
      rw [hAA']
      exact (conj_eq_of_scalar l A' (g : GL (Fin d) K)).symm
    have h1 : β (QuotientGroup.mk g) = QuotientGroup.mk x' := hβA g x' hx'
    have h2 : uConjAut h hd1 Au (QuotientGroup.mk g) = QuotientGroup.mk x' := by
      simpa [x', projH] using (uConjAut_proj h hd1 Au g)
    rw [h1, h2]
  have hβ3' : (uConjAut h hd1 Au) ^ 3 = 1 := by
    rw [← hβeq]
    exact hβ3
  have hmap3 : uConjAut h hd1 (Au ^ 3) = 1 := by
    rw [map_pow]
    exact hβ3'
  obtain ⟨c, hc⟩ := (uConjAut_eq_one_iff h hd (Au ^ 3)).1 hmap3
  have hA'3 : A' ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    simpa [Au] using hc
  have hA'3mem : A' ^ 3 ∈ uU h d := pow_mem hA'uU 3
  have hc_mem : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ uU h d := by
    rwa [← hA'3]
  have hc_norm : h.norm (c : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary h hd1 1 hc_mem
  have hcbar : bar (c : K) * (c : K) = 1 := by
    have hh := hc_norm
    unfold UnitaryFieldData.norm at hh
    rw [hbarh, mul_comm] at hh
    exact hh
  have hc_pow : (c : K) ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← hbarapp]
    exact hcbar
  have hc_unit_pow : (c : Kˣ) ^ (2 ^ n + 1) = 1 := by
    apply Units.ext
    simpa using hc_pow
  obtain ⟨ρ, hρ, hρ3⟩ := exists_cube_eq_of_pow_succ_eq_one hn hc_unit_pow
  have hρinv_unit : (ρ⁻¹ : Kˣ) ^ (2 ^ n + 1) = 1 := by
    rw [inv_pow, hρ, inv_one]
  have hρinv_pow : ((ρ⁻¹ : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hρinv_unit
  have hρinv_norm : h.norm ((ρ⁻¹ : Kˣ) : K) = 1 := by
    calc h.norm ((ρ⁻¹ : Kˣ) : K) = ((ρ⁻¹ : Kˣ) : K) * h.bar ((ρ⁻¹ : Kˣ) : K) := rfl
      _ = ((ρ⁻¹ : Kˣ) : K) ^ (2 ^ n + 1) := by
          rw [hbarh, hbarapp, pow_succ, mul_comm]
      _ = 1 := hρinv_pow
  let B : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) ρ⁻¹ * A'
  have hscalar_mem : Matrix.GeneralLinearGroup.scalar (Fin d) ρ⁻¹ ∈ uU h d :=
    scalar_mem_primeFormUnitary_one h hρinv_norm
  have hBmem : B ∈ uU h d := by
    dsimp [B]
    exact mul_mem hscalar_mem hA'uU
  have hBpow : B ^ 3 = 1 := by
    have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) ρ⁻¹) A' :=
      Matrix.GeneralLinearGroup.scalar_commute ρ⁻¹ A'
    have hs : (Matrix.GeneralLinearGroup.scalar (Fin d) ρ⁻¹) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ := by
      rw [← map_pow]
      congr 1
      rw [inv_pow, hρ3]
    calc B ^ 3 = (Matrix.GeneralLinearGroup.scalar (Fin d) ρ⁻¹) ^ 3 * A' ^ 3 := by
          dsimp [B]
          exact hcomm.mul_pow 3
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ *
            Matrix.GeneralLinearGroup.scalar (Fin d) c := by rw [hs, hA'3]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hBmat : (((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ *
      ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := (mem_uU h).1 hBmem
  have hBdet_mul : h.bar ((B : Matrix (Fin d) (Fin d) K).det) *
      (B : Matrix (Fin d) (Fin d) K).det = 1 := by
    have hh := congrArg Matrix.det hBmat
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det] at hh
    exact hh
  have hBdet_pow : (B : Matrix (Fin d) (Fin d) K).det ^ (2 ^ n + 1) = 1 := by
    have hh := hBdet_mul
    rw [hbarh, hbarapp, ← pow_succ] at hh
    exact hh
  have hBdet3 : (B : Matrix (Fin d) (Fin d) K).det ^ 3 = 1 := by
    have hh := congrArg (fun x : GL (Fin d) K =>
      (x : Matrix (Fin d) (Fin d) K).det) hBpow
    simpa [Units.val_pow_eq_pow_val, Matrix.det_pow] using hh
  have hBdet : (B : Matrix (Fin d) (Fin d) K).det = 1 := by
    have hdvd3 : orderOf ((B : Matrix (Fin d) (Fin d) K).det) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one hBdet3
    have hdvdq : orderOf ((B : Matrix (Fin d) (Fin d) K).det) ∣ 2 ^ n + 1 :=
      orderOf_dvd_of_pow_eq_one hBdet_pow
    have hcop : Nat.Coprime 3 (2 ^ n + 1) :=
      (Nat.prime_three.coprime_iff_not_dvd).2 (not_three_dvd_two_pow_add_one_of_even hn)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvdq)
  have hBSU : B ∈ StatedSU d (2 ^ n) K := by
    change B ∈ unitarySU 2 n K d
    exact (mem_unitarySU_iff h).2 ⟨hBdet, hBmat⟩
  refine ⟨B, hBSU, hBpow, ?_⟩
  intro g g' hgg'
  apply hβA g g'
  calc g' = B * g * B⁻¹ := hgg'
    _ = A' * g * A'⁻¹ := by
        rw [show B = Matrix.GeneralLinearGroup.scalar (Fin d) ρ⁻¹ * A' from rfl]
        exact conj_eq_of_scalar (ρ⁻¹) A' g
    _ = A * g * A⁻¹ := by
        rw [hAA']
        exact (conj_eq_of_scalar l A' g).symm

end CFSG.LieType.SemisimpleCentralizers.OrderThree
