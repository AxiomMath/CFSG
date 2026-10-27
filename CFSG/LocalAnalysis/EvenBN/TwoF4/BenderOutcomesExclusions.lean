module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
public import CFSG.Models.BenderSuzuki
public import CFSG.RankThree.PartOne.BRANCH.RankSylow
public import CFSG.RankThree.PartOne.N143X.G2Rank
public import CFSG.StronglyEmbedded.BenderBinaryHermitian
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

section Unitary

open Subgroup CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open scoped LinearAlgebra.Projectivization

namespace U3

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem mul_eq_zero_of_sq_mem_center {x y w : K} {M : GL (Fin 3) K}
    (hM : (M : Matrix (Fin 3) (Fin 3) K) = !![1, x, y; 0, 1, w; 0, 0, 1])
    (hc : M * M ∈ Subgroup.center (GL (Fin 3) K)) : x * w = 0 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, hu⟩ := hc
  have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  have h2 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 2) hu
  simp [Matrix.mul_apply, Fin.sum_univ_three, hM] at h1 h2
  linear_combination -h2 - y * CharTwo.two_eq_zero (R := K)

theorem card_le_of_mul_self_eq_one {n : ℕ} (J : HermitianForm 3 K)
    (hKcard : Nat.card K = (2 ^ n) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hn : 1 ≤ n)
    {E : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let G := ProjectiveSpecialUnitaryMatrixGroup J
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite G := Finite.of_injective (fun x : G => (x : Matrix.ProjGenLinGroup (Fin 3) K))
    Subtype.coe_injective
  rcases External.huppert_II_10_12 J (2 ^ n) hKcard hfixed hJ with
    ⟨hΩcard, rho, pinf, -, -, hUcard,
      ⟨R, D, hRle, hDle, hN, hinf, hsup, -, hRcard, -, -, hDcard, -, ⟨coordR, hcoordR⟩, -, -⟩,
      htwo, -, -⟩
  let P := ℙ K (Fin 3 → K)
  let A : Set P := {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
    x = Projectivization.mk K v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
  let Ω := {x : P // x ∈ A}
  let : MulAction G Ω := MulAction.compHom Ω rho
  have hsmul : ∀ (g : G) (x : Ω), g • x = rho g x := fun _ _ => rfl
  have hq : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hE x x.2)⟩
  have hodd : ¬ 2 ∣ Nat.card Ω := by
    rw [hΩcard]
    have : Even ((2 ^ n) ^ 3) := hq.pow_of_ne_zero (by norm_num)
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr this.add_one
  obtain ⟨b, hb⟩ := hE2.nonempty_fixed_point_of_prime_not_dvd_card Ω hodd
  obtain ⟨g, hg⟩ : ∃ g : G, rho g b = pinf := by
    by_cases hbp : b = pinf
    · exact ⟨1, by rw [map_one, hbp]; rfl⟩
    · have h3 : 1 < Nat.card Ω := by
        rw [hΩcard]
        have : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow _ _ (by positivity)
        omega
      have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp h3
      obtain ⟨c, hc⟩ := exists_ne pinf
      obtain ⟨g, hg, -⟩ := htwo b pinf pinf c hbp hc.symm
      exact ⟨g, hg⟩
  set E'' := E.map (MulAut.conj g).toMonoidHom with hE''
  have hE''fix : ∀ y ∈ E'', rho y pinf = pinf := by
    rintro _ ⟨x, hx, rfl⟩
    have hbx : rho x b = b := by
      have := hb ⟨x, hx⟩
      rwa [Subgroup.mk_smul, hsmul] at this
    change rho (g * x * g⁻¹) pinf = pinf
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hg, map_inv,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply, hbx]
  set U := (MulAction.stabilizer (Equiv.Perm Ω) pinf).comap rho with hU
  have hE''U : E'' ≤ U := fun y hy => hE''fix y hy
  have hE''2 : IsPGroup 2 E'' := hE2.map _
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := n * 3) (by rw [hRcard, ← pow_mul])
  have hP2 : IsPGroup 2 (E'' ⊔ R : Subgroup G) :=
    hE''2.to_sup_of_normal_right' hR2 (hE''U.trans (hsup ▸ hN))
  have hPU : E'' ⊔ R ≤ U := sup_le hE''U hRle
  have hgdvd : Nat.gcd (2 ^ n + 1) 3 ∣ (2 ^ n) ^ 2 - 1 := by
    have h1 : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      have := Nat.sq_sub_sq (2 ^ n) 1
      rw [one_pow] at this
      rw [this, mul_comm]
    rw [h1]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
  have hmodd : Odd (((2 ^ n) ^ 2 - 1) / Nat.gcd (2 ^ n + 1) 3) := by
    have h1 : Odd ((2 ^ n) ^ 2 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) (hq.pow_of_ne_zero (by norm_num))
        odd_one
    exact h1.of_dvd_nat (Nat.div_dvd_of_dvd hgdvd)
  have hUcard' : Nat.card U = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) / Nat.gcd (2 ^ n + 1) 3) := by
    rw [hUcard, Nat.mul_div_assoc _ hgdvd]
  obtain ⟨a, ha⟩ := hP2.exists_card_eq
  have hdvd : 2 ^ a ∣ (2 ^ n) ^ 3 := by
    have h1 := card_dvd_of_le hPU
    rw [ha, hUcard'] at h1
    exact (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hmodd)).dvd_of_dvd_mul_right h1
  have hER : E'' ≤ R := by
    have heq : E'' ⊔ R = R := (eq_of_le_of_card_ge le_sup_right (by
      rw [ha, hRcard]
      exact Nat.le_of_dvd (by positivity) hdvd)).symm
    exact heq ▸ le_sup_left
  have hE''sq : ∀ y ∈ E'', y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hE x hx, map_one]
  have key : ∀ y (hy : y ∈ E''), (coordR.symm ⟨y, hER hy⟩ : {z : K × K //
      z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0}).1.1 = 0 := by
    intro y hy
    set z := coordR.symm ⟨y, hER hy⟩ with hz
    obtain ⟨M, hM, hMy⟩ := hcoordR z
    have hzy : ((coordR z : R) : G) = y := by rw [hz, Equiv.apply_symm_apply]
    have h1 : Matrix.ProjGenLinGroup.mk (M * M) = 1 := by
      rw [map_mul, ← hMy, hzy]
      have := congrArg (fun w : G => (w : Matrix.ProjGenLinGroup (Fin 3) K)) (hE''sq y hy)
      simpa using this
    rw [Matrix.ProjGenLinGroup.mk_eq_one] at h1
    have h2 := mul_eq_zero_of_sq_mem_center hM h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [neg_eq_zero, map_eq_zero_iff _ J.conj.injective] at h3
      exact h3
  let f : E'' → {x : K // J.conj x = x} := fun y =>
    ⟨(coordR.symm ⟨y, hER y.2⟩ : {z : K × K // z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0}).1.2,
      by
        have h1 := (coordR.symm ⟨y, hER y.2⟩).2
        rw [key y y.2, zero_mul, add_zero] at h1
        linear_combination h1 - (coordR.symm ⟨y, hER y.2⟩ :
          {z : K × K // z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0}).1.2 *
            CharTwo.two_eq_zero (R := K)⟩
  have hf : Function.Injective f := by
    intro y y' hyy
    have h1 : (coordR.symm ⟨y, hER y.2⟩ : {z : K × K //
        z.2 + J.conj z.2 + z.1 * J.conj z.1 = 0}) = coordR.symm ⟨y', hER y'.2⟩ :=
      Subtype.ext (Prod.ext ((key y y.2).trans (key y' y'.2).symm) (congrArg Subtype.val hyy))
    have h2 := congrArg (fun w => ((coordR w : R) : G)) h1
    simp only [Equiv.apply_symm_apply] at h2
    exact Subtype.ext h2
  have hcard := Nat.card_le_card_of_injective f hf
  rw [hfixed, hE'', card_map_of_injective (MulAut.conj g).injective] at hcard
  exact hcard

end U3

theorem card_le_of_lieModel_PSU3 {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSU 3 2 n) {E : Subgroup X} (hE : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 ^ n := by
  have hn := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 h
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_psu3_of_lieModel_PSU3 h
  let k := GaloisField 2 n
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian n (by omega)
  have : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e₂⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hKcard hfixed
  have hmodel : PSU3Model n = CFSG.Open.PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
  let e : X ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    (e₁.trans (MulEquiv.subgroupCongr hmodel.symm)).trans e₂.symm
  have hb := U3.card_le_of_mul_self_eq_one J hKcard hfixed hJ (by omega)
    (E := E.map e.toMonoidHom) (by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, hE y hy, map_one])
  rwa [card_map_of_injective e.injective] at hb

end Unitary

section GTwo

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem card_le_of_lieModel_G2_three
    {X : Type} [Group X] (h : LieModel X .G2 0 3 1)
    {E : Subgroup X} (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 2 ^ 4 := by
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ : UntwistedChevalleyModel X .G2 (3 ^ 1) := by
    rcases h with ⟨ht, -⟩ | ⟨-, -, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hC : Subgroup.center (adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let e : X ≃* adjointGroup .G2 K :=
    e₀.trans ((QuotientGroup.quotientMulEquivOfEq hC).trans QuotientGroup.quotientBot)
  have : Finite (adjointGroup .G2 K) := by
    have : Finite K := ‹_›
    exact Nat.finite_of_card_ne_zero (by
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
      decide)
  obtain ⟨T, ψ, hψ, hT⟩ := CFSG.RankThree.PartOne.N143X.exists_torus_negOne_G2 K
  have hGcard := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := K)
  rw [hK] at hGcard hT
  have hidx : T.index = 265356 := by
    have h1 := T.index_mul_card
    rw [hT, hGcard] at h1
    change T.index * 16 = 4245696 at h1
    omega
  have hb := CFSG.RankThree.PartOne.BRANCH.card_le_of_torus (a := 2) Nat.prime_two ψ hψ
    (by rw [hidx]; decide) (E := E.map e.toMonoidHom) (by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_pow, hE y hy, map_one])
  rw [card_map_of_injective e.injective] at hb
  exact hb

end GTwo

section LinearThree

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover

namespace L3

variable {K : Type} [Field K]

theorem mul_eq_of_dual_apply (A : GL (Fin 3) K) (σ : K ≃+* K) {i j : Fin 3} (hij : i ≠ j)
    {u : SpecialLinearGroup (Fin 3) K} {N : Matrix (Fin 3) (Fin 3) K}
    (hu : (u : Matrix (Fin 3) (Fin 3) K) = 1 + N) (hN : N * N = 0) {k : Fin 3} (hNk : N k k = 0)
    (h : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K)
      (proj 3 K (SpecialLinearGroup.transvection hij 1)) = proj 3 K u) :
    N * (A : Matrix (Fin 3) (Fin 3) K) = (A : Matrix (Fin 3) (Fin 3) K) * single j i (-1) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj] at h
  refine CFSG.SeitzReduction.LinearPilot.mul_eq_of_proj_eq A ?_ hu
    (single_mul_single_of_ne _ _ _ _ hij _) hN hNk h
  rw [coe_slConjugation, SpecialLinearGroup.map_apply_coe, SpecialLinearGroup.coe_transpose,
    SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_coe, transpose_add,
    transpose_one, transpose_single]
  congr 2
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, single_apply, one_apply]
  split_ifs <;> simp

theorem col_eq_zero_of_dual_mem_projRad_zero (A : GL (Fin 3) K) (σ : K ≃+* K) {j : Fin 3}
    (h0j : (0 : Fin 3) ≠ j)
    (h : (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K)
      (proj 3 K (SpecialLinearGroup.transvection h0j 1)) ∈ projRad K 0) :
    (A : Matrix (Fin 3) (Fin 3) K) 1 j = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 2 j = 0 := by
  obtain ⟨a, c, hac⟩ := mem_projRad_zero.1 h
  have key := mul_eq_of_dual_apply A σ h0j (u := unipU K a 0 c)
    (N := !![0, a, c; 0, 0, 0; 0, 0, 0])
    (by ext r s; fin_cases r <;> fin_cases s <;> simp [coe_unipU])
    (by ext r s; fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
    (k := 0) (by simp) hac.symm
  have e1 := congrFun (congrFun key 1) 0
  have e2 := congrFun (congrFun key 2) 0
  fin_cases j
  · exact absurd rfl h0j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, single_apply] at e1 e2 ⊢
    exact ⟨e1, e2⟩

theorem not_dual_le_projRad_zero (A : GL (Fin 3) K) (σ : K ≃+* K)
    (h : ∀ x ∈ projRad K 0, (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) x ∈ projRad K 0) :
    False := by
  obtain ⟨h11, h21⟩ := col_eq_zero_of_dual_mem_projRad_zero A σ (by decide)
    (h _ (LinearThree.proj_transvection_zero_one_mem_projRad 1))
  obtain ⟨h12, h22⟩ := col_eq_zero_of_dual_mem_projRad_zero A σ (by decide)
    (h _ (LinearThree.proj_transvection_zero_two_mem_projRad 0 1))
  apply Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_three, h11, h21, h12, h22]
  ring

theorem not_dual_le_projRad_one (A : GL (Fin 3) K) (σ : K ≃+* K)
    (h : ∀ x ∈ projRad K 1, (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K) x ∈ projRad K 1) :
    False := by
  obtain ⟨b₀, c₀, h₀⟩ := mem_projRad_one.1 (h _
    (LinearThree.proj_transvection_zero_two_mem_projRad 1 1))
  obtain ⟨b₁, c₁, h₁⟩ := mem_projRad_one.1 (h _
    (LinearThree.proj_transvection_one_two_mem_projRad 1))
  have k₀ := mul_eq_of_dual_apply A σ (show (0 : Fin 3) ≠ 2 by decide)
    (u := unipU K 0 b₀ c₀) (N := !![0, 0, c₀; 0, 0, b₀; 0, 0, 0])
    (by ext r s; fin_cases r <;> fin_cases s <;> simp [coe_unipU])
    (by ext r s; fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
    (k := 0) (by simp) h₀.symm
  have k₁ := mul_eq_of_dual_apply A σ (show (1 : Fin 3) ≠ 2 by decide)
    (u := unipU K 0 b₁ c₁) (N := !![0, 0, c₁; 0, 0, b₁; 0, 0, 0])
    (by ext r s; fin_cases r <;> fin_cases s <;> simp [coe_unipU])
    (by ext r s; fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_three])
    (k := 0) (by simp) h₁.symm
  have e01 := congrFun (congrFun k₀ 0) 1
  have e11 := congrFun (congrFun k₀ 1) 1
  have e00 := congrFun (congrFun k₀ 0) 0
  have e10 := congrFun (congrFun k₀ 1) 0
  have e20 := congrFun (congrFun k₀ 2) 0
  have f01 := congrFun (congrFun k₁ 0) 1
  have f11 := congrFun (congrFun k₁ 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, single_apply] at e01 e11 e00 e10 e20 f01 f11
  have hcol : (A : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    by_cases h21 : (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0
    · rw [h21] at f01 f11
      simp at f01 f11
      exact ⟨f01, f11⟩
    · have hc : c₀ = 0 := e01.resolve_right h21
      have hb : b₀ = 0 := e11.resolve_right h21
      rw [hc] at e00
      rw [hb] at e10
      simp at e00 e10
      exact ⟨e00, e10⟩
  apply Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_three, hcol.1, hcol.2, e20]
  ring

theorem not_le_projRad_of_not_mem [Finite K] {y : MulAut (projectiveSL 3 K)}
    (hy : y ∉ semilinearAutGroup 3 K) (i : Fin 2) : ¬ ∀ x ∈ projRad K i, y x ∈ projRad K i := by
  intro h
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 y
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · apply hy
    rw [pow_zero, mul_one]
    exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ)
  · rw [pow_one] at h
    fin_cases i
    · exact not_dual_le_projRad_zero A σ h
    · exact not_dual_le_projRad_one A σ h

theorem false_of_not_mem_semilinear [Finite K] [CharP K 2] {E : Subgroup (projectiveSL 3 K)}
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hcard : Nat.card E = Nat.card K ^ 2)
    {y : MulAut (projectiveSL 3 K)} (hy : y ∉ semilinearAutGroup 3 K)
    (hyE : ∀ x ∈ E, y x ∈ E) : False := by
  obtain ⟨g, hg⟩ := LinearThree.exists_conj_le_projUnip hE2
  set τ : MulAut (projectiveSL 3 K) := MulAut.conj g⁻¹ with hτ
  set F := E.map (τ : projectiveSL 3 K →* projectiveSL 3 K) with hF
  have hFU : F ≤ projUnip K := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [hτ, MulAut.conj_apply] using hg a ha
  have hF2 : ∀ a ∈ F, a ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MonoidHom.coe_ofClass, ← map_pow, hE2 a ha, map_one]
  have hFcard : Nat.card F = Nat.card K ^ 2 := by
    rw [hF, card_map_of_injective τ.injective, hcard]
  have hR := LinearThree.radicals_projUnip (K := K)
  have hτmem : τ ∈ semilinearAutGroup 3 K :=
    linearAutGroup_le_semilinearAutGroup ((standard_outer_quotients (n := 3) (K := K)).1
      ⟨g⁻¹, rfl⟩)
  have hy' : τ * y * τ⁻¹ ∉ semilinearAutGroup 3 K := by
    intro h
    apply hy
    have hyeq : y = τ⁻¹ * (τ * y * τ⁻¹) * τ := by group
    rw [hyeq]
    exact mul_mem (mul_mem (inv_mem hτmem) h) hτmem
  have hyF : ∀ x ∈ F, (τ * y * τ⁻¹) x ∈ F := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨y a, hyE a ha, ?_⟩
    simp [MulAut.mul_apply]
  rcases LinearThree.le_projRad_of_le_projUnip hFU hF2 with h | h
  · have hFeq : F = projRad K 0 := eq_of_le_of_card_ge h (by rw [hR.card₁, hFcard])
    exact not_le_projRad_of_not_mem hy' 0 (hFeq ▸ hyF)
  · have hFeq : F = projRad K 1 := eq_of_le_of_card_ge h (by rw [hR.card₂, hFcard])
    exact not_le_projRad_of_not_mem hy' 1 (hFeq ▸ hyF)

theorem conj_mem_semilinearAutGroup [Finite K] (g : MulAut (projectiveSL 3 K))
    {x : MulAut (projectiveSL 3 K)} (hx : x ∈ semilinearAutGroup 3 K) :
    g * x * g⁻¹ ∈ semilinearAutGroup 3 K := by
  have htop := (automorphism_generation (K := K) (n := 3) le_rfl).1
  have hN := (standard_outer_quotients (n := 3) (K := K)).2.2.2.1
  have hg : g ∈ standardAutGroup 3 K := htop ▸ mem_top g
  have hx' : x ∈ standardAutGroup 3 K := semilinearAutGroup_le_standardAutGroup hx
  have h := hN.conj_mem ⟨x, hx'⟩ (by rw [mem_subgroupOf]; exact hx) ⟨g, hg⟩
  rw [mem_subgroupOf] at h
  exact h

end L3

end LinearThree

end CFSG.LocalAnalysis.EvenBN.TwoF4

end
