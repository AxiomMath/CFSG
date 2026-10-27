module

public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.ClassicalInvolution.RouteD.TWYType

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.RouteD.TWY
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K]
variable {σ : K ≃+* K} [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem finrank_Qn (E : QuadExt F K σ) (n : ℕ) :
    Module.finrank F (Fin n → K) = 2 * n := by
  let : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [E.finrank_eq]
  ring

omit [Finite K] [CharP K 2] in
theorem normQuad_eq_zero_iff (E : QuadExt F K σ) {x : K} :
    normQuad E x = 0 ↔ x = 0 := by
  rw [normQuad]
  exact normForm_eq_zero_iff (normTailData E)

omit [Finite K] [CharP K 2] in
theorem not_isPlusType_normQuad (E : QuadExt F K σ) :
    ¬ IsPlusType (normQuad E) := by
  rintro ⟨W, hW, hWs⟩
  have hdim : Module.finrank F K = 2 := E.finrank_eq
  rw [hdim] at hW
  have hW1 : Module.finrank F W = 1 := by omega
  have hbot : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW1
    omega
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  exact hx0 ((normQuad_eq_zero_iff E).1 (hWs x hxW))

omit [Finite K] [CharP K 2] in
theorem not_isPlusType_Qn_one (E : QuadExt F K σ) :
    ¬ IsPlusType (Qn E 1) := by
  rintro ⟨W, hW, hWs⟩
  have hdim : Module.finrank F (Fin 1 → K) = 2 := by
    simpa using finrank_Qn E 1
  rw [hdim] at hW
  have hW1 : Module.finrank F W = 1 := by omega
  have hbot : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW1
    omega
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hQ : Qn E 1 x = 0 := hWs x hxW
  have hQ' : normQuad E (x 0) = 0 := by
    simpa [Qn_apply, Fin.sum_univ_one] using hQ
  have hx00 : x 0 = 0 := (normQuad_eq_zero_iff E).1 hQ'
  exact hx0 (funext fun i => by fin_cases i; exact hx00)

private noncomputable def splitEquiv (n : ℕ) : (Fin (n + 1) → K) ≃ₗ[F] ((Fin n → K) × K) where
  toFun x := (fun i => x (Fin.castSucc i), x (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  map_add' x y := by
    ext <;> simp
  map_smul' c x := by
    ext <;> simp
  left_inv x := by
    ext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  right_inv p := by
    ext <;> simp

noncomputable def isometryQnSucc (E : QuadExt F K σ) (n : ℕ) :
    (Qn E (n + 1)).IsometryEquiv ((Qn E n).prod (normQuad E)) where
  toLinearEquiv := splitEquiv (F := F) (K := K) n
  map_app' x := by
    rw [QuadraticMap.prod_apply, Qn_apply, Qn_apply, Fin.sum_univ_castSucc]
    rfl

theorem isPlusType_Qn_iff (E : QuadExt F K σ) (n : ℕ) :
    IsPlusType (Qn E n) ↔ Even n := by
  let : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  let : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  induction n with
  | zero =>
    constructor
    · intro _
      exact ⟨0, rfl⟩
    · intro _
      exact isPlusType_of_subsingleton (Qn E 0)
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn
      rw [show Even 1 ↔ False by simp [Nat.even_add_one]]
      exact iff_false_intro (not_isPlusType_Qn_one E)
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hdim_n : Module.finrank F (Fin n → K) = 2 * n := finrank_Qn E n
      have hdim_N : Module.finrank F K = 2 * 1 := by rw [E.finrank_eq]
      rw [isPlusType_congr (isometryQnSucc E n)]
      rw [isPlusType_prod_iff (Qn_polarBilin_nondegenerate E n)
        (normQuad_polarBilin_nondegenerate E) hn1 (by norm_num) hdim_n hdim_N]
      simp only [ih]
      have hN : IsPlusType (normQuad E) ↔ False :=
        iff_false_intro (not_isPlusType_normQuad E)
      rw [hN, Nat.even_add_one]
      tauto

theorem nonempty_isometryEquiv_quadPlus (E : QuadExt F K σ) {n : ℕ} (he : Even n) :
    Nonempty ((Qn E n).IsometryEquiv (quadPlus n F)) := by
  let : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  let : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  exact nonempty_isometry_quadPlus (Qn_polarBilin_nondegenerate E n)
    (finrank_Qn E n) ((isPlusType_Qn_iff E n).mpr he)

theorem nonempty_isometryEquiv_quadMinus (E : QuadExt F K σ) {n : ℕ} (ho : Odd n)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nonempty ((Qn E n).IsometryEquiv (quadMinus n F b c)) := by
  let : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  let : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have hn : 1 ≤ n := by
    rcases ho with ⟨k, hk⟩
    omega
  have hdim : Module.finrank F (Fin n → K) = 2 * n := finrank_Qn E n
  have hodd : ¬ Even n := by
    rcases ho with ⟨k, hk⟩
    rw [hk, Nat.even_add_one]
    simp
  exact nonempty_isometry_of_not_isPlusType (Qn_polarBilin_nondegenerate E n)
    hn hdim (fun h => hodd ((isPlusType_Qn_iff E n).mp h)) hirr

end CFSG.ClassicalInvolution.PhanDn
