module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClLift
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ClCore
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81Basic

public section

namespace CFSG.ComponentClassification.CatFC.DS81.ClSU

open Matrix Subgroup CFSG.Open CFSG.ComponentClassification.CatFC.DS81.ClLift

theorem eq_one_of_pow_eightynine_of_pow_two_pow_add_one {K : Type} [Field K] {c : K} {f : ℕ}
    (h89 : c ^ 89 = 1) (hq : c ^ (2 ^ f + 1) = 1) : c = 1 :=
  eq_one_of_pow_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 89)).mpr
      (ClArith.not_eightynine_dvd_two_pow_add_one f)).symm hq h89

theorem eightynine_dvd_card_centralizer {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ f) ^ 2)
    (τ : StatedProj (StatedSU n (2 ^ f) K)) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSU n (2 ^ f) K))))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set (StatedProj (StatedSU n (2 ^ f) K)))) := by
  classical
  set θ : K →+* K := iterateFrobenius K 2 f with hθdef
  have hθ : ∀ c, θ c = c ^ (2 ^ f) := fun _ => rfl
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hθθ : ∀ c, θ (θ c) = c := by
    intro c
    rw [hθ, hθ, ← pow_mul, ← sq, ← hcard]
    exact FiniteField.pow_card c
  have hmap : ∀ A : Matrix (Fin n) (Fin n) K, A.map θ = A.map (· ^ 2 ^ f) := fun A => by
    ext i j; simp [hθ]
  have hmem : ∀ A : GL (Fin n) K, A ∈ StatedSU n (2 ^ f) K ↔
      (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
        ((A : Matrix (Fin n) (Fin n) K).map (· ^ 2 ^ f))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 :=
    fun A => by
      have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := n) hn).1
      have := Set.ext_iff.1 h A
      simpa using this
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨th, rfl⟩ := QuotientGroup.mk_surjective τ
  have hτ2 : (QuotientGroup.mk th : StatedProj (StatedSU n (2 ^ f) K)) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk th : StatedProj (StatedSU n (2 ^ f) K))
    rwa [hτ] at this
  obtain ⟨yh, b, hyb, hy1, hc⟩ := exists_commuting_pow_lift th hτ2 h23
  set g : Matrix (Fin n) (Fin n) K :=
    (((yh : StatedSU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hg
  have hgform : (g.map θ)ᵀ * 1 * g = 1 := by
    rw [Matrix.mul_one, hmap]
    exact ((hmem _).mp yh.2).2
  have hgb : g ^ (23 ^ b) = 1 := (pow_eq_one_iff_matrix yh _).mp hyb
  have hg1 : g ≠ 1 := by
    intro h
    apply hy1
    rw [(matrix_eq_one_iff yh).mp h, QuotientGroup.mk_one]
  obtain ⟨zM, hzR, hzform, hz89, hz1⟩ := ClCore.exists_form_order_eightynine θ hθθ
    (1 : Matrix (Fin n) (Fin n) K) (by simp) (by simp) g hgform hgb hg1
  have hdet : zM.det = 1 := by
    apply eq_one_of_pow_eightynine_of_pow_two_pow_add_one (f := f)
    · rw [← Matrix.det_pow, hz89, Matrix.det_one]
    · have h1 := congrArg Matrix.det hzform
      have hdm : (zM.map θ).det = θ zM.det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
      rw [Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose, hdm, hθ, Matrix.det_one] at h1
      rw [pow_succ]; exact h1
  let zU : GL (Fin n) K := glOfPow89 zM hz89
  have hzU : (zU : Matrix (Fin n) (Fin n) K) = zM := rfl
  have hzmem : zU ∈ StatedSU n (2 ^ f) K := by
    rw [hmem, hzU]
    refine ⟨hdet, ?_⟩
    rw [← hmap]
    simpa only [Matrix.mul_one] using hzform
  let zh : StatedSU n (2 ^ f) K := ⟨zU, hzmem⟩
  have hzh : (((zh : StatedSU n (2 ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = zM := rfl
  have hcm : Commute ((((th : StatedSU n (2 ^ f) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) g := (commute_iff_matrix th yh).mp hc
  have hcz : Commute zM ((((th : StatedSU n (2 ^ f) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hzR hcm).symm
  have hzth : Commute th zh := by
    rw [commute_iff_matrix, hzh]
    exact hcz.symm
  have hzh89 : zh ^ 89 = 1 := (pow_eq_one_iff_matrix zh 89).mpr (by rw [hzh]; exact hz89)
  have hzne : (QuotientGroup.mk zh : StatedProj (StatedSU n (2 ^ f) K)) ≠ 1 := by
    apply mk_ne_one_of_not_scalar
    intro c hcM
    rw [hzh] at hcM
    have hc89 : c ^ 89 = 1 := by
      have h1 : Matrix.scalar (Fin n) (c ^ 89) = Matrix.scalar (Fin n) 1 := by
        rw [map_pow, ← hcM, hz89, map_one]
      exact (Matrix.scalar_inj).mp h1
    have hcq : θ c * c = 1 := by
      refine form_scalar θ (1 : Matrix (Fin n) (Fin n) K) (by simp) c ?_
      rw [← hcM]
      simpa only [Matrix.mul_one, Matrix.one_mul] using hzform
    rw [hθ, ← pow_succ] at hcq
    have hc1 : c = 1 := eq_one_of_pow_eightynine_of_pow_two_pow_add_one hc89 hcq
    apply hz1
    rw [hcM, hc1, map_one]
  exact eightynine_dvd_of_commute th zh hzth hzh89 hzne

theorem lie23To89_psu {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hm : StatedClassicalModel X .PSU n 2 f) (τ : X) (hτ : orderOf τ = 2)
    (h23 : 23 ∣ Nat.card ↥(centralizer ({τ} : Set X))) :
    89 ∣ Nat.card ↥(centralizer ({τ} : Set X)) := by
  obtain ⟨hadm, K, _, _, hcard, ⟨φ⟩⟩ := hm
  have hn : 3 ≤ n := hadm.2.2.1
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  rw [card_centralizer_eq φ τ] at h23 ⊢
  exact eightynine_dvd_card_centralizer (by omega) hcard (φ τ)
    (by rw [MulEquiv.orderOf_eq]; exact hτ) h23

end CFSG.ComponentClassification.CatFC.DS81.ClSU
