module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AutTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutCard
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutClass

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups

section Final

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem transpose_inv_of_transpose_eq' (A : GL (Fin 3) F)
    (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) :
    ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have h1 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← hA, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]
  calc ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ
      = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *
          ((A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * (A : Matrix (Fin 3) (Fin 3) F)) *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [Matrix.mul_assoc]
    _ = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [h1, Matrix.one_mul]

theorem graph_involution_not_fix_sylow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hF : Nat.card F = p)
    (A : GL (Fin 3) F) (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A)
    (P : Sylow 2 (projectiveSL 3 F))
    (hP : ∀ t ∈ (P : Subgroup (projectiveSL 3 F)), (conjAut 3 F A * dualAut 3 F) t = t) :
    False := by
  have := Fintype.ofFinite F
  have hKF : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime hKF
  have hodd : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  have hR' := transpose_inv_of_transpose_eq' A hA
  have hR0 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
    intro h
    have h1 : (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h, Matrix.mul_zero] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp at h2
  have hinj := soProj_injective hR0
  have hle : (P : Subgroup (projectiveSL 3 F)) ≤
      (soProj ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).range := by
    intro t ht
    obtain ⟨y, hy⟩ := exists_mem_soForm_of_fixed A (hP t ht)
    exact ⟨y, hy⟩
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    card_soForm hodd (A⁻¹) hR', hF] at hdvd
  exact not_card_dvd_of_sylow hp2 hF P hdvd

end Final

theorem two_ne_zero_of_charP_ge_three {p : ℕ} {F : Type} [Field F] [CharP F p] (hp3 : 3 ≤ p) :
    (2 : F) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  have h2 : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem oddAutInner_psl3 {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : StatedClassicalModel K .PSL 3 p 1) (β : K ≃* K) (hβ : ∀ x, β (β x) = x)
    (hP : ∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) : IsInnerAut β := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    have hKF : Fintype.card F = p ^ 1 := by rw [← Nat.card_eq_fintype_card, hcard]
    have : CharP F p := charP_of_card_eq_prime_pow hKF
    exact two_ne_zero_of_charP_ge_three (by have := hp.two_le; omega)
  let ψ : K ≃* projectiveSL 3 F :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)
  have hβ'2 : transAut ψ β * transAut ψ β = 1 := transAut_mul_self ψ β hβ
  have hF : Nat.card F = p := by rw [hcard, pow_one]
  rcases classify_involution hF h2 (transAut ψ β) hβ'2 with ⟨g, hg⟩ | ⟨A, hA, hβ'⟩
  · refine isInnerAut_of_transAut_mem_inner ψ β ⟨g⁻¹, ?_⟩
    ext x
    rw [MulAut.conj_apply, inv_inv]
    exact (hg x).symm
  · exfalso
    obtain ⟨P, hP⟩ := hP
    obtain ⟨P', hP'coe⟩ : ∃ P' : Sylow 2 (projectiveSL 3 F),
        (P' : Subgroup (projectiveSL 3 F)) = (P : Subgroup K).map ψ.toMonoidHom :=
      ⟨P.mapSurjective (f := ψ.toMonoidHom) ψ.surjective, rfl⟩
    refine graph_involution_not_fix_sylow hp2 hF A hA P' fun t ht => ?_
    rw [← hβ']
    rw [hP'coe] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    change transAut ψ β (ψ s) = ψ s
    rw [transAut_apply, hP s hs]

end CFSG.QuasithinUnique.Ch1
