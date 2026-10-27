module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizer

open Matrix

variable {K : Type*} [Field K]

theorem card_projGenLinGroup_three_of_card_eq_eight (hK : Nat.card K = 8) :
    Nat.card (ProjGenLinGroup (Fin 3) K) = 16482816 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let := Fintype.ofFinite K
  have hKf : Fintype.card K = 8 := by rw [← Nat.card_eq_fintype_card, hK]
  have hGL : Nat.card (GL (Fin 3) K) = 115379712 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_three, hKf]
    norm_num
  have hscalar : Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Kˣ → GL (Fin 3) K) := by
    intro a b hab
    apply Units.ext
    simpa [GeneralLinearGroup.scalar] using
      congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hab
  have hcenter : Nat.card (Subgroup.center (GL (Fin 3) K)) = 7 := by
    rw [GeneralLinearGroup.center_eq_range_scalar,
      ← Nat.card_congr (MonoidHom.ofInjective hscalar).toEquiv, Nat.card_units, hK]
  have hindex : (Subgroup.center (GL (Fin 3) K)).index = Nat.card (ProjGenLinGroup (Fin 3) K) :=
    rfl
  have h := (Subgroup.center (GL (Fin 3) K)).index_mul_card
  rw [hindex, hcenter, hGL] at h
  omega

theorem exists_pow_three_eq_of_card_eq_eight (hK : Nat.card K = 8) (r : Kˣ) :
    ∃ k : Kˣ, k ^ 3 = r := by
  have hcop : (Nat.card Kˣ).Coprime 3 := by
    rw [Nat.card_units, hK]
    norm_num
  exact ⟨(powCoprime hcop).symm r, by rw [← powCoprime_apply hcop, Equiv.apply_symm_apply]⟩

@[expose] noncomputable def projectiveSpecialLinearEquivPGLThree (hK : Nat.card K = 8) :
    ProjectiveSpecialLinearGroup (Fin 3) K ≃* ProjGenLinGroup (Fin 3) K :=
  MulEquiv.ofBijective ProjectiveSpecialLinearGroup.toPGL
    ⟨ProjectiveSpecialLinearGroup.toPGL_injective,
      ProjectiveSpecialLinearGroup.toPGL_surj_of_roots fun r => by
        simpa only [Fintype.card_fin] using exists_pow_three_eq_of_card_eq_eight hK r⟩

theorem isSimpleGroup_projGenLinGroup_three (hK : Nat.card K = 8) :
    IsSimpleGroup (ProjGenLinGroup (Fin 3) K) :=
  have := (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1
  (projectiveSpecialLinearEquivPGLThree hK).symm.isSimpleGroup

theorem eq_top_of_index_lt_prime_dvd {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hpG : p ∣ Nat.card G) (hlt : H.index < p) :
    H = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom G (G ⧸ H)).ker with
    hbot | htop
  · have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) :=
      (MonoidHom.ker_eq_bot_iff _).mp hbot
    have hdvd := Subgroup.card_dvd_of_injective _ hinj
    rw [Nat.card_perm] at hdvd
    have := (hp.dvd_factorial).mp (hpG.trans hdvd)
    exact absurd hlt (not_lt.mpr this)
  · rw [← Subgroup.normalCore_eq_ker] at htop
    exact top_le_iff.mp (htop ▸ H.normalCore_le)

theorem projective_linear_three_eight_small_order_exclusion (hK : Nat.card K = 8) :
    ¬ ∃ H : Subgroup (ProjGenLinGroup (Fin 3) K), Nat.card H = 2 ^ 9 * 73 * 9 := by
  rintro ⟨H, hH⟩
  have := isSimpleGroup_projGenLinGroup_three hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Finite (ProjGenLinGroup (Fin 3) K) := Finite.of_surjective _ ProjGenLinGroup.mk_surjective
  have hcard := card_projGenLinGroup_three_of_card_eq_eight hK
  have hindex : H.index = 49 := by
    have h := H.card_mul_index
    rw [hH, hcard] at h
    omega
  have htop := eq_top_of_index_lt_prime_dvd H (p := 73) (by norm_num)
    (by rw [hcard]; norm_num) (by rw [hindex]; norm_num)
  rw [htop, Subgroup.index_top] at hindex
  omega

local instance scalarRangeNormal (n : Type*) [Fintype n] [DecidableEq n] (R : Type*)
    [CommRing R] : ((GeneralLinearGroup.scalar n : Rˣ →* GL n R).range).Normal := by
  rw [← GeneralLinearGroup.center_eq_range_scalar]
  infer_instance

theorem projective_linear_three_eight_small_order_exclusion_scalars (hK : Nat.card K = 8) :
    ¬ ∃ H : Subgroup (GL (Fin 3) K ⧸ (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K).range),
      Nat.card H = 2 ^ 9 * 73 * 9 := by
  rintro ⟨H, hH⟩
  let e : GL (Fin 3) K ⧸ (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K).range ≃*
      ProjGenLinGroup (Fin 3) K :=
    QuotientGroup.quotientMulEquivOfEq GeneralLinearGroup.center_eq_range_scalar.symm
  exact projective_linear_three_eight_small_order_exclusion hK
    ⟨H.map e.toMonoidHom, by rw [Subgroup.card_map_of_injective e.injective, hH]⟩

end CFSG.ProperTwoGeneratedCore.CosetNormalizer
