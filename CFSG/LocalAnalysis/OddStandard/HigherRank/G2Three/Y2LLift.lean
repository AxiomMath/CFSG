module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LPibar
public import Certificates.Certificate442314

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup Matrix

theorem y2l_claimA_codes {la lb : List ℕ}
    (hla : la ∈ y2l_bits 9) (hlb : lb ∈ y2l_bits 9)
    (h2 : y2l_pow3 (y2l_perturb y2l_alpha0 la) 2 = y2l_one3)
    (h3 : y2l_pow3 (y2l_perturb y2l_beta0 lb) 3 = y2l_one3)
    (hr : y2l_relOK (y2l_perturb y2l_alpha0 la) (y2l_perturb y2l_beta0 lb) = true) :
    ∃ lk ∈ y2l_bits 9,
      y2l_mul3 (y2l_mul3 (y2l_perturb y2l_one3 lk) y2l_alpha0) (y2l_perturb y2l_one3 lk) =
        y2l_perturb y2l_alpha0 la ∧
      y2l_mul3 (y2l_mul3 (y2l_perturb y2l_one3 lk) y2l_beta0) (y2l_perturb y2l_one3 lk) =
        y2l_perturb y2l_beta0 lb := by
  have h := (Certificates.certificate442314 : y2l_claimACheck () = true)
  simp only [y2l_claimACheck] at h
  have h1 := List.all_eq_true.mp h la hla
  simp only [h2, beq_self_eq_true, Bool.not_true, Bool.false_or] at h1
  have h1' := List.all_eq_true.mp h1 lb hlb
  simp only [h3, hr, beq_self_eq_true, Bool.not_true, Bool.false_or] at h1'
  obtain ⟨lk, hlk, he⟩ := List.mem_map.mp (List.contains_iff_mem.mp h1')
  simp only [Prod.mk.injEq] at he
  exact ⟨lk, hlk, he.1, he.2⟩

theorem y2l_claimA {A B : Matrix (Fin 3) (Fin 3) (ZMod 4)}
    (hA : y2l_red A = y2l_red (y2l_dec y2l_alpha0))
    (hB : y2l_red B = y2l_red (y2l_dec y2l_beta0)) (h2 : A ^ 2 = 1) (h3 : B ^ 3 = 1)
    (h7 : (A * B) ^ 7 = 1) (h4 : (A * B * A * (B * B)) ^ 4 = 1) :
    ∃ K : Matrix (Fin 3) (Fin 3) (ZMod 4), K * K = 1 ∧
      A = K * y2l_dec y2l_alpha0 * K ∧ B = K * y2l_dec y2l_beta0 * K := by
  obtain ⟨DA, hDA, rfl⟩ := y2l_exists_perturb hA
  obtain ⟨DB, hDB, rfl⟩ := y2l_exists_perturb hB
  have hA' : y2l_dec (y2l_perturb y2l_alpha0 (y2l_enc DA)) =
      y2l_dec y2l_alpha0 + (2 : ZMod 4) • DA := by
    rw [y2l_dec_perturb rfl (y2l_length_enc DA), y2l_dec_enc]
  have hB' : y2l_dec (y2l_perturb y2l_beta0 (y2l_enc DB)) =
      y2l_dec y2l_beta0 + (2 : ZMod 4) • DB := by
    rw [y2l_dec_perturb rfl (y2l_length_enc DB), y2l_dec_enc]
  have e2 : y2l_pow3 (y2l_perturb y2l_alpha0 (y2l_enc DA)) 2 = y2l_one3 :=
    y2l_eq_of_dec (y2l_nf_pow3 _ _) y2l_nf_one3 (by rw [y2l_dec_pow3, hA', h2, y2l_dec_one3])
  have e3 : y2l_pow3 (y2l_perturb y2l_beta0 (y2l_enc DB)) 3 = y2l_one3 :=
    y2l_eq_of_dec (y2l_nf_pow3 _ _) y2l_nf_one3 (by rw [y2l_dec_pow3, hB', h3, y2l_dec_one3])
  have hr : y2l_relOK (y2l_perturb y2l_alpha0 (y2l_enc DA))
      (y2l_perturb y2l_beta0 (y2l_enc DB)) = true := by
    set a := y2l_perturb y2l_alpha0 (y2l_enc DA)
    set b := y2l_perturb y2l_beta0 (y2l_enc DB)
    have e7 : y2l_pow3 (y2l_mul3 a b) 7 = y2l_one3 :=
      y2l_eq_of_dec (y2l_nf_pow3 _ 7) y2l_nf_one3 (by
        rw [y2l_dec_pow3, y2l_dec_mul3, hA', hB', h7, y2l_dec_one3])
    have e4 : y2l_pow3 (y2l_mul3 (y2l_mul3 (y2l_mul3 a b) a) (y2l_mul3 b b)) 4 = y2l_one3 :=
      y2l_eq_of_dec (y2l_nf_pow3 _ 4) y2l_nf_one3 (by
        rw [y2l_dec_pow3, y2l_dec_mul3, y2l_dec_mul3, y2l_dec_mul3, y2l_dec_mul3, hA', hB', h4,
          y2l_dec_one3])
    rw [y2l_relOK, e7, e4]
    rfl
  obtain ⟨lk, hlk, hka, hkb⟩ :=
    y2l_claimA_codes (y2l_enc_mem_bits hDA) (y2l_enc_mem_bits hDB) e2 e3 hr
  have hK : y2l_dec (y2l_perturb y2l_one3 lk) = 1 + (2 : ZMod 4) • y2l_dec lk := by
    rw [y2l_dec_perturb rfl (y2l_length_of_mem_bits hlk), y2l_dec_one3]
  refine ⟨y2l_dec (y2l_perturb y2l_one3 lk), by rw [hK]; exact y2l_sq_one_add_two _, ?_, ?_⟩
  · rw [← hA', ← hka, y2l_dec_mul3, y2l_dec_mul3]
  · rw [← hB', ← hkb, y2l_dec_mul3, y2l_dec_mul3]

variable {X : Type} [Group X] {M : Subgroup X} [M.Normal]

theorem y2l_exists_lift [Finite X]
    (τ : M ≃* Multiplicative (Fin 3 → ZMod 4)) (hC : centralizer (M : Set X) = M)
    (ψ : X →* GL (Fin 3) (ZMod 2)) (hψ : Function.Surjective ψ) (hker : ψ.ker = M)
    (hidx : M.index = 168) :
    ∃ (τ' : M ≃* Multiplicative (Fin 3 → ZMod 4)) (xa xb : X),
      y2l_rho τ' xa = y2l_dec y2l_alpha0 ∧ y2l_rho τ' xb = y2l_dec y2l_beta0 := by
  have hk := y2l_ker_pibar τ hC ψ hψ hker
  have hs := y2l_pibar_surj τ hk hidx
  have key : ∀ (x : X) (l : List ℕ), y2l_red (y2l_rho τ x) = y2l_red (y2l_dec l) →
      l = y2l_one3 → y2l_rho τ x = 1 := fun x l h hl =>
    y2l_rho_of_mem τ (hk ▸ MonoidHom.mem_ker.mpr ((y2l_pibar_eq_one_iff τ).mpr (by
      rw [h, hl, y2l_dec_one3, map_one])))
  have hα : y2l_red (y2l_dec y2l_alpha0) * y2l_red (y2l_dec y2l_alpha0) = 1 := by
    rw [← map_mul, ← y2l_dec_mul3, show y2l_mul3 y2l_alpha0 y2l_alpha0 = y2l_one3 by decide,
      y2l_dec_one3, map_one]
  have hβ : y2l_red (y2l_dec y2l_beta0) *
      (y2l_red (y2l_dec y2l_beta0) * y2l_red (y2l_dec y2l_beta0)) = 1 := by
    rw [← map_mul, ← map_mul, ← y2l_dec_mul3, ← y2l_dec_mul3,
      show y2l_mul3 y2l_beta0 (y2l_mul3 y2l_beta0 y2l_beta0) = y2l_one3 by decide, y2l_dec_one3,
      map_one]
  have hβ' : y2l_red (y2l_dec y2l_beta0) * y2l_red (y2l_dec y2l_beta0) *
      y2l_red (y2l_dec y2l_beta0) = 1 := by
    rw [mul_assoc, hβ]
  obtain ⟨xa, hxa⟩ := hs ⟨_, _, hα, hα⟩
  obtain ⟨xb, hxb⟩ := hs ⟨_, _, hβ, hβ'⟩
  have ha : y2l_red (y2l_rho τ xa) = y2l_red (y2l_dec y2l_alpha0) := by
    rw [← y2l_coe_pibar, hxa]
  have hb : y2l_red (y2l_rho τ xb) = y2l_red (y2l_dec y2l_beta0) := by
    rw [← y2l_coe_pibar, hxb]
  have h2 : y2l_rho τ xa ^ 2 = 1 := by
    rw [← map_pow]
    refine key _ (y2l_pow3 y2l_alpha0 2) ?_ (by decide)
    simp only [map_pow, ha, y2l_dec_pow3]
  have h3 : y2l_rho τ xb ^ 3 = 1 := by
    rw [← map_pow]
    refine key _ (y2l_pow3 y2l_beta0 3) ?_ (by decide)
    simp only [map_pow, hb, y2l_dec_pow3]
  have h7 : (y2l_rho τ xa * y2l_rho τ xb) ^ 7 = 1 := by
    rw [← map_mul, ← map_pow]
    refine key _ (y2l_pow3 (y2l_mul3 y2l_alpha0 y2l_beta0) 7) ?_ (by decide)
    simp only [map_pow, map_mul, ha, hb, y2l_dec_pow3, y2l_dec_mul3]
  have h4 : (y2l_rho τ xa * y2l_rho τ xb * y2l_rho τ xa * (y2l_rho τ xb * y2l_rho τ xb)) ^ 4 =
      1 := by
    simp only [← map_mul, ← map_pow]
    refine key _ (y2l_pow3 (y2l_mul3 (y2l_mul3 (y2l_mul3 y2l_alpha0 y2l_beta0) y2l_alpha0)
      (y2l_mul3 y2l_beta0 y2l_beta0)) 4) ?_ (by decide)
    simp only [map_pow, map_mul, ha, hb, y2l_dec_pow3, y2l_dec_mul3]
  obtain ⟨K, hK, hA, hB⟩ := y2l_claimA ha hb h2 h3 h7 h4
  refine ⟨τ.trans (y2l_rowAut K hK), xa, xb, ?_, ?_⟩
  · rw [y2l_rho_trans, hA, show K * (K * y2l_dec y2l_alpha0 * K) * K =
      K * K * y2l_dec y2l_alpha0 * (K * K) by simp only [mul_assoc], hK, one_mul, mul_one]
  · rw [y2l_rho_trans, hB, show K * (K * y2l_dec y2l_beta0 * K) * K =
      K * K * y2l_dec y2l_beta0 * (K * K) by simp only [mul_assoc], hK, one_mul, mul_one]

end CFSG.OddStandard.HigherRank.G2Three.Sec2
