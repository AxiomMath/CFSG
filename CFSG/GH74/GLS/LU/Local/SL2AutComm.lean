module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.IVK.Lifted.Companion

public section

open Matrix CFSG CFSG.GorensteinWalter
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL)
open CFSG.GH74.GLS.IVK.Lifted
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_card_pow)
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

section Comm

variable {F : Type} [Field F]

theorem slAutComm_center {G : Type*} [Group G] (k : G) (β : MulAut G)
    (hcomm : β * MulAut.conj k = MulAut.conj k * β) : k⁻¹ * β k ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨x, rfl⟩ := β.surjective g
  have h := DFunLike.congr_fun hcomm x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h
  calc β x * (k⁻¹ * β k) = k⁻¹ * (k * β x * k⁻¹) * β k := by group
    _ = k⁻¹ * (β k * β x * (β k)⁻¹) * β k := by rw [h]
    _ = k⁻¹ * β k * β x := by group

theorem slAutComm_apply_eq {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (k : SL(2, F)) (hk : orderOf k = r)
    (β : MulAut SL(2, F)) (hcomm : β * MulAut.conj k = MulAut.conj k * β) : β k = k := by
  have hz := slAutComm_center k β hcomm
  have hz2 : (k⁻¹ * β k) * (k⁻¹ * β k) = 1 := sq_eq_one_of_mem_center_sl2 hz
  have hβk : β k = k * (k⁻¹ * β k) := by group
  have hkz : Commute k (k⁻¹ * β k) := Subgroup.mem_center_iff.1 hz k
  have hrk : k ^ r = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
  have hβr : (β k) ^ r = 1 := by
    rw [← map_pow, hrk, map_one]
  have hzr : (k⁻¹ * β k) ^ r = 1 := by
    have h1 : (β k) ^ r = k ^ r * (k⁻¹ * β k) ^ r := by
      conv_lhs => rw [hβk]
      exact hkz.mul_pow r
    rw [hβr, hrk, one_mul] at h1
    exact h1.symm
  have h2 : orderOf (k⁻¹ * β k) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
  have h3 : orderOf (k⁻¹ * β k) ∣ r := orderOf_dvd_of_pow_eq_one hzr
  have h4 : orderOf (k⁻¹ * β k) ∣ Nat.gcd r 2 := Nat.dvd_gcd h3 h2
  rw [(Nat.coprime_primes hr Nat.prime_two).2 hr2] at h4
  have h5 : k⁻¹ * β k = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  rw [hβk, h5, mul_one]

theorem slAutComm_nonscalar {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (k : SL(2, F)) (hk : orderOf k = r) :
    ∀ c : F, (k : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro c hc
  have hdet : c * c = 1 := by
    have := k.det_coe
    rw [hc, Matrix.det_smul, Matrix.det_one] at this
    simpa [sq] using this
  have hkk : k * k = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul,
      hdet, one_smul]
    rfl
  have h2 : r ∣ 2 := hk ▸ orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hkk)
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)

theorem slAutComm_trace_mem_fixedField (σ : F ≃+* F) (G : GL (Fin 2) F) (k : SL(2, F))
    (h : SpecialLinearGroup.toGL k =
      G * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL k) * G⁻¹) :
    (k : Matrix (Fin 2) (Fin 2) F) 0 0 + (k : Matrix (Fin 2) (Fin 2) F) 1 1 ∈ fixedField σ := by
  rw [mem_fixedField_iff]
  have h1 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h
  simp only [Units.val_mul] at h1
  have h2 := congrArg Matrix.trace h1
  rw [Matrix.trace_units_conj, Matrix.trace_fin_two, Matrix.trace_fin_two] at h2
  simp only [GeneralLinearGroup.map_apply] at h2
  rw [map_add]
  exact h2.symm

end Comm

section Main

variable {F : Type} [Field F] [Finite F]

theorem slAutComm_card_fixedField {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f) (σ : F ≃+* F) :
    orderOf σ ∣ f ∧ Nat.card (fixedField σ) = p ^ (f / orderOf σ) := by
  have hs0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  have hpow : Nat.card (fixedField σ) ^ orderOf σ = p ^ f := by
    rw [← hF]
    exact fixedField_card_pow σ
  have hdvd : Nat.card (fixedField σ) ∣ p ^ f := hpow ▸ dvd_pow_self _ hs0
  obtain ⟨g, -, hg⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hgs : g * orderOf σ = f := by
    apply Nat.pow_right_injective hp.two_le
    simp only
    rw [pow_mul, ← hg, hpow]
  refine ⟨⟨g, by rw [← hgs, mul_comm]⟩, ?_⟩
  rw [hg, ← hgs, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs0)]

theorem slAutComm_dvd_pow_sub_one {p g r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = p ^ g) (c : SL(2, K)) (hc : orderOf c = r) :
    r ∣ p ^ (2 * g) - 1 := by
  have h1 : r ∣ Nat.card SL(2, K) := hc ▸ orderOf_dvd_natCard c
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK] at h1
  rcases (Nat.Prime.dvd_mul hr).1 h1 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h)) hrp
  · rwa [← pow_mul, mul_comm] at h

theorem sl2_aut_matrix_form_of_commute {p f r : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hp2 : p ≠ 2) (h3 : 3 < p ^ f) (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p) (hrf : ¬ r ∣ f)
    (hgood : ∀ s : ℕ, Odd s → 1 < s → s ∣ f → ¬ r ∣ p ^ (2 * (f / s)) - 1)
    (k : SL(2, F)) (hk : orderOf k = r) (β : MulAut SL(2, F)) {m : ℕ} (hm : Odd m) (hβ : β ^ m = 1)
    (hcomm : β * MulAut.conj k = MulAut.conj k * β) :
    ∃ G : GL (Fin 2) F, β = slConjugation F G ∧
      (G : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F) =
        (k : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) := by
  have _ := hrf
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h3' : 3 < Nat.card F := hF ▸ h3
  have hfix : β k = k := slAutComm_apply_eq hr hr2 k hk β hcomm
  have hσ : (gammaOf hodd h3' β).right = 1 := by
    by_contra hσne
    obtain ⟨G, hG⟩ := exists_rep hodd h3' β
    set σ := (gammaOf hodd h3' β).right
    have hσm : σ ^ m = 1 := by
      have h1 : (gammaOf hodd h3' β ^ m).right = (gammaOf hodd h3' β).right ^ m :=
        map_pow (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)) (gammaOf hodd h3' β) m
      rw [← map_pow, hβ, map_one] at h1
      exact h1.symm
    have hsm : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one hσm
    have hs_odd : Odd (orderOf σ) := Odd.of_dvd_nat hm hsm
    have hs_gt : 1 < orderOf σ := by
      have hs0 : 0 < orderOf σ := orderOf_pos σ
      have hs1 : orderOf σ ≠ 1 := fun h => hσne (orderOf_eq_one_iff.1 h)
      omega
    obtain ⟨hsf, hcard⟩ := slAutComm_card_fixedField hp hF σ
    have hGk : SpecialLinearGroup.toGL k =
        G * GeneralLinearGroup.map (σ : F →+* F) (SpecialLinearGroup.toGL k) * G⁻¹ := by
      have := hG k
      rwa [hfix] at this
    have htr := slAutComm_trace_mem_fixedField σ G k hGk
    obtain ⟨c, hc⟩ := exists_sl_companion_order (fixedField σ) k (slAutComm_nonscalar hr hr2 k hk) htr
    exact hgood _ hs_odd hs_gt hsf
      (slAutComm_dvd_pow_sub_one hp hr hrp (K := ↥(fixedField σ)) hcard c (hc.trans hk))
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3' β hσ
  refine ⟨G, hG, ?_⟩
  have h1 := congrArg SpecialLinearGroup.toGL hfix
  rw [hG, slConjugation_toGL] at h1
  have h2 : G * SpecialLinearGroup.toGL k = SpecialLinearGroup.toGL k * G := by
    calc G * SpecialLinearGroup.toGL k = (G * SpecialLinearGroup.toGL k * G⁻¹) * G := by group
      _ = SpecialLinearGroup.toGL k * G := by rw [h1]
  have h3 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h2
  simpa using h3

end Main

end CFSG.GH74.GLS.LU.Local
