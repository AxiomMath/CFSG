module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eBlock
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)
open CFSG.GroupTheory.WeirSylow (IsPlusType natCard_orthogonalGroup_of_type)

theorem prod_Icc_pow_sub_one_le (q m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) ≤ q ^ (m * (m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (by omega), show (m + 1) * (m + 1 + 1) = m * (m + 1) +
      2 * (m + 1) by ring, pow_add]
    exact Nat.mul_le_mul ih (Nat.sub_le _ _)

theorem exists_prime_dvd_card_psl2 {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ k) :
    ∃ ℓ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ ℓ ∣ p ^ k * ((p ^ k) ^ 2 - 1) := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  by_cases hp3 : p = 3
  · subst hp3
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this
      norm_num at h5
    obtain ⟨ℓ, hℓ⟩ := P51e.exists_isPrimDiv (le_refl 3) (show 3 ≤ 2 * k by omega)
    refine ⟨ℓ, hℓ.1, hℓ.ne_two (by decide) (by omega), fun h => ?_, ?_⟩
    · exact hℓ.not_dvd_base (by norm_num) (by omega) (by subst h; exact dvd_refl 3)
    · refine Dvd.dvd.mul_left ?_ _
      rw [← pow_mul, mul_comm k 2]
      exact hℓ.2.1
  · refine ⟨p, hp, hp2, hp3, Dvd.dvd.mul_right (dvd_pow_self p hk) _⟩


theorem false_of_mul_sq_sub_le {q z c : ℕ} (hc : 1 ≤ c) (hz : 1 ≤ z) (hqz : (c + 1) * z ≤ q)
    (h : q * (q ^ 2 - 1) ≤ c * q ^ 2 * z) : False := by
  have hq : 2 ≤ q := le_trans (by nlinarith) hqz
  obtain ⟨r, hr⟩ : ∃ r, q ^ 2 = r + 1 := ⟨q ^ 2 - 1, by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega⟩
  rw [hr, Nat.add_sub_cancel] at h
  have hsq : q * q = r + 1 := by rw [← hr, sq]
  have h1 : r ≤ c * z * q := by
    have h2 : q * r ≤ q * (c * z * q) := by
      calc q * r ≤ c * (r + 1) * z := h
        _ = q * (c * z * q) := by rw [← hsq]; ring
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  have h3 : (c + 1) * z * q ≤ r + 1 := by
    rw [← hsq]
    exact Nat.mul_le_mul_right q hqz
  nlinarith

theorem false_of_odd_block {q₀ a b Ω : ℕ} (hq₀ : 3 ≤ q₀) (ha : 2 ≤ a)
    (h : 2 * q₀ ^ (a ^ 2) * ∏ i ∈ Finset.Icc 1 a, (q₀ ^ (2 * i) - 1) = 2 ^ b * Ω)
    (hΩ : Ω * 2 = q₀ ^ (a ^ 2) * ((q₀ ^ (a ^ 2)) ^ 2 - 1)) : False := by
  set q := q₀ ^ (a ^ 2) with hq
  have hP : ∏ i ∈ Finset.Icc 1 a, (q₀ ^ (2 * i) - 1) ≤ q * q₀ ^ a := by
    rw [hq, ← pow_add, show a ^ 2 + a = a * (a + 1) by ring]
    exact prod_Icc_pow_sub_one_le q₀ a
  have hΩX : Ω ≤ 2 * q * ∏ i ∈ Finset.Icc 1 a, (q₀ ^ (2 * i) - 1) := by
    rw [h]
    exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b)
  have hz : 1 ≤ q₀ ^ a := Nat.one_le_pow _ _ (by omega)
  refine false_of_mul_sq_sub_le (q := q) (c := 4) (z := q₀ ^ a) (by norm_num) hz ?_ ?_
  ·
    have h9 : 9 ≤ q₀ ^ (a ^ 2 - a) := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ q₀ ^ 2 := Nat.pow_le_pow_left hq₀ 2
        _ ≤ q₀ ^ (a ^ 2 - a) := Nat.pow_le_pow_right (by omega) (by
            have : a * 2 ≤ a ^ 2 := by nlinarith
            omega)
    have hsplit : q = q₀ ^ a * q₀ ^ (a ^ 2 - a) := by
      rw [hq, ← pow_add]
      congr 1
      have : a ≤ a ^ 2 := by nlinarith
      omega
    rw [hsplit]
    nlinarith
  · calc q * (q ^ 2 - 1) = Ω * 2 := hΩ.symm
      _ ≤ 2 * q * (q * q₀ ^ a) * 2 := by
          have := Nat.mul_le_mul_left (2 * q) hP
          nlinarith
      _ = 4 * q ^ 2 * q₀ ^ a := by ring

theorem false_of_even_block {q₀ m b Ω e : ℕ} (hq₀ : 3 ≤ q₀) (hm : 2 ≤ m) (he : e ≤ q₀ ^ (m + 1) + 1)
    (h : 2 * q₀ ^ (m * (m + 1)) * e * ∏ i ∈ Finset.Icc 1 m, (q₀ ^ (2 * i) - 1) = 2 ^ b * Ω)
    (hΩ : Ω * 2 = q₀ ^ (m * (m + 1)) * ((q₀ ^ (m * (m + 1))) ^ 2 - 1)) : False := by
  set q := q₀ ^ (m * (m + 1)) with hq
  have hP : ∏ i ∈ Finset.Icc 1 m, (q₀ ^ (2 * i) - 1) ≤ q := prod_Icc_pow_sub_one_le q₀ m
  have hz : 1 ≤ q₀ ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
  have he2 : e ≤ 2 * q₀ ^ (m + 1) := by omega
  have hΩX : Ω ≤ 2 * q * e * ∏ i ∈ Finset.Icc 1 m, (q₀ ^ (2 * i) - 1) := by
    rw [h]
    exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b)
  refine false_of_mul_sq_sub_le (q := q) (c := 8) (z := q₀ ^ (m + 1)) (by norm_num) hz ?_ ?_
  ·
    have h27 : 9 ≤ q₀ ^ (m * (m + 1) - (m + 1)) := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ q₀ ^ 2 := Nat.pow_le_pow_left hq₀ 2
        _ ≤ q₀ ^ (m * (m + 1) - (m + 1)) := Nat.pow_le_pow_right (by omega) (by
            have : (m + 1) * 2 + 2 ≤ m * (m + 1) + 2 := by nlinarith
            omega)
    have hsplit : q = q₀ ^ (m + 1) * q₀ ^ (m * (m + 1) - (m + 1)) := by
      rw [hq, ← pow_add]
      congr 1
      have : m + 1 ≤ m * (m + 1) := by nlinarith
      omega
    rw [hsplit]
    nlinarith
  · calc q * (q ^ 2 - 1) = Ω * 2 := hΩ.symm
      _ ≤ 2 * q * (2 * q₀ ^ (m + 1)) * q * 2 := by
          have h1 := Nat.mul_le_mul (Nat.mul_le_mul_left (2 * q) he2) hP
          nlinarith
      _ = 8 * q ^ 2 * q₀ ^ (m + 1) := by ring

variable {K : Type} [Field K] [Finite K] {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem block_psl2_orderData (hK : ringChar K ≠ 2) {p f k : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty) (h3 : 3 ≤ I.card)
    (h5 : 5 ≤ p ^ k) (hcard : Nat.card (blockP K hw I) * 2 = p ^ k * ((p ^ k) ^ 2 - 1)) :
    ∃ b, Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I)))) =
        2 ^ b * Nat.card (blockP K hw I) ∧ k = f * ((I.card - 1) ^ 2 / 4) := by
  obtain ⟨hp2, -⟩ := GSThmB.QPUCl.prime_ne_two_and_one_le hK hp hKc
  have := GSThmB.QPUCl.finite_linearEquiv K I.card
  have hR : ((diagGL (wRes_ne_zero hw I) : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K)ᵀ = diagGL (wRes_ne_zero hw I) := by
    rw [coe_diagGL]
    exact diagonal_transpose _
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK _ hR
  have hdim : Module.finrank K (Fin I.card → K) = I.card := Module.finrank_fin_fun K
  have hcardP := GSThmB.QPUCl.card_blockP_eq hK hw hIc
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I)) with hQdef
  have hΩO : Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := Subgroup.card_subgroup_dvd_card _
  obtain ⟨ℓ, hℓ, hℓ2, hℓ3, hℓd⟩ := exists_prime_dvd_card_psl2 hp hp2 h5
  have hℓP : ℓ ∣ Nat.card (blockP K hw I) := by
    rw [← hcard] at hℓd
    rcases (Nat.Prime.dvd_mul hℓ).1 hℓd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h) hℓ2
  obtain ⟨b, hb⟩ : ∃ b, Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
      2 ^ b * Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
    rcases P51e.orth_index_cases hK hQnd (by omega) with h | h
    · exact h
    · rcases h ℓ hℓ (by rw [hcardP] at hℓP; exact hℓP.trans hΩO) with h' | h'
      · exact absurd h' hℓ2
      · exact absurd h' hℓ3
  rw [← hcardP] at hb
  refine ⟨b, hb, ?_⟩
  have hfacO := GSThmB.QPUCl.factorization_card_orthogonalGroup hK hp hKc hQnd (by omega)
  rw [hdim, hb, GSThmB.QPUCl.factorization_two_pow_mul hp2 b _ Nat.card_pos.ne'] at hfacO
  have hfacP : (Nat.card (blockP K hw I) * 2).factorization p = k := by
    rw [hcard, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    · have hcop : Nat.Coprime ((p ^ k) ^ 2 - 1) p :=
        CatLeafProof.coprime_pow_sub_one hp (dvd_pow_self p (by rintro rfl; simp at h5))
          (Nat.one_le_pow _ _ hp.pos) (by norm_num)
      rw [Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hcop.symm),
        add_zero]
    · have : 1 < (p ^ k) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
      omega
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  rw [Nat.factorization_mul Nat.card_pos.ne' two_ne_zero, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp2', add_zero] at hfacP
  rw [← hfacP, hfacO]

include hw in
theorem block_psl2_cases (hK : ringChar K ≠ 2) {p f k : ℕ} (hp : p.Prime)
    (hKc : Nat.card K = p ^ f) {I : Finset (Fin d)} (hIc : Iᶜ.Nonempty) (h3 : 3 ≤ I.card)
    (h5 : 5 ≤ p ^ k) (hcard : Nat.card (blockP K hw I) * 2 = p ^ k * ((p ^ k) ^ 2 - 1)) :
    (I.card = 3 ∧ k = f) ∨ (I.card = 4 ∧ k = 2 * f ∧
      ¬ IsPlusType (CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I)))) := by
  obtain ⟨b, hb, hk⟩ := block_psl2_orderData hw hK hp hKc hIc h3 h5 hcard
  obtain ⟨hp2, hf⟩ := GSThmB.QPUCl.prime_ne_two_and_one_le hK hp hKc
  have hq₀ : 3 ≤ p ^ f := by
    have h3p : 3 ≤ p := by have := hp.two_le; omega
    calc 3 ≤ p ^ 1 := by rw [pow_one]; exact h3p
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have := GSThmB.QPUCl.finite_linearEquiv K I.card
  have hR : ((diagGL (wRes_ne_zero hw I) : GL (Fin I.card) K) :
      Matrix (Fin I.card) (Fin I.card) K)ᵀ = diagGL (wRes_ne_zero hw I) := by
    rw [coe_diagGL]
    exact diagonal_transpose _
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK _ hR
  have hdim : Module.finrank K (Fin I.card → K) = I.card := Module.finrank_fin_fun K
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm (diagGL (wRes_ne_zero hw I)) with hQdef
  have hpk : p ^ k = (p ^ f) ^ ((I.card - 1) ^ 2 / 4) := by rw [hk, pow_mul]
  rw [hpk] at hcard
  obtain ⟨n', hn' | hn'⟩ := Nat.even_or_odd' I.card
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    have he : (I.card - 1) ^ 2 / 4 = m * (m + 1) := by
      rw [hn', show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
        show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]
      omega
    rw [he] at hcard hk
    have hdim' : Module.finrank K (Fin I.card → K) = 2 * (m + 1) := by rw [hdim, hn']
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hm1 : m = 1 := by omega
      subst hm1
      refine Or.inr ⟨by omega, by omega, fun hplus => ?_⟩
      have hO := natCard_orthogonalGroup_of_type hQnd hdim' (Or.inl ⟨rfl, hplus⟩)
      rw [hb, hKc, Finset.Icc_self, Finset.prod_singleton, pow_one] at hO
      simp only [show 1 * (1 + 1) = 2 from rfl, show 1 + 1 = 2 from rfl] at hO hcard
      set Ω := Nat.card (blockP K hw I) with hΩ
      set q₀ := p ^ f with hq₀def
      set Y : ℤ := (q₀ : ℤ) ^ 2 with hY
      have hY9 : 9 ≤ Y := by
        rw [hY]
        have : (3 : ℤ) ≤ (q₀ : ℤ) := by exact_mod_cast hq₀
        nlinarith
      have hc : (Ω : ℤ) * 2 = Y * (Y ^ 2 - 1) := by
        have h1 : 1 ≤ (q₀ ^ 2) ^ 2 := Nat.one_le_pow _ _ (by positivity)
        have h2 := congrArg (fun x : ℕ => (x : ℤ)) hcard
        simp only [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] at h2
        rw [hY]
        linear_combination h2
      have hE : (2 : ℤ) ^ b * (Ω : ℤ) = 2 * Y * (Y - 1) * (Y - 1) := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hO
        rw [hY]
        linear_combination hO
      have key : (Y * (Y - 1)) * ((2 : ℤ) ^ b * (Y + 1)) = (Y * (Y - 1)) * (4 * (Y - 1)) := by
        linear_combination 2 * hE - (2 : ℤ) ^ b * hc
      have key' := mul_left_cancel₀ (by nlinarith : Y * (Y - 1) ≠ 0) key
      rcases b with _ | _ | b
      · norm_num at key'
        omega
      · norm_num at key'
        omega
      · have h4 : (4 : ℤ) ≤ 2 ^ (b + 2) := by
          rw [pow_add]
          have : (1 : ℤ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
          nlinarith
        nlinarith
    · exfalso
      rcases P51e.natCard_orth_even hQnd hdim' with hO | hO <;> rw [hO, hKc] at hb
      · exact false_of_even_block hq₀ hm (by omega) hb hcard
      · exact false_of_even_block hq₀ hm le_rfl hb hcard
  ·
    have he : (I.card - 1) ^ 2 / 4 = n' ^ 2 := by
      rw [hn', show 2 * n' + 1 - 1 = 2 * n' by omega, show (2 * n') ^ 2 = 4 * n' ^ 2 by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [he] at hcard hk
    rcases Nat.lt_or_ge n' 2 with hn2 | hn2
    · have hn1 : n' = 1 := by omega
      subst hn1
      exact Or.inl ⟨by omega, by rw [hk, one_pow, mul_one]⟩
    · exfalso
      have hdim' : Module.finrank K (Fin I.card → K) = 2 * n' + 1 := by rw [hdim, hn']
      have hO := P51e.natCard_orth_odd hK hQnd hdim'
      rw [hO, hKc] at hb
      exact false_of_odd_block hq₀ hn2 hb hcard

end CFSG.ComponentClassification.HarrisLit.T1.P58b.OLie
