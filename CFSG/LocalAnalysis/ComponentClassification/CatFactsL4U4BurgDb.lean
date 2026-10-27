module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4BurgDa
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.BurgD

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.Burgoyne.PSL
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem trace_diag_ite {n : ℕ} (J : Finset (Fin n)) (u v : K) :
    (diagonal fun i => if i ∈ J then u else v).trace = (J.card : K) * u + (Jᶜ.card : K) * v := by
  rw [trace_diagonal, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.filter_not, Finset.filter_mem_eq_inter,
    Finset.univ_inter, ← Finset.compl_eq_univ_sdiff, nsmul_eq_mul, nsmul_eq_mul]

theorem spectral (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)} (hJ : Odd J.card) {u v u' v' c : K}
    (huv : u ≠ v) (huv' : u' ≠ v') (B : GL (Fin 4) K)
    (h : (B : Matrix (Fin 4) (Fin 4) K) * (diagonal fun i => if i ∈ J then u else v) *
      ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        c • diagonal fun i => if i ∈ J then u' else v') :
    c * u' = u ∧ c * v' = v := by
  set D : Matrix (Fin 4) (Fin 4) K := diagonal fun i => if i ∈ J then u else v with hD
  set D' : Matrix (Fin 4) (Fin 4) K := diagonal fun i => if i ∈ J then u' else v' with hD'
  set Bm : Matrix (Fin 4) (Fin 4) K := (B : Matrix (Fin 4) (Fin 4) K) with hBm
  set Bi : Matrix (Fin 4) (Fin 4) K := ((B⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hBi
  have hBBi : Bm * Bi = 1 := by rw [hBm, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBiB : Bi * Bm = 1 := by rw [hBm, hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hle : J.card ≤ 4 := by simpa using J.card_le_univ
  have hJne : J.Nonempty := Finset.card_pos.1 (by obtain ⟨m, hm⟩ := hJ; omega)
  obtain ⟨i₁, hi₁⟩ := hJne
  have hJc : Jᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    obtain ⟨m, hm⟩ := hJ
    omega
  obtain ⟨i₂, hi₂⟩ := hJc
  rw [Finset.mem_compl] at hi₂
  have hz : (D - u • 1) * (D - v • 1) = 0 := by
    rw [hD, smul_one_eq_diagonal, smul_one_eq_diagonal, diagonal_sub, diagonal_sub,
      diagonal_mul_diagonal, ← diagonal_zero]
    congr 1
    funext i
    split_ifs <;> ring
  have hconj : ∀ w : K, Bm * (D - w • 1) * Bi = c • D' - w • 1 := by
    intro w
    rw [Matrix.mul_sub, Matrix.sub_mul, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hBBi]
  have hz' : (c • D' - u • 1) * (c • D' - v • 1) = 0 := by
    rw [← hconj u, ← hconj v]
    calc Bm * (D - u • 1) * Bi * (Bm * (D - v • 1) * Bi)
        = Bm * (D - u • 1) * (Bi * Bm) * (D - v • 1) * Bi := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hBiB, Matrix.mul_one, Matrix.mul_assoc Bm, hz, Matrix.mul_zero,
          Matrix.zero_mul]
  have hdiag : ∀ w : K, c • D' - w • (1 : Matrix (Fin 4) (Fin 4) K) =
      diagonal fun i => c * (if i ∈ J then u' else v') - w := by
    intro w
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, hD', diagonal_apply,
      diagonal_apply, one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hent : ∀ i, (c * (if i ∈ J then u' else v') - u) *
      (c * (if i ∈ J then u' else v') - v) = 0 := by
    intro i
    have := congrFun (congrFun hz' i) i
    rw [hdiag, hdiag, diagonal_mul_diagonal, diagonal_apply_eq] at this
    simpa using this
  have h₁ := hent i₁
  have h₂ := hent i₂
  simp only [hi₁, hi₂, ite_true, ite_false] at h₁ h₂
  have htr : c * ((J.card : K) * u' + (Jᶜ.card : K) * v') =
      (J.card : K) * u + (Jᶜ.card : K) * v := by
    have := congrArg Matrix.trace h
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBiB, Matrix.one_mul, Matrix.trace_smul,
      smul_eq_mul, trace_diag_ite, trace_diag_ite] at this
    exact this.symm
  have hcard : Jᶜ.card = 4 - J.card := by rw [Finset.card_compl, Fintype.card_fin]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h
    have h0 : D = 0 := by
      calc D = Bi * (Bm * D * Bi) * Bm := by
            simp only [← Matrix.mul_assoc, hBiB, Matrix.one_mul]
            rw [Matrix.mul_assoc, hBiB, Matrix.mul_one]
        _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
    have e1 := congrFun (congrFun h0 i₁) i₁
    have e2 := congrFun (congrFun h0 i₂) i₂
    rw [hD, diagonal_apply_eq] at e1 e2
    simp only [hi₁, hi₂, ite_true, ite_false, Matrix.zero_apply] at e1 e2
    exact huv (e1.trans e2.symm)
  rcases mul_eq_zero.1 h₁ with h₁ | h₁ <;> rcases mul_eq_zero.1 h₂ with h₂ | h₂
  ·
    exact absurd (mul_left_cancel₀ hc0 (by linear_combination h₁ - h₂)) huv'
  · exact ⟨by linear_combination h₁, by linear_combination h₂⟩
  ·
    exfalso
    obtain ⟨m, hm⟩ := hJ
    have hu : c * u' = v := by linear_combination h₁
    have hv : c * v' = u := by linear_combination h₂
    have htr' : (J.card : K) * v + (Jᶜ.card : K) * u = (J.card : K) * u + (Jᶜ.card : K) * v := by
      rw [← htr, mul_add, ← mul_assoc, ← mul_assoc, mul_comm c, mul_comm c, mul_assoc,
        mul_assoc, hu, hv]
    rw [hcard] at htr'
    rcases (show J.card = 1 ∨ J.card = 3 by omega) with hk | hk
    · rw [hk] at htr'
      norm_num at htr'
      apply huv
      have : (2 : K) * (u - v) = 0 := by linear_combination htr'
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 h2
      · exact sub_eq_zero.1 h0
    · rw [hk] at htr'
      norm_num at htr'
      apply huv
      have : (2 : K) * (u - v) = 0 := by linear_combination -htr'
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 h2
      · exact sub_eq_zero.1 h0
  · exact absurd (mul_left_cancel₀ hc0 (by linear_combination h₁ - h₂)) huv'

theorem exists_proj (h2 : (2 : K) ≠ 0) {J : Finset (Fin 4)} (hJ : Odd J.card)
    {B : Matrix (Fin 4) (Fin 4) K} (hB : B * signMat K J = signMat K J * B) {l : K}
    (hl : B * B = l • 1) (hdet : IsUnit B.det) (hns : ∀ c : K, B ≠ c • 1) :
    ∃ (P : Matrix (Fin 4) (Fin 4) K) (ε : K), P * P = P ∧ P ≠ 0 ∧ ε * ε = 1 ∧
      signMat K J * P = ε • P ∧ P * signMat K J = ε • P ∧
      ∀ M : Matrix (Fin 4) (Fin 4) K, M * B = B * M → M * P = P * M := by
  obtain ⟨k, hk⟩ := exists_singleton_block hJ
  set ν := B k k with hν
  have hlν : l = ν * ν := by
    have h := mul_self_apply_singleton h2 hk hB
    rw [hl, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h
    exact h
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [hlν, h0, mul_zero, zero_smul] at hl
    have := congrArg Matrix.det hl
    rw [det_mul, Matrix.det_zero] at this
    exact (hdet.mul hdet).ne_zero this
  have h2ν : (2 : K) * ν ≠ 0 := mul_ne_zero h2 hν0
  set P : Matrix (Fin 4) (Fin 4) K := ((2 : K) * ν)⁻¹ • (ν • 1 - B) with hP
  have hrow : ∀ j, (ν • (1 : Matrix (Fin 4) (Fin 4) K) - B) k j = 0 := by
    intro j
    rw [Matrix.sub_apply, Matrix.smul_apply, one_apply, smul_eq_mul]
    by_cases hj : k = j
    · subst hj
      simp [hν]
    · simp only [hj, ite_false, mul_zero, zero_sub, neg_eq_zero]
      exact (apply_eq_zero_of_commute h2 hk hB (Ne.symm hj)).2
  have hcol : ∀ i, (ν • (1 : Matrix (Fin 4) (Fin 4) K) - B) i k = 0 := by
    intro i
    rw [Matrix.sub_apply, Matrix.smul_apply, one_apply, smul_eq_mul]
    by_cases hi : i = k
    · subst hi
      simp [hν]
    · simp only [hi, ite_false, mul_zero, zero_sub, neg_eq_zero]
      exact (apply_eq_zero_of_commute h2 hk hB hi).1
  set ε : K := if k ∈ J then 1 else -1 with hε
  have hSi : ∀ i, i ≠ k → signMat K J i i = ε := by
    intro i hi
    rw [signMat, diagonal_apply_eq, hε]
    by_cases hkJ : k ∈ J
    · have : i ∉ J := fun h => ((hk i hi).1 h) hkJ
      simp [hkJ, this]
    · have : i ∈ J := (hk i hi).2 hkJ
      simp [hkJ, this]
  refine ⟨P, ε, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hsq : (ν • (1 : Matrix (Fin 4) (Fin 4) K) - B) * (ν • 1 - B) =
        ((2 : K) * ν) • (ν • 1 - B) := by
      have e1 : (ν • (1 : Matrix (Fin 4) (Fin 4) K)) * (ν • 1) = (ν * ν) • 1 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
      have e2 : (ν • (1 : Matrix (Fin 4) (Fin 4) K)) * B = ν • B := by
        rw [Matrix.smul_mul, Matrix.one_mul]
      have e3 : B * (ν • (1 : Matrix (Fin 4) (Fin 4) K)) = ν • B := by
        rw [Matrix.mul_smul, Matrix.mul_one]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, e1, e2, e3, hl, hlν, two_mul,
        add_smul, smul_sub, smul_smul]
      abel
    rw [hP, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul,
      mul_assoc, inv_mul_cancel₀ h2ν, mul_one]
  ·
    intro h0
    rw [hP] at h0
    have h1 : ν • (1 : Matrix (Fin 4) (Fin 4) K) - B = 0 := by
      have := congrArg (fun M => ((2 : K) * ν) • M) h0
      simp only [smul_smul, mul_inv_cancel₀ h2ν, one_smul, smul_zero] at this
      exact this
    exact hns ν (sub_eq_zero.1 h1).symm
  · rw [hε]
    split_ifs <;> norm_num
  ·
    ext i j
    have hd : (signMat K J * P) i j = (if i ∈ J then (-1 : K) else 1) * P i j := by
      rw [signMat, diagonal_mul]
    rw [hd, Matrix.smul_apply, smul_eq_mul]
    by_cases hi : i = k
    · subst hi
      rw [hP, Matrix.smul_apply, hrow, smul_zero, mul_zero, mul_zero]
    · have := hSi i hi
      rw [signMat, diagonal_apply_eq] at this
      rw [this]
  ·
    ext i j
    have hd : (P * signMat K J) i j = P i j * (if j ∈ J then (-1 : K) else 1) := by
      rw [signMat, mul_diagonal]
    rw [hd, Matrix.smul_apply, smul_eq_mul]
    by_cases hj : j = k
    · subst hj
      rw [hP, Matrix.smul_apply, hcol, smul_zero, zero_mul, mul_zero]
    · have := hSi j hj
      rw [signMat, diagonal_apply_eq] at this
      rw [this, mul_comm]
  · intro M hM
    rw [hP, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, hM]

@[expose] def projHom {G : Type*} [Monoid G] (ι : G →* Matrix (Fin 4) (Fin 4) K)
    {P : Matrix (Fin 4) (Fin 4) K} (hP : P * P = P) (hι : ∀ g, ι g * P = P * ι g) :
    G →* Matrix (Fin 4) (Fin 4) K where
  toFun g := ι g * P + (1 - P)
  map_one' := by rw [map_one, Matrix.one_mul, add_sub_cancel]
  map_mul' g h := by
    have e1 : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]
    have e2 : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hP, sub_self]
    have e3 : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.one_mul, e1, sub_zero]
    change ι (g * h) * P + (1 - P) = (ι g * P + (1 - P)) * (ι h * P + (1 - P))
    have t1 : ι g * P * (ι h * P) = ι g * ι h * P := by
      rw [← Matrix.mul_assoc (ι g * P) (ι h) P, Matrix.mul_assoc (ι g) P (ι h), ← hι h,
        ← Matrix.mul_assoc (ι g) (ι h) P, Matrix.mul_assoc (ι g * ι h) P P, hP]
    have t2 : ι g * P * (1 - P) = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
    have t3 : (1 - P) * (ι h * P) = 0 := by
      rw [hι h, ← Matrix.mul_assoc, e2, Matrix.zero_mul]
    rw [map_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, e3, add_zero,
      zero_add]

theorem projHom_apply {G : Type*} [Monoid G] (ι : G →* Matrix (Fin 4) (Fin 4) K)
    {P : Matrix (Fin 4) (Fin 4) K} (hP : P * P = P) (hι : ∀ g, ι g * P = P * ι g) (g : G) :
    projHom ι hP hι g = ι g * P + (1 - P) := rfl

theorem eq_neg_one_of_orderOf {R : Type*} [Group R] [Finite R] {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (e : R ⧸ pPrimeCore 2 R ≃* SL(2, F)) {w : R} (hw : orderOf w = 2) :
    e (QuotientGroup.mk w) = -1 := by
  have hw2 : w * w = 1 := by rw [← pow_two, ← hw, pow_orderOf_eq_one]
  rcases Burgoyne.C.eq_one_or_eq_neg_one h2 (e (QuotientGroup.mk w))
    (by rw [← map_mul, ← QuotientGroup.mk_mul, hw2, QuotientGroup.mk_one, map_one]) with h | h
  · exfalso
    apply Burgoyne.C.not_mem_pPrimeCore_of_orderOf hw
    have : (QuotientGroup.mk w : R ⧸ pPrimeCore 2 R) = 1 := e.injective (by rw [h, map_one])
    exact (QuotientGroup.eq_one_iff w).1 this
  · exact h

theorem mul_inv_mem_of_rep {L : Type*} [Group L] [Finite L] {Q : Subgroup L} {F : Type*}
    [Field F] (h2 : (2 : F) ≠ 0) (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F)) {γ : L → L}
    (hγ : ∀ a ∈ Q, γ a ∈ Q) {M : Type*} [Monoid M] (π : Q →* M)
    (hπ : ∀ a (ha : a ∈ Q), π ⟨γ a, hγ a ha⟩ = π ⟨a, ha⟩) {c : L} (hcQ : c ∈ Q)
    (hc : orderOf c = 2) (hπc : π ⟨c, hcQ⟩ ≠ 1) :
    ∀ a ∈ Q, γ a * a⁻¹ ∈ (pPrimeCore 2 Q).map Q.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 Q with hO
  have hOn : O.Normal := pPrimeCore_normal
  set N := π.ker ⊔ O with hN
  set c' : Q := ⟨c, hcQ⟩ with hc'def
  have hc' : orderOf c' = 2 := by rw [hc'def, Subgroup.orderOf_mk]; exact hc
  have hcN : c' ∉ N := by
    intro hmem
    obtain ⟨k, hk, o, ho, hko⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
    have hπk : π k = 1 := hk
    have hodd : Odd (orderOf o) := by
      have hdvd : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := _root_.orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at hdvd
      exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card)
    have h1 : π c' = π o := by rw [← hko, map_mul, hπk, one_mul]
    have hsq : π c' * π c' = 1 := by
      rw [← map_mul, ← pow_two, ← hc', pow_orderOf_eq_one, map_one]
    obtain ⟨r, hr⟩ := hodd
    apply hπc
    calc π c' = (π c' * π c') ^ r * π c' := by rw [hsq, one_pow, one_mul]
      _ = π c' ^ orderOf o := by rw [hr, pow_succ, pow_mul, pow_two]
      _ = 1 := by rw [h1, ← map_pow, pow_orderOf_eq_one, map_one]
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hdvd
    have hz' : orderOf (z : Q) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
    have hq : (QuotientGroup.mk (z : Q) : Q ⧸ O) = QuotientGroup.mk c' :=
      e.injective (by rw [eq_neg_one_of_orderOf h2 e hz', eq_neg_one_of_orderOf h2 e hc'])
    have hmem : (z : Q)⁻¹ * c' ∈ O := QuotientGroup.eq.1 hq
    apply hcN
    have : c' = (z : Q) * ((z : Q)⁻¹ * c') := by group
    rw [this]
    exact mul_mem z.2 (mem_sup_right hmem)
  have hNO : N ≤ O := le_sSup ⟨Subgroup.sup_normal _ _, hNodd⟩
  intro a ha
  have hker : (⟨γ a, hγ a ha⟩ : Q) * (⟨a, ha⟩ : Q)⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, hπ a ha, ← map_mul, mul_inv_cancel, map_one]
  exact ⟨_, hNO (mem_sup_left hker), rfl⟩

end CFSG.ComponentClassification.CatFactsL4U4.BurgD
