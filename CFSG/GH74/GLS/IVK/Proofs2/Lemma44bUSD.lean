module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bUW

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma44bUSD

open Matrix CFSG.BrauerLinearThree CFSG.Open

variable {F : Type} [Field F]

@[expose] def adj (f : F →+* F) (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  (A.map f)ᵀ

theorem adj_mul (f : F →+* F) (A B : Matrix (Fin 2) (Fin 2) F) :
    adj f (A * B) = adj f B * adj f A := by
  simp [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one (f : F →+* F) : adj f (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  simp [adj]

theorem conj_unitary (f : F →+* F) {B Bi D G : Matrix (Fin 2) (Fin 2) F} (hB : adj f B * B = G)
    (hD : adj f D * G * D = G) (hBi : B * Bi = 1) :
    adj f (B * D * Bi) * (B * D * Bi) = 1 := by
  rw [adj_mul, adj_mul]
  calc adj f Bi * (adj f D * adj f B) * (B * D * Bi)
      = adj f Bi * (adj f D * (adj f B * B) * D) * Bi := by simp only [Matrix.mul_assoc]
    _ = adj f Bi * (adj f D * G * D) * Bi := by rw [hB]
    _ = adj f Bi * G * Bi := by rw [hD]
    _ = adj f Bi * (adj f B * B) * Bi := by rw [hB]
    _ = adj f (B * Bi) * (B * Bi) := by rw [adj_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hBi, adj_one, Matrix.mul_one]

section Arithmetic

variable {p n : ℕ}

theorem sq_sub_one (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

theorem card_units_eq (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F) :
    Nat.card Fˣ = (p ^ n) ^ 2 - 1 := by
  have : Finite F := h.finite
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_units, h.card, ← pow_mul, mul_comm n 2]

theorem exists_neg_one_norm (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F)
    (hq : (p ^ n) % 4 = 1) (hq1 : 1 < p ^ n) :
    ∃ r : Fˣ, h.bar (r : F) * (r : F) = -1 := by
  have : Finite F := h.finite
  obtain ⟨t, ht⟩ : ∃ t, p ^ n = 2 * t + 1 := ⟨p ^ n / 2, by omega⟩
  have ht1 : 1 ≤ t := by omega
  have hsq : (p ^ n) ^ 2 - 1 = 2 * (t * (p ^ n + 1)) := by
    rw [ht]
    apply Nat.sub_eq_of_eq_add
    ring
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hepos : 0 < t * (p ^ n + 1) := Nat.mul_pos ht1 (by omega)
  have hdvd : t * (p ^ n + 1) ∣ orderOf g := ⟨2, by rw [hg, card_units_eq h, hsq]; ring⟩
  have hord : orderOf (g ^ (t * (p ^ n + 1))) = 2 := by
    rw [orderOf_pow_of_dvd hepos.ne' hdvd, hg, card_units_eq h, hsq]
    exact Nat.mul_div_cancel 2 hepos
  have hneg : g ^ (t * (p ^ n + 1)) = -1 := units_eq_neg_one_of_orderOf_eq_two hord
  refine ⟨g ^ t, ?_⟩
  have e1 : ((g ^ t : Fˣ) : F) ^ (p ^ n) * ((g ^ t : Fˣ) : F) =
      (((g ^ t) ^ (p ^ n + 1) : Fˣ) : F) := by
    simp [pow_succ]
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, e1, ← pow_mul, hneg,
    Units.val_neg, Units.val_one]

theorem exists_lam (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F)
    (hq : (p ^ n) % 4 = 1) (hq1 : 1 < p ^ n) {k : ℕ} (hk : (p ^ n - 1).factorization 2 = k) :
    ∃ lam : Fˣ, orderOf lam = 2 ^ (k + 1) := by
  have : Finite F := h.finite
  obtain ⟨-, hdvdk, -⟩ := wreathed_arith hq hq1
  rw [hk] at hdvdk
  apply exists_orderOf_eq_of_dvd_natCard (α := Fˣ)
  rw [card_units_eq h, sq_sub_one _ hq1.le, pow_succ]
  obtain ⟨v, hv⟩ : ∃ v, p ^ n + 1 = 2 * (2 * v + 1) := ⟨(p ^ n - 1) / 4, by omega⟩
  exact mul_dvd_mul hdvdk ⟨2 * v + 1, hv⟩

end Arithmetic

section Main

variable {p n : ℕ}

theorem exists_GU2_semidihedral
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p n F)
    (hq : (p ^ n) % 4 = 1) {k : ℕ} (hk : (p ^ n - 1).factorization 2 = k) :
    2 ≤ k ∧ ∃ M : Subgroup ↥(GU2Stated (p ^ n) F), Nat.card M = 2 ^ (k + 2) ∧
      Nonempty (↥M ≃* SemidihedralGroup (k + 2)) := by
  have hfin : Finite F := h.finite
  have hq1 : 1 < p ^ n := Nat.one_lt_pow (by have := h.one_le; omega) h.prime.one_lt
  obtain ⟨hk2, -, -⟩ := wreathed_arith hq hq1
  rw [hk] at hk2
  refine ⟨hk2, ?_⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn : 1 ≤ n := h.one_le
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have h2F : (2 : F) ≠ 0 := by
    intro h2
    have hcp : CharP F p := h.charP
    have h3 : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h2)
    have h4 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h3
    have h5 := h.prime.two_le
    omega
  obtain ⟨r, hbr⟩ := exists_neg_one_norm h hq hq1
  obtain ⟨lam, hlam⟩ := exists_lam h hq hq1 hk
  set μ : Fˣ := (lam ^ (p ^ n))⁻¹ with hμdef
  have hμF : (μ : F) = (h.bar (lam : F))⁻¹ := by
    rw [hμdef, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
  have hbl : h.bar (lam : F) * (μ : F) = 1 := by
    rw [hμF]
    exact mul_inv_cancel₀ ((map_ne_zero h.bar).mpr lam.ne_zero)
  have hbm : h.bar (μ : F) * (lam : F) = 1 := by
    rw [hμF, map_inv₀, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar]
    exact inv_mul_cancel₀ lam.ne_zero
  let Bm : Matrix (Fin 2) (Fin 2) F := !![1, 1; (r : F), -(r : F)]
  have hdetB : Bm.det ≠ 0 := by
    have hd : Bm.det = -(2 * (r : F)) := by
      rw [Matrix.det_fin_two]
      simp [Bm]
      ring
    rw [hd]
    exact neg_ne_zero.mpr (mul_ne_zero h2F r.ne_zero)
  let B : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Bm hdetB
  have hBval : (B : Matrix (Fin 2) (Fin 2) F) = Bm := rfl
  let Gm : Matrix (Fin 2) (Fin 2) F := !![0, 2; 2, 0]
  have hBG : adj h.bar Bm * Bm = Gm := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj, Bm, Gm, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hbr | linear_combination (-1 : F) * hbr
  let D' : GL (Fin 2) F := CFSG.DesarguesianPlanes.diagGL lam μ
  have hDval : (D' : Matrix (Fin 2) (Fin 2) F) = !![(lam : F), 0; 0, (μ : F)] := rfl
  have hDG : adj h.bar (D' : Matrix (Fin 2) (Fin 2) F) * Gm * (D' : Matrix (Fin 2) (Fin 2) F) =
      Gm := by
    rw [hDval]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj, Gm, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination 2 * hbl | linear_combination 2 * hbm
  let c : GL (Fin 2) F := B * D' * B⁻¹
  have hcu : adj h.bar (c : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := conj_unitary h.bar (B := (B : Matrix (Fin 2) (Fin 2) F))
      (Bi := ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      (D := (D' : Matrix (Fin 2) (Fin 2) F)) (G := Gm) (by rw [hBval]; exact hBG) hDG
      (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    have e : (c : Matrix (Fin 2) (Fin 2) F) = (B : Matrix (Fin 2) (Fin 2) F) *
        (D' : Matrix (Fin 2) (Fin 2) F) * ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [Units.val_mul, Units.val_mul]
    rw [e]
    exact this
  have hc : c ∈ GU2Stated (p ^ n) F := (Lemma41aU3.mem_GU2Stated_iff h).mpr hcu
  let s : GL (Fin 2) F := CFSG.DesarguesianPlanes.diagGL 1 (-1)
  have hs : s ∈ GU2Stated (p ^ n) F := Lemma44bUW.unitary_diag_mem h (by simp) (by simp)
  have hsB : s * B = B * CFSG.DesarguesianPlanes.swapGL := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hBval]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [s, CFSG.DesarguesianPlanes.diagGL, CFSG.DesarguesianPlanes.swapGL, Matrix.GeneralLinearGroup.mkOfDetNeZero, Bm, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hs' : s = B * CFSG.DesarguesianPlanes.swapGL * B⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hsB
  obtain ⟨u, hu, hqu⟩ := exists_odd_eq_two_pow_factorization_mul (n := p ^ n - 1) (by omega)
  rw [hk] at hqu
  obtain ⟨w, hw⟩ := hu
  obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ k = Y + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hYodd : ∃ z, Y = 2 * z + 1 := by
    have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    exact ⟨Y / 2, by omega⟩
  obtain ⟨z, hz⟩ := hYodd
  have hqn : p ^ n = (Y + 1) * (2 * w + 1) + 1 := by
    rw [← hY, ← hw]
    omega
  have hYk : 2 ^ k - 1 = Y := by omega
  have h1 : lam ^ (Y + p ^ n) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hlam, pow_succ, hY]
    refine ⟨w + 1, ?_⟩
    rw [hqn]
    ring
  have h2 : lam ^ (p ^ n * Y + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hlam, pow_succ, hY]
    refine ⟨2 * z * w + z + w + 1, ?_⟩
    rw [hqn, hz]
    ring
  have hlN : lam ^ Y = μ := by
    have h3 : lam ^ Y * lam ^ (p ^ n) = 1 := by rw [← pow_add]; exact h1
    exact eq_inv_of_mul_eq_one_left h3
  have hμN : μ ^ Y = lam := by
    have h3 : lam ^ (p ^ n * Y) * lam = 1 := by rw [← pow_succ]; exact h2
    rw [hμdef, inv_pow, ← pow_mul]
    exact inv_eq_of_mul_eq_one_right h3
  have hDN : D' ^ Y = CFSG.DesarguesianPlanes.diagGL μ lam := by
    show (CFSG.DesarguesianPlanes.diagGL lam μ : GL (Fin 2) F) ^ Y = CFSG.DesarguesianPlanes.diagGL μ lam
    rw [CFSG.DesarguesianPlanes.diagGL_pow, hlN, hμN]
  have hswapD : CFSG.DesarguesianPlanes.swapGL * D' * CFSG.DesarguesianPlanes.swapGL⁻¹ = (CFSG.DesarguesianPlanes.diagGL μ lam : GL (Fin 2) F) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact CFSG.DesarguesianPlanes.swapGL_mul_diagGL lam μ
  have hconj : s * c * s⁻¹ = c ^ Y := by
    have e1 : s * c * s⁻¹ = B * (CFSG.DesarguesianPlanes.swapGL * D' * CFSG.DesarguesianPlanes.swapGL⁻¹) * B⁻¹ := by
      show s * (B * D' * B⁻¹) * s⁻¹ = _
      rw [hs']
      group
    have e2 : c ^ Y = B * D' ^ Y * B⁻¹ := conj_pow
    rw [e1, e2, hswapD, hDN]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDord : orderOf D' = 2 ^ (k + 1) := by
    apply orderOf_eq_prime_pow (p := 2) (n := k)
    · intro hx
      have hx' : (CFSG.DesarguesianPlanes.diagGL (lam ^ 2 ^ k) (μ ^ 2 ^ k) : GL (Fin 2) F) = 1 := by
        have hx2 : (CFSG.DesarguesianPlanes.diagGL lam μ : GL (Fin 2) F) ^ 2 ^ k = 1 := hx
        rwa [CFSG.DesarguesianPlanes.diagGL_pow] at hx2
      have h0 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hx'
      simp [CFSG.DesarguesianPlanes.diagGL, Matrix.GeneralLinearGroup.mkOfDetNeZero] at h0
      have h3 : lam ^ 2 ^ k = 1 := Units.ext (by simpa using h0)
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rw [hlam] at h4
      have h5 := Nat.le_of_dvd (by positivity) h4
      have h6 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    · show (CFSG.DesarguesianPlanes.diagGL lam μ : GL (Fin 2) F) ^ 2 ^ (k + 1) = 1
      rw [CFSG.DesarguesianPlanes.diagGL_pow]
      have e1 : lam ^ 2 ^ (k + 1) = 1 := by rw [← hlam]; exact pow_orderOf_eq_one lam
      have e2 : μ ^ 2 ^ (k + 1) = 1 := by
        rw [hμdef, inv_pow, ← pow_mul, mul_comm, pow_mul, e1, one_pow, inv_one]
      rw [e1, e2, CFSG.DesarguesianPlanes.diagGL_one_one]
  have hcord : orderOf c = 2 ^ (k + 1) := by
    have := MulEquiv.orderOf_eq (MulAut.conj B) D'
    rw [MulAut.conj_apply] at this
    exact this.trans hDord
  let cP : ↥(GU2Stated (p ^ n) F) := ⟨c, hc⟩
  let sP : ↥(GU2Stated (p ^ n) F) := ⟨s, hs⟩
  have hhP : orderOf cP = 2 ^ (k + 1) := (Subgroup.orderOf_coe cP).symm.trans hcord
  have htP : sP ^ 2 = 1 := by
    apply Subtype.ext
    show (CFSG.DesarguesianPlanes.diagGL 1 (-1) : GL (Fin 2) F) ^ 2 = 1
    rw [CFSG.DesarguesianPlanes.diagGL_pow, one_pow, neg_one_sq, CFSG.DesarguesianPlanes.diagGL_one_one]
  have hconjP : sP * cP * sP⁻¹ = cP ^ (2 ^ k - 1) := by
    rw [hYk]
    exact Subtype.ext hconj
  obtain ⟨hcard, e, -, -⟩ := semidihedral_sup_zpowers (m := k) hk2 hhP htP hconjP
  exact ⟨Subgroup.zpowers cP ⊔ Subgroup.zpowers sP, hcard, ⟨e.symm⟩⟩

end Main

end Lemma44bUSD


end CFSG.GH74.GLS.IVK.Proofs2
