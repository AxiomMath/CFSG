module

public import CFSG.CGT.Timmesfeld75.JLemmaRoot
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.CGT.Timmesfeld75.ListWCL2
public import CFSG.CGT.Timmesfeld75.ListWCLin
public import CFSG.CGT.Timmesfeld75.ListWCAlt
public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld.ClassicalOrders

theorem ppd_dvd_sq_add_one {r s : ℕ} (hs : 0 < s) (h : IsPrimitivePrimeDivisor r (4 * s)) :
    r ∣ 2 ^ (2 * s) + 1 :=
  (h.dvd_add_one_iff (by omega) (2 * s)).2
    ⟨by rw [← mul_assoc, show 2 * 2 = 4 by norm_num], fun hd => by
      have := Nat.le_of_dvd (by omega) hd
      omega⟩

theorem ppd_dvd_card_sz {r a : ℕ}
    (h : IsPrimitivePrimeDivisor r (4 * (2 * a + 1))) : r ∣ Nat.card (Sz a) := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
  have := ppd_dvd_sq_add_one (by omega : 0 < 2 * a + 1) h
  rwa [mul_comm 2 (2 * a + 1), pow_mul] at this

section Families

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem false_of_psl {n m a : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ m)
    (e : K ≃* StatedProj (StatedSL n F)) (hTq : 2 * a + 1 = m * (n - 1)) {X : Subgroup K}
    (hX : Nat.card X = Nat.card (Sz a)) : False := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * (2 * a + 1)) (by omega)
    (by omega)
  have hrX : r ∣ Nat.card X := hX ▸ ppd_dvd_card_sz hr
  have hrK : r ∣ Nat.card K := hrX.trans (Subgroup.card_subgroup_dvd_card X)
  have hPSLdvd : Nat.card (StatedProj (StatedSL n F)) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin n) F) := by
    rw [← Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj n F).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  have hrSL : r ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) F) := by
    rw [Nat.card_congr e.toEquiv] at hrK
    exact hrK.trans hPSLdvd
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega)] at hrSL
  rcases (Nat.Prime.dvd_mul hr.prime).1 hrSL with h1 | h1
  · have h2 : r ∣ Nat.card F := hr.prime.dvd_of_dvd_pow h1
    rw [hF] at h2
    have h3 : r ∣ 2 := hr.prime.dvd_of_dvd_pow h2
    exact hr.ne_two (by omega) ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).1 h3)
  · obtain ⟨j, hj, hrj⟩ := (Prime.dvd_finsetProd_iff hr.prime.prime _).1 h1
    rw [hF, ← pow_mul, mul_comm] at hrj
    have hd := (hr.dvd_sub_one_iff (by omega) _).1 hrj
    have hjn := (Finset.mem_Icc.1 hj)
    have hle := Nat.le_of_dvd (by nlinarith [hjn.1]) hd
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [hTq, Nat.add_sub_cancel] at hle
    have hjm : j * m ≤ (n' + 1) * m := Nat.mul_le_mul_right m hjn.2
    have hn1 : 1 ≤ n' := by omega
    nlinarith [Nat.mul_le_mul_left m hn1]

omit [Finite K] in
theorem false_of_psu3 {m a : ℕ} (hm : 2 ≤ m)
    (e : K ≃* CFSG.Open.PSU3 2 m) (hTq : 2 * a + 1 = m) {X : Subgroup K}
    (hX : Nat.card X = Nat.card (Sz a)) : False := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * (2 * a + 1)) (by omega)
    (by omega)
  have hrX : r ∣ Nat.card X := hX ▸ ppd_dvd_card_sz hr
  have hrK : r ∣ Nat.card K := hrX.trans (Subgroup.card_subgroup_dvd_card X)
  rw [Nat.card_congr e.toEquiv] at hrK
  have hmul := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd (p := m)
    (by omega)
  have hrP : r ∣ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 + 1)) :=
    hmul ▸ Dvd.dvd.mul_right hrK _
  rw [hTq] at hr
  have hm0 : 0 < m := by omega
  rcases (Nat.Prime.dvd_mul hr.prime).1 hrP with h1 | h1
  · have h2 : r ∣ 2 := hr.prime.dvd_of_dvd_pow (hr.prime.dvd_of_dvd_pow h1)
    exact hr.ne_two (by omega) ((Nat.prime_dvd_prime_iff_eq hr.prime Nat.prime_two).1 h2)
  rcases (Nat.Prime.dvd_mul hr.prime).1 h1 with h2 | h2
  · rw [← pow_mul, mul_comm] at h2
    have hd := (hr.dvd_sub_one_iff (by omega) _).1 h2
    have := Nat.le_of_dvd (by omega) hd
    omega
  · rw [← pow_mul] at h2
    have hd := ((hr.dvd_add_one_iff (by omega) _).1 h2).1
    have hd' : 4 * m ∣ 6 * m := by
      have : 2 * (m * 3) = 6 * m := by ring
      rwa [this] at hd
    have := Nat.dvd_of_mul_dvd_mul_right hm0 hd'
    omega

theorem eq_top_of_card_sz [IsSimpleGroup K]
    (hnab : ∃ x y : K, x * y ≠ y * x) {T : Subgroup K} (hT : IsWC T) (h4 : 4 ≤ Nat.card T)
    (hconcl : Lemma26Concl K T) {a : ℕ} (hTq : Nat.card T = 2 ^ (2 * a + 1))
    {X : Subgroup K} (hX : Nat.card X = Nat.card (Sz a)) : X = ⊤ := by
  classical
  have hT1 : T ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at h4; omega
  have hc : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · obtain ⟨x, y, hxy⟩ := hnab
      have hx : x ∈ Subgroup.center K := h ▸ Subgroup.mem_top x
      exact absurd (Subgroup.mem_center_iff.1 hx y).symm hxy
  let eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)
  obtain ⟨hmod, -⟩ := hconcl
  rcases hmod with ⟨n, m, hn, hm, hmodel⟩ | ⟨m, hm, hmodel⟩ | ⟨s, hs, hs3, hmodel⟩ | ⟨e⟩
  ·
    have hmodel' := statedClassicalModel_of_mulEquiv eK.symm hmodel
    obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := hmodel'
    have : CharP F 2 := charP_two_of_card hF
    have hcard : Nat.card T = 2 ^ (m * (n - 1)) := by
      rcases Nat.lt_or_ge n 3 with hn3 | hn3
      · have hn2 : n = 2 := by omega
        subst hn2
        have := (psl2_wc (statedClassicalModel_of_mulEquiv eK.symm hmodel) hT hT1).1.1
        simpa using this
      · have := (lin_wc hn3 e hT hT1).1
        rw [this, hF, ← pow_mul]
    have hs' : 2 * a + 1 = m * (n - 1) := Nat.pow_right_injective le_rfl (hTq.symm.trans hcard)
    exact (false_of_psl hn hm hF e hs' hX).elim
  ·
    have hmodel' := statedClassicalModel_of_mulEquiv eK.symm hmodel
    have hcard := (psu3_wc hm hmodel' hT hT1).1.1
    obtain ⟨e⟩ := exists_psu3_of_statedClassicalModel hm hmodel'
    have hs' : 2 * a + 1 = m := Nat.pow_right_injective le_rfl (hTq.symm.trans hcard)
    exact (false_of_psu3 hm e hs' hX).elim
  ·
    have hK : CFSG.Blueprint.LieModel K .twistedB2 0 2 s :=
      lieModel_twistedB2_iff.2 (suzukiModel_of_mulEquiv eK.symm (lieModel_twistedB2_iff.1 hmodel))
    have hcard := (sz_wc hK hT hT1).1.1
    obtain ⟨a', ha', hs', ⟨e⟩⟩ := exists_sz_of_lieModel hK
    have hsa : 2 * a + 1 = s := Nat.pow_right_injective le_rfl (hTq.symm.trans hcard)
    have haa : a' = a := by omega
    subst haa
    apply Subgroup.eq_top_of_card_eq
    rw [hX, Nat.card_congr e.toEquiv]
  ·
    exfalso
    have e' : K ≃* alternatingGroup (Fin 6) := eK.trans e.some
    have h44 := (alt67_wc le_rfl (by norm_num) e' hT h4).1
    rw [hTq] at h44
    have : 2 * a + 1 = 2 :=
      Nat.pow_right_injective le_rfl (h44.trans (by norm_num : (4 : ℕ) = 2 ^ 2))
    omega

end Families

end CFSG.CGT.T75M
