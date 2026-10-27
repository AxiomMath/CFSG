module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusOrder
public import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.CatDistinct

theorem catalogIs_isL2n_card_of_odd {S : Type} [Group S] [Finite S] {r : ℕ} (hr : Odd r)
    (h : catalogIs S (S10.isL2n r)) : Nat.card S = 2 ^ r * ((2 ^ r) ^ 2 - 1) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isL2n] at hi
  | alternating m hm =>
      simp only [S10.isL2n] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact absurd hr (by norm_num : ¬ Odd 2)
  | sporadic s => simp [S10.isL2n] at hi
  | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A n q =>
          rcases n with _ | _ | n <;> simp [S10.isL2n] at hi
          obtain ⟨hp, hn⟩ := hi
          haveI : Fact q.p.Prime := ⟨hp ▸ Nat.prime_two⟩
          have hcardS : Nat.card S =
              Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (1 + 1))
                (GaloisField q.p q.exponent)) :=
            Nat.card_congr
              (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)).toEquiv
          have hfieldcard : Nat.card (GaloisField q.p q.exponent) = 2 ^ r := by
            rw [GaloisField.card (p := q.p) (n := q.exponent) q.exponent_pos.ne', hp, hn]
          rw [hcardS, CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear_eq_orderA
            (GaloisField q.p q.exponent) 1, hfieldcard]
          exact CatDistinct.orderA_one_eq (k := r) hr.pos
      | _ => simp [S10.isL2n] at hi

section SL

variable {E : Type} [Field E] [Finite E] {m e : ℕ}

theorem card_centerQuot_mul_gcd_SL (hm : 2 ≤ m)
    (hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤) {T : Type*} [Group T]
    (g : Matrix.SpecialLinearGroup (Fin m) E →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) :
    Nat.card (T ⧸ Subgroup.center T) * m.gcd (Nat.card E - 1) =
      Nat.card E ^ (m * (m - 1) / 2) * ∏ i ∈ Finset.Icc 2 m, (Nat.card E ^ i - 1) := by
  have h1 := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := E) (n := m) (by omega),
    CFSG.OrderReductions.LinearOrders.card_specialLinear_center E m (by omega)] at h1
  exact h1.symm

private theorem exists_odd_card_centerQuot_SL (hm : 2 ≤ m) (he : 1 ≤ e) (hE : Nat.card E = 2 ^ e)
    (hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤) {T : Type*} [Group T]
    [Finite T] (g : Matrix.SpecialLinearGroup (Fin m) E →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) :
    ∃ O : ℕ, Odd O ∧
      Nat.card (T ⧸ Subgroup.center T) = 2 ^ (e * (m * (m - 1) / 2)) * O := by
  have hform := card_centerQuot_mul_gcd_SL hm hperf g hg hker
  have hodd1 : Odd (Nat.card E - 1) := by
    rw [hE]
    exact CatDistinct.odd_two_pow_sub_one he
  have hgodd : Odd (m.gcd (Nat.card E - 1)) := Odd.of_dvd_nat hodd1 (Nat.gcd_dvd_right _ _)
  have hPodd : Odd (∏ i ∈ Finset.Icc 2 m, (Nat.card E ^ i - 1)) := by
    refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun i hi => ?_)
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    rw [hE, ← pow_mul]
    exact CatDistinct.odd_two_pow_sub_one (by nlinarith)
  haveI : Finite (T ⧸ Subgroup.center T) := inferInstance
  obtain ⟨u, O, hO, hcard⟩ := Nat.exists_eq_two_pow_mul_odd
    (Nat.card_pos (α := T ⧸ Subgroup.center T)).ne'
  rw [hcard, show Nat.card E ^ (m * (m - 1) / 2) = 2 ^ (e * (m * (m - 1) / 2)) by
    rw [hE, ← pow_mul], mul_assoc] at hform
  obtain ⟨hu, -⟩ := CatDistinct.two_pow_mul_odd_inj (hO.mul hgodd)
    hPodd hform
  exact ⟨O, hO, by rw [hcard, hu]⟩

private theorem card_centerQuot_SL_two (he : 1 ≤ e) (hE : Nat.card E = 2 ^ e)
    (hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) E) = ⊤) {T : Type*} [Group T]
    (g : Matrix.SpecialLinearGroup (Fin 2) E →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) :
    Nat.card (T ⧸ Subgroup.center T) = 2 ^ e * ((2 ^ e) ^ 2 - 1) := by
  have hform := card_centerQuot_mul_gcd_SL (by norm_num : 2 ≤ 2) hperf g hg hker
  have hg1 : (2 : ℕ).gcd (Nat.card E - 1) = 1 := by
    rw [hE]
    exact Nat.coprime_two_left.2 (CatDistinct.odd_two_pow_sub_one he)
  rw [hg1, mul_one, hE] at hform
  simpa using hform

theorem false_of_SL_centerQuot_isL2n_even (hm : 2 ≤ m) (he : 1 ≤ e) (hev : Even e)
    (hE : Nat.card E = 2 ^ e) (hperf : commutator (Matrix.SpecialLinearGroup (Fin m) E) = ⊤)
    {T : Type} [Group T] [Finite T] (g : Matrix.SpecialLinearGroup (Fin m) E →* T)
    (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E)) {r : ℕ} (hr : Odd r)
    (hL : catalogIs (T ⧸ Subgroup.center T) (S10.isL2n r)) : False := by
  obtain ⟨O, hO, hcard⟩ := exists_odd_card_centerQuot_SL hm he hE hperf g hg hker
  have h2 := catalogIs_isL2n_card_of_odd hr hL
  have hodd2 : Odd ((2 ^ r) ^ 2 - 1) := CatDistinct.odd_pow_two_pow_sub_one hr.pos (by norm_num)
  rw [hcard] at h2
  obtain ⟨hexp, -⟩ := CatDistinct.two_pow_mul_odd_inj hO hodd2 h2
  have hev' : Even (e * (m * (m - 1) / 2)) := hev.mul_right _
  rw [hexp] at hev'
  exact (Nat.not_even_iff_odd.2 hr) hev'

theorem eq_of_SL_two_centerQuot_isL2n (he : 1 ≤ e) (hE : Nat.card E = 2 ^ e)
    (hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) E) = ⊤)
    {T : Type} [Group T] [Finite T] (g : Matrix.SpecialLinearGroup (Fin 2) E →* T)
    (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) E)) {r : ℕ} (hr : Odd r)
    (hL : catalogIs (T ⧸ Subgroup.center T) (S10.isL2n r)) : e = r := by
  have h1 := card_centerQuot_SL_two he hE hperf g hg hker
  have h2 := catalogIs_isL2n_card_of_odd hr hL
  rw [h1] at h2
  have h3 : orderA 1 (2 ^ e) = orderA 1 (2 ^ r) := by
    rw [CatDistinct.orderA_one_eq he, CatDistinct.orderA_one_eq hr.pos, h2]
  exact orderA_one_two_pow_injective he hr.pos h3

end SL

section SU

variable {E : Type} [Field E] [Finite E]

private theorem toNat_pow_sub_neg_one_pow (Q i : ℕ) (hQ : 1 ≤ Q) :
    (((Q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat = if Even i then Q ^ i - 1 else Q ^ i + 1 := by
  have h1 : 1 ≤ Q ^ i := Nat.one_le_pow _ _ hQ
  have hc : ((Q : ℕ) : ℤ) ^ i = ((Q ^ i : ℕ) : ℤ) := by push_cast; rfl
  split_ifs with hi
  · rw [hi.neg_one_pow, hc]
    omega
  · rw [(Nat.not_even_iff_odd.1 hi).neg_one_pow, hc]
    omega

private theorem card_centerQuot_mul_gcd_SU {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t)
    (hne : (r + 1, 2 ^ t) ≠ (3, 2)) (hE : Nat.card E = (2 ^ t) ^ 2)
    (hperf : commutator ↥(StatedSU (r + 1) (2 ^ t) E) = ⊤) {T : Type*} [Group T]
    (g : ↥(StatedSU (r + 1) (2 ^ t) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU (r + 1) (2 ^ t) E)) :
    Nat.card (T ⧸ Subgroup.center T) * Nat.gcd (r + 1) (2 ^ t + 1) =
      (2 ^ t) ^ (r * (r + 1) / 2) * CatDistinct.twP r (2 ^ t) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := t) hE
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 t E :=
    CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hE ht
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := E) (p := 2)
    (f := t) hE (by omega : 3 ≤ r + 1) hne
  have hZ : Nat.card (Subgroup.center ↥(StatedSU (r + 1) (2 ^ t) E)) =
      Nat.gcd (r + 1) (2 ^ t + 1) := by
    rw [hQ.2]
    exact CFSG.LocalAnalysis.RankFourTheoremC.card_scalars_statedSU (K := E) (r := 2)
      (f := t) hE (by omega)
  have hsplit := KD264Lie.card_eq_card_centerQuotient_mul_card_center_of_surjective hperf g hg hker
  rw [KD264Lie.card_statedSU_eq_nat hUF (by omega), hZ] at hsplit
  have hN : (r + 1) * (r + 1 - 1) / 2 = r * (r + 1) / 2 := by
    rw [Nat.add_sub_cancel, Nat.mul_comm]
  have hP : ∏ i ∈ Finset.Icc 2 (r + 1), ((((2 ^ t : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) =
      CatDistinct.twP r (2 ^ t) := by
    unfold CatDistinct.twP
    refine Finset.prod_congr rfl fun i _ => ?_
    exact toNat_pow_sub_neg_one_pow (2 ^ t) i (Nat.one_le_two_pow)
  rw [hN, hP] at hsplit
  exact hsplit.symm

private theorem urn_size_one {r : ℕ} (hr : 4 ≤ r) :
    2 ^ r * (2 ^ 1) ^ (r * (r + 3) / 2) + 1 < (2 ^ 1) ^ (r * (r + 1)) := by
  obtain ⟨S, hS⟩ : ∃ S, S = r * (r + 3) / 2 := ⟨_, rfl⟩
  have h2S : 2 * S = r * (r + 3) := by
    have h : Even (r * (r + 3)) := by
      rcases Nat.even_or_odd r with h | h
      · exact h.mul_right _
      · exact (h.add_odd (by decide : Odd 3)).mul_left _
    obtain ⟨c, hc⟩ := h
    omega
  have hle : r + S + 1 ≤ r * (r + 1) := by nlinarith
  rw [pow_one, ← hS]
  calc 2 ^ r * 2 ^ S + 1 = 2 ^ (r + S) + 1 := by rw [pow_add]
    _ < 2 ^ (r + S + 1) := by
        rw [pow_succ]
        have : 1 < 2 ^ (r + S) := Nat.one_lt_two_pow (by omega)
        omega
    _ ≤ 2 ^ (r * (r + 1)) := Nat.pow_le_pow_right (by norm_num) hle

theorem false_of_SU_centerQuot_isL2n {r t : ℕ} (hr : 2 ≤ r) (ht : 1 ≤ t)
    (hne : (r + 1, 2 ^ t) ≠ (3, 2)) (hE : Nat.card E = (2 ^ t) ^ 2)
    (hperf : commutator ↥(StatedSU (r + 1) (2 ^ t) E) = ⊤) {T : Type} [Group T] [Finite T]
    (g : ↥(StatedSU (r + 1) (2 ^ t) E) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center ↥(StatedSU (r + 1) (2 ^ t) E)) {k : ℕ} (hk : Odd k)
    (hL : catalogIs (T ⧸ Subgroup.center T) (S10.isL2n k)) : False := by
  have hform := card_centerQuot_mul_gcd_SU hr ht hne hE hperf g hg hker
  have h2 := catalogIs_isL2n_card_of_odd hk hL
  have hgcd : 1 ≤ Nat.gcd (r + 1) (2 ^ t + 1) := CatDistinct.one_le_gcd_twisted
  have hgodd : Odd (Nat.gcd (r + 1) (2 ^ t + 1)) := CatDistinct.odd_gcd_twisted ht
  have hodd2 : Odd ((2 ^ k) ^ 2 - 1) := CatDistinct.odd_pow_two_pow_sub_one hk.pos (by norm_num)
  obtain ⟨hkt, hAB⟩ := CatDistinct.two_pow_mul_odd_inj (u := k)
    (v := t * (r * (r + 1) / 2)) (hodd2.mul hgodd) (CatDistinct.odd_twP ht)
    (by
      rw [pow_mul] at *
      rw [h2, mul_assoc] at hform
      exact hform)
  have htodd : Odd t := by
    rw [hkt] at hk
    exact (Nat.odd_mul.1 hk).1
  have h2e : r * (r + 1) / 2 * 2 = r * (r + 1) :=
    Nat.div_mul_cancel (Nat.even_mul_succ_self r).two_dvd
  have hk2 : (2 ^ k) ^ 2 = (2 ^ t) ^ (r * (r + 1)) := by
    rw [← pow_mul, ← pow_mul, hkt, ← mul_assoc, mul_assoc t, h2e]
    ring_nf
  have hle := CatDistinct.twP_le r (2 ^ t) Nat.one_le_two_pow
  have hsize : 2 ^ r * (2 ^ t) ^ (r * (r + 3) / 2) + 1 < (2 ^ t) ^ (r * (r + 1)) := by
    by_cases ht1 : t = 1
    · subst ht1
      have hr4 : 4 ≤ r := by
        by_contra hlt
        have : r = 2 ∨ r = 3 := by omega
        rcases this with rfl | rfl
        · exact hne rfl
        · rw [hkt] at hk
          norm_num at hk
      exact urn_size_one hr4
    · have ht3 : 3 ≤ t := by
        obtain ⟨c, hc⟩ := htodd
        omega
      exact CatDistinct.urn_size hr ht3
  have hlow : (2 ^ k) ^ 2 - 1 ≤ ((2 ^ k) ^ 2 - 1) * Nat.gcd (r + 1) (2 ^ t + 1) :=
    Nat.le_mul_of_pos_right _ hgcd
  rw [hAB, hk2] at hlow
  omega

end SU

end CFSG.LocalAnalysis.GLTheoremA.T1428
