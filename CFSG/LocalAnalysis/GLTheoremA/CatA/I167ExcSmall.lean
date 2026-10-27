module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Types
import CFSG.HardMathSupport.Dickson.Bal207.SU38Exc
import CFSG.RankThree.PartTwo.Sec4.Ronan148LOrder3
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172V2
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcOrdMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem card_pSimple_dvd_of_le_aux1 (p : ℕ) (J : Subgroup Ω) :
    Nat.card (PSimple p J) ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  have hZker : Subgroup.center ↥J ≤ (chevQuotHom p J).ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hc : (pQuotHom p J z : PQuot p J) ∈ Subgroup.center (PQuot p J) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := pQuotHom_surjective p J y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]
    exact (QuotientGroup.eq_one_iff _).2 hc
  exact Subgroup.card_dvd_of_surjective
    (QuotientGroup.lift_surjective_of_surjective (Subgroup.center ↥J) (chevQuotHom p J)
      (chevQuotHom_surjective p J) hZker)

private theorem card_pSimple_dvd_of_le_aux2 {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime)
    (hX : CFSG.Open.IsQuasisimple ↥X) (hJX : J ≤ X) (hdvd : p ∣ Nat.card ↥X) :
    Nat.card (PSimple p J) ∣ Nat.card (PSimple p X) := by
  have heq : Nat.card (↥X ⧸ Subgroup.center ↥X) = Nat.card (PSimple p X) :=
    Nat.card_congr
      (CFSG.LocalAnalysis.GLTheoremA.H81Orth.centerQuotEquivPSimple_of_dvd_card hp hX hdvd).toEquiv
  have h2 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    CFSG.HardMathSupport.Dickson.Bal207.su38_card_center_quot_dvd hJX
  rw [heq] at h2
  exact (card_pSimple_dvd_of_le_aux1 p J).trans h2

private theorem card_pSimple_dvd_of_le_aux3 {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime) (hJX : J ≤ X)
    (hdvd : ¬ p ∣ Nat.card ↥X) :
    Nat.card (PSimple p J) ∣ Nat.card (PSimple p X) := by
  have hcopX : Nat.Coprime p (Nat.card ↥X) := (hp.coprime_iff_not_dvd).2 hdvd
  have hcopJ : Nat.Coprime p (Nat.card ↥J) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hJX) hcopX
  have htopX : GLAPPrimeCore p ↥X = ⊤ := by
    show CFSG.pPrimeCore p ↥X = ⊤
    refine top_le_iff.mp (le_sSup ?_)
    refine ⟨inferInstance, ?_⟩
    rwa [Subgroup.card_top]
  have htopJ : GLAPPrimeCore p ↥J = ⊤ := by
    show CFSG.pPrimeCore p ↥J = ⊤
    refine top_le_iff.mp (le_sSup ?_)
    refine ⟨inferInstance, ?_⟩
    rwa [Subgroup.card_top]
  have h1X : Nat.card (PSimple p X) = 1 := by
    haveI : Subsingleton (PQuot p X) := by
      change Subsingleton (↥X ⧸ GLAPPrimeCore p ↥X)
      rw [htopX]
      exact QuotientGroup.subsingleton_quotient_top
    exact Nat.card_of_subsingleton (1 : PSimple p X)
  have h1J : Nat.card (PSimple p J) = 1 := by
    haveI : Subsingleton (PQuot p J) := by
      change Subsingleton (↥J ⧸ GLAPPrimeCore p ↥J)
      rw [htopJ]
      exact QuotientGroup.subsingleton_quotient_top
    exact Nat.card_of_subsingleton (1 : PSimple p J)
  rw [h1J, h1X]

theorem card_pSimple_dvd_of_le {p : ℕ} {X J : Subgroup Ω} (hp : p.Prime) (hX : CFSG.Open.IsQuasisimple ↥X)
    (hJX : J ≤ X) : Nat.card (PSimple p J) ∣ Nat.card (PSimple p X) := by
  by_cases hdvd : p ∣ Nat.card ↥X
  · exact card_pSimple_dvd_of_le_aux2 hp hX hJX hdvd
  · exact card_pSimple_dvd_of_le_aux3 hp hJX hdvd

section Orders


private theorem type167J_order_facts_aux2 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    orderD n (2 ^ k) =
      (2 ^ k) ^ (n * (n - 1)) * ((2 ^ k) ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1) := by
  have hodd : Odd ((2 ^ k) ^ n - 1) := by
    rw [← pow_mul]
    exact CFSG.LocalAnalysis.GLTheoremA.S172.odd_two_pow_sub_one (by nlinarith)
  have hg : Nat.gcd 4 ((2 ^ k) ^ n - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  unfold orderD
  rw [hg, Nat.div_one]

private theorem type167J_order_facts_aux3 (k : ℕ) (hk : 1 ≤ k) :
    orderA 3 (2 ^ k) =
      (2 ^ k) ^ 6 * (((2 ^ k) ^ 2 - 1) * (((2 ^ k) ^ 3 - 1) * ((2 ^ k) ^ 4 - 1))) := by
  have hodd : Odd ((2 ^ k) - 1) := CFSG.LocalAnalysis.GLTheoremA.S172.odd_two_pow_sub_one hk
  have hg : Nat.gcd 4 ((2 ^ k) - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  unfold orderA
  rw [hg, Nat.div_one]
  have hI : Finset.Icc 2 (3 + 1) = {2, 3, 4} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]

private theorem type167J_order_facts_aux4 (k : ℕ) : 7 ∣ (2 ^ k) ^ 3 - 1 := by
  have h := Nat.sub_one_dvd_pow_sub_one (2 ^ 3) k
  have hpow : (2 ^ 3) ^ k = (2 ^ k) ^ 3 := by rw [← pow_mul, ← pow_mul]; ring
  rw [hpow] at h
  norm_num at h
  exact h

private theorem type167J_order_facts_aux5 (k : ℕ) : 7 ∣ (2 ^ k) ^ (2 * 3) - 1 := by
  have h := Nat.sub_one_dvd_pow_sub_one (2 ^ 3) (2 * k)
  have hpow : (2 ^ 3) ^ (2 * k) = (2 ^ k) ^ (2 * 3) := by rw [← pow_mul, ← pow_mul]; ring
  rw [hpow] at h
  norm_num at h
  exact h

private theorem type167J_order_facts_aux6 {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k) :
    7 ∣ orderD n (2 ^ k) := by
  rw [type167J_order_facts_aux2 n k (by omega) hk]
  by_cases h3 : n = 3
  · subst h3
    have h7 := type167J_order_facts_aux4 k
    exact (dvd_mul_of_dvd_right h7 ((2 ^ k) ^ (3 * (3 - 1)))).trans (dvd_mul_right _ _)
  · have hmem : 3 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨by norm_num, by omega⟩
    have h7 : 7 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1) :=
      (type167J_order_facts_aux5 k).trans (Finset.dvd_prod_of_mem _ hmem)
    exact dvd_mul_of_dvd_right h7 ((2 ^ k) ^ (n * (n - 1)) * ((2 ^ k) ^ n - 1))

private theorem type167J_order_facts_aux7 {n : ℕ} (hn : 6 ≤ n) :
    7 ∣ orderTwistedD n 2 := by
  change 7 ∣ ordTwistedD n 2
  rw [CFSG.LargeExtraspecial.A2Mod.Ord.ordTwistedD_two_eq (by omega)]
  have hmem : 3 ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.2 ⟨by norm_num, by omega⟩
  have h7 : 7 ∣ (2 : ℕ) ^ (2 * 3) - 1 := by norm_num
  have hfac : 7 ∣ ∏ i ∈ Finset.Icc 1 (n - 1), ((2 : ℕ) ^ (2 * i) - 1) :=
    h7.trans (Finset.dvd_prod_of_mem _ hmem)
  exact dvd_mul_of_dvd_right hfac ((2 : ℕ) ^ (n * (n - 1)) * ((2 : ℕ) ^ n + 1))

private theorem type167J_order_facts_aux8 {k : ℕ} (hk : 2 ≤ k) : 7 ∣ orderA 3 (2 ^ k) := by
  rw [type167J_order_facts_aux3 k (by omega)]
  have h7 := type167J_order_facts_aux4 k
  have h1 : 7 ∣ ((2 ^ k) ^ 3 - 1) * ((2 ^ k) ^ 4 - 1) := dvd_mul_of_dvd_left h7 _
  have h2 : 7 ∣ ((2 ^ k) ^ 2 - 1) * (((2 ^ k) ^ 3 - 1) * ((2 ^ k) ^ 4 - 1)) :=
    dvd_mul_of_dvd_right h1 _
  exact dvd_mul_of_dvd_right h2 _

private theorem type167J_order_facts_aux9 {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hpos : 0 < orderD n (2 ^ k)) : 2 ^ (n * (n - 1)) ≤ orderD n (2 ^ k) := by
  have hdvd : (2 ^ k) ^ (n * (n - 1)) ∣ orderD n (2 ^ k) := by
    rw [type167J_order_facts_aux2 n k hn hk]
    exact ⟨((2 ^ k) ^ n - 1) * (∏ i ∈ Finset.Icc 1 (n - 1), ((2 ^ k) ^ (2 * i) - 1)),
      by ring⟩
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  exact le_trans (Nat.pow_le_pow_left h2k _) (Nat.le_of_dvd hpos hdvd)

private theorem type167J_order_facts_aux10 {k : ℕ} (hk : 2 ≤ k)
    (hpos : 0 < orderD 3 (2 ^ k)) : 20160 < orderD 3 (2 ^ k) := by
  have hdvd : (2 ^ k) ^ 6 * ((2 ^ k) ^ 3 - 1) ∣ orderD 3 (2 ^ k) := by
    rw [type167J_order_facts_aux2 3 k (by norm_num) (by omega)]
    exact ⟨∏ i ∈ Finset.Icc 1 (3 - 1), ((2 ^ k) ^ (2 * i) - 1), rfl⟩
  refine lt_of_lt_of_le ?_ (Nat.le_of_dvd hpos hdvd)
  have hq : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq6 : 4 ^ 6 ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left hq 6
  have h3 : 63 ≤ (2 ^ k) ^ 3 - 1 := by
    have h64 : 4 ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left hq 3
    norm_num at h64
    omega
  calc 20160 < 4 ^ 6 * 63 := by norm_num
    _ ≤ (2 ^ k) ^ 6 * ((2 ^ k) ^ 3 - 1) := Nat.mul_le_mul hq6 h3

private theorem type167J_order_facts_aux11 {k : ℕ} (hk : 2 ≤ k)
    (hpos : 0 < orderA 3 (2 ^ k)) : 20160 < orderA 3 (2 ^ k) := by
  have hdvd : (2 ^ k) ^ 6 * ((2 ^ k) ^ 3 - 1) ∣ orderA 3 (2 ^ k) := by
    rw [type167J_order_facts_aux3 k (by omega)]
    have h1 : (2 ^ k) ^ 3 - 1 ∣
        ((2 ^ k) ^ 2 - 1) * (((2 ^ k) ^ 3 - 1) * ((2 ^ k) ^ 4 - 1)) :=
      dvd_mul_of_dvd_right (dvd_mul_right ((2 ^ k) ^ 3 - 1) ((2 ^ k) ^ 4 - 1))
        ((2 ^ k) ^ 2 - 1)
    exact mul_dvd_mul_left ((2 ^ k) ^ 6) h1
  refine lt_of_lt_of_le ?_ (Nat.le_of_dvd hpos hdvd)
  have hq : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq6 : 4 ^ 6 ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left hq 6
  have h3 : 63 ≤ (2 ^ k) ^ 3 - 1 := by
    have h64 : 4 ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left hq 3
    norm_num at h64
    omega
  calc 20160 < 4 ^ 6 * 63 := by norm_num
    _ ≤ (2 ^ k) ^ 6 * ((2 ^ k) ^ 3 - 1) := Nat.mul_le_mul hq6 h3

private theorem type167J_order_facts_aux15 {n : ℕ} (hno : Odd n) (hn5 : 5 ≤ n) :
    20160 < orderA (n - 1) 2 := by
  rcases eq_or_lt_of_le hn5 with h5 | h7
  · subst h5
    decide
  · have h7' : 7 ≤ n := by
      obtain ⟨c, hc⟩ := hno
      omega
    have hprof := CFSG.LargeExtraspecial.A2Mod.Ord.two_pow_le_of_profile
      (CFSG.LargeExtraspecial.A2Mod.Ord.profile_A (n := n - 1) (by omega))
    have hN : 21 ≤ (n - 1) * ((n - 1) + 1) / 2 := by
      have : 42 ≤ (n - 1) * ((n - 1) + 1) := by
        have := Nat.mul_le_mul (show 6 ≤ n - 1 by omega) (show 7 ≤ (n - 1) + 1 by omega)
        simpa using this
      omega
    exact lt_of_lt_of_le (by norm_num : 20160 < 2 ^ 21)
      (le_trans (Nat.pow_le_pow_right (by norm_num) hN) hprof)

private theorem type167J_order_facts_aux12 {S : Type} [Group S] [Finite S] {n : ℕ}
    (hno : Odd n) (hn5 : 5 ≤ n) (h : catalogIs S (isLnA n 2)) :
    20160 < Nat.card S ∧ 3 ∣ Nat.card S ∧ 7 ∣ Nat.card S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -⟩
  · cases i with
    | cyclic pp hpp => simp [onLie] at h1
    | alternating m hm => simp [onLie] at h1
    | sporadic s => simp [onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        change r + 1 = n ∧ q.card = 2 at h1
        obtain ⟨hr, hq⟩ := h1
        have hcard : Nat.card S = orderA (n - 1) 2 := by
          rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A r q, hv⟩ S ⟨e⟩]
          change orderA r q.card = orderA (n - 1) 2
          rw [hq]
          congr 1
          omega
        rw [hcard]
        exact ⟨type167J_order_facts_aux15 hno hn5,
          CFSG.LargeExtraspecial.A2Mod.Ord.dvd_ordA_two (n := n - 1) (a := 2)
            (p := 3) (by norm_num) (by omega) (by norm_num),
          CFSG.LargeExtraspecial.A2Mod.Ord.dvd_ordA_two (n := n - 1) (a := 3)
            (p := 7) (by norm_num) (by omega) (by norm_num)⟩
      | _ => simp [onLie, isLnEps] at h1
  · omega
  · omega
  · omega
  · omega

private theorem type167J_order_facts_aux13 {S : Type} [Group S] [Finite S] {n : ℕ}
    (hne : Even n) (hn6 : 6 ≤ n) (h : catalogIs S (isOmMA n 2)) :
    20160 < Nat.card S ∧ 3 ∣ Nat.card S ∧ 7 ∣ Nat.card S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hm, h2⟩
  · cases i with
    | cyclic pp hpp => simp [isOmM, onLie] at h1
    | alternating m hm => simp [isOmM, onLie] at h1
    | sporadic s => simp [isOmM, onLie] at h1
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedD r q =>
        change r = n ∧ q.card = 2 at h1
        obtain ⟨hr, hq⟩ := h1
        subst r
        have hcard : Nat.card S = orderTwistedD n 2 := by
          rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedD n q, hv⟩ S ⟨e⟩]
          change orderTwistedD n q.card = orderTwistedD n 2
          rw [hq]
        rw [hcard]
        refine ⟨?_, ?_, ?_⟩
        · have hprof := CFSG.LargeExtraspecial.A2Mod.Ord.two_pow_le_of_profile
            (CFSG.LargeExtraspecial.A2Mod.Ord.profile_2D (n := n) (by omega))
          have hN : 30 ≤ n * (n - 1) := by
            have := Nat.mul_le_mul (show 6 ≤ n by omega) (show 5 ≤ n - 1 by omega)
            simpa using this
          exact lt_of_lt_of_le (by norm_num : 20160 < 2 ^ 30)
            (le_trans (Nat.pow_le_pow_right (by norm_num) hN) hprof)
        · rw [← hq]
          exact CFSG.RankThree.PartTwo.Sec4.Ronan148L.three_dvd_lieOrderFormula hv
            (by intro m hh; cases hh)
        · exact type167J_order_facts_aux7 hn6
      | _ => simp [isOmM, onLie] at h1
  · omega

private theorem type167J_order_facts_aux16 {S : Type} [Group S] [Finite S] {n k : ℕ}
    (hno : Odd n) (hn3 : 3 ≤ n) (hk5 : k = 1 → 5 ≤ n) (hk1 : 1 ≤ k)
    (h : catalogIs S (isOmP n (2 ^ k))) :
    20160 < Nat.card S ∧ 3 ∣ Nat.card S ∧ 7 ∣ Nat.card S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic pp hpp => simp [isOmP, onLie] at hi
  | alternating m hm => simp [isOmP, onLie] at hi
  | sporadic s => simp [isOmP, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D r q =>
      change r = n ∧ q.card = 2 ^ k at hi
      obtain ⟨hr, hq⟩ := hi
      subst r
      have hcard : Nat.card S = orderD n (2 ^ k) := by
        rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.D n q, hv⟩ S ⟨e⟩]
        change orderD n q.card = orderD n (2 ^ k)
        rw [hq]
      rw [hcard]
      have hpos : 0 < orderD n (2 ^ k) := hcard ▸ Nat.card_pos
      refine ⟨?_, ?_, ?_⟩
      · by_cases h3 : n = 3
        · subst h3
          have hk2 : 2 ≤ k := by
            rcases Nat.eq_or_lt_of_le hk1 with hk1' | hk1'
            · subst hk1'
              exact absurd (hk5 rfl) (by omega)
            · omega
          exact type167J_order_facts_aux10 hk2 hpos
        · have hn5 : 5 ≤ n := by
            obtain ⟨c, hc⟩ := hno
            omega
          have hb := type167J_order_facts_aux9 (n := n) (k := k) (by omega) hk1 hpos
          have hN : 20 ≤ n * (n - 1) := by
            have := Nat.mul_le_mul (show 5 ≤ n by omega) (show 4 ≤ n - 1 by omega)
            simpa using this
          exact lt_of_lt_of_le (by norm_num : 20160 < 2 ^ 20)
            (le_trans (Nat.pow_le_pow_right (by norm_num) hN) hb)
      · rw [← hq]
        exact CFSG.RankThree.PartTwo.Sec4.Ronan148L.three_dvd_lieOrderFormula hv
          (by intro m hh; cases hh)
      · exact type167J_order_facts_aux6 hn3 hk1
    | _ => simp [isOmP, onLie] at hi

private theorem type167J_order_facts_aux17 {S : Type} [Group S] [Finite S] {k : ℕ}
    (hk2 : 2 ≤ k) (h : catalogIs S (isLnA 4 (2 ^ k))) :
    20160 < Nat.card S ∧ 3 ∣ Nat.card S ∧ 7 ∣ Nat.card S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h2a | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩ | ⟨hm, hq, hi⟩
  · cases i with
    | cyclic pp hpp => simp [onLie, isLnEps] at h2a
    | alternating m hm => simp [onLie, isLnEps] at h2a
    | sporadic s => simp [onLie, isLnEps] at h2a
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A r q =>
        change r + 1 = 4 ∧ q.card = 2 ^ k at h2a
        obtain ⟨hr, hq⟩ := h2a
        have hr3 : r = 3 := by omega
        subst hr3
        have hcard : Nat.card S = orderA 3 (2 ^ k) := by
          rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 3 q, hv⟩ S ⟨e⟩]
          change orderA 3 q.card = orderA 3 (2 ^ k)
          rw [hq]
        rw [hcard]
        have hpos : 0 < orderA 3 (2 ^ k) := hcard ▸ Nat.card_pos
        exact ⟨type167J_order_facts_aux11 hk2 hpos,
          (by rw [← hq]
              exact CFSG.RankThree.PartTwo.Sec4.Ronan148L.three_dvd_lieOrderFormula hv
                (by intro m hh; cases hh)),
          type167J_order_facts_aux8 hk2⟩
      | _ => simp [onLie, isLnEps] at h2a
  · omega
  · omega
  · omega
  · have h4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

private theorem type167J_order_facts_aux14 {S : Type} [Group S] [Finite S] {n k : ℕ}
    (hno : Odd n) (hn3 : 3 ≤ n) (hk5 : k = 1 → 5 ≤ n) (hk1 : 1 ≤ k)
    (h : catalogIs S (isOmPA n (2 ^ k))) :
    20160 < Nat.card S ∧ 3 ∣ Nat.card S ∧ 7 ∣ Nat.card S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with h1 | ⟨hn3', h2⟩
  · exact type167J_order_facts_aux16 hno hn3 hk5 hk1 ⟨i, h1, ⟨e⟩⟩
  · subst hn3'
    have hk2 : 2 ≤ k := by
      rcases Nat.eq_or_lt_of_le hk1 with hk1' | hk1'
      · subst hk1'
        exact absurd (hk5 rfl) (by omega)
      · omega
    exact type167J_order_facts_aux17 hk2 ⟨i, h2, ⟨e⟩⟩

theorem type167J_order_facts {p : ℕ} {J : Subgroup Ω} (h : Type167J p J) :
    20160 < Nat.card (PSimple p J) ∧ 3 ∣ Nat.card (PSimple p J) ∧ 7 ∣ Nat.card (PSimple p J) := by
  rcases h with ⟨hp3, n, hno, hn5, hcat⟩ | ⟨hp3, n, hne, hn6, hcat⟩ |
    ⟨n, k, hno, hn3, hk5, hk1, hpdiv, hcat⟩
  · subst hp3
    exact type167J_order_facts_aux12 hno hn5 hcat
  · subst hp3
    exact type167J_order_facts_aux13 hne hn6 hcat
  · exact type167J_order_facts_aux14 hno hn3 hk5 hk1 hcat

theorem exc_small_card_cases {S : Type} [Group S] [Finite S] (h : catalogIs S ExcSmallIdx) :
    Nat.card S ≤ 20160 ∨ ¬ 3 ∣ Nat.card S ∨ ¬ 7 ∣ Nat.card S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hi | hi
  · exact Or.inl (CFSG.LocalAnalysis.GLTheoremA.K1419E.l3u3Ord_card_ambiguous_le ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie dl =>
      obtain ⟨d, hv⟩ := dl
      have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩ S ⟨e⟩
      cases d with
      | suzuki m =>
        exact Or.inr (Or.inl (by
          rw [hcard]
          exact CFSG.LocalAnalysis.GLTheoremA.K1419E.l3u3Ord_not_three_dvd_orderSuzuki m))
      | tits =>
        exact Or.inr (Or.inr (by
          rw [hcard]
          exact CFSG.LocalAnalysis.GLTheoremA.K1419E.l3u3Ord_orderTits.1))
      | _ => exact hi.elim

theorem false_of_exc_small {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x)
    (hs : catalogIs (PSimple p X) ExcSmallIdx) : False := by
  have hdvd : Nat.card (PSimple p J) ∣ Nat.card (PSimple p X) :=
    card_pSimple_dvd_of_le H.hp H.hX H.hJX
  obtain ⟨hlt, h3, h7⟩ := type167J_order_facts H.htype
  have hpos : 0 < Nat.card (PSimple p X) := Nat.card_pos
  rcases exc_small_card_cases hs with h | h | h
  · have := Nat.le_of_dvd hpos hdvd
    omega
  · exact h (dvd_trans h3 hdvd)
  · exact h (dvd_trans h7 hdvd)

end Orders

end CFSG.LocalAnalysis.GLTheoremA.I167

end
