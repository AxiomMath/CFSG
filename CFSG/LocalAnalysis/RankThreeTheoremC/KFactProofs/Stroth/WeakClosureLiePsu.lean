module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTwistFrame
public import CFSG.GroupTheory.WeirSylow.Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsuFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsuDiag
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open
open CFSG.Quasithin (StatedGU)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU unitarySU_eq_gramSU card_gramSU gramForm_isSymm
  gramForm_separatingLeft)

@[expose] def suProj (n q : ℕ) (L : Type) [Field L] :
    StatedSU n q L →* StatedProj (StatedSU n q L) :=
  QuotientGroup.mk' ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L))

private theorem pow_add_one_eq_one_of_scalar_mem {L : Type} [Field L] [Finite L] {q n : ℕ}
    (hq : Nat.card L = q ^ 2) (hn : 1 ≤ n) {c : Lˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n q L) : c ^ (q + 1) = 1 := by
  haveI : Fintype L := Fintype.ofFinite L
  have hq' : Fintype.card L = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hq]
  obtain ⟨f, hqf, h⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData L hq'
  have hK : Nat.card L = (ringChar L ^ f) ^ 2 := by rw [← hqf, hq]
  rw [hqf] at hc ⊢
  exact ((CFSG.LinearGroups.scalar_mem_statedSU_iff h.prime hK hn c).1 hc).2

private theorem prod_Icc_neg_sub_one (q n : ℕ) (hn : 1 ≤ n) :
    ∏ i ∈ Finset.Icc 1 n, ((-(q : ℤ)) ^ i - 1) =
      (∏ i ∈ Finset.Icc 1 n, (-1 : ℤ) ^ i) *
        (((q : ℤ) + 1) * ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1) ^ i)) := by
  have hterm : ∀ i : ℕ, (-(q : ℤ)) ^ i - 1 = (-1 : ℤ) ^ i * ((q : ℤ) ^ i - (-1) ^ i) := by
    intro i
    have h1 : ((-1 : ℤ) ^ i) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [neg_pow (q : ℤ) i]
    linear_combination h1
  have hsplit : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 n := by simp
  simp only [hterm]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [hsplit, Finset.prod_insert h1]
  ring

private theorem natCard_statedGU_eq_mul_statedSU {L : Type} [Field L] [Finite L] {q : ℕ}
    (hq : Nat.card L = q ^ 2) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (StatedGU n q L) = (q + 1) * Nat.card (StatedSU n q L) := by
  haveI : Fintype L := Fintype.ofFinite L
  have hq' : Fintype.card L = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hq]
  obtain ⟨f, hqf, h⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData L hq'
  have hG := CFSG.GroupTheory.WeirSylow.natCard_statedGU_cast hq' hn
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) L)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) hn).2.1
  have hS : (Nat.card (StatedSU n q L) : ℤ) =
      (q : ℤ) ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1) ^ i) := by
    rw [hqf, show StatedSU n (ringChar L ^ f) L = unitarySU (ringChar L) f L n from rfl,
      unitarySU_eq_gramSU h, card_gramSU, hU]
  have hs2 : (∏ i ∈ Finset.Icc 1 n, (-1 : ℤ) ^ i) * ∏ i ∈ Finset.Icc 1 n, (-1 : ℤ) ^ i = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have hint : (Nat.card (StatedGU n q L) : ℤ) =
      ((q + 1 : ℕ) : ℤ) * (Nat.card (StatedSU n q L) : ℤ) := by
    rw [hG, prod_Icc_neg_sub_one q n hn, hS]
    push_cast
    linear_combination ((q : ℤ) ^ (n * (n - 1) / 2) * ((q : ℤ) + 1) *
      ∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1) ^ i)) * hs2
  exact_mod_cast hint

private theorem suProj_comp_injective {p : ℕ} [Fact p.Prime] {n q : ℕ} {L : Type} [Field L]
    (hpq1 : ¬ p ∣ q + 1)
    (hd : ∀ c : Lˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n q L → c ^ (q + 1) = 1)
    {A : Type} [Group A] (T : A →* StatedSU n q L) (hT : Function.Injective T)
    (hA : ∀ a : A, ∃ k : ℕ, a ^ p ^ k = 1) : Function.Injective ((suProj n q L).comp T) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : (QuotientGroup.mk (T x) : StatedProj (StatedSU n q L)) = 1 := hx
  have hmem : T x ∈ (StatedScalars (Fin n) L).subgroupOf (StatedSU n q L) :=
    (QuotientGroup.eq_one_iff (T x)).1 hx'
  obtain ⟨k, hk⟩ := hA x
  have h2 : T x ^ (q + 1) = 1 := by
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hmem
    have hc' : c ^ (q + 1) = 1 := hd c (by rw [hc]; exact (T x).2)
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc, ← map_pow, hc', map_one]
  have hpk : T x ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hcop : Nat.Coprime (q + 1) (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hpq1).symm
  have h3 : orderOf (T x) ∣ Nat.gcd (q + 1) (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hpk)
  rw [hcop.gcd_eq_one] at h3
  have h4 : T x = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact hT (by rw [map_one]; exact h4)

private theorem factorization_card_projSU {p : ℕ} [Fact p.Prime] {n q : ℕ} {L : Type} [Field L]
    [Finite L]
    (hZ : ¬ p ∣ Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L))) :
    (Nat.card (StatedProj (StatedSU n q L))).factorization p =
      (Nat.card (StatedSU n q L)).factorization p := by
  have hP : Nat.card (StatedProj (StatedSU n q L)) ≠ 0 := Nat.card_pos.ne'
  have hZ0 : Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L)) ≠ 0 :=
    Nat.card_pos.ne'
  have hcard : Nat.card (StatedSU n q L) =
      Nat.card (StatedProj (StatedSU n q L)) *
        Nat.card ((StatedScalars (Fin n) L).subgroupOf (StatedSU n q L)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hcard, Nat.factorization_mul hP hZ0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hZ, add_zero]

theorem wcOn_projSU_of_not_dvd_add_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {L : Type}
    [Field L] [Finite L] {q : ℕ} (hq : Nat.card L = q ^ 2) (hpq : ¬ p ∣ q) (hpq1 : ¬ p ∣ q + 1)
    (n : ℕ) : WCOn p (StatedProj (StatedSU n q L)) := by
  have hp : p.Prime := Fact.out
  have hp1 : Odd p := hp.odd_of_ne_two hp2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    haveI : Subsingleton (GL (Fin 0) L) := ⟨fun a b => Units.ext (Matrix.ext fun i => i.elim0)⟩
    have hH : Nat.card (StatedSU 0 q L) = 1 := Nat.card_of_subsingleton 1
    have hQ : Nat.card (StatedProj (StatedSU 0 q L)) ∣ 1 := by
      have := Subgroup.card_quotient_dvd_card
        ((StatedScalars (Fin 0) L).subgroupOf (StatedSU 0 q L))
      rwa [hH] at this
    apply WCOn.of_factorization_le_one
    rw [Nat.dvd_one.1 hQ, Nat.factorization_one]
    simp
  · haveI : Fintype L := Fintype.ofFinite L
    have hq' : Fintype.card L = q ^ 2 := by rw [← Nat.card_eq_fintype_card, hq]
    have hsc : ∀ c : Lˣ, Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n q L →
        c ^ (q + 1) = 1 := fun c hc => pow_add_one_eq_one_of_scalar_mem hq hn hc
    have hZ := StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSU n q L) hp hpq1 hsc
    have hSU0 : Nat.card (StatedSU n q L) ≠ 0 := Nat.card_pos.ne'
    have hfac : (Nat.card (StatedProj (StatedSU n q L))).factorization p =
        (Nat.card (StatedGU n q L)).factorization p := by
      rw [factorization_card_projSU hZ, natCard_statedGU_eq_mul_statedSU hq hn,
        Nat.factorization_mul (by omega : q + 1 ≠ 0) hSU0, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hpq1, zero_add]
    obtain ⟨e, he⟩ : ∃ e, orderOf (-(q : ZMod p)) = e := ⟨_, rfl⟩
    obtain ⟨a, ha_def⟩ : ∃ a, padicValInt p ((-(q : ℤ)) ^ e - 1) = a := ⟨_, rfl⟩
    obtain ⟨r, hr_def⟩ : ∃ r, n / e = r := ⟨_, rfl⟩
    have hGUfac : (Nat.card (StatedGU n q L)).factorization p =
        a * r + r.factorial.factorization p := by
      rw [CFSG.GroupTheory.WeirSylow.factorization_card_statedGU hp1 L hq' hpq hn, he, ha_def,
        hr_def, Nat.factorization_def _ hp]
    have hepos : 0 < e := by
      rw [← he, ← CFSG.GroupTheory.WeirSylow.ordMod_neg_natCast (p := p) q]
      exact CFSG.GroupTheory.WeirSylow.ordMod_pos (by rw [dvd_neg]; exact_mod_cast hpq)
    have hq2 : 2 ≤ q := by
      by_contra hlt
      have hq1' : q ≤ 1 := by omega
      have h1 : q ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hq1' 2
      have hL1 : 1 < Nat.card L := Finite.one_lt_card
      rw [one_pow, ← hq] at h1
      omega
    have hne : (-(q : ℤ)) ^ e - 1 ≠ 0 := by
      intro h0
      have h1 : (-(q : ℤ)) ^ e = 1 := sub_eq_zero.1 h0
      have h2 : q ^ e = 1 := by
        have := congrArg Int.natAbs h1
        simpa [Int.natAbs_pow] using this
      have h3 : 1 < q ^ e := Nat.one_lt_pow hepos.ne' (by omega)
      rw [h2] at h3
      exact absurd h3 (lt_irrefl 1)
    have ha1 : 1 ≤ a := by
      rw [← ha_def]
      have hdvd : (p : ℤ) ∣ (-(q : ℤ)) ^ e - 1 :=
        (CFSG.GroupTheory.WeirSylow.dvd_pow_sub_one_iff e).2
          (by rw [CFSG.GroupTheory.WeirSylow.ordMod_neg_natCast q, he])
      have hdvd1 : (p : ℤ) ^ 1 ∣ (-(q : ℤ)) ^ e - 1 := by rw [pow_one]; exact hdvd
      rcases (padicValInt_dvd_iff 1 _).1 hdvd1 with h0 | h1
      · exact absurd h0 hne
      · exact h1
    obtain ⟨μ, hμ, ⟨F⟩⟩ := nonempty_suFrame hp2 hq' hpq hpq1 n he ha_def hr_def
    have hinj : Function.Injective ((suProj n q L).comp F.T) :=
      suProj_comp_injective hpq1 hsc F.T F.T_injective fun c => ⟨a, pow_pPow_eq_one_pi c⟩
    exact (F.map (suProj n q L) hinj).wcOn hp2 ha1 hμ (hfac.trans hGUfac)

theorem crossClassical_psu : CrossClassical .PSU 3 := by
  intro K _ _ n ℓ f p _ hp2 hpℓ hn hnot h
  have hp := (Fact.out : p.Prime)
  have h' := h
  obtain ⟨hadm, F, _, _, hF, ⟨e⟩⟩ := h'
  have hℓ : ℓ.Prime := hadm.1
  have hpq : ¬ p ∣ ℓ ^ f := by
    intro hd
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow hd))
  by_cases hq1 : p ∣ ℓ ^ f + 1
  · by_cases hpn : p ∣ n
    · have hspec : ¬ (n = 3 ∧ p = 3 ∧ ¬ 9 ∣ ℓ ^ f + 1) := by
        rintro ⟨rfl, rfl, h9⟩
        apply hnot
        refine Or.inr (Or.inr ⟨rfl, rfl, Or.inr ⟨rfl, ?_⟩⟩)
        omega
      refine WCOn.of_not_isMulCommutative fun P => ?_
      exact InnerAction.n1PSU_holds K n ℓ f h p hp hp2 hpn hq1 hspec P P.isPGroup' P.not_dvd_index
    · exact WCOn.of_mulEquiv e (wcOn_projSU_of_dvd_add_one hp2 hF hn hq1 hpn)
  · exact WCOn.of_mulEquiv e (wcOn_projSU_of_not_dvd_add_one hp2 hF hpq hq1 n)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
