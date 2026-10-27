module

public import CFSG.LieType.SeitzGeneration.ExcTorusRank
public import CFSG.LieType.SeitzGeneration.ExcTorusF4One
public import CFSG.LieType.SeitzGeneration.ExcTorusF4Two
public import CFSG.LieType.SeitzGeneration.ExcPlaneF4Rest

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.TauCetiBridge TauCeti

theorem rankLE1_of_elemAbelian_cyclic {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (h : ∀ F : Subgroup G, IsElemAbelian p F → IsCyclic F) : RankLE1 p G := by
  intro F hF
  have := h F hF
  have hexp : Monoid.exponent F ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hF.2 x x.2)
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hp.pos hexp

section Adjoint


theorem rankLE1_F4 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card K) (hcnt : degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1) :
    RankLE1 p (adjointGroup Tag.F4 K) := by
  have he0 := orderOf_natCast_ne_zero hp hpq
  have hlt := orderOf_lt_prime hp hpq (rfl : orderOf ((Nat.card K : ℕ) : ZMod p) = _)
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt he0 hlt
  have he4 : 4 ≤ e := by
    by_contra h
    have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
    interval_cases e <;> revert hcnt <;> decide
  have hp3 : 3 < p := by omega
  by_cases hdvd : p ∣ Nat.card (adjointGroup Tag.F4 K)
  · intro F hF
    obtain ⟨m, hm, hpm⟩ := exists_dvd_phi_of_dvd_card_F4 hp hpq hdvd
    have hsmall : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 → False := by
      intro hm'
      have hm0 : 0 < m := by omega
      have hΦ : exhaustionPhi m = Polynomial.cyclotomic m ℤ := by
        rcases hm' with rfl | rfl | rfl | rfl | rfl
        · exact (Polynomial.cyclotomic_one ℤ).symm
        · exact (Polynomial.cyclotomic_two ℤ).symm
        · exact cyclotomic_three_eq.symm
        · exact cyclotomic_four_eq.symm
        · exact cyclotomic_six_eq.symm
      rw [hΦ] at hpm
      have hdvdm : (p : ℤ) ∣ (Nat.card K : ℤ) ^ m - 1 := by
        have := Polynomial.eval_dvd (x := (Nat.card K : ℤ))
          (Polynomial.cyclotomic.dvd_X_pow_sub_one m ℤ)
        simpa using hpm.trans this
      have hq1 : 1 ≤ Nat.card K ^ m := Nat.one_le_pow _ _ Nat.card_pos
      have h3 : p ∣ Nat.card K ^ m - 1 := by
        refine Int.natCast_dvd_natCast.1 ?_
        rw [Nat.cast_sub hq1]
        simpa using hdvdm
      have h4 := (dvd_pow_sub_one_iff_orderOf Nat.card_pos he).1 h3
      have h5 := Nat.le_of_dvd hm0 h4
      have h6 : e ≤ 6 := by omega
      interval_cases e <;> first | (revert hcnt; decide) | omega
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hsmall (by omega)).elim
    · exact (hsmall (by omega)).elim
    · exact (hsmall (by omega)).elim
    · exact (hsmall (by omega)).elim
    · exact (hsmall (by omega)).elim
    · obtain ⟨-, -, hcyc⟩ := F4_eight_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 hpm
      obtain ⟨T, -, -, -, -, hQ, -⟩ := hcyc
      exact rankLE1_of_elemAbelian_cyclic hp
        (fun F hF => hQ F (isPGroup_of_isElemAbelian hF)) F hF
    · obtain ⟨-, -, hcyc⟩ := F4_twelve_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 hpm
      obtain ⟨T, -, -, -, -, hQ, -⟩ := hcyc
      exact rankLE1_of_elemAbelian_cyclic hp
        (fun F hF => hQ F (isPGroup_of_isElemAbelian hF)) F hF
  · intro F hF
    have h1 : p ^ (Nat.card (adjointGroup Tag.F4 K)).factorization p = 1 := by
      rw [Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero]
    rw [elemAbelian_card_eq_one_of_ordProj hp h1 hF]
    exact hp.one_lt.le

theorem not_rankLE2_F4 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) (hcnt : 3 ≤ degCount Tag.F4 (orderOf ((Nat.card K : ℕ) : ZMod p))) :
    ¬ RankLE2 p (adjointGroup Tag.F4 K) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have h30 := le_thirty_of_degCount_pos (τ := Tag.F4) (e := e) (by simp) (by omega)
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
  interval_cases e <;> first | exact absurd hcnt (by decide) | skip
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_F4_one K hp hp3 he
    exact not_rankLE2_of_elemAbelian hp (by norm_num) hE hc
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_F4_two K hp hp3 he
    exact not_rankLE2_of_elemAbelian hp (by norm_num) hE hc

end Adjoint

section Cat


theorem rankLE1_cat_F4 (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid) {p : ℕ}
    (hp : p.Prime) (hpq : p ≠ q.p)
    (hcnt : degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1) :
    RankLE1 p (Cat ⟨.F4 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact RankLE1.of_mulEquiv e.symm (rankLE1_F4 K hp hpK hcnt)

theorem not_rankLE2_cat_F4 (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hcnt : 3 ≤ degCount Tag.F4 (orderOf ((q.card : ℕ) : ZMod p))) :
    ¬ RankLE2 p (Cat ⟨.F4 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  exact fun h => not_rankLE2_F4 K hp hp3 hpK hcnt (RankLE2.of_mulEquiv e h)

end Cat

end CFSG.LieType.SeitzGeneration
