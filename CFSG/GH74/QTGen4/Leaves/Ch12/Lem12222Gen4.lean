module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem22F
public import CFSG.GH74.QTGen4.OrderOverH

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem pCore_two_eq_bot_of_isPGroup {P : Type} [Group P] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPp : IsPGroup p P) : CFSG.pCore 2 P = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (CFSG.pCore 2 P) := CFSG.pCore_isPGroup
  have hp' : IsPGroup p (CFSG.pCore 2 P) := hPp.to_subgroup _
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨x, hx⟩
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hp') ⟨x, hx⟩
  have hab : 2 ^ a = p ^ b := ha.symm.trans hb
  have ha0 : a = 0 := by
    by_contra hne
    have h2d : 2 ∣ p ^ b := hab ▸ dvd_pow_self 2 hne
    have : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2d
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  rw [ha0, pow_zero, orderOf_eq_one_iff] at ha
  exact congrArg Subtype.val ha

theorem frattini_eq_bot_of_dvd_20160 {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hPp : IsPGroup p P) (hdvd : Nat.card P ∣ 20160) (hcyc : ¬ IsCyclic P) :
    frattini P = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (IsPGroup p P) := ⟨hPp⟩
  obtain ⟨k, hk⟩ := hPp.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    · rw [pow_zero] at hk
      haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hk).1
      exact hcyc inferInstance
    · exact hcyc (isCyclic_of_prime_card (hk.trans (pow_one p)))
  rw [hk] at hdvd
  have hp3 : p = 3 := by
    have hsq : p ^ 2 ∣ 20160 := (pow_dvd_pow p hk2).trans hdvd
    have h2le := hp.two_le
    have hle : p ≤ 141 := by
      have : p ^ 2 ≤ 20160 := Nat.le_of_dvd (by norm_num) hsq
      by_contra h
      push Not at h
      nlinarith
    interval_cases p <;> first | rfl | omega | (exfalso; norm_num at hp) | (exfalso; norm_num at hsq)
  subst hp3
  have hk2' : k = 2 := by
    by_contra hne
    have hk3 : 3 ≤ k := by omega
    have h27 : 3 ^ 3 ∣ 20160 := (pow_dvd_pow 3 hk3).trans hdvd
    norm_num at h27
  subst hk2'
  have hcomm : IsMulCommutative P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hk
  have hex : ∀ x : P, x ^ 3 = 1 := by
    intro x
    have hdvd9 : orderOf x ∣ 3 ^ 2 := hk ▸ orderOf_dvd_natCard x
    by_contra hx3
    have hne9 : orderOf x ≠ 3 ^ 2 := by
      intro h9
      exact hcyc (isCyclic_of_orderOf_eq_card x (h9.trans hk.symm))
    have : orderOf x ∣ 3 := by
      rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvd9 with ⟨i, hi, hio⟩
      interval_cases i
      · rw [hio, pow_zero]
        exact one_dvd _
      · rw [hio, pow_one]
      · exact absurd hio hne9
    exact hx3 (orderOf_dvd_iff_pow_eq_one.mp this)
  refine (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := P) (p := 3)).mpr ?_
  exact
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hex }

theorem lem12222Frattini_F4_holds : Lem12222Frattini_F4 := by
  intro G _ _ T L V H P U I h n p hyp hNE hC hpre hUO hcyc
  obtain ⟨hHs, -, hp, hp2, hPp, hPH, -⟩ := hpre
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := CFSG.Quasithin.exists_sylow_coe_eq hyp.sylow
  have hdvd := CFSG.GH74.QTGen4.modO2_dvd_of_inH
    (CFSG.GH74.QTGen4.Finite4.gen4 (G := G) : CFSG.GH74.Gen4 G) hyp.qtke.2.1 S hHs.1 hPH
  rw [pCore_two_eq_bot_of_isPGroup hp hp2 hPp] at hdvd
  have hcard : Nat.card (↥P ⧸ (⊥ : Subgroup ↥P)) = Nat.card ↥P :=
    Nat.card_congr (QuotientGroup.quotientBot (G := ↥P)).toEquiv
  rw [hcard] at hdvd
  exact frattini_eq_bot_of_dvd_20160 hp hp2 hPp hdvd hcyc

end CFSG.GH74.QTGen4.Leaves
