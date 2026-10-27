module

public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.GH74.GLS.IVK.Statements.Sec1
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.Glauberman.Dickson CFSG.GorensteinWalter

theorem isElementaryAbelian_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    [hH : CFSG.IsElementaryAbelian p H] : CFSG.IsElementaryAbelian p G :=
  CFSG.IsElementaryAbelian.of_mulEquiv e.symm inferInstance

theorem ivk_1_2l : IVK_1_2l := by
  intro F _ _ hF K _ _ e X hXodd hXnil
  obtain ⟨p, n, hp, hpodd, hn, hq⟩ := isOddPrimePower_of_L2Field hF
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hpodd) even_two
  let φ : K ≃* PSL2 F := toPSL e
  let X' : Subgroup (PSL2 F) := X.map φ.toMonoidHom
  let eX : X ≃* X' := Subgroup.equivMapOfInjective X φ.toMonoidHom φ.injective
  have hodd' : Odd (Nat.card X') := by rw [← Nat.card_congr eX.toEquiv]; exact hXodd
  have hnil' : Group.IsNilpotent X' :=
    Group.nilpotent_of_surjective eX.toMonoidHom eX.surjective
  have hqodd : Odd (p ^ n) := hpodd.pow
  have hdvd1 : ∀ z, z ∣ (p ^ n + 1) / Nat.gcd 2 (p ^ n - 1) → z ∣ p ^ n + 1 := fun z hz =>
    hz.trans (Nat.div_dvd_of_dvd ((Nat.gcd_dvd_left 2 (p ^ n - 1)).trans (by
      obtain ⟨k, hk⟩ := hqodd
      exact ⟨k + 1, by omega⟩)))
  have hdvd2 : ∀ z, z ∣ (p ^ n - 1) / Nat.gcd 2 (p ^ n - 1) → z ∣ p ^ n - 1 := fun z hz =>
    hz.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 2 (p ^ n - 1)))
  rcases dickson_odd hq hp2 X' hodd' with ⟨m, hm, hcard, hel⟩ | ⟨z, hz, hcard, hcyc⟩ |
    ⟨m, t, hm1, hmf, htm, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, hfaith⟩
  · right
    refine ⟨p, hp, isElementaryAbelian_of_mulEquiv eX, ?_⟩
    rw [Nat.card_congr eX.toEquiv, hcard, hq]
    exact pow_dvd_pow p hm
  · left
    refine ⟨isCyclic_of_surjective eX.symm.toMonoidHom eX.symm.surjective, ?_⟩
    rw [Nat.card_congr eX.toEquiv, hcard, hq]
    rcases hz with h | h
    · exact Or.inr (hdvd1 z h)
    · exact Or.inl (hdvd2 z h)
  · right
    have hm0 : m ≠ 0 := by omega
    have hcop : Nat.Coprime p t := by
      have h1 : Nat.Coprime p (p ^ m - 1) := by
        have h4 : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp.pos
        have h3 : Nat.Coprime (p ^ m) (p ^ m - 1) :=
          (Nat.coprime_self_sub_right h4).mpr (Nat.coprime_one_right _)
        exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p hm0) h3
      exact Nat.Coprime.coprime_dvd_right htm h1
    have hCbot : C = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [Subgroup.mem_bot]
      refine hfaith c hc (fun x hx => ?_)
      have hxp : x ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
      have hcc : orderOf c ∣ t := by
        have := Subgroup.orderOf_dvd_natCard C hc
        rwa [hCcard] at this
      have hcop2 : (orderOf c).Coprime (orderOf x) :=
        Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hxp)
          (Nat.Coprime.coprime_dvd_left hcc hcop.symm)
      exact (Group.IsNilpotent.commute_of_orderOf_coprime hcop2).eq
    have hEtop : E = ⊤ := by
      rw [hCbot, sup_bot_eq] at hsup
      exact hsup
    subst hEtop
    have hEA : CFSG.IsElementaryAbelian p X' :=
      isElementaryAbelian_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup ↥X') ≃* ↥X').symm
    refine ⟨p, hp, isElementaryAbelian_of_mulEquiv eX, ?_⟩
    rw [Nat.card_congr eX.toEquiv, ← Subgroup.card_top (G := X'), hEcard, hq]
    exact pow_dvd_pow p (by omega)


end CFSG.GH74.GLS.IVK.Proofs2
