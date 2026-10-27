module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Yardstones.Md0ec50421ce4 CFSG.Open

private theorem card_pSimple_dvd_card {Y : Type} [Group Y] [Finite Y] (p : ℕ) (J : Subgroup Y) :
    Nat.card (PSimple p J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

private theorem prime_mul_card_dvd_of_not_mem {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {x : Y} (hx : orderOf x = p) {J : Subgroup Y}
    (hJ : J ≤ Subgroup.centralizer {x}) (hxJ : x ∉ J) : p * Nat.card J ∣ Nat.card Y := by
  have hcomm : ∀ (a : ↥J) (b : Subgroup.zpowers x),
      Commute (J.subtype a) ((Subgroup.zpowers x).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
    have h1 : Commute (a : Y) x := Subgroup.mem_centralizer_singleton_iff.1 (hJ a.2)
    show Commute (a : Y) (b : Y)
    rw [← hk]
    exact h1.zpow_right k
  let f : ↥J × Subgroup.zpowers x →* Y :=
    MonoidHom.noncommCoprod J.subtype (Subgroup.zpowers x).subtype hcomm
  have hinf : Subgroup.zpowers x ⊓ J = ⊥ := by
    have hle : Subgroup.zpowers x ⊓ J ≤ Subgroup.zpowers x := inf_le_left
    have hcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
    have hd : Nat.card ↥(Subgroup.zpowers x ⊓ J) ∣ p := hcard ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : Subgroup.zpowers x ⊓ J = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [h, hcard])
      have hxm : x ∈ Subgroup.zpowers x ⊓ J := by rw [heq]; exact Subgroup.mem_zpowers x
      exact hxJ hxm.2
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have h1 : (a : Y) * (b : Y) = 1 := by simpa [f] using hab
    have hbJ : (b : Y) ∈ J := by
      have : (b : Y) = (a : Y)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact J.inv_mem a.2
    have hb1 : (b : Y) ∈ Subgroup.zpowers x ⊓ J := ⟨b.2, hbJ⟩
    rw [hinf, Subgroup.mem_bot] at hb1
    have hb : b = 1 := Subtype.ext hb1
    have ha : (a : Y) = 1 := by rw [hb1, mul_one] at h1; exact h1
    have ha' : a = 1 := Subtype.ext ha
    rw [hb, ha']
    rfl
  have hdvd : Nat.card (↥J × Subgroup.zpowers x) ∣ Nat.card Y :=
    Subgroup.card_dvd_of_injective f hinj
  rw [Nat.card_prod, Nat.card_zpowers, hx, mul_comm] at hdvd
  exact hdvd

private theorem prime_mul_card_pSimple_dvd_of_mem {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {x : Y} (hx : orderOf x = p) {J : Subgroup Y}
    (hJ : J ≤ Subgroup.centralizer {x}) (hxJ : x ∈ J) :
    p * Nat.card (PSimple p J) ∣ Nat.card Y := by
  set y : ↥J := ⟨x, hxJ⟩ with hy
  have hyo : orderOf y = p := by rw [← hx, ← Subgroup.orderOf_coe]
  let π : ↥J →* PQuot p J := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcen : π y ∈ Subgroup.center (PQuot p J) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := hπ g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 (hJ g'.2)
    show (g' : Y) * x = x * g'
    exact this
  have hne : π y ≠ 1 := by
    intro h
    have hmem : y ∈ GLAPPrimeCore p ↥J := (QuotientGroup.eq_one_iff y).1 h
    have h1' : orderOf y ∣ Nat.card (CFSG.pPrimeCore p ↥J) := Subgroup.orderOf_dvd_natCard _ hmem
    have h1 : p ∣ Nat.card (CFSG.pPrimeCore p ↥J) := by rwa [hyo] at h1'
    have h2 : Nat.Coprime p (Nat.card (CFSG.pPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h2 dvd_rfl h1)
  have hpow : (π y) ^ p = 1 := by
    have h : (π y) ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rwa [hyo] at h
  have hord : orderOf (π y) = p := orderOf_eq_prime hpow hne
  have hdvd : p ∣ Nat.card (Subgroup.center (PQuot p J)) := by
    have := Subgroup.orderOf_dvd_natCard _ hcen
    rwa [hord] at this
  have hbc := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot p J))
  have h1 : p * Nat.card (PSimple p J) ∣ Nat.card (PQuot p J) := by
    rw [hbc, mul_comm]
    exact Nat.mul_dvd_mul_left _ hdvd
  have h2 : Nat.card (PQuot p J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  exact h1.trans (h2.trans (Subgroup.card_subgroup_dvd_card J))

theorem prime_mul_card_pSimple_dvd {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {x : Y} (hx : orderOf x = p) {J : Subgroup Y} (hJ : J ≤ Subgroup.centralizer {x}) :
    p * Nat.card (PSimple p J) ∣ Nat.card Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hxJ : x ∈ J
  · exact prime_mul_card_pSimple_dvd_of_mem hx hJ hxJ
  · exact (Nat.mul_dvd_mul_left p (card_pSimple_dvd_card p J)).trans
      (prime_mul_card_dvd_of_not_mem hp hx hJ hxJ)

end CFSG.LocalAnalysis.GLTheoremA.H1420
