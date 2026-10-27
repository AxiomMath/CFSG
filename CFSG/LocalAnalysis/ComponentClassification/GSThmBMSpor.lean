module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Blueprint

namespace MonsterArith

theorem two_pow_le_of_dvd {q : ℕ} (hq : Odd q) (h3 : 3 ≤ q) (h : 2 ^ 42 ∣ q * (q ^ 2 - 1)) :
    2 ^ 41 ≤ q + 1 := by
  obtain ⟨k, rfl⟩ := hq
  have hk : 1 ≤ k := by omega
  have e : (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) = 2 ^ 2 * ((2 * k + 1) * (k * (k + 1))) := by
    have h1 : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [h1, Nat.add_sub_cancel]
    ring
  rw [e, show (2 : ℕ) ^ 42 = 2 ^ 2 * 2 ^ 40 by norm_num] at h
  have h1 : 2 ^ 40 ∣ (2 * k + 1) * (k * (k + 1)) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hcop : Nat.Coprime (2 ^ 40) (2 * k + 1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (odd_two_mul_add_one k))
  have h2 : 2 ^ 40 ∣ k * (k + 1) := hcop.dvd_of_dvd_mul_left h1
  rcases Nat.even_or_odd k with hke | hko
  · have hc : Nat.Coprime (2 ^ 40) (k + 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hke.add_one)
    have h4 := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_right h2)
    norm_num at h4 ⊢
    omega
  · have hc : Nat.Coprime (2 ^ 40) k := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hko)
    have h4 := Nat.le_of_dvd (by omega) (hc.dvd_of_dvd_mul_left h2)
    norm_num at h4 ⊢
    omega

theorem prime_pow_le_of_dvd_monsterOrder {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ f ∣ Open.monsterOrder) : p ^ f ≤ 3 ^ 20 := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · norm_num
  have key : ∀ e a : ℕ, Open.monsterOrder = p ^ e * a → Nat.Coprime p a → p ^ e ≤ 3 ^ 20 →
      p ^ f ≤ 3 ^ 20 := by
    intro e a hN hpa hle
    rw [hN] at h
    exact (Nat.le_of_dvd (pow_pos hp.pos e)
      ((Nat.Coprime.pow_left f hpa).dvd_of_dvd_mul_right h)).trans hle
  have hpd : p ∣ 2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 *
      41 * 47 * 59 * 71 := (dvd_pow_self p hf.ne').trans h
  rcases hp.dvd_mul.mp hpd with hpd | h71
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h71
    exact key 1 (Open.monsterOrder / 71 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h59
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h59
    exact key 1 (Open.monsterOrder / 59 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h47
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h47
    exact key 1 (Open.monsterOrder / 47 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h41
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h41
    exact key 1 (Open.monsterOrder / 41 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h31
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h31
    exact key 1 (Open.monsterOrder / 31 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h29
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h29
    exact key 1 (Open.monsterOrder / 29 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h23
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h23
    exact key 1 (Open.monsterOrder / 23 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h19
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h19
    exact key 1 (Open.monsterOrder / 19 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h17
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h17
    exact key 1 (Open.monsterOrder / 17 ^ 1) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h13
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h13)
    exact key 3 (Open.monsterOrder / 13 ^ 3) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h11
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h11)
    exact key 2 (Open.monsterOrder / 11 ^ 2) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h7
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h7)
    exact key 6 (Open.monsterOrder / 7 ^ 6) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h5
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h5)
    exact key 9 (Open.monsterOrder / 5 ^ 9) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  rcases hp.dvd_mul.mp hpd with hpd | h3
  swap
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h3)
    exact key 20 (Open.monsterOrder / 3 ^ 20) (by norm_num [Open.monsterOrder])
      (by norm_num [Open.monsterOrder]) (by norm_num)
  exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)) hp2

theorem not_smallCentralQuotient {Y : Type} [Group Y] (h41 : 2 ^ 41 ∣ Nat.card (Y ⧸ center Y))
    (hM : Nat.card (Y ⧸ center Y) ∣ Open.monsterOrder) :
    ¬ RestrictedStd.SmallCentralQuotient Y := by
  rintro (⟨p, f, hp, hp2, -, h5, hm⟩ | ⟨⟨e7⟩⟩ | h34)
  · have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hN : 2 * Nat.card (Y ⧸ center Y) = p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [card_of_lieModel_psl_two hp2 hm]
      exact RestrictedStd.Spor.two_mul_ordA_one hqodd
    have hqM : p ^ f ∣ Open.monsterOrder := by
      have h1 : p ^ f ∣ 2 * Nat.card (Y ⧸ center Y) := by
        rw [hN]
        exact dvd_mul_right _ _
      exact ((Nat.coprime_two_right.mpr hqodd).dvd_of_dvd_mul_left h1).trans hM
    have hle := prime_pow_le_of_dvd_monsterOrder hp hp2 hqM
    have h42 : 2 ^ 42 ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [← hN, show (2 : ℕ) ^ 42 = 2 * 2 ^ 41 by norm_num]
      exact Nat.mul_dvd_mul_left 2 h41
    have hge := two_pow_le_of_dvd hqodd (by omega) h42
    norm_num at hle hge
    omega
  · rw [Nat.card_congr e7.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin] at h41
    norm_num [Nat.factorial] at h41
  · rw [card_of_lieModel_L34 h34] at h41
    norm_num at h41

end MonsterArith

theorem sporadicCase_M :
    RestrictedStd.SporadicCase .M := by
  intro A _ _ W _ hWs hWnab hCW hcat hsW a ha L hLW hne hL hstd hs
  exfalso
  obtain ⟨eW⟩ := hsW
  have hinner : ∀ α : MulAut W, ∃ w : W, α = MulAut.conj w := fun α => by
    obtain ⟨w, hw⟩ := CatLeafProof.monsterInnerInput W hWs ⟨eW⟩ α
    exact ⟨w, hw.symm⟩
  have haW : a ∈ W := RestrictedStd.mem_of_forall_inner hCW hinner a
  obtain ⟨B, hB, ⟨eB⟩⟩ := RestrictedStd.exists_isComponent_centralizer_of_mem haW hLW hL
  have ha' : orderOf (⟨a, haW⟩ : W) = 2 := by rw [Subgroup.orderOf_mk, ha]
  have hsB : RestrictedStd.SmallCentralQuotient B := RestrictedStd.smallCentralQuotient_of_mulEquiv
    eB (RestrictedStd.smallCentralQuotient_of_smallSource hs)
  obtain ⟨h41, -⟩ := CatLeafProof.monsterLocalComponentsInput W hWs ⟨eW⟩ _ ha' B hB
  obtain ⟨eG⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple eW
  have hM : Nat.card (↥B ⧸ center ↥B) ∣ Open.monsterOrder := by
    rw [← YGroups.Y443.natCard_Gmat_eq_monsterOrder, ← Nat.card_congr eG.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_subgroup_dvd_card B).trans
      (Subgroup.card_subgroup_dvd_card _))
  exact MonsterArith.not_smallCentralQuotient h41 hM hsB

end CFSG.ComponentClassification.GSThmB
