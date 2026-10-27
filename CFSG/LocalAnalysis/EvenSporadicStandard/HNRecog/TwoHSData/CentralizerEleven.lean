module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ProdCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup

private lemma prime_eq_of_dvd_two_pow_mul (p : ℕ) (hp : p.Prime)
    (h : p ∣ 2 ^ 11 * 3 ^ 2 * 5 ^ 3 * 7 * 11) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  rcases hp.dvd_mul.mp h with h | h11
  · rcases hp.dvd_mul.mp h with h | h7
    · rcases hp.dvd_mul.mp h with h | h5
      · rcases hp.dvd_mul.mp h with h2 | h3
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
        · exact Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)))
      · exact Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp (hp.dvd_of_dvd_pow h5))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h7))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_eleven).mp h11))))

private lemma eleven_dvd_centralizer_of_comm {G : Type*} [Group G] {x e : G}
    (hx : orderOf x = 11) (hcomm : x * e = e * x) :
    11 ∣ Nat.card ↥(Subgroup.centralizer ({e} : Set G)) := by
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  have h := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, hx] at h

theorem centralizer_eleven_of_data {G : Type} [Group G] [Finite G] (a : G)
    (hcard : Nat.card G = 2 ^ 11 * 3 ^ 2 * 5 ^ 3 * 7 * 11) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hacen : ∀ g : G, g * a = a * g)
    (h3 : ∀ e : G, orderOf e = 3 → ¬ 11 ∣ Nat.card ↥(centralizer ({e} : Set G)))
    (h5 : ∀ e : G, orderOf e = 5 → ¬ 11 ∣ Nat.card ↥(centralizer ({e} : Set G)))
    (h7 : ∀ e : G, orderOf e = 7 → ¬ 11 ∣ Nat.card ↥(centralizer ({e} : Set G)))
    (h2 : ∀ e : G, orderOf e = 2 → e ≠ a → ¬ 11 ∣ Nat.card ↥(centralizer ({e} : Set G)))
    (h4 : ∀ g : G, g * g = a → ¬ 11 ∣ Nat.card ↥(centralizer ({g} : Set G))) :
    ∀ x : G, orderOf x = 11 → IsShapeCentralizerEleven ↥(centralizer ({x} : Set G)) := by
  intro x hx
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  change IsShapeCentralizerEleven ↥C
  have hxC : x ∈ C := by
    change x ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
  have haC : a ∈ C := by
    change a ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hacen x).symm
  let aC : ↥C := ⟨a, haC⟩
  have hoa : orderOf a = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rwa [pow_two]) ha1
  have h2dvd : 2 ∣ Nat.card ↥C := by
    have h := Subgroup.orderOf_dvd_natCard C haC
    rwa [hoa] at h
  have h11dvd : 11 ∣ Nat.card ↥C := by
    have h := Subgroup.orderOf_dvd_natCard C hxC
    rwa [hx] at h
  have hpC_eq : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥C → p = 2 ∨ p = 11 := by
    intro p hp hpC
    have hpG : p ∣ Nat.card G := hpC.trans (Subgroup.card_subgroup_dvd_card C)
    have hmem := prime_eq_of_dvd_two_pow_mul p hp (by rwa [hcard] at hpG)
    rcases hmem with hp2 | hp3 | hp5 | hp7 | hp11
    · exact Or.inl hp2
    · exfalso
      have h3dvd : 3 ∣ Nat.card ↥C := hp3 ▸ hpC
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) (p := 3) h3dvd
      have heG : orderOf (e : G) = 3 := by rw [Subgroup.orderOf_coe, he]
      have hcomm : x * (e : G) = (e : G) * x :=
        (Subgroup.mem_centralizer_singleton_iff.mp e.2).symm
      exact (h3 (e : G) heG) (eleven_dvd_centralizer_of_comm hx hcomm)
    · exfalso
      have h5dvd : 5 ∣ Nat.card ↥C := hp5 ▸ hpC
      haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) (p := 5) h5dvd
      have heG : orderOf (e : G) = 5 := by rw [Subgroup.orderOf_coe, he]
      have hcomm : x * (e : G) = (e : G) * x :=
        (Subgroup.mem_centralizer_singleton_iff.mp e.2).symm
      exact (h5 (e : G) heG) (eleven_dvd_centralizer_of_comm hx hcomm)
    · exfalso
      have h7dvd : 7 ∣ Nat.card ↥C := hp7 ▸ hpC
      haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
      obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) (p := 7) h7dvd
      have heG : orderOf (e : G) = 7 := by rw [Subgroup.orderOf_coe, he]
      have hcomm : x * (e : G) = (e : G) * x :=
        (Subgroup.mem_centralizer_singleton_iff.mp e.2).symm
      exact (h7 (e : G) heG) (eleven_dvd_centralizer_of_comm hx hcomm)
    · exact Or.inr hp11
  have h4not : ¬ 4 ∣ Nat.card ↥C := by
    intro h4dvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let P : Sylow 2 ↥C := default
    have hPsub_le : ∀ t : ↥(P : Subgroup ↥C), (t : ↥C) = 1 ∨ (t : ↥C) = aC := by
      intro t
      by_cases ht : (t : ↥C) = 1
      · exact Or.inl ht
      · right
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).mp P.isPGroup' t
        have hk0 : k ≠ 0 := by
          intro hk0
          apply ht
          have htP : t = 1 := orderOf_eq_one_iff.mp (by rw [hk, hk0]; norm_num)
          rw [htP]
          rfl
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        let w : ↥C := t
        have hw : orderOf w = 2 ^ k := by
          change orderOf (t : ↥C) = 2 ^ k
          rw [Subgroup.orderOf_coe, hk]
        let s : ↥C := w ^ (2 ^ (k - 1))
        have hs2 : s * s = 1 := by
          have h1 : (2 : ℕ) ^ (k - 1) * 2 = 2 ^ k := by
            rw [← Nat.pow_succ]
            congr 1
            omega
          have hmid : s * s = w ^ (2 ^ k) := by
            change (w ^ (2 ^ (k - 1))) * (w ^ (2 ^ (k - 1))) = w ^ (2 ^ k)
            rw [← pow_two, ← pow_mul, h1]
          rw [hmid, ← hw, pow_orderOf_eq_one]
        have hs1 : s ≠ 1 := by
          intro hs
          have hdvd : orderOf w ∣ 2 ^ (k - 1) :=
            orderOf_dvd_iff_pow_eq_one.mpr (show w ^ (2 ^ (k - 1)) = 1 from hs)
          rw [hw] at hdvd
          have hle : k ≤ k - 1 :=
            (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2 : ℕ))).mp hdvd
          omega
        have hsorder : orderOf s = 2 := by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact orderOf_eq_prime (by rwa [pow_two]) hs1
        have hsG_order : orderOf (s : G) = 2 := by
          rw [Subgroup.orderOf_coe, hsorder]
        have hs_comm : x * (s : G) = (s : G) * x :=
          (Subgroup.mem_centralizer_singleton_iff.mp s.2).symm
        have hs_eq_a : s = aC := by
          by_cases hsa : (s : G) = a
          · exact Subtype.ext hsa
          · exfalso
            exact (h2 (s : G) hsG_order hsa) (eleven_dvd_centralizer_of_comm hx hs_comm)
        by_cases hk1' : k = 1
        · have hws : w = s := by
            change w = w ^ (2 ^ (k - 1))
            rw [hk1']
            norm_num
          change w = aC
          rw [hws]
          exact hs_eq_a
        · exfalso
          have hk2 : 2 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk1 (Ne.symm hk1'))
          let u : ↥C := w ^ (2 ^ (k - 2))
          have hu2 : (u : G) * (u : G) = a := by
            have h1 : (2 : ℕ) ^ (k - 2) * 2 = 2 ^ (k - 1) := by
              rw [← Nat.pow_succ]
              congr 1
              omega
            have hsub : u * u = aC := by
              have hmid : u * u = w ^ (2 ^ (k - 1)) := by
                change (w ^ (2 ^ (k - 2))) * (w ^ (2 ^ (k - 2))) = w ^ (2 ^ (k - 1))
                rw [← pow_two, ← pow_mul, h1]
              rw [hmid, show w ^ (2 ^ (k - 1)) = s from rfl]
              exact hs_eq_a
            simpa using congrArg Subtype.val hsub
          have hu_comm : x * (u : G) = (u : G) * x :=
            (Subgroup.mem_centralizer_singleton_iff.mp u.2).symm
          exact (h4 (u : G) hu2) (eleven_dvd_centralizer_of_comm hx hu_comm)
    have hPle_zpowers : (P : Subgroup ↥C) ≤ Subgroup.zpowers aC := by
      intro t ht
      rcases hPsub_le ⟨t, ht⟩ with h | h
      · have h1 : t = 1 := h
        rw [h1]
        exact Subgroup.one_mem _
      · have h2 : t = aC := h
        rw [h2]
        exact Subgroup.mem_zpowers aC
    have hPcard_le : Nat.card P ≤ 2 := by
      have hdvd : Nat.card ↥(P : Subgroup ↥C) ∣ Nat.card ↥(Subgroup.zpowers aC) :=
        Subgroup.card_dvd_of_le hPle_zpowers
      rw [Nat.card_zpowers] at hdvd
      have hoaC : orderOf aC = 2 := by
        rw [← Subgroup.orderOf_coe aC]
        exact hoa
      rw [hoaC] at hdvd
      simpa using Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    have hPcard : Nat.card P = 2 ^ (Nat.card ↥C).factorization 2 := P.card_eq_multiplicity
    have hfac : 2 ≤ (Nat.card ↥C).factorization 2 := by
      have hC_ne : Nat.card ↥C ≠ 0 := by
        haveI : Nonempty ↥C := ⟨1⟩
        exact Nat.card_pos.ne'
      exact (Nat.prime_two.pow_dvd_iff_le_factorization hC_ne).mp (by simpa using h4dvd)
    have hP4 : 4 ∣ Nat.card P := by
      rw [hPcard]
      simpa using pow_dvd_pow (2 : ℕ) hfac
    have hle4 : 4 ≤ Nat.card P := by
      haveI : Nonempty P := ⟨1⟩
      exact Nat.le_of_dvd Nat.card_pos hP4
    omega
  have h121G : ¬ 11 ^ 2 ∣ Nat.card G := by
    rw [hcard]
    norm_num
  have h121not : ¬ 11 ^ 2 ∣ Nat.card ↥C :=
    fun h => h121G (h.trans (Subgroup.card_subgroup_dvd_card C))
  have hC_dvd_22 : Nat.card ↥C ∣ 22 := by
    refine (Nat.dvd_iff_prime_pow_dvd_dvd 22 (Nat.card ↥C)).mpr ?_
    intro p k hp hpk
    by_cases hk : k = 0
    · rw [hk]
      simp
    · have hpdvd : p ∣ Nat.card ↥C := dvd_trans (dvd_pow_self p hk) hpk
      rcases hpC_eq p hp hpdvd with hp2 | hp11
      · rw [hp2] at hpk ⊢
        have hk_le : k ≤ 1 := Nat.le_of_not_lt (by
          intro h1
          have h2k : 2 ≤ k := Nat.succ_le_of_lt h1
          exact h4not (by simpa using dvd_trans (pow_dvd_pow 2 h2k) hpk))
        have hk_eq : k = 1 := le_antisymm hk_le (Nat.one_le_iff_ne_zero.mpr hk)
        rw [hk_eq]
        norm_num
      · rw [hp11] at hpk ⊢
        have hk_le : k ≤ 1 := Nat.le_of_not_lt (by
          intro h1
          have h2k : 2 ≤ k := Nat.succ_le_of_lt h1
          exact h121not (dvd_trans (pow_dvd_pow 11 h2k) hpk))
        have hk_eq : k = 1 := le_antisymm hk_le (Nat.one_le_iff_ne_zero.mpr hk)
        rw [hk_eq]
        norm_num
  have h22dvd : 22 ∣ Nat.card ↥C := by
    have hcop : Nat.Coprime 2 11 := by decide
    simpa using hcop.mul_dvd_of_dvd_of_dvd h2dvd h11dvd
  have hCcard : Nat.card ↥C = 22 := Nat.dvd_antisymm hC_dvd_22 h22dvd
  let V : Subgroup G := Subgroup.zpowers a
  let S : Subgroup G := Subgroup.zpowers x
  have hVcard : Nat.card ↥V = 2 := by
    change Nat.card ↥(Subgroup.zpowers a) = 2
    rw [Nat.card_zpowers, hoa]
  have hScard : Nat.card ↥S = 11 := by
    change Nat.card ↥(Subgroup.zpowers x) = 11
    rw [Nat.card_zpowers, hx]
  have hVX : V ≤ C := Subgroup.zpowers_le.mpr haC
  have hSX : S ≤ C := Subgroup.zpowers_le.mpr hxC
  have hza : V ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hacen)
  have hVcen : ∀ v ∈ V, ∀ y ∈ C, y * v = v * y := by
    intro v hv y hy
    exact (Subgroup.mem_center_iff.mp (hza hv)) y
  have hVS : ∀ v ∈ V, v ∈ S → v = 1 := by
    have hcop : Nat.Coprime (Nat.card ↥V) (Nat.card ↥S) := by
      rw [hVcard, hScard]
      decide
    have hbot : V ⊓ S = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
    intro v hv hvS
    have hmem : v ∈ V ⊓ S := ⟨hv, hvS⟩
    rw [hbot] at hmem
    simpa using hmem
  have hX : Nat.card ↥C = Nat.card ↥V * Nat.card ↥S := by
    rw [hVcard, hScard, hCcard]
  obtain ⟨eX⟩ := nonempty_mulEquiv_prod_of_central C V S hVX hSX hVcen hVS hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  have eV : ↥V ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hVcard (by simp [ZMod.card])
  have eS : ↥S ≃* Multiplicative (ZMod 11) :=
    mulEquivOfPrimeCardEq hScard (by simp [ZMod.card])
  exact ⟨eX.trans ((MulEquiv.prodCongr eV eS).trans MulEquiv.prodComm)⟩

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
