module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Sporadic.SmallOddCore

variable {G : Type*} [Group G]

theorem orderOf_mul_eq_three_of_cube {d e : G} (hd : d * d = 1)
    (h : d * e * (d * e) * (d * e) = 1) (hne : d * e ≠ e * d) : orderOf (d * e) = 3 := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have h3 : (d * e) ^ 3 = 1 := by rw [pow_succ, pow_succ, pow_one]; exact h
  have h1 : d * e ≠ 1 := by
    intro h1
    apply hne
    have : e = d⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, hdi]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 h1

theorem cube_eq_one_of_orderOf {d e : G} (hd : d * d = 1) (he : e * e = 1)
    (h : orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) (hne : d * e ≠ e * d) :
    d * e * (d * e) * (d * e) = 1 := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  rcases h with h | h | h
  · exfalso
    apply hne
    have h1 : d * e = 1 := orderOf_eq_one_iff.1 h
    have : e = d⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this, hdi]
  · exfalso
    apply hne
    have h2 : (d * e) ^ 2 = 1 := h ▸ pow_orderOf_eq_one (d * e)
    have h3 : (d * e) * (d * e) = 1 := by rw [← sq]; exact h2
    have h4 : d * e = (d * e)⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [h4, mul_inv_rev, hdi, hei]
  · have h3 : (d * e) ^ 3 = 1 := h ▸ pow_orderOf_eq_one (d * e)
    rw [pow_succ, pow_succ, pow_one] at h3
    exact h3

theorem commute_of_separated {E : Set G} (hE2 : ∀ e ∈ E, e * e = 1)
    (hE3 : ∀ e ∈ E, ∀ f ∈ E, e * f ≠ f * e → e * f * (e * f) * (e * f) = 1)
    {N : Subgroup G} (hN : ∀ g ∈ N, orderOf g ≠ 3) {D₀ : Set G} (hD₀ : D₀ ⊆ E)
    (hnorm : ∀ d ∈ D₀, ∀ n ∈ N, d * n * d⁻¹ ∈ N)
    (hstab : ∀ d ∈ D₀, ∀ n ∈ N, n⁻¹ * d * n ∈ D₀)
    (hsep : ∀ d ∈ D₀, ∀ d' ∈ D₀, d ≠ d' → d * d' = d' * d →
      ∃ e ∈ D₀, e * d' = d' * e ∧ e * d ≠ d * e) :
    ∀ n ∈ N, ∀ d ∈ D₀, n * d = d * n := by
  intro n hn d hd
  set d' := n⁻¹ * d * n with hd'def
  have hd'D : d' ∈ D₀ := hstab d hd n hn
  have hdd : d * d = 1 := hE2 d (hD₀ hd)
  have hdd' : d' * d' = 1 := hE2 d' (hD₀ hd'D)
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hz : d * d' ∈ N := by
    have h1 : d * n⁻¹ * d⁻¹ ∈ N := hnorm d hd _ (N.inv_mem hn)
    have h2 : d * d' = d * n⁻¹ * d⁻¹ * n := by rw [hd'def, hdi]; group
    rw [h2]
    exact N.mul_mem h1 hn
  have hc : d * d' = d' * d := by
    by_contra hne
    exact hN _ hz (orderOf_mul_eq_three_of_cube hdd (hE3 d (hD₀ hd) d' (hD₀ hd'D) hne) hne)
  have heq : d = d' := by
    by_contra hne
    obtain ⟨e, heD, he1, he2⟩ := hsep d hd d' hd'D hne hc
    have hee : e * e = 1 := hE2 e (hD₀ heD)
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
    have hw : d * d' * (e * (d * d') * e⁻¹) ∈ N :=
      N.mul_mem hz (hnorm e heD _ hz)
    have hc1 : d' * e = e * d' := he1.symm
    have hc2 : d' * d = d * d' := hc.symm
    have hcalc : d * d' * (e * (d * d') * e⁻¹) = (d * e) ^ 2 := by
      rw [hei, sq]
      calc d * d' * (e * (d * d') * e) = d * (d' * e) * d * (d' * e) := by group
        _ = d * (e * d') * d * (e * d') := by rw [hc1]
        _ = d * e * (d' * d) * e * d' := by group
        _ = d * e * (d * d') * e * d' := by rw [hc2]
        _ = d * e * d * (d' * e) * d' := by group
        _ = d * e * d * (e * d') * d' := by rw [hc1]
        _ = d * e * d * e * (d' * d') := by group
        _ = d * e * (d * e) := by rw [hdd']; group
    rw [hcalc] at hw
    have h3 : orderOf (d * e) = 3 := orderOf_mul_eq_three_of_cube hdd
      (hE3 d (hD₀ hd) e (hD₀ heD) (fun h => he2 h.symm)) (fun h => he2 h.symm)
    have h4 : orderOf ((d * e) ^ 2) = 3 := by
      have h5 := orderOf_pow' (d * e) (two_ne_zero : (2 : ℕ) ≠ 0)
      rw [h3] at h5
      rw [h5]
      norm_num
    exact hN _ hw h4
  have : n⁻¹ * d * n = d := heq.symm
  calc n * d = n * (n⁻¹ * d * n) := by rw [this]
    _ = d * n := by group

theorem gLAPPrimeCoreOf_eq_bot_of_separated [Finite G] {E : Set G} (hE2 : ∀ e ∈ E, e * e = 1)
    (hE3 : ∀ e ∈ E, ∀ f ∈ E, e * f ≠ f * e → e * f * (e * f) * (e * f) = 1)
    (hEc : ∀ e ∈ E, ∀ g : G, g * e * g⁻¹ ∈ E) {s : G}
    (hsep : ∀ d ∈ E, d * s = s * d → ∀ d' ∈ E, d' * s = s * d' → d ≠ d' → d * d' = d' * d →
      ∃ e ∈ E, e * s = s * e ∧ e * d' = d' * e ∧ e * d ≠ d * e)
    (hY : ∀ y : G, y * s = s * y → (∀ d ∈ E, d * s = s * d → y * d = d * y) → y * y * y = 1) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  set C := Subgroup.centralizer ({s} : Set G) with hC
  set N := GLAPPrimeCoreOf 3 C with hNdef
  have hcop : Nat.Coprime 3 (Nat.card N) := coprime_card_GLAPPrimeCoreOf Nat.prime_three C
  have hN : ∀ g ∈ N, orderOf g ≠ 3 := by
    intro g hg h3
    have hdvd : orderOf g ∣ Nat.card N := by
      have := Subgroup.orderOf_dvd_natCard N hg
      exact this
    rw [h3] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop hdvd
  have hmemC : ∀ g : G, g ∈ C ↔ g * s = s * g := fun g => by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
  set D₀ : Set G := {d | d ∈ E ∧ d * s = s * d} with hD₀
  have hcomm := commute_of_separated hE2 hE3 hN (D₀ := D₀) (fun d hd => hd.1)
    (fun d hd n hn => GLAPPrimeCoreOf_conj_mem d ((hmemC d).2 hd.2) n hn)
    (fun d hd n hn => by
      have hnC : n ∈ C := GLAPPrimeCoreOf_le C hn
      refine ⟨?_, ?_⟩
      · have := hEc d hd.1 n⁻¹
        simpa using this
      · exact (hmemC _).1 (C.mul_mem (C.mul_mem (C.inv_mem hnC) ((hmemC d).2 hd.2)) hnC))
    (fun d hd d' hd' hne hdd' => by
      obtain ⟨e, heE, hes, he1, he2⟩ := hsep d hd.1 hd.2 d' hd'.1 hd'.2 hne hdd'
      exact ⟨e, ⟨heE, hes⟩, he1, he2⟩)
  rw [eq_bot_iff]
  intro n hn
  have hnC : n ∈ C := GLAPPrimeCoreOf_le C hn
  have h3 : n ^ 3 = 1 := by
    rw [pow_succ, pow_succ, pow_one]
    exact hY n ((hmemC n).1 hnC) fun d hdE hds => hcomm n hn d ⟨hdE, hds⟩
  have hdvd : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · rw [orderOf_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _
  · exact absurd h1 (hN n hn)

theorem gLAPPrimeCoreOf_eq_bot_of_card_le [Finite G] {p : ℕ} (hp : p.Prime) {C P : Subgroup G}
    (hPC : P ≤ C) (hPp : IsPGroup p P) {r m : ℕ}
    (hL : Nat.card (GLAPPrimeCoreOf p C) ≤ r) (hlt : r * m < Nat.card P)
    (h2 : ∀ q : ℕ, q.Prime → q ∣ Nat.card (GLAPPrimeCoreOf p C) → q = 2)
    (hm : ∀ w ∈ GLAPPrimeCoreOf p C, w * w = 1 → w ≠ 1 → ∀ Q : Subgroup G, IsPGroup p Q →
      Q ≤ Subgroup.centralizer ({w} : Set G) → Nat.card Q ≤ m) :
    GLAPPrimeCoreOf p C = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  set L := GLAPPrimeCoreOf p C with hLdef
  have hLne : Nat.card L ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨q, hq, hqL⟩ := Nat.exists_prime_and_dvd hLne
  have hq2 : q = 2 := h2 q hq hqL
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) q hqL
  set w : G := (x : G) with hw
  have hwo : orderOf w = 2 := by rw [hw, Subgroup.orderOf_coe, hx, hq2]
  have hwL : w ∈ L := x.2
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo, sq] at this
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hwo; omega
  have hcls : conjClass P w ⊆ (L : Set G) := by
    rintro _ ⟨g, hg, rfl⟩
    exact GLAPPrimeCoreOf_conj_mem g (hPC hg) w hwL
  have hncard : (conjClass P w).ncard ≤ r := by
    calc (conjClass P w).ncard ≤ (L : Set G).ncard := Set.ncard_le_ncard hcls (Set.toFinite _)
      _ = Nat.card L := (Nat.card_coe_set_eq (L : Set G)).symm
      _ ≤ r := hL
  have horb := ncard_conjClass_mul_card P w
  have hQ : Nat.card ↥(P ⊓ Subgroup.centralizer ({w} : Set G)) ≤ m :=
    hm w hwL hww hw1 _ (hPp.to_le inf_le_left) inf_le_right
  have : Nat.card P ≤ r * m := by
    rw [← horb]
    exact Nat.mul_le_mul hncard hQ
  omega

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
