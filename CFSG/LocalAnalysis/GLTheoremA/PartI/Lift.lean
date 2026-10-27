module

public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

private theorem mem_normalizer_inf_lift {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (hA h) (hB h)

private theorem card_eq_pow_mul_of_pow_mem {p : ℕ} (hp : p.Prime) {O X : Subgroup G}
    (hOX : O ≤ X) (hXN : X ≤ Subgroup.normalizer (O : Set G))
    (hq : ∀ x ∈ X, ∃ k : ℕ, x ^ (p ^ k) ∈ O) :
    ∃ j : ℕ, Nat.card X = p ^ j * Nat.card O := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (O.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).2 hXN
  have hQ : IsPGroup p (↥X ⧸ O.subgroupOf X) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := hq x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 hk
  obtain ⟨j, hj⟩ := hQ.exists_card_eq
  have hidx : (O.subgroupOf X).index = p ^ j := hj
  have hcard : Nat.card (O.subgroupOf X) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOX).toEquiv
  have hmul : (O.subgroupOf X).index * Nat.card (O.subgroupOf X) = Nat.card X :=
    Subgroup.index_mul_card _
  rw [hidx, hcard] at hmul
  exact ⟨j, hmul.symm⟩

theorem exists_pGroup_lift {p : ℕ} (hp : p.Prime) {O E' D N : Subgroup G}
    (hO : ¬ p ∣ Nat.card O) (hOE : O ≤ E') (hEN : E' ≤ Subgroup.normalizer (O : Set G))
    (hEp : ∀ e ∈ E', ∃ k : ℕ, e ^ (p ^ k) ∈ O) (hD : IsPGroup p D)
    (hDE : D ≤ Subgroup.normalizer (E' : Set G)) (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hNO : N ≤ Subgroup.normalizer (O : Set G)) (hENO : E' ≤ N ⊔ O) :
    ∃ W : Subgroup G, W ≤ N ⊓ E' ∧ IsPGroup p W ∧ D ≤ Subgroup.normalizer (W : Set G) ∧
      W ⊔ O = E' := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : Subgroup G, N₂ = N ⊓ E' := ⟨_, rfl⟩
  have hN₂E : N₂ ≤ E' := by rw [hN₂]; exact inf_le_right
  have hN₂N : N₂ ≤ N := by rw [hN₂]; exact inf_le_left
  have hN₂O : N₂ ≤ Subgroup.normalizer (O : Set G) := hN₂N.trans hNO
  have hDN₂ : D ≤ Subgroup.normalizer (N₂ : Set G) := fun d hd => by
    rw [hN₂]
    exact mem_normalizer_inf_lift (hDN hd) (hDE hd)
  have hsup : N₂ ⊔ O = E' := by
    refine le_antisymm (sup_le hN₂E hOE) ?_
    intro e he
    have hmem : e ∈ (N ⊔ O : Subgroup G) := hENO he
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right N O hNO] at hmem
    obtain ⟨n, hn, o, ho, hno⟩ := Set.mem_mul.1 hmem
    have hnE : n ∈ E' := by
      have hn' : n = e * o⁻¹ := by rw [← hno, mul_inv_cancel_right]
      rw [hn']
      exact E'.mul_mem he (E'.inv_mem (hOE ho))
    have hnN₂ : n ∈ N₂ := by
      rw [hN₂]
      exact ⟨hn, hnE⟩
    rw [← hno]
    exact Subgroup.mul_mem_sup hnN₂ ho
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, H = D ⊔ N₂ := ⟨_, rfl⟩
  have hDH' : D ≤ H := by rw [hH]; exact le_sup_left
  have hN₂H : N₂ ≤ H := by rw [hH]; exact le_sup_right
  have hHN : H ≤ Subgroup.normalizer (N₂ : Set G) := by
    rw [hH]
    exact sup_le hDN₂ Subgroup.le_normalizer
  have hDHp : IsPGroup p (D.subgroupOf H) :=
    hD.of_equiv (Subgroup.subgroupOfEquivOfLe hDH').symm
  obtain ⟨P, hDP⟩ := IsPGroup.exists_le_sylow hDHp
  obtain ⟨Pg, hPg⟩ : ∃ Pg : Subgroup G, Pg = (P : Subgroup H).map H.subtype := ⟨_, rfl⟩
  have hPgH : Pg ≤ H := by rw [hPg]; exact Subgroup.map_subtype_le _
  have hPgp : IsPGroup p Pg := by rw [hPg]; exact P.isPGroup'.map H.subtype
  have hDPg : D ≤ Pg := by
    intro d hd
    have hdH : d ∈ H := hDH' hd
    have hmem0 : (⟨d, hdH⟩ : ↥H) ∈ D.subgroupOf H := Subgroup.mem_subgroupOf.2 hd
    have hmem : (⟨d, hdH⟩ : ↥H) ∈ (P : Subgroup H) := hDP hmem0
    rw [hPg]
    exact Subgroup.mem_map_of_mem _ hmem
  have hPcard : Nat.card (P : Subgroup H) = Nat.card Pg := by
    rw [hPg]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv
  have hHP : Nat.card H = (P : Subgroup H).index * Nat.card Pg := by
    rw [← hPcard]
    exact (Subgroup.index_mul_card _).symm
  have hPnd : ¬ p ∣ (P : Subgroup H).index := Sylow.not_dvd_index P
  have hPgN : Pg ≤ Subgroup.normalizer (N₂ : Set G) := hPgH.trans hHN
  have hid := card_sup_mul_card_inf_of_le_normalizer hPgN
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le (inf_le_left : N₂ ⊓ Pg ≤ N₂)
  have hWpos : 0 < Nat.card (N₂ ⊓ Pg : Subgroup G) := Nat.card_pos
  have hqpos : 0 < Nat.card Pg := Nat.card_pos
  have htq : Nat.card (N₂ ⊔ Pg : Subgroup G) = t * Nat.card Pg := by
    apply Nat.eq_of_mul_eq_mul_left hWpos
    rw [mul_comm (Nat.card (N₂ ⊓ Pg : Subgroup G)), hid, ht]
    ring
  have hdvd : Nat.card (N₂ ⊔ Pg : Subgroup G) ∣ Nat.card H :=
    Subgroup.card_dvd_of_le (sup_le hN₂H hPgH)
  rw [htq, hHP] at hdvd
  have htidx : t ∣ (P : Subgroup H).index := Nat.dvd_of_mul_dvd_mul_right hqpos hdvd
  have htp : ¬ p ∣ t := fun h => hPnd (h.trans htidx)
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = ((N₂ ⊓ Pg) ⊔ O) ⊓ N₂ := ⟨_, rfl⟩
  have hKN₂ : K ≤ N₂ := by rw [hK]; exact inf_le_right
  have hKW : N₂ ⊓ Pg ≤ K := by
    rw [hK]
    exact le_inf le_sup_left inf_le_left
  have hKO : O ⊓ N₂ ≤ K := by
    rw [hK]
    exact le_inf (inf_le_left.trans le_sup_right) inf_le_right
  have hKle : K ≤ (N₂ ⊓ Pg) ⊔ O := by rw [hK]; exact inf_le_left
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hKN₂
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hKW
  obtain ⟨r', hr'⟩ := Subgroup.card_dvd_of_le hKO
  have hOsup : O ⊔ N₂ = E' := by rw [sup_comm]; exact hsup
  obtain ⟨j, hj⟩ := card_eq_pow_mul_of_pow_mem hp hOE hEN hEp
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hmpos : 0 < Nat.card (O ⊓ N₂ : Subgroup G) := Nat.card_pos
  have hm : Nat.card N₂ = Nat.card (O ⊓ N₂ : Subgroup G) * p ^ j := by
    have h := card_sup_mul_card_inf_of_le_normalizer hN₂O
    rw [hOsup, hj] at h
    apply Nat.eq_of_mul_eq_mul_left hOpos
    rw [← h]
    ring
  have hkt : t = r * k := by
    apply Nat.eq_of_mul_eq_mul_left hWpos
    rw [← ht, hk, hr]
    ring
  have hpr : r' * k = p ^ j := by
    apply Nat.eq_of_mul_eq_mul_left hmpos
    rw [← hm, hk, hr']
    ring
  have hkt' : k ∣ t := Dvd.intro_left r hkt.symm
  have hkp : k ∣ p ^ j := Dvd.intro_left r' hpr
  have hkp' : ¬ p ∣ k := fun h => htp (h.trans hkt')
  have hcop : Nat.Coprime k (p ^ j) :=
    Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hkp').symm
  have hk1 : k = 1 := Nat.Coprime.eq_one_of_dvd hcop hkp
  have hKeq : K = N₂ := by
    apply Subgroup.eq_of_le_of_card_ge hKN₂
    rw [hk, hk1, mul_one]
  have hN₂sub : N₂ ≤ (N₂ ⊓ Pg) ⊔ O := (le_of_eq hKeq.symm).trans hKle
  refine ⟨N₂ ⊓ Pg, (inf_le_left : N₂ ⊓ Pg ≤ N₂).trans (le_of_eq hN₂), hPgp.to_le inf_le_right,
    ?_, ?_⟩
  · intro d hd
    have hdPg : d ∈ Pg := hDPg hd
    exact mem_normalizer_inf_lift (hDN₂ hd) (Subgroup.le_normalizer hdPg)
  · refine le_antisymm (sup_le (inf_le_left.trans hN₂E) hOE) ?_
    rw [← hsup]
    exact sup_le hN₂sub le_sup_right

theorem exists_two_subgroup_lift {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {O T' E : Subgroup G}
    (hO : ¬ p ∣ Nat.card O) (hOT : O < T') (hTN : T' ≤ Subgroup.normalizer (O : Set G))
    (hT2 : ∀ t ∈ T', ∃ k : ℕ, t ^ (2 ^ k) ∈ O) (hE : IsPGroup p E)
    (hET : E ≤ Subgroup.normalizer (T' : Set G)) :
    ∃ T : Subgroup G, T ≤ T' ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := card_eq_pow_mul_of_pow_mem Nat.prime_two hOT.le hTN hT2
  have hTp : ¬ p ∣ Nat.card T' := by
    rw [hj]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
    · exact hO h1
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hj
    exact hOT.ne (Subgroup.eq_of_le_of_card_ge hOT.le hj.le)
  have h2T : 2 ∣ Nat.card T' := by
    rw [hj]
    exact (dvd_pow_self 2 hj0).mul_right _
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_sylow_normalized (r := 2) hET hE hTp
  refine ⟨(P : Subgroup T').map T'.subtype, Subgroup.map_subtype_le _, ?_,
    P.isPGroup'.map T'.subtype, hP⟩
  intro h
  apply P.ne_bot_of_dvd_card h2T
  exact (Subgroup.map_eq_bot_iff_of_injective _ T'.subtype_injective).1 h

theorem exists_two_subgroup_of_even {p : ℕ} (hp : p.Prime) {O E : Subgroup G}
    (hO : ¬ p ∣ Nat.card O) (hO2 : 2 ∣ Nat.card O) (hE : IsPGroup p E)
    (hEO : E ≤ Subgroup.normalizer (O : Set G)) :
    ∃ T : Subgroup G, T ≤ O ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_sylow_normalized (r := 2) hEO hE hO
  refine ⟨(P : Subgroup O).map O.subtype, Subgroup.map_subtype_le _, ?_,
    P.isPGroup'.map O.subtype, hP⟩
  intro h
  apply P.ne_bot_of_dvd_card hO2
  exact (Subgroup.map_eq_bot_iff_of_injective _ O.subtype_injective).1 h

end CFSG.LocalAnalysis.GLTheoremA
