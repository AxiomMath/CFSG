module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Layer0
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.AutModel

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def tC (t : G) : ↥(centralizer ({t} : Set G)) :=
  ⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem le_centralizer_singleton {t : G} (ht : t ∈ centralizer (L : Set G)) :
    L ≤ centralizer ({t} : Set G) := by
  intro l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.1 ht l hl

theorem normal_subgroupOf_centralizer (h : StdHyp G L) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    (L.subgroupOf (centralizer ({t} : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_centralizer_singleton (t := t) ht)).2
    (h.centralizer_le_normalizer ht ht2)

theorem card_of_isSporadic_m12 (hL : IsSporadic L .M12) :
    Nat.card ↥L = 95040 := by
  obtain ⟨e⟩ := hL
  exact (Nat.card_congr e.toEquiv).trans m12_card

theorem exists_equiv_D24
    (hL : IsSporadic L .M12) {t : G} (ht : t ∈ centralizer (L : Set G)) :
    Nonempty (↥(L.subgroupOf (centralizer ({t} : Set G))) ≃* ↥D24) := by
  obtain ⟨e⟩ := hL
  exact ⟨(Subgroup.subgroupOfEquivOfLe (le_centralizer_singleton (t := t) ht)).trans
    (e.trans m12EquivD)⟩

theorem not_mem_of_isSporadic_m12
    (hL : IsSporadic L .M12) {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    t ∉ L := by
  intro htL
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_m12 hL
  have ht_center : (⟨t, htL⟩ : L) ∈ center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    show (l : G) * t = t * (l : G)
    exact Subgroup.mem_centralizer_iff.1 ht (l : G) l.2
  have ht_one : (⟨t, htL⟩ : L) = 1 := by
    have : (⟨t, htL⟩ : L) ∈ (⊥ : Subgroup L) := by
      rw [← hZ]
      exact ht_center
    simpa using this
  have ht_eq : t = 1 := by
    have := congrArg (fun x : L => (x : G)) ht_one
    simpa using this
  rw [ht_eq, orderOf_one] at ht2
  norm_num at ht2

section Certified


theorem centralizes_iff_mem_zpowers (h : StdHyp G L) (hL : IsSporadic L .M12) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    ∀ c : ↥(centralizer ({t} : Set G)),
      (∀ n : ↥(L.subgroupOf (centralizer ({t} : Set G))), c * n * c⁻¹ = n) ↔
        c ∈ zpowers (tC t) := by
  intro c
  let C := centralizer ({t} : Set G)
  have hcC : (c : G) ∈ C := c.2
  have h1 : (∀ n : ↥(L.subgroupOf C), c * n * c⁻¹ = n) ↔
      (c : G) ∈ centralizer (L : Set G) := by
    constructor
    · intro hc
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      let n : ↥(L.subgroupOf C) :=
        ⟨⟨l, le_centralizer_singleton (t := t) ht hl⟩, by
          rw [Subgroup.mem_subgroupOf]; exact hl⟩
      have hval : (c : G) * l * (c : G)⁻¹ = l := by
        have := congrArg (fun x : C => (x : G)) (hc n)
        simpa [n] using this
      exact (mul_inv_eq_iff_eq_mul.mp hval).symm
    · intro hcL n
      apply Subtype.ext
      show (c : G) * (n : G) * (c : G)⁻¹ = (n : G)
      have hnL : (n : G) ∈ L := by
        simpa using (Subgroup.mem_subgroupOf.mp n.2)
      have hcomm : (n : G) * (c : G) = (c : G) * (n : G) :=
        Subgroup.mem_centralizer_iff.1 hcL (n : G) hnL
      exact mul_inv_eq_iff_eq_mul.mpr hcomm.symm
  have h2 : (c : G) ∈ centralizer (L : Set G) ↔ (c : G) ∈ zpowers t := by
    have hInf := h.centralizer_inf_centralizer_eq_zpowers
      (h.card_sylow_eq_two_m12 hL) ht ht2
    rw [← hInf]
    exact ⟨fun hL => ⟨hL, hcC⟩, fun h => h.1⟩
  have h3 : (c : G) ∈ zpowers t ↔ c ∈ zpowers (tC t) := by
    rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; simp [tC, hk])⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have := congrArg (fun x : C => (x : G)) hk
      simpa [tC, Subgroup.coe_zpow] using this
  exact h1.trans (h2.trans h3)

theorem card_centralizer_singleton (h : StdHyp G L) (hL : IsSporadic L .M12) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hout : ¬ centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)) :
    Nat.card ↥(centralizer ({t} : Set G)) = 4 * Nat.card ↥L := by
  let C := centralizer ({t} : Set G)
  let K := L ⊔ zpowers t
  have hLC : L ≤ C := le_centralizer_singleton (t := t) ht
  have hKC : K ≤ C :=
    sup_le hLC (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
  have hKcard : Nat.card ↥K = 2 * Nat.card ↥L :=
    CFSG.Sporadic.SmallOddCore.card_sup_zpowers (P := L) (u := t)
      (by rw [← ht2]; exact pow_orderOf_eq_one t)
      (fun p hp => by
        have hcomm : t * p = p * t := (Subgroup.mem_centralizer_iff.1 ht p hp).symm
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hp)
      (not_mem_of_isSporadic_m12 hL ht ht2)
  have hLq : IsSporadic (L ⧸ center L) .M12 := by
    have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_m12 hL
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hdvd : K.relIndex C ∣ 2 :=
    (h.relIndex_sup_zpowers_dvd (h.card_sylow_eq_two_m12 hL) ht ht2).trans
      (index_dvd_two_of_isSporadic_m12 hLq)
  have hrel : K.relIndex C = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
    · exfalso
      exact hout ((Subgroup.relIndex_eq_one.1 h1).trans
        (sup_le_sup le_rfl (zpowers_le.2 ht)))
    · exact h2
  have hcardC : Nat.card ↥C = K.relIndex C * Nat.card ↥K := by
    have h := Subgroup.relIndex_mul_card (H := K) (K := C)
    rw [inf_eq_left.2 hKC] at h
    exact h.symm
  rw [hcardC, hrel, hKcard]
  ring

end Certified

end CFSG.EvenSporadicStandard.M12Std.PropA
