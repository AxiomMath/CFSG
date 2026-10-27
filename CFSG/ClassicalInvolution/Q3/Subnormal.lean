module

public import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem commutator_le_of_isSubnormal {p : ℕ} (hp : p.Prime) {J H N P : Subgroup G}
    (hJ : IsSubnormal J H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hcop : ¬ p ∣ Nat.card N) (hPJ : P ≤ J) (hP : IsPGroup p P) : ⁅N, P⁆ ≤ J := by
  induction hJ generalizing P with
  | @refl K =>
    have hHN : K ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hPJ.trans hHN)).trans hNH
  | @step J M H hJM hJn hMH ih =>
    have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
    have hMH' : M ≤ H := isSubnormal_le hMH
    have hPM : P ≤ M := hPJ.trans hJM
    have h1 : ⁅N, P⁆ ≤ M := ih hNH hN hPM hP
    have hPnorm : P ≤ Subgroup.normalizer (N : Set G) := fun x hx => hHN (hMH' (hPM hx))
    have hA : ⁅⁅N, P⁆, P⁆ ≤ J := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      have haM : a ∈ M := h1 ha
      have hxJ : x ∈ J := hPJ hx
      have hconj : a * x * a⁻¹ ∈ J :=
        (Subgroup.normal_subgroupOf_iff hJM).mp hJn x a hxJ haM
      rw [commutatorElement_def]
      have := J.mul_mem hconj (J.inv_mem hxJ)
      simpa [mul_assoc] using this
    rw [CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp P N hP hcop
      hPnorm] at hA
    exact hA

theorem commutator_le_inf_of_isSubnormal {p : ℕ} (hp : p.Prime) {J H N P : Subgroup G}
    (hJ : IsSubnormal J H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hcop : ¬ p ∣ Nat.card N) (hPJ : P ≤ J) (hP : IsPGroup p P) : ⁅N, P⁆ ≤ J ⊓ N := by
  refine le_inf (commutator_le_of_isSubnormal hp hJ hNH hN hcop hPJ hP) ?_
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hN
  have hJH : J ≤ H := isSubnormal_le hJ
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((hPJ.trans hJH).trans hHN)

theorem commutator_oddCoreIn_le {J H P : Subgroup G} (hJ : IsSubnormal J H) (hPJ : P ≤ J)
    (hP : IsPGroup 2 P) : ⁅oddCoreIn H, P⁆ ≤ oddCoreIn J := by
  have hHN : H ≤ Subgroup.normalizer (oddCoreIn H : Set G) := normalizer_oddCoreIn H
  have hN : ((oddCoreIn H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (oddCoreIn_le H)).mpr hHN
  have hcop : ¬ 2 ∣ Nat.card (oddCoreIn H) := fun h =>
    (Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn H)) (even_iff_two_dvd.mpr h)
  have h1 := commutator_le_inf_of_isSubnormal Nat.prime_two hJ (oddCoreIn_le H) hN hcop hPJ hP
  have hJH : J ≤ H := isSubnormal_le hJ
  refine h1.trans ?_
  refine le_oddCoreIn_of_normalizes inf_le_left ?_ ?_
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyJ, hyO⟩
      exact ⟨J.mul_mem (J.mul_mem hx hyJ) (J.inv_mem hx),
        conj_mem_oddCoreIn (hJH hx) hyO⟩
    · rintro ⟨hyJ, hyO⟩
      refine ⟨?_, ?_⟩
      · have := J.mul_mem (J.mul_mem (J.inv_mem hx) hyJ) hx
        simpa [mul_assoc] using this
      · have := conj_mem_oddCoreIn (inv_mem (hJH hx)) hyO
        simpa [mul_assoc] using this
  · exact (odd_card_oddCoreIn H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)


theorem not_three_dvd_card_of_isPGroup_two {U : Subgroup G} (hU : IsPGroup 2 U) :
    ¬ 3 ∣ Nat.card U := by
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [hk]
  intro h
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  omega

theorem le_normalizer_of_isSubnormal {K H U Q : Subgroup G} {g : G} (hK : IsSubnormal K H)
    (hUH : U ≤ H) (hUn : (U.subgroupOf H).Normal) (hU : IsPGroup 2 U) (hgK : g ∈ K)
    (hg : IsPGroup 3 (Subgroup.zpowers g)) (hKQ : K = Q ⊔ Subgroup.zpowers g)
    (hKU : K ⊓ U = Q) (hQ : ⁅Q, Subgroup.zpowers g⁆ = Q) :
    U ≤ Subgroup.normalizer (K : Set G) := by
  have hcop := not_three_dvd_card_of_isPGroup_two hU
  have hKH : K ≤ H := isSubnormal_le hK
  have hHU : H ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mp hUn
  have hgU : Subgroup.zpowers g ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hHU (hKH hgK)
  have hzK : Subgroup.zpowers g ≤ K := (Subgroup.zpowers_le).mpr hgK
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three (Subgroup.zpowers g) U hg hcop hgU
  have hcomm_le_U : ⁅U, Subgroup.zpowers g⁆ ≤ U :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hgU
  have hcomm_le_K : ⁅U, Subgroup.zpowers g⁆ ≤ K :=
    commutator_le_of_isSubnormal Nat.prime_three hK hUH hUn hcop hzK hg
  have hcommQ : ⁅U, Subgroup.zpowers g⁆ ≤ Q := hKU ▸ le_inf hcomm_le_K hcomm_le_U
  have hQU : Q ≤ U := hKU ▸ inf_le_right
  have hQK : Q ≤ K := hKU ▸ inf_le_left
  have hfix : ∀ a ∈ U ⊓ Subgroup.centralizer (Subgroup.zpowers g : Set G),
      a ∈ Subgroup.normalizer (K : Set G) := by
    rintro a ⟨haU, hac⟩
    have haH : a ∈ H := hUH haU
    set φ : G →* G := (MulAut.conj a).toMonoidHom with hφ
    have hφinj : Function.Injective φ := (MulAut.conj a).injective
    have hφapply : ∀ x, φ x = a * x * a⁻¹ := fun x => rfl
    have hφx : ∀ x ∈ Subgroup.zpowers g, φ x = x := by
      intro x hx
      have h := Subgroup.mem_centralizer_iff.mp hac x hx
      rw [hφapply, mul_inv_eq_iff_eq_mul]
      exact h.symm
    have hmapH : H.map φ = H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact H.mul_mem (H.mul_mem haH hy) (H.inv_mem haH)
      · intro hx
        exact ⟨a⁻¹ * x * a, H.mul_mem (H.mul_mem (H.inv_mem haH) hx) haH, by rw [hφapply]; group⟩
    have hmapU : U.map φ = U := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact U.mul_mem (U.mul_mem haU hy) (U.inv_mem haU)
      · intro hx
        exact ⟨a⁻¹ * x * a, U.mul_mem (U.mul_mem (U.inv_mem haU) hx) haU, by rw [hφapply]; group⟩
    have hK' : IsSubnormal (K.map φ) H := by
      have := isSubnormal_map_conj hK a
      rwa [hmapH] at this
    have hzK' : Subgroup.zpowers g ≤ K.map φ := by
      intro x hx
      exact ⟨x, hzK hx, hφx x hx⟩
    have hc' : ⁅U, Subgroup.zpowers g⁆ ≤ K.map φ :=
      commutator_le_of_isSubnormal Nat.prime_three hK' hUH hUn hcop hzK' hg
    have hc'Q : ⁅U, Subgroup.zpowers g⁆ ≤ Q.map φ := by
      have h1 : ⁅U, Subgroup.zpowers g⁆ ≤ K.map φ ⊓ U := le_inf hc' hcomm_le_U
      rwa [← hmapU, ← Subgroup.map_inf_eq K U φ hφinj, hmapU, hKU] at h1
    have hQle : Q ≤ Q.map φ := by
      refine le_trans ?_ hc'Q
      calc Q = ⁅Q, Subgroup.zpowers g⁆ := hQ.symm
        _ ≤ ⁅U, Subgroup.zpowers g⁆ := Subgroup.commutator_mono hQU le_rfl
    have hQeq : Q = Q.map φ :=
      Subgroup.eq_of_le_of_card_ge hQle
        (by rw [Subgroup.card_map_of_injective hφinj])
    have hKeq : K.map φ = K := by
      conv_lhs => rw [hKQ]
      rw [Subgroup.map_sup, ← hQeq, MonoidHom.map_zpowers, hφx g (Subgroup.mem_zpowers g)]
      exact hKQ.symm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hKeq]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hKeq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := hφinj (by rw [hyx]; rfl)
      exact this ▸ hy
  calc U = ⁅U, Subgroup.zpowers g⁆ ⊔ (U ⊓ Subgroup.centralizer (Subgroup.zpowers g : Set G)) := hfac
    _ ≤ Subgroup.normalizer (K : Set G) := by
        refine sup_le (fun x hx => ?_) fun a ha => hfix a ha
        exact Subgroup.le_normalizer (hQK (hcommQ hx))

end CFSG.ClassicalInvolution.Q3
