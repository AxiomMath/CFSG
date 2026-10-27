module

public import CFSG.Walter.W67.W1Basic
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.GH74.Uniqueness.SU.SU4Defs

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def sylowIn {N P : Subgroup X} (hP : IsSylowIn N P) : Sylow 2 ↥N :=
  IsPGroup.toSylow (P := P.subgroupOf N) hP.2.1.comap_subtype
    (fun hd => (Nat.not_even_iff_odd.mpr hP.2.2) (even_iff_two_dvd.mpr hd))

omit [Finite X] in
theorem coe_sylowIn {N P : Subgroup X} (hP : IsSylowIn N P) :
    (sylowIn hP : Subgroup ↥N) = P.subgroupOf N := rfl

theorem isSylowIn_inf_normal (T : Sylow 2 X) (N : Subgroup X) [N.Normal] :
    IsSylowIn N ((T : Subgroup X) ⊓ N) := by
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal (p := 2) T (N := N)
  refine ⟨inf_le_right, ?_, ?_⟩
  · have h1 : IsPGroup 2 (((T : Subgroup X) ⊓ N).subgroupOf N) := hQ ▸ Q.isPGroup'
    exact IsPGroup.of_equiv h1 (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      (T : Subgroup X) ⊓ N ≤ N))
  · have h1 : ¬ 2 ∣ (((T : Subgroup X) ⊓ N).subgroupOf N).index := by
      rw [← hQ]
      exact Q.not_dvd_index
    exact Nat.not_even_iff_odd.mp (fun hev => h1 (even_iff_two_dvd.mp hev))

omit [Finite X] in
theorem subgroupOf_inf_eq (P K N : Subgroup X) :
    (P ⊓ K).subgroupOf N = P.subgroupOf N ⊓ K.subgroupOf N :=
  Subgroup.comap_inf _ _ _

theorem card_inf_of_sylowIn {N P K : Subgroup X} (hP : IsSylowIn N P) (hKN : K ≤ N)
    (hK : N ≤ normalizer (K : Set X)) :
    Nat.card (P ⊓ K : Subgroup X) = 2 ^ (Nat.card K).factorization 2 := by
  have hKn : (K.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mpr hK
  obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal (p := 2) (sylowIn hP) (N := K.subgroupOf N)
  have h1 : Nat.card ↥Q = 2 ^ (Nat.card (K.subgroupOf N)).factorization 2 :=
    Sylow.card_eq_multiplicity Q
  have hcK : Nat.card (K.subgroupOf N) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  have hPK : (P ⊓ K : Subgroup X) ≤ N := inf_le_right.trans hKN
  have hAB : (sylowIn hP : Subgroup ↥N) ⊓ K.subgroupOf N = (P ⊓ K).subgroupOf N := by
    rw [coe_sylowIn, subgroupOf_inf_eq]
  have h2 : Nat.card ↥Q = Nat.card (P ⊓ K : Subgroup X) := by
    rw [show Nat.card ↥Q = Nat.card ↥(Q : Subgroup ↥(K.subgroupOf N)) from rfl, hQ]
    calc Nat.card ↥(((sylowIn hP : Subgroup ↥N) ⊓ K.subgroupOf N).subgroupOf (K.subgroupOf N))
        = Nat.card ↥((sylowIn hP : Subgroup ↥N) ⊓ K.subgroupOf N) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      _ = Nat.card ↥((P ⊓ K).subgroupOf N) := by rw [hAB]
      _ = Nat.card (P ⊓ K : Subgroup X) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
  rw [← h2, h1, hcK]

omit [Finite X] in
theorem sup_le_normalizer_of_commute {K C : Subgroup X} (hKC : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a) :
    K ⊔ C ≤ normalizer (K : Set X) := by
  refine sup_le Subgroup.le_normalizer fun c hc => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hcomm : ∀ k ∈ K, c * k * c⁻¹ = k := fun k hk => by
    rw [← hKC k hk c hc, mul_inv_cancel_right]
  constructor
  · intro hh
    rw [hcomm h hh]
    exact hh
  · intro hh
    have e := hcomm _ hh
    have h5 : c * h * c⁻¹ = h := by
      calc c * h * c⁻¹ = c⁻¹ * (c * (c * h * c⁻¹) * c⁻¹) * c := by group
        _ = c⁻¹ * (c * h * c⁻¹) * c := by rw [e]
        _ = h := by group
    rw [h5] at hh
    exact hh

theorem inf_sup_eq_of_isSylowIn {K C P : Subgroup X} (hKC : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a)
    (hP : IsSylowIn (K ⊔ C) P) : (P ⊓ K) ⊔ (P ⊓ C) = P := by
  have hNK := sup_le_normalizer_of_commute hKC
  have hNC : K ⊔ C ≤ normalizer (C : Set X) := by
    have := sup_le_normalizer_of_commute (K := C) (C := K) (fun a ha b hb => (hKC b hb a ha).symm)
    rwa [sup_comm] at this
  have hKN : K ≤ K ⊔ C := le_sup_left
  have hCN : C ≤ K ⊔ C := le_sup_right
  have hKCN : K ⊓ C ≤ K ⊔ C := inf_le_left.trans hKN
  have hNKC : K ⊔ C ≤ normalizer ((K ⊓ C : Subgroup X) : Set X) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNK hn)) h
    have h2 := (Subgroup.mem_normalizer_iff.mp (hNC hn)) h
    simp only [Subgroup.mem_inf]
    exact and_congr h1 h2
  have hcP : Nat.card ↥P = 2 ^ (Nat.card ↥(K ⊔ C)).factorization 2 := by
    have := card_inf_of_sylowIn hP (le_refl (K ⊔ C)) Subgroup.le_normalizer
    rwa [inf_of_le_left hP.1] at this
  have hcK := card_inf_of_sylowIn hP hKN hNK
  have hcC := card_inf_of_sylowIn hP hCN hNC
  have hcI := card_inf_of_sylowIn hP hKCN hNKC
  have hRQ : ∀ a ∈ P ⊓ K, ∀ b ∈ P ⊓ C, a * b = b * a := fun a ha b hb => hKC a ha.2 b hb.2
  obtain ⟨hprod, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (P ⊓ K) (P ⊓ C) hRQ
  obtain ⟨hprod2, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute K C hKC
  have hint : (P ⊓ K) ⊓ (P ⊓ C) = P ⊓ (K ⊓ C) := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [hint] at hprod
  have hfac : (Nat.card ↥(K ⊔ C)).factorization 2 + (Nat.card ↥(K ⊓ C)).factorization 2 =
      (Nat.card K).factorization 2 + (Nat.card C).factorization 2 := by
    have h : (Nat.card ↥(K ⊔ C) * Nat.card ↥(K ⊓ C)).factorization 2 =
        (Nat.card ↥K * Nat.card ↥C).factorization 2 := congrArg (fun n => n.factorization 2) hprod2
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h
    simpa using h
  have hcard : Nat.card ↥((P ⊓ K) ⊔ (P ⊓ C)) = Nat.card ↥P := by
    have h1 : Nat.card ↥P * Nat.card ↥(P ⊓ (K ⊓ C)) = Nat.card ↥(P ⊓ K) * Nat.card ↥(P ⊓ C) := by
      rw [hcP, hcI, hcK, hcC, ← pow_add, ← pow_add, hfac]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (hprod.trans h1.symm)
  have hle : (P ⊓ K) ⊔ (P ⊓ C) ≤ P := sup_le inf_le_left inf_le_left
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])

theorem mem_sup_of_isSylowIn_commute {K C P : Subgroup X}
    (hKC : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a) (hP : IsSylowIn (K ⊔ C) P) {t : X} (ht : t ∈ P) :
    ∃ r ∈ P ⊓ K, ∃ q ∈ P ⊓ C, r * q = t := by
  have hRQ : ∀ a ∈ P ⊓ K, ∀ b ∈ P ⊓ C, a * b = b * a := fun a ha b hb => hKC a ha.2 b hb.2
  have hmem : t ∈ (P ⊓ K) ⊔ (P ⊓ C) := by
    rw [inf_sup_eq_of_isSylowIn hKC hP]
    exact ht
  exact SU1.mem_sup_of_commute hRQ hmem

end CFSG.GH74.Uniqueness.SU.SU10
