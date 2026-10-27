module

public import CFSG.LargeExtraspecial.S6ThreeC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem nqRep_mem_nqSub {t : S.O} [hN : NQHyp S g t]
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) {D : Subgroup S.O}
    (htD : t ∈ D) (hDR : ∀ r ∈ Rbar S g t, ∀ x ∈ D, r * x * r⁻¹ ∈ D) (e : Y)
    {v : NQ S g t} (hv : v ∈ nqSub S g t D) : nqRep S g t hY e v ∈ nqSub S g t D := by
  obtain ⟨n, rfl⟩ := nqMk_surjective v
  have heR : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV hN.conj_mem t).range := by
    rw [range_resV, hY]; exact e.2
  obtain ⟨x, hx⟩ := heR
  rw [nqRep_apply hY hx.symm n, mem_nqSub htD, coe_nConj]
  exact hDR x x.2 _ ((mem_nqSub htD n).mp hv)

theorem nqSub_top {t : S.O} [NQHyp S g t] : nqSub S g t ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro m _
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  exact ⟨n, mem_top _, rfl⟩

theorem finrank_NQ_of_card {t : S.O} [NQHyp S g t] (ht1 : t ≠ 1) (htt : t * t = 1)
    (htN : t ∈ Nbar S g t) {e : ℕ} (he : Nat.card (Nbar S g t) = 2 ^ (e + 1)) :
    finrank (ZMod 2) (NQ S g t) = e := by
  have h1 := card_inf_Nbar_eq ht1 htt htN (X := ⊤) (mem_top t)
  rw [nqSub_top, finrank_top, top_inf_eq, he, pow_succ, mul_comm] at h1
  exact (Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by norm_num) h1)).symm

theorem eq_zpowers_or_eq_Nbar {t : S.O} [NQHyp S g t] {D : Subgroup S.O}
    (htD : zpowers t ≤ D) (hDN : D ≤ Nbar S g t)
    (h : nqSub S g t D = ⊥ ∨ nqSub S g t D = ⊤) : D = zpowers t ∨ D = Nbar S g t := by
  have htD' : t ∈ D := htD (mem_zpowers t)
  rcases h with h | h
  · left
    refine le_antisymm (fun x hx => ?_) htD
    have hm : nqMk (⟨x, hDN hx⟩ : Nbar S g t) ∈ nqSub S g t D := ⟨⟨x, hDN hx⟩, hx, rfl⟩
    rw [h, Submodule.mem_bot, nqMk_eq_zero_iff] at hm
    exact hm
  · right
    refine le_antisymm hDN fun x hx => ?_
    have hm : nqMk (⟨x, hx⟩ : Nbar S g t) ∈ nqSub S g t D := h ▸ Submodule.mem_top
    exact (mem_nqSub htD' _).mp hm

theorem eq_zero_or_eq_of_dvd_of_le {k P : ℕ} (h : P ∣ k) (hk : k ≤ P) : k = 0 ∨ k = P := by
  obtain ⟨c, rfl⟩ := h
  rcases Nat.lt_or_ge c 2 with hc | hc
  · interval_cases c <;> simp
  · left
    have : P * 2 ≤ P * c := Nat.mul_le_mul_left P hc
    have hP : P = 0 := by omega
    simp [hP]

theorem eq_zpowers_or_eq_Nbar_of_dvd {t : S.O} [NQHyp S g t] {D : Subgroup S.O}
    (htD : zpowers t ≤ D) (hDN : D ≤ Nbar S g t)
    (hdvd : finrank (ZMod 2) (NQ S g t) ∣ finrank (ZMod 2) (nqSub S g t D)) :
    D = zpowers t ∨ D = Nbar S g t := by
  refine eq_zpowers_or_eq_Nbar htD hDN ?_
  rcases eq_zero_or_eq_of_dvd_of_le hdvd (Submodule.finrank_le _) with h | h
  · exact Or.inl (Submodule.finrank_eq_zero.mp h)
  · exact Or.inr (Submodule.eq_top_of_finrank_eq h)

end CFSG.LargeExtraspecial.S14
