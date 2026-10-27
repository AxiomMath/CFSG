module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsOuter

public section

namespace CFSG.ComponentClassification.CatLeafProof.Q81P2

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4.OutInv

theorem not_isPGroup_of_closure_odd {H : Type*} [Group H] [Finite H] {T : Set H}
    (hT : ∀ t ∈ T, Odd (orderOf t)) (h2 : 2 ∣ Nat.card (closure T)) :
    ¬ IsPGroup 2 (H ⧸ pPrimeCore 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hP
  have hle : closure T ≤ pPrimeCore 2 H := by
    rw [closure_le]
    intro t ht
    obtain ⟨k, hk⟩ := hP (QuotientGroup.mk t)
    have h1 : orderOf (QuotientGroup.mk t : H ⧸ pPrimeCore 2 H) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    have h2' : orderOf (QuotientGroup.mk t : H ⧸ pPrimeCore 2 H) ∣ orderOf t :=
      orderOf_map_dvd (QuotientGroup.mk' (pPrimeCore 2 H)) t
    have h3 : orderOf (QuotientGroup.mk t : H ⧸ pPrimeCore 2 H) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k
        (Nat.coprime_two_right.mpr (Odd.of_dvd_nat (hT t ht) h2'))) h1
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl (h2.trans (card_dvd_of_le hle))
    pPrimeCore_coprime_card

theorem not_isPGroup_fixSub {P : Type*} [Group P] [Finite P] {α : MulAut P} {T : Set P}
    (hT : ∀ t ∈ T, α t = t ∧ Odd (orderOf t)) (h2 : 2 ∣ Nat.card (closure T)) :
    ¬ IsPGroup 2 (↥(fixSub α) ⧸ pPrimeCore 2 ↥(fixSub α)) := by
  refine not_isPGroup_of_closure_odd (T := (fixSub α).subtype ⁻¹' T) (fun t ht => ?_) ?_
  · rw [← Subgroup.orderOf_coe]
    exact (hT _ ht).2
  · have himg : (fixSub α).subtype '' ((fixSub α).subtype ⁻¹' T) = T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, mem_fixSub.mpr (hT x hx).1⟩, hx, rfl⟩
    have hmap : (closure ((fixSub α).subtype ⁻¹' T)).map (fixSub α).subtype = closure T := by
      rw [MonoidHom.map_closure, himg]
    rw [← hmap, card_map_of_injective (fixSub α).subtype_injective] at h2
    exact h2

theorem two_dvd_card_range {G P : Type*} [Group G] [Group P] (ρ : G →* P) {x : G} {n : ℕ}
    (hx : orderOf (ρ x) = n) (hn : 2 ∣ n) : 2 ∣ Nat.card ρ.range := by
  have hmem : ρ x ∈ ρ.range := ⟨x, rfl⟩
  have h := orderOf_dvd_natCard (⟨_, hmem⟩ : ρ.range)
  rw [Subgroup.orderOf_mk, hx] at h
  exact hn.trans h

theorem exists_odd_of_hom {G P : Type*} [Group G] [Group P] {α : MulAut P} (ρ : G →* P)
    (hfix : ∀ g, α (ρ g) = ρ g) {S : Set G} (hS : closure S = ⊤)
    (hSo : ∀ s ∈ S, Odd (orderOf s)) (h2 : 2 ∣ Nat.card ρ.range) :
    ∃ T : Set P, (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
  refine ⟨ρ '' S, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨hfix s, Odd.of_dvd_nat (hSo s hs) (orderOf_map_dvd ρ s)⟩
  · have hcl : closure (ρ '' S) = ρ.range := by
      rw [← MonoidHom.map_closure, hS, MonoidHom.range_eq_map]
    rw [hcl]
    exact h2

theorem exists_odd_congr {L P : Type*} [Group L] [Group P] (e : L ≃* P) (β : MulAut L)
    {T : Set P} (hT : ∀ t ∈ T, MulAut.congr e β t = t ∧ Odd (orderOf t))
    (h2 : 2 ∣ Nat.card (closure T)) :
    ∃ T' : Set L, (∀ t ∈ T', β t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T') := by
  refine ⟨e ⁻¹' T, fun t ht => ⟨?_, ?_⟩, ?_⟩
  · have h : e (β (e.symm (e t))) = e t := (hT _ ht).1
    rw [MulEquiv.symm_apply_apply] at h
    exact e.injective h
  · rw [← MulEquiv.orderOf_eq e]
    exact (hT _ ht).2
  · have himg : e.toMonoidHom '' (e ⁻¹' T) = T := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨e.symm x, by simpa using hx, by simp⟩
    have hmap : (closure (e ⁻¹' T)).map e.toMonoidHom = closure T := by
      rw [MonoidHom.map_closure, himg]
    rw [← hmap, card_map_of_injective e.injective] at h2
    exact h2

end CFSG.ComponentClassification.CatLeafProof.Q81P2
