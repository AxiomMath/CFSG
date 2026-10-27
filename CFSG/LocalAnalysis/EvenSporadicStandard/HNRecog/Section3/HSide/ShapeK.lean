module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.MapShape

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem pow_eight_eq_one_of_mem {T : Subgroup (Equiv.Perm (Fin 5))}
    (h2 : IsPGroup 2 T) {u : Equiv.Perm (Fin 5)} (hu : u ∈ T) : u ^ 8 = 1 := by
  obtain ⟨k, hk⟩ := (isPGroup_iff_orderOf_dvd_pow.mp h2) (⟨u, hu⟩ : T)
  simp only [Subgroup.orderOf_mk] at hk
  have hord120 : orderOf u ∣ 120 := by
    have h := orderOf_dvd_natCard (G := Equiv.Perm (Fin 5)) u
    rw [Nat.card_perm] at h
    norm_num at h
    exact h
  have hcop : Nat.Coprime (orderOf u) 15 :=
    Nat.Coprime.coprime_dvd_left hk (Nat.Coprime.pow_left k (by norm_num))
  have h8 : orderOf u ∣ 8 := by
    have hmul : orderOf u ∣ 15 * 2 ^ 3 := by
      rw [show (15 : ℕ) * 2 ^ 3 = 120 by norm_num]
      exact hord120
    exact hcop.dvd_of_dvd_mul_left hmul
  exact orderOf_dvd_iff_pow_eq_one.mp h8

theorem eq_bot_of_normal_isPGroup_sym_five (T : Subgroup (Equiv.Perm (Fin 5))) (hT : T.Normal)
    (h2 : IsPGroup 2 T) : T = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  by_contra hne
  have hcheck : ∀ t : Equiv.Perm (Fin 5), t ≠ 1 →
      t ^ 8 ≠ 1 ∨ ∃ g : Equiv.Perm (Fin 5), (g * t * g⁻¹ * t⁻¹) ^ 8 ≠ 1 := by
    decide +kernel
  rcases hcheck t hne with h | ⟨g, hg⟩
  · exact h (pow_eight_eq_one_of_mem h2 ht)
  · have hmem : g * t * g⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem (hT.conj_mem t ht g) (T.inv_mem ht)
    exact hg (pow_eight_eq_one_of_mem h2 hmem)

theorem isShapeZ2Z4StarExtra_pCoreOf {H : Type} [Group H] {K : Subgroup H} (h : IsShapeK ↥K) :
    IsShapeZ2Z4StarExtra ↥(CFSG.Open.pCoreOf 2 K) := by
  obtain ⟨N, hN, hNp, hNcard, ⟨φ⟩, hcen, Q, hQplus, hQsup, hQcard⟩ := h
  haveI := hN
  have hpCore : CFSG.pCore 2 ↥K = N := by
    apply le_antisymm
    · let π : ↥K →* Equiv.Perm (Fin 5) := φ.toMonoidHom.comp (QuotientGroup.mk' N)
      have hπsurj : Function.Surjective π :=
        φ.surjective.comp (QuotientGroup.mk'_surjective N)
      have hPmap : (CFSG.pCore 2 ↥K).map π = ⊥ :=
        eq_bot_of_normal_isPGroup_sym_five _
          ((CFSG.pCore_normal (p := 2) (G := ↥K)).map π hπsurj)
          ((CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map π)
      intro x hx
      have hxmap : π x ∈ (CFSG.pCore 2 ↥K).map π := ⟨x, hx, rfl⟩
      rw [hPmap] at hxmap
      have hx1 : π x = 1 := by simpa using hxmap
      have hq : (QuotientGroup.mk' N) x = 1 := by
        apply φ.injective
        rw [map_one]
        exact hx1
      exact (QuotientGroup.eq_one_iff x).mp hq
    · exact le_sSup ⟨hN, hNp⟩
  have hshapeN : IsShapeZ2Z4StarExtra ↥N :=
    ⟨hNp, hNcard, hcen, Q, hQplus, hQsup, hQcard⟩
  rw [show CFSG.Open.pCoreOf 2 K = N.map K.subtype by rw [CFSG.Open.pCoreOf, hpCore]]
  exact IsShapeZ2Z4StarExtra.map (Subgroup.subtype_injective K) hshapeN

end CFSG.EvenSporadicStandard.HNRecog.Section3
