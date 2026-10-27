module

public import CFSG.GroupTheory.HallHigmanPiCore

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

universe u

open scoped commutatorElement

theorem exists_perfect_map_eq_top {Q : Type*} [Group Q]
    (hQ : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = (⊤ : Subgroup Q)) :
    ∀ (n : ℕ) {H : Type u} [Group H] [Finite H] (f : H →* Q), Nat.card H = n →
      Function.Surjective f → ∃ K : Subgroup H, ⁅K, K⁆ = K ∧ K.map f = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H _ _ f hn hf
    by_cases hH : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = (⊤ : Subgroup H)
    · exact ⟨⊤, hH, by rw [Subgroup.map_top, MonoidHom.range_eq_top]; exact hf⟩
    · set K₀ : Subgroup H := ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ with hK₀
      have hlt : Nat.card K₀ < n := by
        rw [← hn]
        refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card K₀))
          fun he => hH ?_
        exact Subgroup.eq_top_of_card_eq K₀ he
      have hmap : K₀.map f = ⊤ := by
        rw [hK₀, Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hf]
        exact hQ
      have hsurj : Function.Surjective (f.comp K₀.subtype) := by
        intro q
        have hq : q ∈ K₀.map f := by rw [hmap]; trivial
        obtain ⟨h, hh, rfl⟩ := hq
        exact ⟨⟨h, hh⟩, rfl⟩
      obtain ⟨K', hK'p, hK'm⟩ := ih (Nat.card K₀) hlt (f.comp K₀.subtype) rfl hsurj
      refine ⟨K'.map K₀.subtype, ?_, ?_⟩
      · rw [← Subgroup.map_commutator, hK'p]
      · rw [Subgroup.map_map]; exact hK'm

theorem isPSolvable_three_of_no_perfect {W : Type*} [Group W] [Finite W] (A : Subgroup W)
    (h : ∀ J : Subgroup W, J ≤ A → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J) :
    CFSG.HallHigman.IsPSolvable 3 ↥A := by
  intro H _ T' _ hs
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h3, hcop⟩ := hcon
  have hdvd : 3 ∣ T'.index := by
    by_contra hnd
    exact hcop ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd)
  have hidx : T'.index = Nat.card (↥H ⧸ T') := Subgroup.index_eq_card T'
  have hcomm : ⁅(⊤ : Subgroup (↥H ⧸ T')), (⊤ : Subgroup (↥H ⧸ T'))⁆ = (⊤ : Subgroup (↥H ⧸ T')) := by
    rcases hs.eq_bot_or_eq_top_of_normal
        ⁅(⊤ : Subgroup (↥H ⧸ T')), (⊤ : Subgroup (↥H ⧸ T'))⁆ with hb | ht
    · exfalso
      let _ : CommGroup (↥H ⧸ T') :=
        { (inferInstance : Group (↥H ⧸ T')) with
          mul_comm := fun a b => by
            have : ⁅a, b⁆ ∈ (⁅(⊤ : Subgroup (↥H ⧸ T')), (⊤ : Subgroup (↥H ⧸ T'))⁆) :=
              Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
            rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
            exact this }
      have hp := IsSimpleGroup.prime_card (α := ↥H ⧸ T')
      rw [← hidx] at hp
      have h3p : 3 = T'.index := by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdvd
        exact this
      exact h3 h3p.symm
    · exact ht
  obtain ⟨K, hKp, hKm⟩ := exists_perfect_map_eq_top hcomm (Nat.card ↥H) (QuotientGroup.mk' T') rfl
    (QuotientGroup.mk'_surjective T')
  have h3K : 3 ∣ Nat.card K := by
    have hc : Nat.card (K.map (QuotientGroup.mk' T')) ∣ Nat.card K := Subgroup.card_map_dvd _ _
    have he : Nat.card (K.map (QuotientGroup.mk' T')) = T'.index := by
      rw [hKm, Subgroup.card_top, hidx]
    rw [he] at hc
    exact hdvd.trans hc
  refine h ((K.map H.subtype).map A.subtype) (Subgroup.map_subtype_le _) ?_ ?_
  · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hKp]
  · rw [Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.card_map_of_injective H.subtype_injective]
    exact h3K

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
