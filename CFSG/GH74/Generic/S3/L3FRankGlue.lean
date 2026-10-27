module

public import CFSG.GH74.Generic.S3.LxySplit

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.GLS.TwoThin CFSG.GH74.E2 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic.S3.L3Ord
open CFSG.Open (ordA ordTwistedA)

theorem l3_card_facts {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hmodel : LieModel X t 3 p f) : 0 < Nat.card X ∧ p ^ (3 * f) ∣ Nat.card X := by
  rcases ht with rfl | rfl
  · have hc : Nat.card X = ordA 2 (p ^ f) := card_of_lieModel_PSL (by norm_num) hmodel
    exact ⟨hc ▸ lt_of_lt_of_le (by norm_num) (le_ordA_two h5), hc ▸ prime_pow_dvd_ordA_two hp hf⟩
  · have hc : Nat.card X = ordTwistedA 2 (p ^ f) := card_of_lieModel_PSU (by norm_num) hp2 hmodel
    exact ⟨hc ▸ lt_of_lt_of_le (by norm_num) (le_ordTwistedA_two h5),
      hc ▸ prime_pow_dvd_ordTwistedA_two hp hf⟩

theorem l3_center_eq_bot {X : Type} [Group X] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hmodel : LieModel X t 3 p f) : center X = ⊥ := by
  obtain ⟨hpos, hdvd⟩ := l3_card_facts ht hp hp2 hf h5 hmodel
  have hs : IsSimpleGroup X := by
    rcases ht with rfl | rfl
    · exact isSimpleGroup_of_lieModel_L3' (Or.inl hmodel)
    · exact isSimpleGroup_of_lieModel_L3' (Or.inr hmodel)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hb | htop
  · exact hb
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (htop ▸ Subgroup.mem_top a) b).symm
    let _ : CommGroup X := { ‹Group X› with mul_comm := hcomm }
    have hprime : (Nat.card X).Prime := IsSimpleGroup.prime_card
    rcases (Nat.dvd_prime hprime).1 hdvd with h1 | h1
    · have : p ^ (3 * f) = 1 := h1
      have h2 : 1 < p ^ (3 * f) := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    · have hpp : (p ^ (3 * f)).Prime := h1 ▸ hprime
      have := (Nat.Prime.pow_eq_iff hpp).1 rfl
      omega

theorem l3_fRank_of_bound
    (hB : ∀ (X : Type) [Group X] (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime →
      p ≠ 2 → 5 ≤ p ^ f → Gen4Comp X → LieModel X t 3 p f →
      ∀ (t' : StatedLieTag) (n' p' f' : ℕ), LieModel X t' n' p' f' →
        FValue t' n' p' f' ≤ (p ^ f) ^ 4 * 6) : L3FRank := by
  intro X _ t p f ht hp hp2 h5 hG hmodel
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at h5
      omega
    · exact h0
  have hcenter : center X = ⊥ := l3_center_eq_bot ht hp hp2 hf h5 hmodel
  let e : X ≃* X ⧸ center X := mulEquivOfCenterBot hcenter
  have hv : FValue t 3 p f = (p ^ f) ^ 4 * 6 := by
    rcases ht with rfl | rfl <;> simp [FValue, lieRankSq, lieTypeRank]
  have hmem : (p ^ f) ^ 4 * 6 ∈ {v : ℕ | HasFValue X v} :=
    ⟨t, 3, p, f, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmodel, hv.symm⟩
  have hub : (p ^ f) ^ 4 * 6 ∈ upperBounds {v : ℕ | HasFValue X v} := by
    rintro v ⟨t', n', p', f', hq, rfl⟩
    exact hB X t p f ht hp hp2 h5 hG hmodel t' n' p' f'
      (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hq)
  exact IsGreatest.csSup_eq ⟨hmem, hub⟩

end CFSG.GH74.Generic.S3
