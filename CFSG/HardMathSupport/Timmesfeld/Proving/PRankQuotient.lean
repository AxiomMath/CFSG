module

public import CFSG.HardMathSupport.Timmesfeld.Proving.ElemAbelianSubgroup
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G]

theorem isElemAbelian_map {p : ℕ} {K : Type*} [Group K] {E : Subgroup G} (f : G →* K)
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem pRank_le_pRank_inf_add_pRank_map {p : ℕ} (hp : p.Prime) [Finite G] (H N : Subgroup G)
    [N.Normal] :
    pRank p H ≤ pRank p (H ⊓ N) + pRank p (H.map (QuotientGroup.mk' N)) := by
  refine (show sSup {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} ≤
      _ from csSup_le' ?_)
  rintro k ⟨E, hEH, hE, hcard⟩
  set ψ : E →* G ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hr : ψ.range = E.map (QuotientGroup.mk' N) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmap : ψ.ker.map E.subtype = E ⊓ N := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyk, rfl⟩
      have hyN : (QuotientGroup.mk' N) y = 1 := hyk
      exact ⟨hy, (QuotientGroup.eq_one_iff y).mp hyN⟩
    · rintro ⟨hxE, hxN⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      exact (QuotientGroup.eq_one_iff x).mpr hxN
  have hk : Nat.card ψ.ker = Nat.card (E ⊓ N : Subgroup G) := by
    rw [← hmap]
    exact Nat.card_congr
      (ψ.ker.equivMapOfInjective E.subtype Subtype.val_injective).toEquiv
  have hA : Nat.card (E ⊓ N : Subgroup G) * Nat.card (E.map (QuotientGroup.mk' N)) =
      Nat.card E := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hr, hk] at h1
    exact h1
  have hdvdA : Nat.card (E ⊓ N : Subgroup G) ∣ p ^ k := by
    rw [← hcard, ← hA]
    exact dvd_mul_right _ _
  have hdvdB : Nat.card (E.map (QuotientGroup.mk' N)) ∣ p ^ k := by
    rw [← hcard, ← hA]
    exact dvd_mul_left _ _
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1 hdvdA
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 hdvdB
  have hkab : k = a + b := by
    apply Nat.pow_right_injective hp.two_le
    simp only
    rw [pow_add, ← ha, ← hb, hA, hcard]
  have hEA : IsElemAbelian p (E ⊓ N : Subgroup G) := isElemAbelian_of_le hE inf_le_left
  have hEB : IsElemAbelian p (E.map (QuotientGroup.mk' N)) := isElemAbelian_map _ hE
  have hA_le : pRank p (H ⊓ N) ≥ a :=
    le_pRank_of_elemAbelian_card hp.two_le (inf_le_inf hEH le_rfl) hEA ha
  have hB_le : pRank p (H.map (QuotientGroup.mk' N)) ≥ b :=
    le_pRank_of_elemAbelian_card hp.two_le (Subgroup.map_mono hEH) hEB hb
  omega

end CFSG.HardMathSupport.Timmesfeld.Proving
