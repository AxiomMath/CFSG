module


public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialBinaryActionCounterexample

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace NoncentralOrderP

theorem exists_subgroup {G : Type} [Group G] [Finite G] {p : ℕ} (hp : Nat.Prime p)
    {P : Subgroup G} (hP : CFSG.IsExtraspecialPGroup p ↥P) (hexp : Monoid.exponent ↥P = p) :
    ∃ X ≤ P, Nat.card ↥X = p ∧ X ≠ centerP P := by
  obtain ⟨-, hcomm, -, hcard⟩ := hP
  have hnc : ∃ x : P, x ∉ Subgroup.center P := by
    by_contra hcon
    push Not at hcon
    have hbot : commutator P = ⊥ := by
      exact (_root_.commutator_eq_bot_iff_center_eq_top P).mpr ((Subgroup.eq_top_iff' _).mpr hcon)
    rw [hbot] at hcomm
    rw [← hcomm] at hcard
    simp at hcard
    exact hp.ne_one hcard.symm
  obtain ⟨x, hx⟩ := hnc
  have hx1 : x ≠ 1 := fun h => hx (h ▸ Subgroup.one_mem _)
  have hord : orderOf x = p := by
    have hd : orderOf x ∣ p := hexp ▸ Monoid.order_dvd_exponent x
    rcases (Nat.dvd_prime hp).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  refine ⟨(Subgroup.zpowers x).map P.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · rw [Subgroup.card_map_of_injective P.subtype_injective, Nat.card_zpowers, hord]
  · intro h
    have hxm : (x : G) ∈ (Subgroup.zpowers x).map P.subtype :=
      ⟨x, Subgroup.mem_zpowers x, rfl⟩
    rw [h] at hxm
    obtain ⟨z, hz, hzx⟩ := hxm
    have : z = x := Subtype.ext hzx
    exact hx (this ▸ hz)

end NoncentralOrderP

end Section5

end CFSG.LocalAnalysis.RankThreeUC
