module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof

theorem exists_normal_index_prime_of_outer {X Q : Type*} [Group X] [Group Q] [Finite X] [Finite Q]
    (ψ : X →* Q) (N : Subgroup Q) [N.Normal] {p : ℕ} (hp : p.Prime) (hN : ¬ p ∣ Nat.card N)
    (hidx : ∃ k : ℕ, N.index = p ^ k) {x : X} (hx : ∃ k : ℕ, orderOf x = p ^ k)
    (hψ : ψ x ≠ 1) : ∃ M : Subgroup X, M.Normal ∧ M.index = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  let θ : X →* Q ⧸ N := (QuotientGroup.mk' N).comp ψ
  have hθx : θ x ≠ 1 := by
    intro h
    have hmem : ψ x ∈ N := (QuotientGroup.eq_one_iff _).mp h
    obtain ⟨a, ha⟩ := hx
    have hord : orderOf (ψ x) ∣ p ^ a := ha ▸ orderOf_map_dvd ψ x
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).mp hord
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hψ (orderOf_eq_one_iff.mp (by simpa using hb))
    have hpdvd : p ∣ orderOf (ψ x) := by
      rw [hb]
      exact dvd_pow_self p hb0
    have hsub : orderOf (⟨ψ x, hmem⟩ : N) = orderOf (ψ x) := Subgroup.orderOf_mk _ _
    exact hN (hpdvd.trans (hsub ▸ orderOf_dvd_natCard _))
  have hZ : IsPGroup p (Q ⧸ N) := by
    obtain ⟨k, hk⟩ := hidx
    exact IsPGroup.of_card (n := k) (by rw [← hk]; rfl)
  have hR : IsPGroup p θ.range := hZ.to_subgroup _
  haveI : Group.IsNilpotent θ.range := hR.isNilpotent
  have hdvd : p ∣ Nat.card θ.range := by
    rcases hR.card_eq_or_dvd with h | h
    · exfalso
      have hmem : θ x ∈ θ.range := ⟨x, rfl⟩
      rw [Subgroup.card_eq_one.mp h] at hmem
      exact hθx (Subgroup.mem_bot.mp hmem)
    · exact h
  obtain ⟨H, hHi, hHn⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hdvd
  refine ⟨H.comap θ.rangeRestrict, hHn.comap _, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ θ.rangeRestrict_surjective, hHi]

end CFSG.LocalAnalysis.RankThreeUC.S15.K7145Proof
