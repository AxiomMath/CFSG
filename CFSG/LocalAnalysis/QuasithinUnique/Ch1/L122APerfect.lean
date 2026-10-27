module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual

public section

namespace CFSG.QuasithinUnique.Vol2Native.L122A

open CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem primeResidual_eq_top_of_perfect {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    {p : ℕ} (hp : p.Prime) (N : Subgroup Y) [N.Normal] (hN : IsPGroup 2 N)
    [IsSimpleGroup (Y ⧸ N)] (hpQ : p ∣ Nat.card (Y ⧸ N)) : primeResidual p Y = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hRn : (primeResidual p Y).Normal := by
    have := primeResidual_characteristic p Y
    infer_instance
  have hRQ : (primeResidual p Y).map (QuotientGroup.mk' N) = ⊤ := by
    rw [primeResidual_map_surjective p _ (QuotientGroup.mk'_surjective N)]
    have hnorm : (primeResidual p (Y ⧸ N)).Normal := by
      have := primeResidual_characteristic p (Y ⧸ N)
      infer_instance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (primeResidual p (Y ⧸ N)) with h | h
    · exfalso
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Y ⧸ N) p hpQ
      have hgmem : g ∈ primeResidual p (Y ⧸ N) := by
        rw [primeResidual_eq_closure]
        exact Subgroup.subset_closure ⟨1, by rw [hg, pow_one]⟩
      rw [h, Subgroup.mem_bot] at hgmem
      rw [hgmem, orderOf_one] at hg
      exact hp.one_lt.ne hg
    · exact h
  have h2 : IsPGroup 2 (Y ⧸ primeResidual p Y) := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    have hy : QuotientGroup.mk' N y ∈ (primeResidual p Y).map (QuotientGroup.mk' N) := by
      rw [hRQ]
      exact Subgroup.mem_top _
    obtain ⟨r, hr, hyr⟩ := Subgroup.mem_map.mp hy
    have hn : r⁻¹ * y ∈ N := (QuotientGroup.eq (s := N)).mp hyr
    obtain ⟨k, hk⟩ := hN ⟨r⁻¹ * y, hn⟩
    refine ⟨k, ?_⟩
    have h1 : (r⁻¹ * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : (QuotientGroup.mk' (primeResidual p Y) y) =
        QuotientGroup.mk' (primeResidual p Y) (r⁻¹ * y) := by
      rw [map_mul]
      have : QuotientGroup.mk' (primeResidual p Y) r⁻¹ = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ((primeResidual p Y).inv_mem hr)
      rw [this, one_mul]
    change (QuotientGroup.mk' (primeResidual p Y) y) ^ 2 ^ k = 1
    rw [h2, ← map_pow, h1, map_one]
  have hnil : Group.IsNilpotent (Y ⧸ primeResidual p Y) := h2.isNilpotent
  have hsub : Subsingleton (Y ⧸ primeResidual p Y) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (Y ⧸ primeResidual p Y) hnil
  rw [eq_top_iff]
  intro y _
  have : QuotientGroup.mk' (primeResidual p Y) y = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff _).mp this

end CFSG.QuasithinUnique.Vol2Native.L122A
