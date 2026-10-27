module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {J : Subgroup G} {Q : Type} [Group Q] [Finite Q]

theorem a10E_le_pre (ψ : ↥J →* Q) (Λ : Subgroup Q) : a10E J ψ Λ ≤ a10Pre J ψ Λ := by
  exact (Subgroup.closure_le _).mpr fun g hg => hg.1

theorem a10Pre_le (ψ : ↥J →* Q) (Λ : Subgroup Q) : a10Pre J ψ Λ ≤ J := by
  exact Subgroup.map_subtype_le _

theorem a10t1_five_lift (ψ : ↥J →* Q) (hψ : Function.Surjective ψ) {q : Q} {k : ℕ}
    (hk : q ^ 5 ^ k = 1) : ∃ l : ↥J, ψ l = q ∧ ∃ a : ℕ, l ^ 5 ^ a = 1 := by
  obtain ⟨l, rfl⟩ := hψ q
  have hl0 : orderOf l ≠ 0 := (orderOf_pos l).ne'
  obtain ⟨a, m, hm, hlm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hl0 5 (by norm_num)
  have hord : orderOf (ψ l) ∣ 5 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime m (orderOf (ψ l)) := by
    have h5 : Nat.Coprime m 5 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm).symm
    exact (Nat.Coprime.pow_right k h5).coprime_dvd_right hord
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨l ^ (m * t), ?_, a, ?_⟩
  · rw [map_pow, pow_mul, ht]
  · have h1 : l ^ (5 ^ a * m) = 1 := by rw [← hlm]; exact pow_orderOf_eq_one l
    rw [← pow_mul]
    have e : m * t * 5 ^ a = (5 ^ a * m) * t := by ring
    rw [e, pow_mul, h1, one_pow]

theorem a10_psi_E (ψ : ↥J →* Q) (hψ : Function.Surjective ψ) {Λ : Subgroup Q} (hΛ : fiveRes Λ = Λ) :
    ((a10E J ψ Λ).subgroupOf J).map ψ = Λ := by
  apply le_antisymm
  · rintro q ⟨j, hj, rfl⟩
    obtain ⟨j', hj', hjj'⟩ := a10E_le_pre ψ Λ (Subgroup.mem_subgroupOf.mp hj)
    have : j' = j := Subtype.ext hjj'
    subst this
    exact hj'
  · calc Λ = fiveRes Λ := hΛ.symm
      _ ≤ _ := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro q ⟨hqΛ, k, hk⟩
        obtain ⟨l, hlq, a, ha⟩ := a10t1_five_lift ψ hψ hk
        refine ⟨l, ?_, hlq⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        refine Subgroup.subset_closure ⟨⟨l, ?_, rfl⟩, a, ?_⟩
        · show ψ l ∈ Λ
          rw [hlq]; exact hqΛ
        · have := congrArg Subtype.val ha
          simpa using this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
