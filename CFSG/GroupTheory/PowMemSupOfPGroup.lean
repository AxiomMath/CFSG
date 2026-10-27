module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

theorem exists_pow_prime_pow_mem_of_mem_sup {p : ℕ} {L T : Subgroup G}
    (hT : IsPGroup p T) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ L ⊔ T) : ∃ k : ℕ, x ^ p ^ k ∈ L := by
  have hsup : ((L ⊔ T : Subgroup G) : Set G) = (T : Set G) * (L : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right T L hTL
  rw [← SetLike.mem_coe, hsup] at hx
  obtain ⟨t, ht, l, hl, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have key : ∀ n : ℕ, ∃ l' ∈ L, (t * l) ^ n = t ^ n * l' := by
    intro n
    induction n with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨l', hl', hn⟩ := ih
      have hconj : t⁻¹ * l' * t ∈ L := by
        have h := (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem ht)) l').mp hl'
        simpa using h
      refine ⟨t⁻¹ * l' * t * l, L.mul_mem hconj hl, ?_⟩
      rw [pow_succ, hn, pow_succ]
      group
  obtain ⟨l', hl', hn⟩ := key (p ^ k)
  exact ⟨k, by rw [hn, htk, one_mul]; exact hl'⟩

theorem isPGroup_quotient_sup_left {p : ℕ} {T C : Subgroup G} (hT : IsPGroup p T)
    [(C.subgroupOf (T ⊔ C)).Normal] :
    IsPGroup p (↥(T ⊔ C) ⧸ C.subgroupOf (T ⊔ C)) := by
  let Csub : Subgroup ↥(T ⊔ C) := C.subgroupOf (T ⊔ C)
  haveI : Csub.Normal := by
    dsimp [Csub]
    infer_instance
  have hCH : C ≤ T ⊔ C := le_sup_right
  have hHnorm : T ⊔ C ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCH).mp (by
      dsimp [Csub] at *
      infer_instance)
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := le_sup_left.trans hHnorm
  let f : ↥T →* (↥(T ⊔ C) ⧸ Csub) :=
    (QuotientGroup.mk' Csub).comp (Subgroup.inclusion (le_sup_left : T ≤ T ⊔ C))
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Csub q
    have hsup : ((T ⊔ C : Subgroup G) : Set G) = (T : Set G) * (C : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right T C hTC
    have hy : (y : G) ∈ (T : Set G) * (C : Set G) := by
      rw [← hsup]
      exact y.2
    obtain ⟨t, ht, c, hc, htc⟩ := hy
    refine ⟨⟨t, ht⟩, ?_⟩
    have htcH : (⟨t, (le_sup_left : T ≤ T ⊔ C) ht⟩ : ↥(T ⊔ C)) *
        ⟨c, (le_sup_right : C ≤ T ⊔ C) hc⟩ = y := Subtype.ext htc
    change QuotientGroup.mk' Csub ⟨t, (le_sup_left : T ≤ T ⊔ C) ht⟩ =
      QuotientGroup.mk' Csub y
    rw [← htcH, map_mul]
    have hc1 : QuotientGroup.mk' Csub ⟨c, (le_sup_right : C ≤ T ⊔ C) hc⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hc)
    rw [hc1, mul_one]
  exact IsPGroup.of_surjective hT f hf

end CFSG.GroupTheory
