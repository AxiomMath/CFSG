module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.LargeExtraspecial.GLR

open CFSG.GH74.GLS.Bg.Thompson Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_extremal_conj_mem_of_sq_eq (hG : ∀ N : Subgroup G, N.index ≠ 2)
    {T U : Subgroup G} (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T)
    (hUidx : U.relIndex T = 2) {g d : G} (hgT : g ∈ T) (hgU : g ∉ U) (hgd : g * g = d)
    (hd : d * d = 1) (hdU : ∀ x : G, x⁻¹ * d * x ∈ T → x⁻¹ * d * x ∈ U) :
    ∃ x : G, x⁻¹ * g * x ∈ U ∧ IsExtremalIn 2 T (x⁻¹ * g * x) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hQn : ∀ t ∈ T, ∀ q ∈ U, t * q * t⁻¹ ∈ U := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hUT hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ U := by
    refine ⟨g, hgT, fun t ht => ?_⟩
    by_cases htU : t ∈ U
    · exact ⟨0, by simpa using htU⟩
    · exact ⟨1, by
        simpa using CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUidx hgT ht hgU htU⟩
  have hpow : ∀ k : ℕ, g ^ (2 * k) = 1 ∨ g ^ (2 * k) = d := by
    intro k
    induction k with
    | zero => exact Or.inl (by simp)
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, pow_two, hgd]
      rcases ih with h | h
      · exact Or.inr (by rw [h, one_mul])
      · exact Or.inl (by rw [h, hd])
  have hb : ∀ (x : G) (k : ℕ), x⁻¹ * g ^ (2 * k) * x ∈ T → x⁻¹ * g ^ (2 * k) * x ∈ U := by
    intro x k hx
    rcases hpow k with h | h
    · rw [h, mul_one, inv_mul_cancel]
      exact U.one_mem
    · rw [h] at hx ⊢
      exact hdU x hx
  have hc : ∀ x : G, x⁻¹ * g * x ∈ T → IsExtremalIn 2 T (x⁻¹ * g * x) →
      x⁻¹ * g * x ∈ U ∨ g⁻¹ * (x⁻¹ * g * x) ∈ U := by
    intro x hxT _
    by_cases hxU : x⁻¹ * g * x ∈ U
    · exact Or.inl hxU
    · exact Or.inr (CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hUidx hgT hxT hgU hxU)
  rcases thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc hgT hgU hb hc with
    ⟨N, hN, -, hNp, hgN⟩ | ⟨x, hx, hext, -⟩
  · exfalso
    have := hN
    have : Group.IsNilpotent (G ⧸ N) := hNp.isNilpotent
    have hbt : (⊥ : Subgroup (G ⧸ N)) ≠ ⊤ := by
      intro h
      apply hgN
      have h1 : (QuotientGroup.mk g : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff g).1 (Subgroup.mem_bot.1 h1)
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ N))).resolve_left hbt
    have hMidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hNp).1 hM
    exact hG _ ((Subgroup.index_comap_of_surjective M (f := QuotientGroup.mk' N)
      QuotientGroup.mk_surjective).trans hMidx)
  · exact ⟨x, hx, hext⟩

omit [Finite G] in
theorem index_ne_two_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (N : Subgroup G) : N.index ≠ 2 := by
  intro hN
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  rcases this.eq_bot_or_eq_top with h | h
  · subst h
    rw [Subgroup.index_bot] at hN
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc : IsCyclic G := isCyclic_of_prime_card hN
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsCyclic.isMulCommutative.is_comm.comm a b)
  · subst h
    rw [Subgroup.index_top] at hN
    exact absurd hN (by norm_num)

theorem exists_extremal_conj_mem_of_sq_eq_of_isSimpleGroup [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {g d : G} (hgT : g ∈ T)
    (hgU : g ∉ U) (hgd : g * g = d) (hd : d * d = 1)
    (hdU : ∀ x : G, x⁻¹ * d * x ∈ T → x⁻¹ * d * x ∈ U) :
    ∃ x : G, x⁻¹ * g * x ∈ U ∧ IsExtremalIn 2 T (x⁻¹ * g * x) :=
  exists_extremal_conj_mem_of_sq_eq (index_ne_two_of_isSimpleGroup hnonab) hT hTidx hUT hUidx
    hgT hgU hgd hd hdU

end CFSG.LargeExtraspecial.GLR
