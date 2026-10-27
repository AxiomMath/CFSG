module

public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.GH74.GLS.Bg.Thompson Subgroup

theorem exists_extremal_conj_mem_of_index_two {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T S : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hST : S ≤ T) (hSidx : S.relIndex T = 2) {u : G} (huT : u ∈ T)
    (huS : u ∉ S) (hu2 : u * u = 1) :
    ∃ g : G, g⁻¹ * u * g ∈ S ∧ IsExtremalIn 2 T (g⁻¹ * u * g) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hSidx
  have hQn : ∀ t ∈ T, ∀ q ∈ S, t * q * t⁻¹ ∈ S := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hST hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ S := by
    refine ⟨u, huT, fun t ht => ?_⟩
    by_cases htS : t ∈ S
    · exact ⟨0, by simpa using htS⟩
    · exact ⟨1, by simpa using CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hSidx huT ht huS htS⟩
  have hsq : u ^ 2 = 1 := by rw [pow_two]; exact hu2
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ T → g⁻¹ * u ^ (2 * k) * g ∈ S := by
    intro g k _
    have h1 : u ^ (2 * k) = 1 := by rw [pow_mul, hsq, one_pow]
    rw [h1]
    simp
  have hc : ∀ g : G, g⁻¹ * u * g ∈ T → IsExtremalIn 2 T (g⁻¹ * u * g) →
      g⁻¹ * u * g ∈ S ∨ u⁻¹ * (g⁻¹ * u * g) ∈ S := by
    intro g hgT _
    by_cases hgS : g⁻¹ * u * g ∈ S
    · exact Or.inl hgS
    · exact Or.inr (CFSG.ThompsonIndexTwo.inv_mul_mem_of_not_mem hSidx huT hgT huS hgS)
  rcases thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc huT huS hb hc with
    ⟨N, hN, hcycN, -, huN⟩ | ⟨g, hg, hext, -⟩
  · exfalso
    rcases hN.eq_bot_or_eq_top with h | h
    · subst h
      have hcycG : IsCyclic G :=
        (QuotientGroup.quotientBot.isCyclic).mp hcycN
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (IsCyclic.isMulCommutative.is_comm.comm a b)
    · exact huN (h ▸ Subgroup.mem_top u)
  · exact ⟨g, hg, hext⟩

end CFSG.QuasithinUnique.DoubleA3
