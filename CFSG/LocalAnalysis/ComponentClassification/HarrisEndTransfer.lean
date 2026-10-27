module

public import CFSG.GH74.GLS.Bg.Local.Transfer1515
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralD

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open CFSG Subgroup GH74.GLS.Bg.Thompson

variable {X : Type} [Group X] [Finite X]

theorem inv_mul_mem_of_cyclic {P Q : Subgroup X} (hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q) {u v : X} (huP : u ∈ P) (hvP : v ∈ P)
    (huQ : u ∉ Q) (hvQ : v ∉ Q) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) : u⁻¹ * v ∈ Q := by
  have hn : (Q.subgroupOf P).Normal := ⟨fun n hn g => hQn g g.2 n hn⟩
  set φ := QuotientGroup.mk' (Q.subgroupOf P) with hφ
  obtain ⟨b, hbP, hb⟩ := hcyc
  have hcy : IsCyclic (↥P ⧸ Q.subgroupOf P) := by
    refine ⟨φ ⟨b, hbP⟩, fun x => ?_⟩
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf P) x
    obtain ⟨k, hk⟩ := hb t t.2
    refine ⟨k, ?_⟩
    show φ ⟨b, hbP⟩ ^ k = φ t
    rw [← map_zpow, hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact hk
  have hord : ∀ y : X, ∀ hy : y ∈ P, y ∉ Q → y ^ 2 = 1 → orderOf (φ ⟨y, hy⟩) = 2 := by
    intro y hy hyQ hy2
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      rw [show (⟨y, hy⟩ : ↥P) ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow, hy2]; rfl),
        map_one]
    · intro h
      apply hyQ
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact h
  have hu := hord u huP huQ hu2
  have hv := hord v hvP hvQ hv2
  have heq : zpowers (φ ⟨u, huP⟩) = zpowers (φ ⟨v, hvP⟩) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hu, hv]
  have hmem : φ ⟨v, hvP⟩ ∈ zpowers (φ ⟨u, huP⟩) := heq ▸ mem_zpowers _
  rcases eq_one_or_eq_of_mem_zpowers hu hmem with h | h
  · exact absurd h (fun h1 => by rw [h1, orderOf_one] at hv; exact absurd hv (by norm_num))
  · have h1 : φ (⟨u, huP⟩⁻¹ * ⟨v, hvP⟩) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1

theorem exists_extremal_conj_of_cyclic [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    {P Q : Subgroup X} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index)
    (hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) (hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q)
    {u : X} (huP : u ∈ P) (huQ : u ∉ Q) (hu2 : u ^ 2 = 1) :
    ∃ g : X, g⁻¹ * u * g ∈ Q ∧ IsExtremalIn 2 P (g⁻¹ * u * g) ∧
      ∀ c ∈ P ⊓ centralizer {u}, g⁻¹ * c * g ∈ P ⊓ centralizer {g⁻¹ * u * g} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : ∀ (g : X) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ P → g⁻¹ * u ^ (2 * k) * g ∈ Q := by
    intro g k _
    rw [pow_mul, hu2, one_pow, mul_one, inv_mul_cancel]
    exact one_mem _
  have hc : ∀ g : X, g⁻¹ * u * g ∈ P → IsExtremalIn 2 P (g⁻¹ * u * g) →
      g⁻¹ * u * g ∈ Q ∨ u⁻¹ * (g⁻¹ * u * g) ∈ Q := by
    intro g hg _
    by_cases hgQ : g⁻¹ * u * g ∈ Q
    · exact Or.inl hgQ
    · right
      have hv2 : (g⁻¹ * u * g) ^ 2 = 1 := by
        rw [sq, show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, ← sq, hu2]
        group
      exact inv_mul_mem_of_cyclic hQn hcyc huP hg huQ hgQ hu2 hv2
  rcases thompson_transfer_1515 hP hPidx hQn hcyc huP huQ hb hc with ⟨N, hN, hcN, -, huN⟩ | h
  · exfalso
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
    ·
      have : IsCyclic X := isCyclic_of_surjective (QuotientGroup.quotientBot.toMonoidHom)
        QuotientGroup.quotientBot.surjective
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (IsCyclic.commGroup.mul_comm a b)
    · exact huN (mem_top u)
  · exact h

theorem exists_extremal_conj_of_relIndex_two [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    {P Q : Subgroup X} (hP : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index) (hQP : Q ≤ P)
    (hidx : Q.relIndex P = 2) {u : X} (huP : u ∈ P) (huQ : u ∉ Q) (hu2 : u ^ 2 = 1) :
    ∃ g : X, g⁻¹ * u * g ∈ Q ∧ IsExtremalIn 2 P (g⁻¹ * u * g) ∧
      ∀ c ∈ P ⊓ centralizer {u}, g⁻¹ * c * g ∈ P ⊓ centralizer {g⁻¹ * u * g} := by
  have hn : (Q.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two hidx
  have hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun t ht q hq =>
    hn.conj_mem ⟨q, hQP hq⟩ hq ⟨t, ht⟩
  refine exists_extremal_conj_of_cyclic hnab hP hPidx hQn ⟨u, huP, fun t ht => ?_⟩ huP huQ hu2
  by_cases htQ : t ∈ Q
  · exact ⟨0, by rw [zpow_zero, inv_one, one_mul]; exact htQ⟩
  · refine ⟨1, ?_⟩
    rw [zpow_one]
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨u, huP⟩ : ↥P)⁻¹)
      (b := ⟨t, ht⟩)).mpr ⟨fun h => absurd (by simpa [mem_subgroupOf] using h) huQ,
        fun h => absurd h htQ⟩
    exact h

end CFSG.ComponentClassification.HarrisLit.HarrisEnd
