module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47b

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1

open Subgroup CFSG.GH74.GLS.Stage1.Thm3.Sec4.M CFSG.GH74.GLS CFSG.GH74

variable {G : Type} [Group G] [Finite G] {z : G} {S P Q F : Subgroup G} {FA : G → Prop}

omit [Finite G] in
theorem exists_gen_of_cyclic {V : Subgroup G} (hV : IsCyclic ↥V) : ∃ g ∈ V, ∀ v ∈ V, v ∈ zpowers g := by
  obtain ⟨g, hg⟩ := hV.exists_generator
  refine ⟨(g : G), g.2, fun v hv => ?_⟩
  obtain ⟨k, hk⟩ := (mem_zpowers_iff).1 (hg ⟨v, hv⟩)
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem invol_mem_zpowers {V : Subgroup G} (hV : IsCyclic ↥V) (hV2 : IsPGroup 2 ↥V) {c t : G}
    (hc : c ∈ V) (hc1 : c ≠ 1) (ht : t ∈ V) (ht2 : t * t = 1) (ht1 : t ≠ 1) : t ∈ zpowers c := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hV2) ⟨c, hc⟩
  have hk' : orderOf c = 2 ^ k := by simpa using hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hc1 (orderOf_eq_one_iff.1 (by simpa using hk'))
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hsq : (c ^ (2 ^ j)) * (c ^ (2 ^ j)) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [← hk']; exact pow_orderOf_eq_one c
  have hne : c ^ (2 ^ j) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [hk']
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hmem : c ^ (2 ^ j) ∈ V := V.pow_mem hc _
  have := B.cyclic_invol_unique hV hmem ht hsq ht2 hne ht1
  rw [← this]
  exact pow_mem (mem_zpowers c) _

@[expose] def HThompson (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ S → Four U → (∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) →
    ∀ u ∈ U, u ≠ 1 → u ≠ z → IsConj z u →
      ∃ x : G, x ∈ normalizer ((S ⊓ centralizer (U : Set G) : Subgroup G) : Set G) ∧
        x * z * x⁻¹ ≠ z

namespace Cfg1

theorem mem_four (h : Cfg1 G z S P Q F FA) {U : Subgroup G} (hU : Four U) (hz : z ∈ U) {u : G}
    (hu : u ∈ U) (hu1 : u ≠ 1) (huz : u ≠ z) {v : G} (hv : v ∈ U) :
    v = 1 ∨ v = z ∨ v = u ∨ v = u * z := by
  have hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => B.comm_of_forall_sq hU.1 ha hb
  have hzc : zpowers z ≤ U := zpowers_le.2 hz
  have huc : zpowers u ≤ U := zpowers_le.2 hu
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers u, a * b = b * a := by
    intro a ha b hb
    exact hc a (hzc ha) b (huc hb)
  have hnorm : zpowers u ≤ normalizer (zpowers z : Set G) := le_normalizer_of_commute hcomm
  have hcard := card_sup_mul_card_inf hnorm
  have hu2 : u * u = 1 := hU.1 u hu
  have hz2 := h.z_sq
  have hcz : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_two_of_sq_one hz2 h.z_ne
  have hcu : Nat.card ↥(zpowers u) = 2 := by
    rw [Nat.card_zpowers]; exact orderOf_two_of_sq_one hu2 hu1
  have hinf : zpowers z ⊓ zpowers u = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rcases (mem_zpowers_of_sq hz2).1 ha.1 with h1 | h1
    · rw [h1]; exact one_mem _
    · rcases (mem_zpowers_of_sq hu2).1 ha.2 with h2 | h2
      · rw [h2]; exact one_mem _
      · exact absurd (h2.symm.trans h1) huz
  rw [hinf, Subgroup.card_bot, hcz, hcu] at hcard
  have hle : zpowers z ⊔ zpowers u ≤ U := sup_le hzc huc
  have hcardU : Nat.card ↥(zpowers z ⊔ zpowers u) = 4 := by omega
  have heq : zpowers z ⊔ zpowers u = U :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hU.2, hcardU])
  rw [← heq] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hv
  rcases (mem_zpowers_of_sq hz2).1 ha with h1 | h1 <;> rcases (mem_zpowers_of_sq hu2).1 hb with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2, hc z hz u hu]

end Cfg1

namespace Cfg1K

theorem mem_PF_of_centralizes (h : Cfg1K G z S P Q F FA) (hF : IsCyclic ↥F) {y u₂ : G}
    (hy : Is47b S P F y) (hu₂ : u₂ ∈ Q) (h2 : u₂ * u₂ = z) (hinv : y * u₂ * y⁻¹ = u₂⁻¹) {s : G}
    (hs : s ∈ S) (hc : s * u₂ = u₂ * s) : s ∈ P ⊔ F := by
  obtain ⟨hyS, hy2, hyPF, -⟩ := hy
  by_contra hsPF
  have hsy : s * y⁻¹ ∈ P ⊔ F := (B.mem_or_mul_inv_mem h.idx hyS hyPF hs).resolve_left hsPF
  have hle : P ⊔ F ≤ centralizer ({u₂} : Set G) := by
    refine sup_le ?_ ?_
    · intro p hp
      exact Subgroup.mem_centralizer_singleton_iff.2 (h.PQ_comm p hp u₂ hu₂)
    · intro t ht
      exact Subgroup.mem_centralizer_singleton_iff.2
        (comm_of_cyclic hF ht (h.Q_le_F hu₂))
  have h1 : (s * y⁻¹) * u₂ = u₂ * (s * y⁻¹) := Subgroup.mem_centralizer_singleton_iff.1 (hle hsy)
  have h3 : y⁻¹ * u₂ = u₂ * y⁻¹ := by
    have : s * (y⁻¹ * u₂) = s * (u₂ * y⁻¹) := by
      calc s * (y⁻¹ * u₂) = (s * y⁻¹) * u₂ := by group
        _ = u₂ * (s * y⁻¹) := h1
        _ = (u₂ * s) * y⁻¹ := by group
        _ = (s * u₂) * y⁻¹ := by rw [hc]
        _ = s * (u₂ * y⁻¹) := by group
    exact mul_left_cancel this
  have h4 : y * u₂ * y⁻¹ = u₂ := by
    calc y * u₂ * y⁻¹ = y * (u₂ * y⁻¹) := by group
      _ = y * (y⁻¹ * u₂) := by rw [h3]
      _ = u₂ := by group
  rw [h4] at hinv
  have h5 : u₂ * u₂ = 1 := by
    calc u₂ * u₂ = u₂ * u₂⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel u₂
  rw [h2] at h5
  exact h.z_ne h5

end Cfg1K

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1
