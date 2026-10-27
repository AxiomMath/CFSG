module

public import CFSG.Certificates.Kernel.TwistDce.Cover
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.TwDce.TwistData

variable {G : Type*} [Group G] {H C : Subgroup G} {u : G} {r : ℕ} (D : TwistData H C u r)

theorem mul_u_mem' (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H) {g : G}
    (hg : ∃ i : Fin r, ∃ a ∈ H, ∃ b ∈ H, g = a * D.x i * b) :
    ∃ i : Fin r, ∃ a ∈ H, ∃ b ∈ H, g * u = a * D.x i * b := by
  obtain ⟨i, a, ha, b, hb, rfl⟩ := hg
  obtain ⟨j, a', ha', b', hb', he⟩ := D.mul_u_mem huC i hb
  refine ⟨j, a * a', H.mul_mem ha ha', b', hb', ?_⟩
  calc a * D.x i * b * u = a * (D.x i * b * u) := by group
    _ = a * (a' * D.x j * b') := by rw [he]
    _ = _ := by group

theorem mul_pow_mem (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H) (m : ℕ) {g : G}
    (hg : ∃ i : Fin r, ∃ a ∈ H, ∃ b ∈ H, g = a * D.x i * b) :
    ∃ i : Fin r, ∃ a ∈ H, ∃ b ∈ H, g * u ^ m = a * D.x i * b := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    rw [pow_succ, ← mul_assoc]
    exact D.mul_u_mem' huC ih

theorem exists_eq_of_pow {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1) (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H)
    (hgen : Subgroup.closure ((H : Set G) ∪ {u}) = ⊤) (g : G) :
    ∃ i : Fin r, ∃ a ∈ H, ∃ b ∈ H, g = a * D.x i * b := by
  have hg : g ∈ Subgroup.closure ((H : Set G) ∪ {u}) := hgen ▸ Subgroup.mem_top g
  have huinv : u⁻¹ = u ^ (n - 1) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hn, hu]
  induction hg using Subgroup.closure_induction_right with
  | one =>
    exact ⟨D.base, (D.x D.base)⁻¹, H.inv_mem D.base_mem, 1, H.one_mem, by group⟩
  | mul_right g _ y hy ih =>
    rcases hy with hy | hy
    · obtain ⟨i, a, ha, b, hb, rfl⟩ := ih
      exact ⟨i, a, ha, b * y, H.mul_mem hb hy, by group⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact D.mul_u_mem' huC ih
  | mul_inv_cancel g _ y hy ih =>
    rcases hy with hy | hy
    · obtain ⟨i, a, ha, b, hb, rfl⟩ := ih
      exact ⟨i, a, ha, b * y⁻¹, H.mul_mem hb (H.inv_mem hy), by group⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy, huinv]
      exact D.mul_pow_mem huC (n - 1) ih

theorem index_le_sum_of_pow {n : ℕ} (hn : 0 < n) (hu : u ^ n = 1)
    (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H) (hgen : Subgroup.closure ((H : Set G) ∪ {u}) = ⊤) [Finite H] :
    H.FiniteIndex ∧ H.index ≤ ∑ i, (D.S i).relIndex H := by
  classical
  let φ : (Σ i : Fin r, H ⧸ (D.S i).subgroupOf H) → G ⧸ H := fun p =>
    Quotient.liftOn' p.2 (fun k : H => ((k * (D.x p.1)⁻¹ : G) : G ⧸ H)) (by
      intro k k' hkk'
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hkk'
      exact D.mk_mul_inv_eq (by simpa using hkk'))
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨i, a, ha, b, hb, hab⟩ := D.exists_eq_of_pow hn hu huC hgen g⁻¹
      refine ⟨⟨i, ((⟨b⁻¹, H.inv_mem hb⟩ : H) : H ⧸ (D.S i).subgroupOf H)⟩, ?_⟩
      change ((b⁻¹ * (D.x i)⁻¹ : G) : G ⧸ H) = (g : G ⧸ H)
      rw [QuotientGroup.eq]
      have hg : g = b⁻¹ * (D.x i)⁻¹ * a⁻¹ := by
        rw [← inv_inv g, hab]; group
      rw [hg]
      have e : (b⁻¹ * (D.x i)⁻¹)⁻¹ * (b⁻¹ * (D.x i)⁻¹ * a⁻¹) = a⁻¹ := by group
      rw [e]
      exact H.inv_mem ha
  have : Finite (G ⧸ H) := Finite.of_surjective φ hsurj
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  calc H.index = Nat.card (G ⧸ H) := Subgroup.index_eq_card H
    _ ≤ Nat.card (Σ i : Fin r, H ⧸ (D.S i).subgroupOf H) := Nat.card_le_card_of_surjective φ hsurj
    _ = ∑ i, Nat.card (H ⧸ (D.S i).subgroupOf H) := Nat.card_sigma
    _ = ∑ i, (D.S i).relIndex H := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Subgroup.relIndex, Subgroup.index_eq_card]

end CFSG.Certificates.TwDce.TwistData

end
