module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.TwDce

variable {G : Type*} [Group G]

structure TwistData (H C : Subgroup G) (u : G) (r : ℕ) where
  x : Fin r → G
  S : Fin r → Subgroup G
  rep : Fin r → Set G
  tgt : (i : Fin r) → G → Fin r
  tgtElt : (i : Fin r) → G → G
  base : Fin r
  base_mem : x base ∈ H
  S_le : ∀ i, S i ≤ H
  S_conj : ∀ i, ∀ s ∈ S i, x i * s * (x i)⁻¹ ∈ H
  rep_le : ∀ i, ∀ k ∈ rep i, k ∈ H
  rep_cover : ∀ i, ∀ h ∈ H, ∃ k ∈ rep i, ∃ s ∈ S i, ∃ c ∈ C, h = s * k * c
  tgtElt_mem : ∀ i, ∀ k ∈ rep i, tgtElt i k ∈ H
  tgt_spec : ∀ i, ∀ k ∈ rep i, x i * k * u * (x (tgt i k) * tgtElt i k)⁻¹ ∈ H

namespace TwistData

variable {H C : Subgroup G} {u : G} {r : ℕ} (D : TwistData H C u r)

theorem mul_u_mem (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H) (i : Fin r) {h : G} (hh : h ∈ H) :
    ∃ j : Fin r, ∃ a ∈ H, ∃ b ∈ H, D.x i * h * u = a * D.x j * b := by
  obtain ⟨k, hk, s, hs, c, hc, rfl⟩ := D.rep_cover i h hh
  refine ⟨D.tgt i k, D.x i * s * (D.x i)⁻¹ * (D.x i * k * u * (D.x (D.tgt i k) * D.tgtElt i k)⁻¹),
    H.mul_mem (D.S_conj i s hs) (D.tgt_spec i k hk), D.tgtElt i k * (u⁻¹ * c * u),
    H.mul_mem (D.tgtElt_mem i k hk) (huC c hc), ?_⟩
  group

theorem exists_eq (hu : u * u = 1) (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H)
    (hgen : Subgroup.closure ((H : Set G) ∪ {u}) = ⊤) (g : G) :
    ∃ i : Fin r, ∃ a ∈ H, ∃ b ∈ H, g = a * D.x i * b := by
  have hg : g ∈ Subgroup.closure ((H : Set G) ∪ {u}) := hgen ▸ Subgroup.mem_top g
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  induction hg using Subgroup.closure_induction_right with
  | one =>
    exact ⟨D.base, (D.x D.base)⁻¹, H.inv_mem D.base_mem, 1, H.one_mem, by group⟩
  | mul_right g _ y hy ih =>
    obtain ⟨i, a, ha, b, hb, rfl⟩ := ih
    rcases hy with hy | hy
    · exact ⟨i, a, ha, b * y, H.mul_mem hb hy, by group⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      obtain ⟨j, a', ha', b', hb', he⟩ := D.mul_u_mem huC i hb
      refine ⟨j, a * a', H.mul_mem ha ha', b', hb', ?_⟩
      calc a * D.x i * b * u = a * (D.x i * b * u) := by group
        _ = a * (a' * D.x j * b') := by rw [he]
        _ = _ := by group
  | mul_inv_cancel g _ y hy ih =>
    obtain ⟨i, a, ha, b, hb, rfl⟩ := ih
    rcases hy with hy | hy
    · exact ⟨i, a, ha, b * y⁻¹, H.mul_mem hb (H.inv_mem hy), by group⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy, huinv]
      obtain ⟨j, a', ha', b', hb', he⟩ := D.mul_u_mem huC i hb
      refine ⟨j, a * a', H.mul_mem ha ha', b', hb', ?_⟩
      calc a * D.x i * b * u = a * (D.x i * b * u) := by group
        _ = a * (a' * D.x j * b') := by rw [he]
        _ = _ := by group

theorem mk_mul_inv_eq {i : Fin r} {k k' : G} (h : k⁻¹ * k' ∈ D.S i) :
    ((k * (D.x i)⁻¹ : G) : G ⧸ H) = ((k' * (D.x i)⁻¹ : G) : G ⧸ H) := by
  rw [QuotientGroup.eq]
  have := D.S_conj i _ h
  rw [show (k * (D.x i)⁻¹)⁻¹ * (k' * (D.x i)⁻¹) = D.x i * (k⁻¹ * k') * (D.x i)⁻¹ by group]
  exact this

theorem index_le_sum (hu : u * u = 1) (huC : ∀ c ∈ C, u⁻¹ * c * u ∈ H)
    (hgen : Subgroup.closure ((H : Set G) ∪ {u}) = ⊤) [Finite H] :
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
      obtain ⟨i, a, ha, b, hb, hab⟩ := D.exists_eq hu huC hgen g⁻¹
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

end TwistData

end CFSG.Certificates.TwDce

end
