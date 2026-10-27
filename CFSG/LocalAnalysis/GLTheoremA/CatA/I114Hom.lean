module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

@[expose] def actK (K : Subgroup Y) (b : Y) (hb : b ∈ Subgroup.normalizer (K : Set Y)) :
    ↥K ≃* ↥K where
  toFun k := ⟨b * k * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb k.1).1 k.2⟩
  invFun k := ⟨b⁻¹ * k * b, by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hb) k.1).1 k.2
    simpa [inv_inv] using this⟩
  left_inv k := Subtype.ext (by simp only [mul_assoc]; group)
  right_inv k := Subtype.ext (by simp only [mul_assoc]; group)
  map_mul' a c := Subtype.ext (by simp only [Subgroup.coe_mul, mul_assoc]; group)

theorem actK_apply (K : Subgroup Y) (b : Y) (hb : b ∈ Subgroup.normalizer (K : Set Y)) (k : ↥K) :
    ((actK K b hb) k : Y) = b * k * b⁻¹ := rfl

@[expose] def NBK (K B : Subgroup Y) : Subgroup Y := Subgroup.normalizer (K : Set Y) ⊓ B

@[expose] def CBK (K B : Subgroup Y) : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y)

theorem NBK_le_normalizer (K B : Subgroup Y) : NBK K B ≤ Subgroup.normalizer (K : Set Y) :=
  inf_le_left

theorem CBK_le_NBK (K B : Subgroup Y) : CBK K B ≤ NBK K B := by
  intro b hb
  obtain ⟨hbB, hbC⟩ := hb
  have hcomm : ∀ k ∈ K, k * b = b * k := fun k hk => Subgroup.mem_centralizer_iff.1 hbC k hk
  have key : ∀ k ∈ K, b * k * b⁻¹ = k := fun k hk => by
    rw [← hcomm k hk]
    group
  have key2 : ∀ k ∈ K, b⁻¹ * k * b = k := fun k hk => by
    calc b⁻¹ * k * b = b⁻¹ * (k * b) := by group
      _ = b⁻¹ * (b * k) := by rw [hcomm k hk]
      _ = k := by group
  have hN : b ∈ Subgroup.normalizer (K : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [key h hh]
      exact hh
    · intro hh
      have e : h = b⁻¹ * (b * h * b⁻¹) * b := by group
      rw [e, key2 _ hh]
      exact hh
  exact ⟨hN, hbB⟩

@[expose] def psiK (K M : Subgroup Y) (hM : M ≤ Subgroup.normalizer (K : Set Y)) :
    ↥M →* MulAut ↥K :=
  MonoidHom.mk' (fun m => actK K m.1 (hM m.2)) (fun a c => by
    ext k
    simp only [MulAut.mul_apply, actK_apply, Subgroup.coe_mul, mul_assoc]
    group)

theorem psiK_apply (K M : Subgroup Y) (hM : M ≤ Subgroup.normalizer (K : Set Y)) (m : ↥M)
    (k : ↥K) : ((psiK K M hM m) k : Y) = m.1 * k * m.1⁻¹ := rfl

theorem psiK_eq_one_iff (K M : Subgroup Y) (hM : M ≤ Subgroup.normalizer (K : Set Y)) (m : ↥M) :
    psiK K M hM m = 1 ↔ ∀ k ∈ K, m.1 * k = k * m.1 := by
  constructor
  · intro h k hk
    have h1 : ((psiK K M hM m) ⟨k, hk⟩ : Y) = k := by
      rw [h]
      rfl
    rw [psiK_apply] at h1
    calc m.1 * k = m.1 * k * m.1⁻¹ * m.1 := by group
      _ = k * m.1 := by rw [h1]
  · intro h
    ext k
    rw [psiK_apply, MulAut.one_apply]
    have := h k.1 k.2
    calc m.1 * k.1 * m.1⁻¹ = k.1 * m.1 * m.1⁻¹ := by rw [this]
      _ = k.1 := by group

theorem ker_psiK_eq (K B : Subgroup Y) :
    (psiK K (NBK K B) (NBK_le_normalizer K B)).ker =
      (CBK K B).subgroupOf (NBK K B) := by
  ext m
  rw [MonoidHom.mem_ker, psiK_eq_one_iff, Subgroup.mem_subgroupOf, CBK, Subgroup.mem_inf]
  constructor
  · intro h
    refine ⟨m.2.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (h k hk).symm
  · intro h k hk
    rw [Subgroup.mem_centralizer_iff] at h
    exact (h.2 k hk).symm

theorem card_NBK_eq [Finite Y] (K B : Subgroup Y) :
    Nat.card (NBK K B) = Nat.card (CBK K B) *
      Nat.card (psiK K (NBK K B) (NBK_le_normalizer K B)).range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (psiK K (NBK K B) (NBK_le_normalizer K B)).ker, mul_comm]
  congr 1
  · rw [ker_psiK_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (CBK_le_NBK K B)).toEquiv
  · exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv

end CFSG.LocalAnalysis.GLTheoremA.I114
