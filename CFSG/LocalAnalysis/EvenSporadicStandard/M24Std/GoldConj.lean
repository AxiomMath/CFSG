module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.M24Std.Gold

open Subgroup

variable {G : Type*} [Group G]

@[expose] def cj (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g x : G} {H : Subgroup G} : x ∈ cj g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conj_mem_cj {g x : G} {H : Subgroup G} (hx : x ∈ H) : g * x * g⁻¹ ∈ cj g H :=
  mem_cj.2 (by simpa [mul_assoc] using hx)

@[simp]
theorem cj_one (H : Subgroup G) : cj 1 H = H := by
  ext x
  simp [mem_cj]

theorem cj_mul (g h : G) (H : Subgroup G) : cj (g * h) H = cj g (cj h H) := by
  ext x
  simp [mem_cj, mul_assoc]

@[simp]
theorem cj_inv_cj (g : G) (H : Subgroup G) : cj g⁻¹ (cj g H) = H := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

@[simp]
theorem cj_cj_inv (g : G) (H : Subgroup G) : cj g (cj g⁻¹ H) = H := by
  rw [← cj_mul, mul_inv_cancel, cj_one]

theorem cj_le_cj {g : G} {H K : Subgroup G} : cj g H ≤ cj g K ↔ H ≤ K :=
  ⟨fun h x hx => by simpa [mul_assoc] using mem_cj.1 (h (conj_mem_cj (g := g) hx)),
    Subgroup.map_mono⟩

theorem cj_le_iff {g : G} {H K : Subgroup G} : cj g H ≤ K ↔ H ≤ cj g⁻¹ K := by
  rw [← cj_le_cj (g := g⁻¹) (H := cj g H), cj_inv_cj]

theorem cj_inf (g : G) (H K : Subgroup G) : cj g (H ⊓ K) = cj g H ⊓ cj g K := by
  ext x
  simp [mem_cj]

theorem cj_sup (g : G) (H K : Subgroup G) : cj g (H ⊔ K) = cj g H ⊔ cj g K :=
  Subgroup.map_sup _ _ _

theorem card_cj (g : G) (H : Subgroup G) : Nat.card (cj g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_cj {p : ℕ} {H : Subgroup G} (h : IsPGroup p H) (g : G) : IsPGroup p (cj g H) :=
  h.map _

theorem mem_normalizer_of_cj_le {y : G} {H : Subgroup G} (h₁ : cj y H ≤ H)
    (h₂ : cj y⁻¹ H ≤ H) : y ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact h₁ (conj_mem_cj hz)
  · intro hz
    have := h₂ (conj_mem_cj (g := y⁻¹) hz)
    simpa [mul_assoc] using this

section Sylow

variable [Finite G]

theorem exists_le_cj_sylow (T : Sylow 2 G) {S : Subgroup G} (hS : IsPGroup 2 S) :
    ∃ x : G, S ≤ cj x T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G T Q
  refine ⟨x, fun s hs => ?_⟩
  have hsQ : s ∈ (Q : Subgroup G) := hQ hs
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hsQ
  obtain ⟨y, hy, rfl⟩ := hsQ
  exact ⟨y, hy, rfl⟩

theorem exists_isPGroup_sup_cj {K P Q : Subgroup G} (hP : IsPGroup 2 P)
    (hQ : IsPGroup 2 Q) (hPK : P ≤ K) (hQK : Q ≤ K) : ∃ k ∈ K, IsPGroup 2 ↥(P ⊔ cj k Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf K) := hP.comap_of_injective K.subtype K.subtype_injective
  have hQ' : IsPGroup 2 (Q.subgroupOf K) := hQ.comap_of_injective K.subtype K.subtype_injective
  obtain ⟨S₁, h₁⟩ := hP'.exists_le_sylow
  obtain ⟨S₂, h₂⟩ := hQ'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S₂ S₁
  refine ⟨k, k.2, ?_⟩
  have hS : IsPGroup 2 ((S₁ : Subgroup K).map K.subtype) := S₁.isPGroup'.map K.subtype
  refine hS.to_le (sup_le ?_ ?_)
  · intro x hx
    exact ⟨⟨x, hPK hx⟩, h₁ hx, rfl⟩
  · intro y hy
    rw [mem_cj] at hy
    have hxS : (⟨(k : G)⁻¹ * y * k, hQK hy⟩ : K) ∈ (S₂ : Subgroup K) := h₂ hy
    have h3 : (MulAut.conj k) • (⟨(k : G)⁻¹ * y * k, hQK hy⟩ : K) ∈
        ((k • S₂ : Sylow 2 K) : Subgroup K) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hxS
    rw [hk] at h3
    refine ⟨_, h3, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]

end Sylow

end CFSG.EvenSporadicStandard.M24Std.Gold
