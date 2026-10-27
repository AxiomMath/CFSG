module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB8
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

section Decomp

variable {G : Type} [Group G]

theorem exists_mul_mul_of_mem_sup {A B C : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAC : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hBC : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) {m : G} (hm : m ∈ A ⊔ B ⊔ C) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, m = a * b * c := by
  have hAN : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    mem_normalizer_of_commute fun b hb => hAB a ha b hb
  have e1 := Subgroup.coe_mul_of_left_le_normalizer_right A B hAN
  have hABN : A ⊔ B ≤ Subgroup.normalizer (C : Set G) := by
    intro x hx
    have hx' : x ∈ (A : Set G) * (B : Set G) := by
      rw [← e1]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    refine mem_normalizer_of_commute fun c hc => ?_
    calc a * b * c = a * (b * c) := by group
      _ = a * (c * b) := by rw [hBC b hb c hc]
      _ = (a * c) * b := by group
      _ = (c * a) * b := by rw [hAC a ha c hc]
      _ = c * (a * b) := by group
  have e2 := Subgroup.coe_mul_of_left_le_normalizer_right (A ⊔ B) C hABN
  have hm' : m ∈ ((A ⊔ B : Subgroup G) : Set G) * (C : Set G) := by
    rw [← e2]
    exact hm
  obtain ⟨x, hx, c, hc, rfl⟩ := hm'
  have hx' : x ∈ (A : Set G) * (B : Set G) := by
    rw [← e1]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

end Decomp

section Card

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a w : G}

theorem Sec4Hyp.card_sec4Psi_le (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w)
    (hwT : w ∈ Subgroup.normalizer (T : Set G)) {f : ℕ}
    (hcardT : Nat.card T = Nat.card (normIn T T₁) * 2 ^ f)
    (hC : Nat.card (normIn T T₁) ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({w} : Set G))) :
    Nat.card ↥(sec4Psi h hw T) ≤ 2 ^ f := by
  have hTab := h.pair.wc.1
  have hwT' : ∀ t ∈ T, w * t * w⁻¹ ∈ T := fun t ht => conj_mem_of_mem_normalizer hwT ht
  let νT : ↥T →* ↥T := normCommHom T w (fun _ hm _ hm' => elemAbelian_mul_comm hTab hm hm') hwT'
  have hA : (sec4Psi h hw T).map (sec4N T T₁ T₂).subtype ≤ νT.range.map T.subtype := by
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    have hm' := Subgroup.mem_subgroupOf.1 hm
    refine ⟨νT ⟨m, hm'.1⟩, ⟨⟨m, hm'.1⟩, rfl⟩, rfl⟩
  have hcardA : Nat.card ↥((sec4Psi h hw T).map (sec4N T T₁ T₂).subtype) =
      Nat.card ↥(sec4Psi h hw T) :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hcardB : Nat.card ↥(νT.range.map T.subtype) = Nat.card ↥νT.range :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hker : Nat.card ↥νT.ker = Nat.card ↥(T ⊓ Subgroup.centralizer ({w} : Set G)) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective T) (K := νT.ker)]
    congr 2
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := congrArg Subtype.val ht
      have h2 : w * (t : G) * w⁻¹ * (t : G)⁻¹ = 1 := h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · rintro ⟨hxT, hxC⟩
      refine ⟨⟨x, hxT⟩, ?_, rfl⟩
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 hxC
      apply Subtype.ext
      show w * x * w⁻¹ * x⁻¹ = 1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h2.symm
  have hmul := Subgroup.card_ker_mul_card_range νT
  have hle : Nat.card ↥(sec4Psi h hw T) ≤ Nat.card ↥νT.range := by
    rw [← hcardA, ← hcardB]
    exact Subgroup.card_le_of_le hA
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  refine le_trans hle ?_
  rw [hker] at hmul
  refine Nat.le_of_mul_le_mul_left ?_ hLpos
  calc Nat.card (normIn T T₁) * Nat.card ↥νT.range
      ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({w} : Set G)) * Nat.card ↥νT.range :=
        Nat.mul_le_mul_right _ hC
    _ = Nat.card T := hmul
    _ = Nat.card (normIn T T₁) * 2 ^ f := hcardT

end Card

end CFSG.CGT.Timmesfeld75
