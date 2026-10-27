module

import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedRankAux
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbedding

theorem injective_comp_subtype_of_coprime {p : ℕ} {Y Z : Type*} [Group Y] [Group Z]
    (g : Y →* Z) (hg : ∀ y, g y = 1 → p.Coprime (orderOf y)) {Q : Subgroup Y}
    (hQ : IsPGroup p Q) : Function.Injective (g.comp Q.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  have h1 : g q = 1 := hq
  rw [Subgroup.mem_bot]
  exact Subtype.ext (eq_one_of_mem_of_coprime hQ q.2 (hg q h1).symm)

theorem card_map_of_coprime {p : ℕ} {Y Z : Type*} [Group Y] [Group Z] (g : Y →* Z)
    (hg : ∀ y, g y = 1 → p.Coprime (orderOf y)) {Q : Subgroup Y} (hQ : IsPGroup p Q) :
    Nat.card (Q.map g) = Nat.card Q := by
  have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup Q))
    (injective_comp_subtype_of_coprime g hg hQ)
  rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  rw [h, Subgroup.card_top]

theorem card_map_le {Y Z : Type*} [Group Y] [Group Z] [Finite Y] (g : Y →* Z) (Q : Subgroup Y) :
    Nat.card (Q.map g) ≤ Nat.card Q :=
  Nat.card_le_card_of_surjective _ (g.subgroupMap_surjective Q)

theorem card_le_of_le_map {X W : Type*} [Group X] [Group W] [Finite X] {p t : ℕ} (φ : X →* W)
    {K : Subgroup X} (hinj : ∀ x ∈ K, φ x = 1 → x = 1)
    (ht : ∀ P : Subgroup X, P ≤ K → IsPGroup p P → Nat.card P ≤ t)
    {P₁ : Subgroup W} (hP₁ : P₁ ≤ K.map φ) (hp : IsPGroup p P₁) : Nat.card P₁ ≤ t := by
  set P₀ := P₁.comap φ ⊓ K with hP₀
  have hinj₀ : Function.Injective (φ.comp P₀.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hinj x x.2.2 hx)
  have hmap : P₀.map φ = P₁ := by
    refine le_antisymm (fun w ⟨x, hx, hxw⟩ => hxw ▸ hx.1) fun w hw => ?_
    obtain ⟨x, hx, rfl⟩ := hP₁ hw
    exact ⟨x, ⟨hw, hx⟩, rfl⟩
  have hcard : Nat.card P₁ = Nat.card P₀ := by
    have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup P₀)) hinj₀
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hmap] at h
    rw [h, Subgroup.card_top]
  have hP₀p : IsPGroup p P₀ := hp.of_injective ((φ.comp P₀.subtype).codRestrict P₁
    fun x => x.2.1) fun a b hab => hinj₀ (congrArg Subtype.val hab)
  rw [hcard]
  exact ht P₀ inf_le_right hP₀p

theorem comm_of_mul_comm {X : Type*} [Group X] {K C : Subgroup X} (hKC : K ⊓ C = ⊥)
    (hcomm : ∀ x ∈ K, ∀ y ∈ C, x * y = y * x) {a b k c : X} (ha : a ∈ K) (hb : b ∈ C)
    (hk : k ∈ K) (hc : c ∈ C) (h : a * b * (k * c) = k * c * (a * b)) : a * k = k * a := by
  have e1 : a * b * (k * c) = a * k * (b * c) := by
    calc a * b * (k * c) = a * (b * k) * c := by group
      _ = a * (k * b) * c := by rw [hcomm k hk b hb]
      _ = a * k * (b * c) := by group
  have e2 : k * c * (a * b) = k * a * (c * b) := by
    calc k * c * (a * b) = k * (c * a) * b := by group
      _ = k * (a * c) * b := by rw [hcomm a ha c hc]
      _ = k * a * (c * b) := by group
  rw [e1, e2] at h
  have hmem : (k * a)⁻¹ * (a * k) ∈ K ⊓ C := by
    refine ⟨K.mul_mem (K.inv_mem (K.mul_mem hk ha)) (K.mul_mem ha hk), ?_⟩
    have e3 : (k * a)⁻¹ * (a * k) = c * b * (b * c)⁻¹ := by
      calc (k * a)⁻¹ * (a * k) = (k * a)⁻¹ * (a * k * (b * c)) * (b * c)⁻¹ := by group
        _ = (k * a)⁻¹ * (k * a * (c * b)) * (b * c)⁻¹ := by rw [h]
        _ = c * b * (b * c)⁻¹ := by group
    rw [e3]
    exact C.mul_mem (C.mul_mem hc hb) (C.inv_mem (C.mul_mem hb hc))
  rw [hKC, Subgroup.mem_bot] at hmem
  calc a * k = (k * a) * ((k * a)⁻¹ * (a * k)) := by group
    _ = k * a := by rw [hmem, mul_one]

end CFSG.AGLEmbedding
