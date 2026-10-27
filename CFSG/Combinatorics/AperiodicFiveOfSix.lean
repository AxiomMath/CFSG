module

public import CFSG.Combinatorics.AperiodicFiveOfSixSupport

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

theorem aperiodic_base_point_excludes_five_of_six_opposite_vertices {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : MooreHyp G)
    (col : G.Coloring Bool) (w : {v : V // col v = false}) (ℓ : Fin 3 → V)
    (hℓ : Function.Injective ℓ) (hwℓ : ∀ i, G.Adj (w : V) (ℓ i))
    (p : Fin 3 → Fin 2 → {v : V // col v = false}) (hpℓ : ∀ i e, G.Adj (p i e : V) (ℓ i))
    (hpw : ∀ i e, p i e ≠ w) (hp : ∀ i, Function.Injective (p i))
    (z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false})
    (c : {v : V // col v = false} → {v : V // col v = false} → Fin 3)
    (ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2)
    (hdata : IsFrameData G col w p z q c ε)
    (r : Fin 3 → {v : V // col v = false} → {v : V // col v = false})
    (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
      (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i) :
    let Γ : SimpleGraph {v : V // col v = false} := pointGraph G col
    let O : Set {v : V // col v = false} := {x | Γ.dist w x = 3}
    let hexagon : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
      Function.Injective x ∧ (∀ n, x n ∈ O) ∧ ∀ n, Γ.Adj (x n) (x (n + 1))
    let periodic : (Fin 6 → {v : V // col v = false}) → Prop := fun x =>
      ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∀ n, c (x n) (x (n + 1)) = ![i, j, k, i, j, k] n
    (¬ ∃ x, hexagon x ∧ periodic x) →
      ∀ (v : V) (C : G.Walk v v), C.IsCycle → C.length = 12 →
        (univ.filter fun x : {v : V // col v = false} => (x : V) ∈ C.support).card = 6 ∧
        (5 ≤ (univ.filter fun x : {v : V // col v = false} =>
            (x : V) ∈ C.support ∧ Γ.dist w x = 3).card →
          ∀ x : {v : V // col v = false}, (x : V) ∈ C.support → x ∈ O) := by
  intro Γ O hexagon periodic haper v C hC hl
  have F : IsFrame G col w ℓ p z q c ε := ⟨H, hℓ, hwℓ, hpℓ, hpw, hp, hdata⟩
  have haper' : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x :=
    fun x hx hpx => haper ⟨x, hx, hpx⟩
  obtain ⟨pt, hper, hadj, hinj, hmem⟩ := exists_hexagon_of_isCycle F hC hl
  have hpt : ∀ a b, a % 6 = b % 6 → pt a = pt b := fun a b h => by rw [hper a, hper b, h]
  have hadj' : ∀ a b, b % 6 = (a + 1) % 6 → Γ.Adj (pt a) (pt b) := fun a b h => by
    rw [hpt b (a + 1) h]
    exact hadj a
  have hne : ∀ a b, a % 6 ≠ b % 6 → pt a ≠ pt b := fun a b h e => h (hinj a b e)
  have hinj6 : Function.Injective fun t : Fin 6 => pt t.val := fun a b h => Fin.ext (by
    have := hinj _ _ h
    omega)
  have hP : (univ.filter fun x : {v : V // col v = false} => (x : V) ∈ C.support) =
      (univ : Finset (Fin 6)).image fun t => pt t.val := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    rw [hmem]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
  refine ⟨by rw [hP, card_image_of_injective _ hinj6, card_univ, Fintype.card_fin],
    fun h5 x hx => ?_⟩
  by_contra hxO
  obtain ⟨t₀, ht₀, rfl⟩ := (hmem x).mp hx
  obtain ⟨t₁, ht₁, h01, hO1⟩ : ∃ t₁ < 6, t₁ ≠ t₀ ∧ pt t₁ ∉ O := by
    by_contra hall
    have hall' : ∀ t₁ < 6, t₁ ≠ t₀ → pt t₁ ∈ O := fun t₁ h1 h2 =>
      by_contra fun h => hall ⟨t₁, h1, h2, h⟩
    have hq : ∀ k, k < 5 → pt (t₀ + 1 + k) ∈ O := fun k hk => by
      rw [hper]
      exact hall' _ (Nat.mod_lt _ (by norm_num)) (by omega)
    have h6 := mem_of_five F hr haper' (hq 0 (by norm_num)) (hq 1 (by norm_num))
      (hq 2 (by norm_num)) (hq 3 (by norm_num)) (hq 4 (by norm_num)) (hadj' _ _ (by omega))
      (hadj' _ _ (by omega)) (hadj' _ _ (by omega)) (hadj' _ _ (by omega))
      (hadj' _ (t₀ + 1 + 5) (by omega)) (hadj' _ (t₀ + 1 + 0) (by omega)) (hne _ _ (by omega))
      (hne _ _ (by omega)) (hne _ _ (by omega))
    rw [hpt (t₀ + 1 + 5) t₀ (by omega)] at h6
    exact hxO h6
  have hsub : (univ.filter fun x : {v : V // col v = false} =>
      (x : V) ∈ C.support ∧ Γ.dist w x = 3) ⊆
      ((univ : Finset (Fin 6)).filter fun t => t ≠ ⟨t₀, ht₀⟩ ∧ t ≠ ⟨t₁, ht₁⟩).image
        fun t => pt t.val := by
    intro y hy
    simp only [mem_filter, mem_univ, true_and] at hy
    obtain ⟨t, ht, rfl⟩ := (hmem y).mp hy.1
    simp only [mem_image, mem_filter, mem_univ, true_and]
    refine ⟨⟨t, ht⟩, ⟨fun e => ?_, fun e => ?_⟩, rfl⟩
    · rw [Fin.mk.injEq] at e
      subst e
      exact hxO hy.2
    · rw [Fin.mk.injEq] at e
      subst e
      exact hO1 hy.2
  have h4 : ((univ : Finset (Fin 6)).filter fun t => t ≠ ⟨t₀, ht₀⟩ ∧ t ≠ ⟨t₁, ht₁⟩).card = 4 :=
    (by decide : ∀ a b : Fin 6, a ≠ b → ((univ : Finset (Fin 6)).filter fun t =>
      t ≠ a ∧ t ≠ b).card = 4) _ _ (fun e => h01 (by rw [Fin.mk.injEq] at e; exact e.symm))
  have := (card_le_card hsub).trans card_image_le
  omega

end CFSG.Combinatorics.AperiodicOppositeComponents
