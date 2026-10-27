module

public import CFSG.GF2Type.Aschbacher1976Full.HSFiniteData
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Six

open Equiv

theorem not_three_case {Q : Type*} [Group Q] (ι : Q →* Perm (Fin 6))
    (hι : Function.Injective ι) {V : List (Perm (Fin 6))} (hK : K4Ok V)
    (hO2 : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) (a : Q) (ha : orderOf a = 2)
    (hD : ∀ s, (∃ x : Q, s = ι (x * a * x⁻¹)) ↔ s ∈ V) : False := by
  obtain ⟨-, hmul, hsq, -⟩ := hK
  have hmemK : ∀ s : Perm (Fin 6), (s = 1 ∨ s ∈ V) ↔ tab s ∈ oneT 6 :: V.map tab := by
    intro s
    simp only [List.mem_cons, mem_map_tab_iff, ← tab_one, tab_injective.eq_iff]
  have hsq' : ∀ s ∈ V, s * s = 1 := by
    intro s hs
    have := hsq (tab s) (List.mem_map_of_mem hs)
    rw [← tab_mul, ← tab_one] at this
    exact tab_injective this
  let K : Subgroup (Perm (Fin 6)) :=
    { carrier := {s | s = 1 ∨ s ∈ V}
      mul_mem' := by
        intro s t hs ht
        have := hmul (tab s) ((hmemK s).1 hs) (tab t) ((hmemK t).1 ht)
        rw [← tab_mul] at this
        exact (hmemK _).2 this
      one_mem' := Or.inl rfl
      inv_mem' := by
        intro s hs
        rcases hs with rfl | hs
        · exact Or.inl inv_one
        · rw [inv_eq_of_mul_eq_one_right (hsq' s hs)]
          exact Or.inr hs }
  have hsqK : ∀ s ∈ K, s * s = 1 := by
    intro s hs
    rcases hs with rfl | hs
    · exact mul_one 1
    · exact hsq' s hs
  have hnormal : (K.comap ι).Normal := by
    refine ⟨fun n hn g => ?_⟩
    change ι n ∈ K at hn
    show ι (g * n * g⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    rcases hn with h1 | hnV
    · rw [h1, mul_one, mul_inv_cancel]
      exact K.one_mem
    · obtain ⟨x, hx⟩ := (hD (ι n)).2 hnV
      have : ι g * ι n * (ι g)⁻¹ = ι ((g * x) * a * (g * x)⁻¹) := by
        rw [hx]
        simp only [map_mul, map_inv]
        group
      rw [this]
      exact Or.inr ((hD _).1 ⟨g * x, rfl⟩)
  have hpg : IsPGroup 2 (K.comap ι) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have hg : ι g.1 ∈ K := g.2
    have h2 : ι (g.1 * g.1) = 1 := by rw [map_mul]; exact hsqK _ hg
    have h3 : g.1 * g.1 = 1 := hι (h2.trans (map_one ι).symm)
    simpa [pow_two] using h3
  have hbot := hO2 _ hnormal hpg
  have haN : a ∈ K.comap ι := by
    show ι a ∈ K
    exact Or.inr ((hD (ι a)).1 ⟨1, by simp⟩)
  rw [hbot, Subgroup.mem_bot] at haN
  rw [haN, orderOf_one] at ha
  exact absurd ha (by norm_num)

theorem canonical (c : Cfg) (hc : c.Ok) {Q : Type*} [Group Q] (ι : Q →* Perm (Fin 6))
    (hι : Function.Injective ι)
    (hO2 : ∀ N : Subgroup Q, N.Normal → IsPGroup 2 N → N = ⊥) (a : Q) (ha : orderOf a = 2)
    (hP1 : ∀ x y : Q, orderOf ((x * a * x⁻¹) * (y * a * y⁻¹)) ≠ 4)
    (hV : ∀ v ∈ c.V, ∃ x : Q, v = ι (x * a * x⁻¹)) :
    Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨ Nonempty (Q ≃* Perm (Fin 5)) := by
  obtain ⟨hS, hI1, hI2, hK⟩ := hc
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, sq] at this
  let D : Set (Perm (Fin 6)) := {s | ∃ x : Q, s = ι (x * a * x⁻¹)}
  have hconjD : ∀ (q x : Q), ι q * ι (x * a * x⁻¹) * (ι q)⁻¹ = ι ((q * x) * a * (q * x)⁻¹) := by
    intro q x
    simp only [map_mul, map_inv]
    group
  have hconj : ∀ s ∈ D, ∀ t ∈ D, s * t * s⁻¹ ∈ D := by
    rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩
    refine ⟨x * a * x⁻¹ * y, ?_⟩
    simp only [map_mul, map_inv]
    group
  have hcompat : ∀ s ∈ D, ∀ t ∈ D, Compat s t := by
    rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩
    unfold Compat
    rw [← map_mul, orderOf_injective ι hι]
    exact hP1 x y
  have hsq : ∀ s ∈ D, s * s = 1 := by
    rintro s ⟨x, rfl⟩
    have : x * a * x⁻¹ * (x * a * x⁻¹) = 1 := by
      calc x * a * x⁻¹ * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    rw [← map_mul, this, map_one]
  have hlen : c.V.length = 3 := hK.1
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∈ c.V := by
    rcases hVV : c.V with _ | ⟨v, vs⟩
    · rw [hVV] at hlen; simp at hlen
    · exact ⟨v, by simp⟩
  have hsupp_conj : ∀ x : Q, (ι (x * a * x⁻¹)).support.card = (ι a).support.card := by
    intro x
    have : ι (x * a * x⁻¹) = ι x * ι a * (ι x)⁻¹ := by simp [map_mul, map_inv]
    rw [this, Equiv.Perm.card_support_conj]
  have hsupp_a : (ι a).support.card = 4 := by
    obtain ⟨x, hx⟩ := hV v₀ hv₀
    have h4 := hK.2.2.2 (tab v₀) (List.mem_map_of_mem hv₀)
    rw [suppT_tab, hx, hsupp_conj] at h4
    exact h4
  have hc2 : ∀ s ∈ D, tab s ∈ c2T := by
    intro s hs
    refine mem_c2T (hsq s hs) ?_
    obtain ⟨x, rfl⟩ := hs
    rw [hsupp_conj, hsupp_a]
  obtain ⟨ls, hls, hmem⟩ := search_generic hS D hc2 hconj hcompat (fun v hv => hV v hv)
  have hnorm : ∀ l : List (Perm (Fin 6)), (∀ s, s ∈ D ↔ s ∈ mk c.V l) →
      ∀ q : Q, ∀ c' ∈ mk c.V l, ι q * c' * (ι q)⁻¹ ∈ mk c.V l := by
    intro l hl q c' hc'
    obtain ⟨x, hx⟩ := (hl c').2 hc'
    rw [hx, hconjD]
    exact (hl _).1 ⟨q * x, rfl⟩
  have hgen : ∀ l : List (Perm (Fin 6)), (∀ s, s ∈ D ↔ s ∈ mk c.V l) →
      ∀ c' ∈ mk c.V l, ∃ q : Q, ι q = c' := by
    intro l hl c' hc'
    obtain ⟨x, hx⟩ := (hl c').2 hc'
    exact ⟨x * a * x⁻¹, hx.symm⟩
  rcases hls with rfl | rfl | rfl
  · exfalso
    refine not_three_case ι hι hK hO2 a ha fun s => ?_
    have h1 : s ∈ mk c.V [] ↔ s ∈ c.V := by simp [mk]
    exact (hmem s).trans h1
  · exact iso_of_blocks ι hι hI1 (hnorm _ hmem) (hgen _ hmem)
  · exact iso_of_blocks ι hι hI2 (hnorm _ hmem) (hgen _ hmem)

end CFSG.GF2Type.Aschbacher1976Full.HS.Six
