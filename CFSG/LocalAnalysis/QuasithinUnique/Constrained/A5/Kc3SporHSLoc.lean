module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporHS

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Kc3J CFSG.QuasithinUnique.A5.Kc3L3

theorem not_delta5Norm_of_cls {K : Type} [Group K] {E : Subgroup K} (f : K → ℕ)
    (hf : ∀ g x : K, f (g * x * g⁻¹) = f x)
    (hfib : ∀ l : List K, l.Nodup → (∀ x ∈ l, x ∈ E ∧ x ≠ 1) → ∀ c : ℕ, (∀ x ∈ l, f x = c) →
      l.length < 10)
    (β : ↥E ≃* Multiplicative ↥(evenWeight 5)) : ¬ Delta5Norm E β := by
  intro hD
  set pairs : List (Fin 5 × Fin 5) :=
    [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)] with hpairs
  let vec : Fin 5 × Fin 5 → ↥(evenWeight 5) := fun p =>
    ⟨Pi.single p.1 1 + Pi.single p.2 1, Delta5.pair_mem p.1 p.2⟩
  let w0' : ↥(evenWeight 5) := ⟨Delta5.w0, Delta5.w0_mem⟩
  have hne : ∀ p ∈ pairs, p.1 ≠ p.2 := by
    intro p hp
    simp only [hpairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hconj : ∀ p ∈ pairs, f (pt β (vec p)) = f (pt β w0') := by
    intro p hp
    obtain ⟨σ, hsign, hσ⟩ := Delta5.pairs_conj p.1 p.2 (hne p hp)
    obtain ⟨l, hl, hact⟩ := hD σ hsign
    have h1 := pt_vact β hl hact w0'
    have h2 : Delta5.vact σ w0' = vec p := Subtype.ext hσ
    rw [h2] at h1
    rw [h1, hf]
  have hptinj : Function.Injective (pt β : ↥(evenWeight 5) → K) := by
    intro w w' h
    have h1 : β.symm (Multiplicative.ofAdd w) = β.symm (Multiplicative.ofAdd w') := Subtype.ext h
    exact Multiplicative.ofAdd.injective (β.symm.injective h1)
  have hnd0 : (pairs.map fun p => (vec p).1).Nodup := by
    simp only [hpairs, vec]
    decide +kernel
  have hnd1 : (pairs.map vec).Nodup := by
    refine List.Nodup.of_map Subtype.val ?_
    simpa [List.map_map, Function.comp_def] using hnd0
  have hvec0 : ∀ p ∈ pairs, vec p ≠ 0 := by
    intro p hp h
    have h1 : Pi.single p.1 (1 : ZMod 2) + Pi.single p.2 1 = (0 : Fin 5 → ZMod 2) :=
      congrArg Subtype.val h
    simp only [hpairs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact absurd h1 (by decide +kernel)
  have hlen := hfib ((pairs.map vec).map (pt β)) (hnd1.map hptinj) ?_ (f (pt β w0')) ?_
  · simp [hpairs] at hlen
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    refine ⟨pt_mem β (vec p), fun h1 => hvec0 p hp ?_⟩
    apply hptinj
    rw [h1, pt_zero]
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hw
    exact hconj p hp

end CFSG.QuasithinUnique.A5.Kc3SporHS
