module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

@[expose] def E4QuatNoGood (M : Type) [Group M] : Prop :=
  ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s → ∀ (x : M) (k : ℕ), x ^ 3 ^ k = 1 →
    conjSub x K = K → (∃ c ∈ K, x * c ≠ c * x) →
      ∃ y : M, y ^ 3 = 1 ∧ (∀ c ∈ K, y * c = c * y) ∧ x * y ≠ y * x

namespace Vtx

variable {M G : Type} [Group M] [Group G]

theorem e4QuatNoGood_of_model (H Kc : Subgroup G)
    (hid : ∀ (K : Subgroup M) (s : M), QuatTwinDatum K s →
      ∃ φ : M →* G, Function.Injective φ ∧ φ.range = H ∧ K.map φ = Kc)
    (hng : ∀ sc, IsUniqueInvolution Kc sc → ∀ x ∈ H, ∀ k : ℕ, x ^ 3 ^ k = 1 →
      conjSub x Kc = Kc → (∃ c ∈ Kc, x * c ≠ c * x) →
        ∃ y ∈ H, y ^ 3 = 1 ∧ (∀ c ∈ Kc, y * c = c * y) ∧ x * y ≠ y * x) :
    E4QuatNoGood M := by
  intro K s hd x k hx3 hxK hact
  obtain ⟨φ, hφ, hrange, hKc⟩ := hid K s hd
  have hs := isUniqueInvolution_map φ hφ hd.inv
  rw [hKc] at hs
  have hxH : φ x ∈ H := hrange ▸ ⟨x, rfl⟩
  have hxK' : conjSub (φ x) Kc = Kc := by rw [← hKc, conjSub_map, hxK]
  have hact' : ∃ c ∈ Kc, φ x * c ≠ c * φ x := by
    obtain ⟨c, hc, hxc⟩ := hact
    refine ⟨φ c, hKc ▸ Subgroup.mem_map_of_mem φ hc, fun h => hxc (hφ ?_)⟩
    rw [map_mul, map_mul, h]
  obtain ⟨y, hyH, hy3, hyC, hxy⟩ :=
    hng _ hs (φ x) hxH k (by rw [← map_pow, hx3, map_one]) hxK' hact'
  rw [← hrange] at hyH
  obtain ⟨y', rfl⟩ := hyH
  refine ⟨y', hφ (by rw [map_pow, hy3, map_one]), fun c hc => hφ ?_, fun h => hxy ?_⟩
  · rw [map_mul, map_mul]
    exact hyC _ (hKc ▸ Subgroup.mem_map_of_mem φ hc)
  · rw [← map_mul, ← map_mul, h]

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
