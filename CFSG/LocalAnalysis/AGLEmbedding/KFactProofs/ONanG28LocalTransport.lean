module

public import CFSG.LocalAnalysis.AGLEmbedding.G28InSitu

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section InSitu

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

theorem G28InSitu.of_mulEquiv (f : X ≃* Y) {T Y₀ V₀ : Subgroup X} {zb : X}
    (h : G28InSitu (T.map f.toMonoidHom) (Y₀.map f.toMonoidHom) (f.toMonoidHom zb)
      (V₀.map f.toMonoidHom)) : G28InSitu T Y₀ zb V₀ := by
  have hinj : Function.Injective f.toMonoidHom := f.injective
  have hmap_le : ∀ {A B : Subgroup X}, A.map f.toMonoidHom ≤ B.map f.toMonoidHom → A ≤ B :=
    fun h => (Subgroup.map_le_map_iff_of_injective hinj).1 h
  have hnorm : ∀ {A B : Subgroup X}, A ≤ Subgroup.normalizer (B : Set X) ↔
      A.map f.toMonoidHom ≤ Subgroup.normalizer ((B.map f.toMonoidHom : Subgroup Y) : Set Y) := by
    intro A B
    constructor
    · intro hA y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
      exact Subgroup.le_normalizer_map f.toMonoidHom (Subgroup.mem_map_of_mem _ (hA ha))
    · intro hA a ha
      have h1 := hA (Subgroup.mem_map_of_mem f.toMonoidHom ha)
      rw [Subgroup.mem_normalizer_iff] at h1 ⊢
      intro b
      have h2 := h1 (f.toMonoidHom b)
      rw [Subgroup.mem_map_iff_mem hinj, ← map_inv, ← map_mul, ← map_mul,
        Subgroup.mem_map_iff_mem hinj] at h2
      exact h2
  have hcent : ∀ {A : Subgroup X} {x : X}, f.toMonoidHom x ∈ Subgroup.centralizer
      ((A.map f.toMonoidHom : Subgroup Y) : Set Y) → x ∈ Subgroup.centralizer (A : Set X) := by
    intro A x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hx (f.toMonoidHom t) (Subgroup.mem_map_of_mem _ ht)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_map_iff_mem hinj).1 h.z_mem
  · exact hcent h.z_center
  · rw [← orderOf_injective f.toMonoidHom hinj zb]
    exact h.z_order
  · intro x hx
    unfold centerOf at hx
    have hx' : f.toMonoidHom x ∈ centerOf (T.map f.toMonoidHom) := by
      unfold centerOf
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 hx).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 t ht)
    have h1 := h.center_le hx'
    rw [← MonoidHom.map_zpowers] at h1
    exact (Subgroup.mem_map_iff_mem hinj).1 h1
  · rw [← Subgroup.card_map_of_injective hinj]
    exact h.card_T
  · exact hmap_le h.V_le
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator]
    exact h.V_perfect
  · exact (hnorm).2 h.V_normal
  · exact (Subgroup.mem_map_iff_mem hinj).1 h.z_mem_V
  · obtain ⟨d, ψ, hd, hψ⟩ := h.V_onto
    exact ⟨d, ψ.comp (Subgroup.equivMapOfInjective V₀ f.toMonoidHom hinj).toMonoidHom, hd,
      hψ.comp (Subgroup.equivMapOfInjective V₀ f.toMonoidHom hinj).surjective⟩
  · intro W hW hN
    rcases h.V_quasi (W.map f.toMonoidHom) (Subgroup.map_mono hW) ((hnorm).1 hN) with h1 | h1
    · exact Or.inl (hmap_le h1)
    · right
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_commutator, Subgroup.map_bot]
      exact h1
  · have h1 := h.V_centralizer
    intro x hx
    have hx' : f.toMonoidHom x ∈ Y₀.map f.toMonoidHom ⊓
        Subgroup.centralizer ((V₀.map f.toMonoidHom : Subgroup Y) : Set Y) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.1 hx).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 v hv)
    have h2 := h1 hx'
    rw [← MonoidHom.map_zpowers] at h2
    exact (Subgroup.mem_map_iff_mem hinj).1 h2
  · intro W hW hN
    rcases h.trichotomy (W.map f.toMonoidHom) (Subgroup.map_mono hW) ((hnorm).1 hN) with
      h1 | h1 | h1
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h1
    · right
      left
      rw [← MonoidHom.map_zpowers] at h1
      exact hmap_le h1
    · exact Or.inr (Or.inr (hmap_le h1))

end InSitu

end CFSG.AGLEmbedding
