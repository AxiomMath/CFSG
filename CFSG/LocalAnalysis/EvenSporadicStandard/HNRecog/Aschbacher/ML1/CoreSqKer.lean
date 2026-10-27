module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreDiag

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf
open scoped commutatorElement

variable {L L' : Type} [Group L] [Group L'] {N : Subgroup L} {N' : Subgroup L'}
  {θ : L →* A5 × A5} {θ' : L' →* A5 × A5} {ψ : A5 × A5 ≃* A5 × A5} {φ : L → L'} {z : L}

private theorem CoreHyp.exists_phi_mul [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z)
    {x : L} {x' : L'} (hx : x ∈ N) (ht : (x, x') ∈ fibre θ θ' ψ N φ) :
    ∃ c : L', (c = 1 ∨ c = φ z) ∧ x' = φ x * c := by
  have hxθ : θ x = 1 := (h.ker x).2 hx
  have hθ'x' : θ' x' = 1 := by
    have h1 := ((mem_fibre_iff θ θ' ψ N φ x x').mp ht).1
    rw [hxθ, map_one] at h1
    exact h1
  have hx'mem : x' ∈ N' := (h.ker' x').1 hθ'x'
  have hphixmem : φ x ∈ N' := h.iso.mem x hx
  have hcompat : Compat N φ x x' := ((mem_fibre_iff θ θ' ψ N φ x x').mp ht).2
  have hwmem : (φ x)⁻¹ * x' ∈ N' := N'.mul_mem (N'.inv_mem hphixmem) hx'mem
  have hwcomm : ∀ y' ∈ N', ((φ x)⁻¹ * x') * y' = y' * ((φ x)⁻¹ * x') := by
    intro y' hy'
    obtain ⟨y, hy, rfl⟩ := h.iso.surj y' hy'
    have hmap : φ (x * y * x⁻¹) = φ x * φ y * (φ x)⁻¹ := by
      rw [h.iso.map_mul (x * y) (N.mul_mem hx hy) x⁻¹ (N.inv_mem hx),
        h.iso.map_mul x hx y hy, h.phi_inv hx]
    have heq : x' * φ y * x'⁻¹ = φ x * φ y * (φ x)⁻¹ := by
      rw [← hcompat y hy, hmap]
    calc
      (φ x)⁻¹ * x' * φ y = (φ x)⁻¹ * ((x' * φ y * x'⁻¹) * x') := by group
      _ = (φ x)⁻¹ * ((φ x * φ y * (φ x)⁻¹) * x') := by rw [heq]
      _ = φ y * ((φ x)⁻¹ * x') := by group
  obtain hw_eq | hw_eq := h.centre' ((φ x)⁻¹ * x') hwmem hwcomm
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [mul_one]
    calc x' = φ x * ((φ x)⁻¹ * x') := by group
      _ = φ x * 1 := by rw [hw_eq]
      _ = φ x := by group
  · refine ⟨φ z, Or.inr rfl, ?_⟩
    rw [← hw_eq]
    group

theorem CoreHyp.ker_comm_mem_graph [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) {t : L × L'}
    (ht : t ∈ fibre θ θ' ψ N φ) (hθ : θ t.1 = 1) {f : L × L'} (hf : f ∈ fibre θ θ' ψ N φ) :
    ⁅t, f⁆ ∈ h.graph := by
  rcases t with ⟨x, x'⟩
  rcases f with ⟨l, l'⟩
  have hxN : x ∈ N := (h.ker x).1 hθ
  obtain ⟨c, hc, hx'eq⟩ := h.exists_phi_mul hxN ht
  have hc_comm : ∀ g : L', g * c = c * g := by
    intro g
    rcases hc with rfl | rfl
    · simp
    · exact h.phiZ_central g
  have hcompat : Compat N φ l l' := ((mem_fibre_iff θ θ' ψ N φ l l').mp hf).2
  have hcomm_pair : ⁅(x, x'), (l, l')⁆ = (⁅x, l⁆, ⁅x', l'⁆) := by
    simp [commutatorElement_def]
  rw [hcomm_pair, h.mem_graph_iff]
  refine ⟨?_, ?_⟩
  · have hxl : l * x⁻¹ * l⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem x⁻¹ (N.inv_mem hxN) l
    have heq : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact N.mul_mem hxN hxl
  · have hxl_mem : l * x⁻¹ * l⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem x⁻¹ (N.inv_mem hxN) l
    have hphi : φ ⁅x, l⁆ = φ x * l' * (φ x)⁻¹ * l'⁻¹ := by
      have heq : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by
        rw [commutatorElement_def]; group
      calc φ ⁅x, l⁆ = φ (x * (l * x⁻¹ * l⁻¹)) := by rw [heq]
        _ = φ x * φ (l * x⁻¹ * l⁻¹) := h.iso.map_mul x hxN _ hxl_mem
        _ = φ x * (l' * φ x⁻¹ * l'⁻¹) := by rw [hcompat x⁻¹ (N.inv_mem hxN)]
        _ = φ x * l' * (φ x)⁻¹ * l'⁻¹ := by rw [h.phi_inv hxN]; group
    have hcomm : ⁅x', l'⁆ = φ x * l' * (φ x)⁻¹ * l'⁻¹ := by
      rw [hx'eq, commutatorElement_def, mul_inv_rev]
      calc
        φ x * c * l' * (c⁻¹ * (φ x)⁻¹) * l'⁻¹
            = φ x * (c * l') * (c⁻¹ * (φ x)⁻¹) * l'⁻¹ := by group
        _ = φ x * (l' * c) * (c⁻¹ * (φ x)⁻¹) * l'⁻¹ := by
              rw [show c * l' = l' * c from (hc_comm l').symm]
        _ = φ x * l' * (φ x)⁻¹ * l'⁻¹ := by group
    rw [hcomm, hphi]

theorem CoreHyp.ker_sq_mem_graph [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) {t : L × L'}
    (ht : t ∈ fibre θ θ' ψ N φ) (hθ : θ t.1 = 1) : t ^ 2 ∈ h.graph := by
  rcases t with ⟨x, x'⟩
  have hxN : x ∈ N := (h.ker x).1 hθ
  obtain ⟨c, hc, hx'eq⟩ := h.exists_phi_mul hxN ht
  have hc_comm : ∀ g : L', g * c = c * g := by
    intro g
    rcases hc with rfl | rfl
    · simp
    · exact h.phiZ_central g
  have hcc : c * c = 1 := by
    rcases hc with rfl | rfl
    · simp
    · rw [← pow_two, h.phiZ_sq]
  have hx'sq : x' ^ 2 = (φ x) ^ 2 := by
    rw [hx'eq, pow_two, pow_two]
    calc (φ x * c) * (φ x * c) = φ x * (c * φ x) * c := by group
      _ = φ x * (φ x * c) * c := by rw [← hc_comm (φ x)]
      _ = φ x * φ x * (c * c) := by group
      _ = φ x * φ x := by rw [hcc, mul_one]
  have ht2 : (x, x') ^ 2 = (x ^ 2, x' ^ 2) := by
    ext <;> simp [pow_two]
  have hp : (x, x') ^ 2 = (x ^ 2, φ (x ^ 2)) := by
    rw [ht2, hx'sq, ← h.phi_pow hxN 2]
  have hx2mem : x ^ 2 ∈ N := by rw [pow_two]; exact N.mul_mem hxN hxN
  rw [hp, h.mem_graph_iff]
  exact ⟨hx2mem, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.ML1