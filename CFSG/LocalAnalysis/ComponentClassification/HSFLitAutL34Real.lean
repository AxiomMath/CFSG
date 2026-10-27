module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Unit
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.UnbalancedLayer Subgroup

variable {G : Type} [Group G]

structure Real (K : Subgroup G) where
  φ : ↥(normalizer (K : Set G)) →* Equiv.Perm (Fin 42)
  mem_R : ∀ g, φ g ∈ R
  ker_iff : ∀ g, φ g = 1 ↔ (g : G) ∈ coreActionKernel K
  map_K : ∀ (k : G) (hk : k ∈ K), φ ⟨k, le_normalizer hk⟩ ∈ S
  onto_S : ∀ s ∈ S, ∃ (k : G) (hk : k ∈ K), φ ⟨k, le_normalizer hk⟩ = s

namespace Real

variable {K : Subgroup G} (ρ : Real K)

@[expose] def img (H : Subgroup G) : Subgroup (Equiv.Perm (Fin 42)) :=
  (H.subgroupOf (normalizer (K : Set G))).map ρ.φ

theorem mem_img {H : Subgroup G} {x : Equiv.Perm (Fin 42)} :
    x ∈ ρ.img H ↔ ∃ g : ↥(normalizer (K : Set G)), (g : G) ∈ H ∧ ρ.φ g = x := by
  simp only [img, mem_map, mem_subgroupOf]

theorem img_le_R (H : Subgroup G) : ρ.img H ≤ R := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := ρ.mem_img.1 hx
  exact ρ.mem_R g

theorem img_mono {H H' : Subgroup G} (h : H ≤ H') : ρ.img H ≤ ρ.img H' := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
  exact ρ.mem_img.2 ⟨g, h hg, rfl⟩

theorem phi_mem_img {H : Subgroup G} {g : ↥(normalizer (K : Set G))} (hg : (g : G) ∈ H) :
    ρ.φ g ∈ ρ.img H := ρ.mem_img.2 ⟨g, hg, rfl⟩

theorem img_isPGroup {H : Subgroup G} (hH : IsPGroup 2 H) : IsPGroup 2 (ρ.img H) :=
  (hH.comap_subtype (K := normalizer (K : Set G))).map ρ.φ

theorem card_eq {H : Subgroup G} (hH : H ≤ normalizer (K : Set G)) :
    Nat.card H = Nat.card (ρ.img H) * Nat.card ↥(H ⊓ coreActionKernel K) := by
  set H' := H.subgroupOf (normalizer (K : Set G))
  set ψ := ρ.φ.comp H'.subtype
  have h1 := card_ker_mul_card_range ψ
  have hr : ψ.range = ρ.img H := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  have hk : Nat.card ψ.ker = Nat.card ↥(H ⊓ coreActionKernel K) := Nat.card_congr
    { toFun := fun x => ⟨x.1.1.1, mem_inf.2 ⟨mem_subgroupOf.1 x.1.2, (ρ.ker_iff _).1 x.2⟩⟩
      invFun := fun h => ⟨⟨⟨h.1, hH (mem_inf.1 h.2).1⟩, mem_subgroupOf.2 (mem_inf.1 h.2).1⟩,
        (ρ.ker_iff _).2 (mem_inf.1 h.2).2⟩
      left_inv := fun x => rfl
      right_inv := fun h => rfl }
  rw [hr, hk, Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv] at h1
  rw [← h1, mul_comm]

theorem img_elem {H : Subgroup G} (hH : IsElemTwo H) :
    (∀ x ∈ ρ.img H, ∀ y ∈ ρ.img H, x * y = y * x) ∧ ∀ x ∈ ρ.img H, x * x = 1 := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
    obtain ⟨h, hh, rfl⟩ := ρ.mem_img.1 hy
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.φ (Subtype.ext (hH.1 _ hg _ hh))
  · obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx
    rw [← map_mul]
    have : g * g = 1 := Subtype.ext (hH.2 _ hg)
    rw [this, map_one]

include ρ in
theorem rank {E : Subgroup G}
    (hE : E ≤ normalizer (K : Set G)) (hEe : IsElemTwo E) :
    Nat.card E ≤ 16 * Nat.card ↥(E ⊓ coreActionKernel K) := by
  rw [ρ.card_eq hE]
  obtain ⟨hc, h2⟩ := ρ.img_elem hEe
  exact Nat.mul_le_mul_right _ (card_le_sixteen (ρ.img_le_R E) hc h2)

theorem unitary {x : G}
    (hxN : x ∈ normalizer (K : Set G)) (hx4 : ρ.φ ⟨x, hxN⟩ = r₄) {Rg : Subgroup G}
    (hR2 : IsPGroup 2 Rg) (hRle : Rg ≤ normalizer (K : Set G) ⊓ centralizer ({x} : Set G)) :
    Nat.card Rg ≤ 32 * Nat.card ↥(Rg ⊓ coreActionKernel K) ∧
      (∀ E : Subgroup G, E ≤ Rg → IsElemTwo E →
        Nat.card E ≤ 8 * Nat.card ↥(E ⊓ coreActionKernel K)) ∧
      ∀ y ∈ Rg, y * y ∉ coreActionKernel K → ∀ a ∈ Rg, ∀ b ∈ Rg, a * y = y * a →
        b * y = y * b → a⁻¹ * b⁻¹ * a * b ∈ coreActionKernel K := by
  have hRN : Rg ≤ normalizer (K : Set G) := fun g hg => (mem_inf.1 (hRle hg)).1
  have hcomm : ∀ x' ∈ ρ.img Rg, x' * r₄ = r₄ * x' := by
    intro x' hx'
    obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hx'
    rw [← hx4, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 (hRle hg)).2)
  obtain ⟨h1, h2, h3⟩ := unitary_facts (ρ.img_le_R Rg) (ρ.img_isPGroup hR2) hcomm
  refine ⟨?_, fun E hER hEe => ?_, fun y hy hy2 a ha b hb hay hby => ?_⟩
  · rw [ρ.card_eq hRN]
    exact Nat.mul_le_mul_right _ h1
  · rw [ρ.card_eq (hER.trans hRN)]
    exact Nat.mul_le_mul_right _ (h2 _ (ρ.img_mono hER) (ρ.img_elem hEe).2)
  · set y' : ↥(normalizer (K : Set G)) := ⟨y, hRN hy⟩
    set a' : ↥(normalizer (K : Set G)) := ⟨a, hRN ha⟩
    set b' : ↥(normalizer (K : Set G)) := ⟨b, hRN hb⟩
    have hy2' : ρ.φ y' * ρ.φ y' ≠ 1 := by
      rw [← map_mul]
      exact fun h => hy2 ((ρ.ker_iff _).1 h)
    have hc := h3 (ρ.φ y') (ρ.phi_mem_img (g := y') hy) hy2' (ρ.φ a')
      (ρ.phi_mem_img (g := a') ha) (ρ.φ b') (ρ.phi_mem_img (g := b') hb)
      (by rw [← map_mul, ← map_mul]; exact congrArg ρ.φ (Subtype.ext hay))
      (by rw [← map_mul, ← map_mul]; exact congrArg ρ.φ (Subtype.ext hby))
    have hk : ρ.φ (a'⁻¹ * b'⁻¹ * a' * b') = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc (ρ.φ a')⁻¹ * (ρ.φ b')⁻¹ * ρ.φ a' * ρ.φ b' =
          (ρ.φ a')⁻¹ * (ρ.φ b')⁻¹ * (ρ.φ a' * ρ.φ b') := by group
        _ = 1 := by rw [hc]; group
    exact (ρ.ker_iff _).1 hk

end Real

end CFSG.ComponentClassification.HSFLit.AutL34
