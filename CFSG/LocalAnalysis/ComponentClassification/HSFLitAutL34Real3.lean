module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Real2

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.UnbalancedLayer Subgroup

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

namespace Real

variable (ρ : Real K)

include ρ in
theorem mem_center_sup
    {Sg : Subgroup G} (hS : IsSylowTwoIn Sg (normalizer (K : Set G)))
    (hZ : Nat.card ↥(Sg ⊓ K ⊓ centralizer ((Sg ⊓ K : Subgroup G) : Set G)) =
      4 * Nat.card ↥(Sg ⊓ K ⊓ zStarIn K))
    {y : G} (hy : y ∈ Sg) {S₁ : Subgroup G} (hS₁ : S₁ ≤ Sg)
    (hcard : Nat.card Sg ≤ 2 * Nat.card S₁)
    (hcomm : ∀ s ∈ S₁, s⁻¹ * y⁻¹ * s * y ∈ coreActionKernel K) :
    y ∈ (Sg ⊓ K ⊓ centralizer ((Sg ⊓ K : Subgroup G) : Set G)) ⊔ (Sg ⊓ coreActionKernel K) := by
  have hSN := hS.1
  have hS2 := GrS4.isPGroup_of_isSylowTwoIn hS
  obtain ⟨heq, h64⟩ := ρ.img_inf_K_eq hS
  set y' : ↥(normalizer (K : Set G)) := ⟨y, hSN hy⟩
  have hcard' : Nat.card (ρ.img Sg) ≤ 2 * Nat.card (ρ.img S₁) := by
    have h1 := ρ.card_eq hSN
    have h2 := ρ.card_eq (hS₁.trans hSN)
    have h3 : Nat.card ↥(S₁ ⊓ coreActionKernel K) ≤ Nat.card ↥(Sg ⊓ coreActionKernel K) :=
      card_le_of_le (inf_le_inf_right _ hS₁)
    have hpos : 0 < Nat.card ↥(Sg ⊓ coreActionKernel K) := Nat.card_pos
    have h4 : Nat.card (ρ.img Sg) * Nat.card ↥(Sg ⊓ coreActionKernel K) ≤
        2 * Nat.card (ρ.img S₁) * Nat.card ↥(Sg ⊓ coreActionKernel K) := by
      rw [← h1]
      calc Nat.card Sg ≤ 2 * Nat.card S₁ := hcard
        _ = 2 * (Nat.card (ρ.img S₁) * Nat.card ↥(S₁ ⊓ coreActionKernel K)) := by rw [h2]
        _ ≤ 2 * (Nat.card (ρ.img S₁) * Nat.card ↥(Sg ⊓ coreActionKernel K)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right h4 hpos
  have hX₁ : ∀ s ∈ ρ.img S₁, s * ρ.φ y' = ρ.φ y' * s := by
    intro s hs
    obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hs
    have h1 : ρ.φ (g⁻¹ * y'⁻¹ * g * y') = 1 := (ρ.ker_iff _).2 (hcomm _ hg)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc ρ.φ g * ρ.φ y' = ρ.φ y' * ρ.φ g *
        ((ρ.φ g)⁻¹ * (ρ.φ y')⁻¹ * ρ.φ g * ρ.φ y') := by group
      _ = ρ.φ y' * ρ.φ g := by rw [h1, mul_one]
  obtain ⟨hyS, hyc⟩ := mem_center_of_half (ρ.img_le_R Sg) (ρ.img_isPGroup hS2) h64
    (ρ.phi_mem_img (g := y') hy) (ρ.img_mono hS₁) hcard' hX₁
  have hyP : ρ.φ y' ∈ ρ.img (Sg ⊓ K) := heq ▸ mem_inf.2 ⟨ρ.phi_mem_img (g := y') hy, hyS⟩
  obtain ⟨p', hp', hpy⟩ := ρ.mem_img.1 hyP
  set P : Subgroup G := Sg ⊓ K
  set Y : Subgroup G := P ⊓ ((centralizer ((ρ.img Sg ⊓ S : Subgroup _) :
    Set (Equiv.Perm (Fin 42)))).comap ρ.φ).map (normalizer (K : Set G)).subtype
  have hmemY : ∀ g : ↥(normalizer (K : Set G)), (g : G) ∈ Y ↔
      (g : G) ∈ P ∧ ∀ s ∈ ρ.img Sg ⊓ S, s * ρ.φ g = ρ.φ g * s := by
    intro g
    rw [mem_inf, mem_map]
    constructor
    · rintro ⟨hgP, n, hn, e⟩
      rw [mem_comap, mem_centralizer_iff] at hn
      have : n = g := Subtype.ext e
      rw [this] at hn
      exact ⟨hgP, hn⟩
    · rintro ⟨hgP, h⟩
      exact ⟨hgP, g, mem_comap.2 (mem_centralizer_iff.2 h), rfl⟩
  have hYN : Y ≤ normalizer (K : Set G) := fun g hg => hSN (mem_inf.1 (mem_inf.1 hg).1).1
  have hZY : P ⊓ centralizer (P : Set G) ≤ Y := by
    intro z hz
    obtain ⟨hzP, hzc⟩ := mem_inf.1 hz
    refine (hmemY ⟨z, hSN (mem_inf.1 hzP).1⟩).2 ⟨hzP, fun s hs => ?_⟩
    rw [← heq] at hs
    obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 hs
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.φ (Subtype.ext (mem_centralizer_iff.1 hzc g hg))
  have hYC : Y ⊓ coreActionKernel K = P ⊓ coreActionKernel K := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    intro g hg
    obtain ⟨hgP, hgC⟩ := mem_inf.1 hg
    refine mem_inf.2 ⟨(hmemY ⟨g, hSN (mem_inf.1 hgP).1⟩).2 ⟨hgP, fun s _ => ?_⟩, hgC⟩
    rw [(ρ.ker_iff ⟨g, hSN (mem_inf.1 hgP).1⟩).2 hgC, mul_one, one_mul]
  have himgY : Nat.card (ρ.img Y) = 4 := by
    rw [← card_center_std (ρ.img_le_R Sg) (ρ.img_isPGroup hS2) h64]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
    constructor
    · intro ht
      obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 ht
      obtain ⟨hgP, hgc⟩ := (hmemY g).1 hg
      exact ⟨heq ▸ ρ.phi_mem_img hgP, fun s hs => (hgc s hs).symm⟩
    · rintro ⟨ht, htc⟩
      rw [← heq] at ht
      obtain ⟨g, hg, rfl⟩ := ρ.mem_img.1 ht
      exact ρ.phi_mem_img ((hmemY g).2 ⟨hg, fun s hs => (htc s (heq ▸ hs)).symm⟩)
  have hPC : P ⊓ coreActionKernel K = P ⊓ zStarIn K := by
    ext g
    simp only [mem_inf]
    exact ⟨fun h => ⟨h.1, (mem_coreActionKernel_iff h.1.2).1 h.2⟩,
      fun h => ⟨h.1, (mem_coreActionKernel_iff h.1.2).2 h.2⟩⟩
  have hcardY : Nat.card Y = 4 * Nat.card ↥(P ⊓ zStarIn K) := by
    rw [ρ.card_eq hYN, himgY, hYC, hPC]
  have hZeq : P ⊓ centralizer (P : Set G) = Y :=
    eq_of_le_of_card_ge hZY (by rw [hcardY, hZ])
  have hpZ : (p' : G) ∈ P ⊓ centralizer (P : Set G) := by
    rw [hZeq]
    refine (hmemY p').2 ⟨hp', fun s hs => ?_⟩
    rw [hpy]
    exact (hyc s hs).symm
  have hq : (p' : G)⁻¹ * y ∈ Sg ⊓ coreActionKernel K := by
    refine mem_inf.2 ⟨Sg.mul_mem (Sg.inv_mem (mem_inf.1 hp').1) hy, ?_⟩
    have : ρ.φ (p'⁻¹ * y') = 1 := by rw [map_mul, map_inv, hpy, inv_mul_cancel]
    exact (ρ.ker_iff _).1 this
  have := mul_mem_sup hpZ hq
  rwa [mul_inv_cancel_left] at this

end Real

end CFSG.ComponentClassification.HSFLit.AutL34
