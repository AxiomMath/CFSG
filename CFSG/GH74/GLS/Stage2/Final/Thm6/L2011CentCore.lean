module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15Perf
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CentCoreC
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CentCoreZ

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final.Thm6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l2011_cent_core {H J F₁ : Subgroup G} (hJH : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J) (hJle : J ≤ H)
    (hJperf : ⁅J, J⁆ = J) (hF₁H : F₁ ≤ H)
    (hF₁N : ∀ f ∈ F₁, ∀ j ∈ J, f * j * f⁻¹ * j⁻¹ ∈ pPrimeCoreOf 2 J)
    (hcop : Nat.Coprime (Nat.card ↥F₁) (Nat.card ↥⁅pPrimeCoreOf 2 J, J⁆))
    {S₀ : Subgroup G} (hS₀J : S₀ ≤ J) (hS₀F : ∀ s ∈ S₀, ∀ f ∈ F₁, s * f * s⁻¹ ∈ F₁) :
    (∀ s ∈ S₀, ∀ f ∈ F₁, s * f = f * s) ∧
      ∀ j ∈ J, ∃ d ∈ J, (∀ f ∈ F₁, d * f = f * d) ∧ j * d⁻¹ ∈ pPrimeCoreOf 2 J := by
  set N : Subgroup G := pPrimeCoreOf 2 J with hN
  set X : Subgroup G := ⁅N, J⁆ with hX
  have hNJ : N ≤ J := Subgroup.map_subtype_le _
  have hNH : ∀ h ∈ H, ∀ b ∈ N, h * b * h⁻¹ ∈ N := fun h hh b hb =>
    L20.pPrimeCoreOf_conj_mem hJH hh hb
  have hXH : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X := by
    intro h hh x hx
    have hmap : X.map (MulAut.conj h).toMonoidHom ≤ X := by
      rw [hX, Subgroup.map_commutator]
      apply Subgroup.commutator_mono
      · rintro _ ⟨b, hb, rfl⟩
        exact hNH h hh b hb
      · rintro _ ⟨b, hb, rfl⟩
        exact hJH h hh b hb
    exact hmap (Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩)
  have hXN : X ≤ N := by
    rw [hX, Subgroup.commutator_le]
    intro n hn j hj
    have : j * n⁻¹ * j⁻¹ ∈ N := hNH j (hJle hj) n⁻¹ (N.inv_mem hn)
    have e : ⁅n, j⁆ = n * (j * n⁻¹ * j⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem hn this
  have hNX : ∀ n ∈ N, ∀ j ∈ J, ⁅n, j⁆ ∈ X := fun n hn j hj => Subgroup.commutator_mem_commutator hn hj
  have hFN : ∀ f ∈ F₁, ∀ j ∈ J, ⁅f, j⁆ ∈ N := fun f hf j hj => hF₁N f hf j hj
  have hJF : ∀ j ∈ J, ∀ f ∈ F₁, ⁅j, f⁆ ∈ X :=
    CentCore.commutator_mem_of_perfect hJle hF₁H hXH hJperf hNX hFN
  have hdisj : Disjoint F₁ X := Subgroup.disjoint_of_coprime_natCard hcop
  have hone : ∀ y, y ∈ F₁ → y ∈ X → y = 1 := fun y h1 h2 => Subgroup.disjoint_def.1 hdisj h1 h2
  have hcomm : ∀ d ∈ J, (∀ f ∈ F₁, d * f * d⁻¹ ∈ F₁) → ∀ f ∈ F₁, d * f = f * d := by
    intro d hd hdF f hf
    have h1 : ⁅d, f⁆ ∈ F₁ := F₁.mul_mem (hdF f hf) (F₁.inv_mem hf)
    have h3 : ⁅d, f⁆ = 1 := hone _ h1 (hJF d hd f hf)
    rw [commutatorElement_def] at h3
    calc d * f = (d * f * d⁻¹ * f⁻¹) * (f * d) := by group
      _ = f * d := by rw [h3, one_mul]
  refine ⟨fun s hs f hf => hcomm s (hS₀J hs) (fun f' hf' => hS₀F s hs f' hf') f hf, ?_⟩
  intro j hj
  have hF₁X : F₁ ≤ normalizer (X : Set G) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hXH f (hF₁H hf) x hx, fun hx => ?_⟩
    have := hXH f⁻¹ (H.inv_mem (hF₁H hf)) _ hx
    simpa [mul_assoc] using this
  obtain ⟨c, hcX, hc⟩ := CentCore.exists_conj_mem_normalizes hF₁X hcop (fun f hf => hJF j hj f hf)
  have hdJ : c⁻¹ * j ∈ J := J.mul_mem (J.inv_mem (hNJ (hXN hcX))) hj
  refine ⟨c⁻¹ * j, hdJ, hcomm _ hdJ (fun f hf => ?_), ?_⟩
  · have := hc f hf
    rwa [show c⁻¹ * (j * f * j⁻¹) * c = c⁻¹ * j * f * (c⁻¹ * j)⁻¹ by group] at this
  · rw [show j * (c⁻¹ * j)⁻¹ = c by group]
    exact hXN hcX

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
