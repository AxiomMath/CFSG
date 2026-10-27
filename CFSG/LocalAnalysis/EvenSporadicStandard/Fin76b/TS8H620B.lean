module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H616
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611E
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H620A
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma620B

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem z_not_mem_cent_alpha {α : G} (hα : AlphaSpec S z t α) :
    z ∉ centralizer ({α} : Set G) := by
  intro hz
  have hαz : α * z = z * α := (mem_centralizer_singleton_iff.1 hz).symm
  have h2 : z * α = t * (z * α) := by rw [← hα.rel, hαz]
  exact h.t_ne (by simpa using h2.symm)

theorem xor_mem_cent_alpha {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {g : G}
    (hg : ∀ q : G, q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ↔
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    Xor (g * z ∈ centralizer ({α} : Set G)) (g ∈ centralizer ({α} : Set G)) := by
  obtain ⟨hgt, hperm⟩ := h.normalizer_Q_perm_W hα hF hM hp hg
  have e : (g * z) * α * (g * z)⁻¹ = (g * α * g⁻¹) * t := by
    calc (g * z) * α * (g * z)⁻¹ = g * (z * α * z⁻¹) * g⁻¹ := by group
      _ = g * (α * t) * g⁻¹ := by rw [h.z_conj_alpha hα]
      _ = (g * α * g⁻¹) * (g * t * g⁻¹) := by group
      _ = (g * α * g⁻¹) * t := by rw [hgt]
  have hαt : α * t ≠ α := fun e => h.t_ne (by simpa using e)
  rw [mem_cent_singleton_iff_conj, mem_cent_singleton_iff_conj, e]
  rcases hperm with ⟨h1, -⟩ | ⟨h1, -⟩
  · right
    refine ⟨h1, ?_⟩
    rw [h1]
    exact hαt
  · left
    refine ⟨?_, ?_⟩
    · rw [h1, mul_assoc, h.t_sq, mul_one]
    · rw [h1]
      exact hαt

theorem relIndex_inf_cent_alpha {α : G} (hα : AlphaSpec S z t α) (hF : EFacts611 E t)
    (hM : OuterMFacts E S z t) (hp : OuterPairing h hα) {Rs : Subgroup G} (hz : z ∈ Rs)
    (hN : ∀ g ∈ Rs, ∀ q : G, q ∈ Fsub h hα ⊓ centralizer ({α} : Set G) ↔
      g * q * g⁻¹ ∈ Fsub h hα ⊓ centralizer ({α} : Set G)) :
    (Rs ⊓ centralizer ({α} : Set G)).relIndex Rs = 2 ∧
      z ∉ Rs ⊓ centralizer ({α} : Set G) := by
  refine ⟨?_, fun hzR => h.z_not_mem_cent_alpha hα hzR.2⟩
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨z, hz⟩, fun b => ?_⟩
  have hx := h.xor_mem_cent_alpha hα hF hM hp (hN b b.2)
  simpa [Subgroup.mem_subgroupOf] using hx

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
