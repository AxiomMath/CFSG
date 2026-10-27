
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final4Base

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def WreathAlt (K : Type*) [Group K] (zb : K ⧸ fusionOddCore K) : Prop :=
  ∃ N₁ N₂ : Subgroup (K ⧸ fusionOddCore K),
    Nonempty (N₁ ≃* alternatingGroup (Fin 6)) ∧ Nonempty (N₂ ≃* alternatingGroup (Fin 6)) ∧
    (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧ Disjoint N₁ N₂ ∧ (N₁ ⊔ N₂).Normal ∧
    (N₁ ⊔ N₂).index = 2 ∧ zb ∉ N₁ ⊔ N₂ ∧ N₁.map (MulAut.conj zb).toMonoidHom = N₂

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G}

theorem lemma66 (hZ : Fin76bNotZ2A6) (hconf : Rest6Config L z t T₀ E Q x β B)
    (hW : WFacts L t E) :
    ∃ hz : z ∈ centralizer ({β} : Set G),
      WreathAlt ↥(centralizer ({β} : Set G)) (QuotientGroup.mk ⟨z, hz⟩) := by
  obtain ⟨y, hyN, hyβ, hyz, hyt⟩ := exists_swap_centralizing_beta hconf hW
  obtain ⟨hz, h64⟩ := hconf.lemma64
  refine ⟨hz, ?_⟩
  rcases h64 with h | h
  · exact absurd h (hZ G L z t T₀ E Q x β B hconf hW y hyN hyβ hyz hyt)
  · exact h

theorem lemma66' (hZ : Fin76bNotZ2A6) (hconf : Rest6Config L z t T₀ E Q x β B)
    (hW : WFacts L t E) {K : Subgroup G} (hK : K = centralizer ({β} : Set G)) :
    ∃ hz : z ∈ K, WreathAlt ↥K (QuotientGroup.mk ⟨z, hz⟩) := by
  subst hK
  exact lemma66 hZ hconf hW

theorem mem_klein_of_comm (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSC : S ≤ centralizer (E : Set G)) (hzS : z ∈ S) {s : G} (hsS : s ∈ S)
    (hsz : s * z = z * s) : s = 1 ∨ s = z ∨ s = t ∨ s = z * t := by
  have hsz' : s ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hsz
  rw [h.cent_eq] at hsz'
  obtain ⟨a, ha, c, hc, hsac⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (zpowers_le.2 h.z_cent) hsz'
  have haS : a ∈ S := by
    have : a = s * c⁻¹ := by rw [hsac]; group
    rw [this]
    exact mul_mem hsS (inv_mem (zpowers_le.2 hzS hc))
  have hat : a ∈ zpowers t :=
    EConfig.le_zpowers_t h hE (hS2.to_le (zpowers_le.2 haS)) (zpowers_le.2 ha)
      (zpowers_le.2 (hSC haS)) (mem_zpowers a)
  rcases mem_zpowers_sq_eq_one h.t_sq hat with ha1 | ha1 <;>
    rcases mem_zpowers_sq_eq_one h.z_sq hc with hc1 | hc1
  · left; rw [hsac, ha1, hc1, mul_one]
  · right; left; rw [hsac, ha1, hc1, one_mul]
  · right; right; left; rw [hsac, ha1, hc1, mul_one]
  · right; right; right; rw [hsac, ha1, hc1, h.t_comm_z]

end CFSG.EvenSporadicStandard.Fin76b
