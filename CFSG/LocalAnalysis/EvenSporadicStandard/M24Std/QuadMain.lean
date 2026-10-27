module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadProp
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDefs

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup Quad

variable {G : Type} [Group G]

theorem exists_cData_of_W [Finite G] {L A : Subgroup G} {z : G} (hs : LocalSetting G L z)
    (hA : SextetType L A) (hF : SextetFacts L A) (hQ : SextetFactsQW L A)
    (hT : TranslationData A z) : ∃ C : Subgroup G, CData A z C := by
  have hAL : A ≤ L := hA.1
  obtain ⟨w, hwN, hw3, hconj, hwfix⟩ := hQ.omega
  have homega : ∀ n ∈ egNL L A, ∃ b ∈ A, n * w * n⁻¹ = w * b ∨ n * w * n⁻¹ = w⁻¹ * b := by
    intro n hn
    have hnwL : n * w * n⁻¹ ∈ L := L.mul_mem (L.mul_mem hn.2 hwN.2) (L.inv_mem hn.2)
    rcases hconj n hn with h | h
    · refine ⟨w⁻¹ * (n * w * n⁻¹),
        hF.cent _ (L.mul_mem (L.inv_mem hwN.2) hnwL) fun a ha => ?_, Or.inl (by group)⟩
      calc w⁻¹ * (n * w * n⁻¹) * a
            = w⁻¹ * ((n * w * n⁻¹) * a * (n * w * n⁻¹)⁻¹) * (n * w * n⁻¹) := by group
        _ = w⁻¹ * (w * a * w⁻¹) * (n * w * n⁻¹) := by rw [h a ha]
        _ = a * (w⁻¹ * (n * w * n⁻¹)) := by group
    · refine ⟨w * (n * w * n⁻¹),
        hF.cent _ (L.mul_mem hwN.2 hnwL) fun a ha => ?_, Or.inr (by group)⟩
      calc w * (n * w * n⁻¹) * a
            = w * ((n * w * n⁻¹) * a * (n * w * n⁻¹)⁻¹) * (n * w * n⁻¹) := by group
        _ = w * (w⁻¹ * a * w) * (n * w * n⁻¹) := by rw [h a ha]
        _ = a * (w * (n * w * n⁻¹)) := by group
  have H : SplitHyp G L A z w := ⟨hs, hAL, hF, hT, hwN, hw3, hwfix, homega⟩
  obtain ⟨C, hAC, hCΛ, hnorm, hzC, hcard, hlam, honto, hnormN⟩ := H.exists_C
  obtain ⟨a₁, ha₁, ha₁1, hgen⟩ := hQ.gen45
  have hker : ∀ c ∈ C, z * c = c * z → c ∈ A := by
    intro c hc hzc
    rcases ker_tau hs hAL hF (hCΛ hc) hzc with h | h
    · exact h
    · exfalso
      apply hzC
      have : z = (z * c) * c⁻¹ := by group
      rw [this]
      exact C.mul_mem (hAC h) (C.inv_mem hc)
  obtain ⟨hab, hdich⟩ := quad_prop14 (L := L) hAC hF.elem
    (fun c hc a ha => lam_comm (hCΛ hc) ha)
    (fun c hc => sq_mem hs hAL hF hT (hCΛ hc))
    (fun c hc d hd => comm_mem hs hAL hF hT (hCΛ hc) (hCΛ hd))
    (fun c hc => tau_mem hs hAL hT (hCΛ hc)) hker honto
    (fun n hn => ⟨nl_comm_z hs hn, hnormN n hn⟩) ha₁ ha₁1 hgen hQ.fix
  exact ⟨C, ⟨hAC, hCΛ, hnorm, hzC, hcard, hab, fun c hc => sq_mem hs hAL hF hT (hCΛ hc),
    fun c hc => tau_mem hs hAL hT (hCΛ hc), honto, hlam, hdich⟩⟩

end CFSG.EvenSporadicStandard.M24Std
