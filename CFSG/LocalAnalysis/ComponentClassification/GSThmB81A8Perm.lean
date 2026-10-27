module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Data
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8PermInputs
public import Certificates.Certificate2019
public import Certificates.Certificate2007
public import Certificates.Certificate2014

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.CatFactsSmall.A8

local notation "P8" => Equiv.Perm (Fin 8)

theorem tau_ok : tauCheck (elemsT QA8) t15 = true :=
  Certificates.certificate2019.1

theorem mem_t15_of_conj {γ : P8} (hγ : γ ∈ QA8.originalSubgroup)
    (h2 : s8 * (γ⁻¹ * s8 * γ) * (s8 * (γ⁻¹ * s8 * γ)) = 1) (h1 : s8 * (γ⁻¹ * s8 * γ) ≠ 1) :
    s8 * (γ⁻¹ * s8 * γ) ∈ t15 := by
  have h := List.all_eq_true.1 tau_ok γ ((mem_elemsT QA8 QA8_ok γ).2 hγ)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    List.any_eq_true] at h
  rcases h with (h | h) | ⟨u, hu, hut⟩
  · exact absurd h2 h
  · exact absurd h h1
  · exact hut ▸ hu

theorem n3_ok : n3Check (elemsT QL8) QL8 n3Data = true :=
  Certificates.certificate2019.2.1

theorem exists_three_cycle {t : P8} (ht : t ∈ t15) :
    ∃ θ e₁ e₂ : P8, θ ∈ QL8.originalSubgroup ∧ e₁ ∈ QL8.originalSubgroup ∧
      e₂ ∈ QL8.originalSubgroup ∧ θ * t = t * θ ∧ e₁ * t = t * e₁ ∧ e₂ * t = t * e₂ ∧
      θ * e₁ * θ⁻¹ = e₂ ∧ θ * e₂ * θ⁻¹ = e₁ * e₂ ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧
      e₁ * e₂ = e₂ * e₁ ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ ∧
      Nat.card ↥(QL8.originalSubgroup ⊓ centralizer ({t} : Set P8)) = 24 ∧
      ∀ c ∈ QL8.originalSubgroup, c * t = t * c →
        c * e₁ * c⁻¹ ∈ four e₁ e₂ ∧ c * e₂ * c⁻¹ ∈ four e₁ e₂ := by
  obtain ⟨⟨t', θ, e₁, e₂⟩, hx, rfl⟩ := List.mem_map.1 ht
  have h := List.all_eq_true.1 n3_ok _ hx
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    Bool.or_eq_true, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hθ, he₁⟩, he₂⟩, hθt⟩, he₁t⟩, he₂t⟩, hθ₁⟩, hθ₂⟩, he₁₁⟩, he₂₂⟩, he₁₂⟩,
    he₁1⟩, he₂1⟩, hne⟩, hcard⟩, hnorm⟩ := h
  refine ⟨θ, e₁, e₂, (mem_iff_sift QL8 QL8_ok θ).2 hθ, (mem_iff_sift QL8 QL8_ok e₁).2 he₁,
    (mem_iff_sift QL8 QL8_ok e₂).2 he₂, hθt, he₁t, he₂t, hθ₁, hθ₂, he₁₁, he₂₂, he₁₂, he₁1, he₂1,
    hne, by rw [card_inf_centralizer QL8 QL8_ok]; exact hcard, fun c hc hct => ?_⟩
  rcases hnorm c ((mem_elemsT QL8 QL8_ok c).2 hc) with h1 | ⟨⟨u, hu, hcu⟩, ⟨w, hw, hcw⟩⟩
  · exact absurd hct h1
  · exact ⟨hcu ▸ hu, hcw ▸ hw⟩

theorem n4_ok : n4Check (elemsT QS8) (elemsT QA8) t15 = true :=
  Certificates.certificate2019.2.2

theorem exists_conj_of_odd {t p θ : P8} (ht : t ∈ t15) (hpt : p * p = t)
    (hps : s8 * p * s8 = p⁻¹) (hθ1 : θ ≠ 1) (hθo : θ ^ 315 = 1) (hθp : θ * p = p * θ)
    (hθs : θ * s8 = s8 * θ) :
    ∃ π ∈ QA8.originalSubgroup, π * t * π⁻¹ = p * s8 := by
  have hall : ∀ x : P8, x ∈ elemsT QS8 := fun x => by
    rw [mem_elemsT QS8 QS8_ok, QS8_eq]
    exact mem_top x
  have hp : p ∈ (elemsT QS8).filter fun p => (t15.any fun t => decide (p * p = t)) &&
      decide (s8 * p * s8 = p⁻¹) := by
    rw [List.mem_filter]
    refine ⟨hall p, ?_⟩
    simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact ⟨⟨t, ht, hpt⟩, hps⟩
  have h := List.all_eq_true.1 n4_ok p hp
  simp only [Bool.or_eq_true, List.all_eq_true, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨π, hπ, hπp⟩
  · exact absurd hθp (h θ ⟨hall θ, ⟨hθs, hθ1⟩, hθo⟩)
  · exact ⟨π, (mem_elemsT QA8 QA8_ok π).1 hπ, hpt ▸ hπp⟩

end CFSG.ComponentClassification.GSThmB.A8
