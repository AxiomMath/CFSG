module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.ClassicalGroups.Unitary

variable {F : Type} [Field F] [Finite F]

theorem card_fixedField_mul_self {σ : F ≃+* F} (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0) :
    Nat.card {c : F // σ c = c} * Nat.card {c : F // σ c = c} = Nat.card F := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  have hωne : σ ω - ω ≠ 0 := by
    intro h
    have h1 : (1 : F) = 0 := by linear_combination -hω - h + σ ω * h2
    exact one_ne_zero h1
  have inj : Function.Injective
      (fun p : {c : F // σ c = c} × {c : F // σ c = c} => p.1.1 + ω * p.2.1) := by
    rintro ⟨α, β⟩ ⟨α', β'⟩ h
    have h0 : α.1 + ω * β.1 = α'.1 + ω * β'.1 := h
    have hα : σ α.1 = α.1 := α.2
    have hα' : σ α'.1 = α'.1 := α'.2
    have hβ : σ β.1 = β.1 := β.2
    have hβ' : σ β'.1 = β'.1 := β'.2
    have h1 : σ (α.1 + ω * β.1) = σ (α'.1 + ω * β'.1) := by rw [h0]
    rw [map_add, map_mul, map_add, map_mul, hα, hα', hβ, hβ'] at h1
    have key : (σ ω - ω) * (β.1 - β'.1) = 0 := by linear_combination h1 - h0
    have hb : β.1 = β'.1 := by
      rcases mul_eq_zero.mp key with h3 | h3
      · exact absurd h3 hωne
      · exact sub_eq_zero.mp h3
    have ha : α.1 = α'.1 := by linear_combination h0 - ω * hb
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have surj : Function.Surjective
      (fun p : {c : F // σ c = c} × {c : F // σ c = c} => p.1.1 + ω * p.2.1) := by
    intro c
    have hβ : σ (c + σ c) = c + σ c := hσ.trace_fixed c
    have hα : σ (c + ω * (c + σ c)) = c + ω * (c + σ c) := by
      rw [map_add, map_mul, hβ]
      linear_combination (σ c + c) * hω + (σ c * (1 - ω) - c * ω) * h2
    refine ⟨(⟨c + ω * (c + σ c), hα⟩, ⟨c + σ c, hβ⟩), ?_⟩
    show c + ω * (c + σ c) + ω * (c + σ c) = c
    linear_combination (ω * (c + σ c)) * h2
  have hbij : Function.Bijective
      (fun p : {c : F // σ c = c} × {c : F // σ c = c} => p.1.1 + ω * p.2.1) := ⟨inj, surj⟩
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective _ hbij)

end CFSG.LocalAnalysis.RankThreeUC
