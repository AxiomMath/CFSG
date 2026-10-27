module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Alt2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

theorem sec1011_alt2_perm (h : Sec1011A2 B t K φ) :
    ∃ Alt : Subgroup (Equiv.Perm (Fin 6)), (Alt = alternatingGroup (Fin 6) ∨ Alt = ⊤) ∧
      Nonempty (↥K ≃* ↥Alt) ∧
      ∃ φ6 : (Fin 6 → ZMod 2) → A,
        (∀ v w, φ6 (v + w) = φ6 v * φ6 w) ∧
        (∀ v, φ6 v = 1 ↔ v = 0 ∨ v = sec1011_one6) ∧
        (∀ a : A, ∃ v, φ6 v = a) ∧
        (∀ α ∈ K, ∃ σ ∈ Alt, ∀ v, α (φ6 v) = φ6 (permVec σ v)) ∧
        (∀ σ ∈ Alt, ∃ α ∈ K, ∀ v, α (φ6 v) = φ6 (permVec σ v)) := by
  obtain ⟨ρ, hinj, hact, hrange⟩ := sec1011_alt2_act h
  have hcore := h.core
  refine ⟨ρ.range, hrange, ⟨MonoidHom.ofInjective hinj⟩, sec1011_phi6 t φ,
    sec1011_phi6_hom hcore, sec1011_phi6_ker hcore, sec1011_phi6_surj hcore, ?_, ?_⟩
  · intro α hα
    exact ⟨ρ ⟨α, hα⟩, ⟨⟨α, hα⟩, rfl⟩,
      fun v => sec1011_phi6_act hcore (α := α) (ρ ⟨α, hα⟩) (hact ⟨α, hα⟩) v⟩
  · rintro σ ⟨α, rfl⟩
    exact ⟨α, α.2, fun v => sec1011_phi6_act hcore (α := (α : MulAut A)) (ρ α) (hact α) v⟩

end CFSG.OddStandard.SmallF3.Omega
