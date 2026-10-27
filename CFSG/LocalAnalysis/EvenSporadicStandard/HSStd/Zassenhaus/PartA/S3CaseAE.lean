module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3CaseAC

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Equiv Subgroup

theorem s3a_A5_simple : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)

section Factors

variable {D : Type} [Group D]

@[expose] def s3a_fE (E : Subgroup D) (e : ↥E ≃* ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) :
    ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) →* D :=
  E.subtype.comp e.symm.toMonoidHom

@[expose] def s3a_j₁ (E : Subgroup D) (e : ↥E ≃* ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) :
    ↥(alternatingGroup (Fin 5)) →* D :=
  (s3a_fE E e).comp (MonoidHom.inl _ _)

@[expose] def s3a_j₂ (E : Subgroup D) (e : ↥E ≃* ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) :
    ↥(alternatingGroup (Fin 5)) →* D :=
  (s3a_fE E e).comp (MonoidHom.inr _ _)

variable (E : Subgroup D) (e : ↥E ≃* ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))

theorem s3a_fE_apply (x : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) :
    s3a_fE E e x = ((e.symm x : ↥E) : D) := rfl

theorem s3a_fE_injective : Function.Injective (s3a_fE E e) := by
  intro x y hxy
  exact e.symm.injective (Subtype.ext hxy)

theorem s3a_fE_mem (x : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) :
    s3a_fE E e x ∈ E := (e.symm x).2

theorem s3a_fE_surj {x : D} (hx : x ∈ E) : ∃ y, s3a_fE E e y = x :=
  ⟨e ⟨x, hx⟩, by simp [s3a_fE_apply]⟩

theorem s3a_j₁_injective : Function.Injective (s3a_j₁ E e) :=
  fun _ _ hab => (Prod.ext_iff.1 (s3a_fE_injective E e hab)).1

theorem s3a_j₂_injective : Function.Injective (s3a_j₂ E e) :=
  fun _ _ hab => (Prod.ext_iff.1 (s3a_fE_injective E e hab)).2

theorem s3a_j₁_apply (a : ↥(alternatingGroup (Fin 5))) : s3a_j₁ E e a = s3a_fE E e (a, 1) := rfl

theorem s3a_j₂_apply (b : ↥(alternatingGroup (Fin 5))) : s3a_j₂ E e b = s3a_fE E e (1, b) := rfl

theorem s3a_fE_mul (a b : ↥(alternatingGroup (Fin 5))) :
    s3a_fE E e (a, b) = s3a_j₁ E e a * s3a_j₂ E e b := by
  rw [s3a_j₁_apply, s3a_j₂_apply, ← map_mul]
  simp

theorem s3a_j_comm (a b : ↥(alternatingGroup (Fin 5))) :
    s3a_j₁ E e a * s3a_j₂ E e b = s3a_j₂ E e b * s3a_j₁ E e a := by
  rw [s3a_j₁_apply, s3a_j₂_apply, ← map_mul, ← map_mul]
  simp

theorem s3a_j₁_mem (a : ↥(alternatingGroup (Fin 5))) : s3a_j₁ E e a ∈ E := s3a_fE_mem E e _

theorem s3a_j₂_mem (a : ↥(alternatingGroup (Fin 5))) : s3a_j₂ E e a ∈ E := s3a_fE_mem E e _

theorem s3a_j₁_ne_j₂ (a b : ↥(alternatingGroup (Fin 5))) (h : s3a_j₁ E e a = s3a_j₂ E e b) :
    a = 1 := by
  have := s3a_fE_injective E e h
  exact (Prod.ext_iff.1 this).1

variable [E.Normal]

@[expose] def s3a_tau (d : D) :
    ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃*
      ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) :=
  (e.symm.trans (MulAut.conjNormal d)).trans e

theorem s3a_tau_spec (d : D) (x : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) :
    s3a_fE E e (s3a_tau E e d x) = d * s3a_fE E e x * d⁻¹ := by
  simp [s3a_tau, s3a_fE_apply, MulAut.conjNormal_apply]

theorem s3a_perm_cases (d : D) :
    ((∀ a, ∃ c, d * s3a_j₁ E e a * d⁻¹ = s3a_j₁ E e c) ∧
      ∀ b, ∃ c, d * s3a_j₂ E e b * d⁻¹ = s3a_j₂ E e c) ∨
    ((∀ a, ∃ c, d * s3a_j₁ E e a * d⁻¹ = s3a_j₂ E e c) ∧
      ∀ b, ∃ c, d * s3a_j₂ E e b * d⁻¹ = s3a_j₁ E e c) := by
  have := s3a_A5_simple
  rcases s3a_aut_prod s3a_A5_noncomm (s3a_tau E e d) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    refine ⟨fun a => ⟨(s3a_tau E e d (a, 1)).1, ?_⟩, fun b => ⟨(s3a_tau E e d (1, b)).2, ?_⟩⟩
    · rw [s3a_j₁_apply, s3a_j₁_apply, ← s3a_tau_spec]
      congr 1
      exact Prod.ext rfl (h1 a)
    · rw [s3a_j₂_apply, s3a_j₂_apply, ← s3a_tau_spec]
      congr 1
      exact Prod.ext (h2 b) rfl
  · right
    refine ⟨fun a => ⟨(s3a_tau E e d (a, 1)).2, ?_⟩, fun b => ⟨(s3a_tau E e d (1, b)).1, ?_⟩⟩
    · rw [s3a_j₁_apply, s3a_j₂_apply, ← s3a_tau_spec]
      congr 1
      exact Prod.ext (h1 a) rfl
    · rw [s3a_j₂_apply, s3a_j₁_apply, ← s3a_tau_spec]
      congr 1
      exact Prod.ext rfl (h2 b)

end Factors

section Card

variable {D : Type} [Group D] [Finite D] {t : D} {K : Subgroup D}

theorem s3a_E_not_comm (h : DShape D t K) (ψ : ↥K ≃* Perm (Fin 5)) (E : Subgroup D)
    (e : ↥E ≃* ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)))
    (hE : ∀ x ∈ E, t * x = x * t) : False := by
  have hle : E ≤ centralizer ({t} : Set D) := fun x hx => by
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hE x hx
  have h1 := Subgroup.card_le_of_le hle
  have h2 : Nat.card E = 3600 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, s3a_card_A5]
  have h3 := s3a_card_cent_le h ψ
  omega

end Card

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
