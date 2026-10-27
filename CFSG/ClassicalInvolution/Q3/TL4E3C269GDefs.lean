module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

@[expose] def E3C269L2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
    (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f →
      LieModel (FStarQuot X) .PSL 2 p f → ∀ ι : QuaternionGroup 2 →* X, Function.Injective ι →
        ∀ t s : X, ι (QuaternionGroup.a 2) = t → t ∈ genFittingFStar X → t * s = s * t →
          s ≠ t → (∃ g : X, s = g * t * g⁻¹) →
            Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤

namespace E3C269G

variable {G P : Type*} [Group G] [Group P]

theorem map_centralizer_singleton (e : G ≃* P) (x : G) :
    (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set P) := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    show e g * e x = e x * e g
    rw [← map_mul, ← map_mul, hg]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy

theorem sup_centralizer_eq_top_of_equiv (e : G ≃* P) {t s : G}
    (h : Subgroup.centralizer ({e t} : Set P) ⊔ Subgroup.centralizer ({e s} : Set P) = ⊤) :
    Subgroup.centralizer ({t} : Set G) ⊔ Subgroup.centralizer ({s} : Set G) = ⊤ := by
  rw [← map_centralizer_singleton, ← map_centralizer_singleton, ← Subgroup.map_sup] at h
  rw [eq_top_iff]
  intro y _
  have hy : e y ∈ (Subgroup.centralizer ({t} : Set G) ⊔
      Subgroup.centralizer ({s} : Set G)).map e.toMonoidHom := by
    rw [h]
    exact Subgroup.mem_top _
  obtain ⟨z, hz, hzy⟩ := hy
  rw [← e.injective hzy]
  exact hz

theorem sup_centralizer_eq_top_of_conj {t s c : G} (hc : c * t = t * c)
    (h : Subgroup.centralizer ({t} : Set G) ⊔
      Subgroup.centralizer ({c * s * c⁻¹} : Set G) = ⊤) :
    Subgroup.centralizer ({t} : Set G) ⊔ Subgroup.centralizer ({s} : Set G) = ⊤ := by
  have hct : MulAut.conj c t = t := by
    rw [MulAut.conj_apply, hc, mul_inv_cancel_right]
  have h' := sup_centralizer_eq_top_of_equiv (MulAut.conj c) (t := t) (s := s)
  rw [hct, MulAut.conj_apply] at h'
  exact h' h

end E3C269G

end CFSG.ClassicalInvolution.Q3.TL4
