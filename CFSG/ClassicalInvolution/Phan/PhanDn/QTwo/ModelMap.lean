module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Model
public import CFSG.LieType.CurtisTits.AmalgamMulEquiv

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.LieType.CurtisTits

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section General

variable {n : ℕ} {M : CoxeterMatrix (Fin n)}
variable {X : Type} [Group X] {Y : Type} [Group Y]

theorem QTwoPhanFamily.levi_map (S : QTwoPhanFamily K M X) (φ : X →* Y)
    (C : Set (Fin n)) : (S.map φ).levi C = (S.levi C).map φ := by
  unfold QTwoPhanFamily.levi
  rw [Subgroup.map_sup]
  congr 1
  · simp only [Subgroup.map_iSup, MonoidHom.range_comp, QTwoPhanFamily.map]
  · simp only [Subgroup.map_iSup, MonoidHom.range_comp, QTwoPhanFamily.map]

theorem QTwoPhanFamily.Faithful.map_of_injective {S : QTwoPhanFamily K M X}
    (h : S.Faithful) {φ : X →* Y} (hφ : Function.Injective φ) :
    (S.map φ).Faithful where
  ι_inj i := by
    change Function.Injective (φ.comp (S.ι i))
    exact hφ.comp (h.ι_inj i)
  θ_inj i j hij := by
    change Function.Injective (φ.comp (S.θ i j))
    exact hφ.comp (h.θ_inj i j hij)
  split C₁ C₂ hC hdisj hno := by
    rw [QTwoPhanFamily.levi_map, QTwoPhanFamily.levi_map,
      ← Subgroup.map_inf_eq _ _ _ hφ, h.split C₁ C₂ hC hdisj hno, Subgroup.map_bot]

end General

namespace QTwoModelD

variable {m : ℕ} {X : Type} [Group X]
variable {Y : Type} [Group Y]

@[expose] noncomputable def map (d : QTwoModelD K m X) (e : X ≃* Y) :
    QTwoModelD K m Y where
  S := d.S.map e.toMonoidHom
  faithful := d.faithful.map_of_injective e.injective
  P C := (d.P C).map e.toMonoidHom
  T i := (d.T i).map e.toMonoidHom
  completion := d.completion.map_mulEquiv (K' := Y) e
  strip := by
    have h := d.strip.map_mulEquiv (K' := Y) e
    have hL : (fun C => (d.S.levi C).map e.toMonoidHom) =
        (fun C => (d.S.map e.toMonoidHom).levi C) := by
      funext C
      exact (QTwoPhanFamily.levi_map d.S e.toMonoidHom C).symm
    rw [hL] at h
    exact h

@[simp] theorem map_S (d : QTwoModelD K m X) (e : X ≃* Y) :
    (d.map e).S = d.S.map e.toMonoidHom := rfl

@[simp] theorem map_P (d : QTwoModelD K m X) (e : X ≃* Y) (C : Set (Fin m)) :
    (d.map e).P C = (d.P C).map e.toMonoidHom := rfl

@[simp] theorem map_T (d : QTwoModelD K m X) (e : X ≃* Y) (i : Fin m) :
    (d.map e).T i = (d.T i).map e.toMonoidHom := rfl

end QTwoModelD

end CFSG.ClassicalInvolution.PhanDn.QTwo
