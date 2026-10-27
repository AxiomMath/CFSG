module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.HardMathSupport.Lang.E6Descent.RankB3

open Module Matrix QuadraticMap CFSG.LieType.Universal.Spin

variable {F : Type} [Field F]

abbrev V3 (F : Type) := Fin 3 ⊕ Fin 3 ⊕ Unit → F

noncomputable abbrev Q3 (F : Type) [Field F] : QuadraticForm F (V3 F) := quadOdd 3 F

def eV : V3 F := Pi.single (.inl 0) 1

def fV : V3 F := Pi.single (.inr (.inl 0)) 1

theorem polar_eV (v : V3 F) : polar (Q3 F) v eV = v (.inr (.inl 0)) :=
  polar_quadOdd_single_inl 3 F v 0

theorem polar_eV_left (v : V3 F) : polar (Q3 F) eV v = v (.inr (.inl 0)) := by
  rw [polar_comm, polar_eV]

theorem Q_eV : Q3 F eV = 0 := by
  rw [quadOdd_apply]
  simp [eV, Pi.single_apply]

def WS (F : Type) [Field F] : Submodule F (V3 F) where
  carrier := {w | w (.inr (.inl 0)) = 0 ∧ w (.inl 0) = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by simp [ha1, hb1], by simp [ha2, hb2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    exact ⟨by simp [ha1], by simp [ha2]⟩

theorem mem_WS {w : V3 F} : w ∈ WS F ↔ w (.inr (.inl 0)) = 0 ∧ w (.inl 0) = 0 := Iff.rfl

noncomputable def eich (w : V3 F) : V3 F →ₗ[F] V3 F :=
  LinearMap.id + (LinearMap.proj (.inr (.inl 0)) : V3 F →ₗ[F] F).smulRight w
    - (((polarBilin (Q3 F)).flip w) + (Q3 F w) • (LinearMap.proj (.inr (.inl 0)) : V3 F →ₗ[F] F)
      ).smulRight eV

theorem eich_apply (w v : V3 F) :
    eich w v = v + (v (.inr (.inl 0))) • w
      - (polar (Q3 F) v w + Q3 F w * v (.inr (.inl 0))) • eV := by
  simp [eich, polarBilin_apply_apply]

theorem eV_f : (eV : V3 F) (.inr (.inl 0)) = 0 := by simp [eV]

theorem eich_f {w : V3 F} (hw : w (.inr (.inl 0)) = 0) (v : V3 F) :
    eich w v (.inr (.inl 0)) = v (.inr (.inl 0)) := by
  simp [eich_apply, hw, eV_f]

theorem eich_zero (v : V3 F) : eich 0 v = v := by
  simp [eich_apply]

theorem eich_mul {w w' : V3 F} (hw : w (.inr (.inl 0)) = 0) (hw' : w' (.inr (.inl 0)) = 0)
    (v : V3 F) : eich w (eich w' v) = eich (w + w') v := by
  rw [eich_apply w (eich w' v), eich_f hw' v, eich_apply w' v, eich_apply (w + w') v]
  have hQ : Q3 F (w + w') = Q3 F w + Q3 F w' + polar (Q3 F) w w' := QuadraticMap.map_add _ _ _
  have hc : polar (Q3 F) w' w = polar (Q3 F) w w' := polar_comm _ _ _
  rw [hQ]
  simp only [polar_add_left, polar_sub_left, polar_smul_left, polar_add_right]
  rw [polar_eV_left, hw, hc]
  module

theorem Q_eich {w : V3 F} (hw : w (.inr (.inl 0)) = 0) (v : V3 F) :
    Q3 F (eich w v) = Q3 F v := by
  rw [eich_apply, sub_eq_add_neg, ← neg_smul]
  have h1 : ∀ x y : V3 F, Q3 F (x + y) = Q3 F x + Q3 F y + polar (Q3 F) x y :=
    fun x y => QuadraticMap.map_add _ _ _
  have h2 : ∀ (c : F) (x : V3 F), Q3 F (c • x) = c * c * Q3 F x :=
    fun c x => QuadraticMap.map_smul _ _ _
  rw [h1, h1, h2, h2, Q_eV]
  simp only [polar_add_left, polar_smul_left, polar_smul_right]
  simp only [polar_eV, hw, smul_eq_mul]
  ring

def dVec (F : Type) [Field F] : Fin 3 ⊕ Fin 3 ⊕ Unit → F :=
  fun i => if i = .inl 0 ∨ i = .inr (.inl 0) then -1 else 1

noncomputable def hV (F : Type) [Field F] : V3 F →ₗ[F] V3 F :=
  Matrix.mulVecLin (Matrix.diagonal (dVec F))

theorem hV_apply (v : V3 F) (i : Fin 3 ⊕ Fin 3 ⊕ Unit) : hV F v i = dVec F i * v i := by
  simp [hV, Matrix.mulVec_diagonal]

theorem hV_hV (v : V3 F) : hV F (hV F v) = v := by
  ext i
  rw [hV_apply, hV_apply, ← mul_assoc]
  by_cases h : i = .inl 0 ∨ i = .inr (.inl 0) <;> simp [dVec, h]

theorem Q_hV (v : V3 F) : Q3 F (hV F v) = Q3 F v := by
  rw [quadOdd_apply, quadOdd_apply]
  simp [Fin.sum_univ_three, hV_apply, dVec]

theorem hV_eV : hV F eV = -eV := by
  ext i
  rw [hV_apply]
  by_cases h : i = .inl 0 ∨ i = .inr (.inl 0)
  · rcases h with rfl | rfl <;> simp [dVec, eV]
  · push Not at h
    simp [dVec, eV, h.1, h.2]

theorem hV_WS {w : V3 F} (hw : w ∈ WS F) : hV F w = w := by
  obtain ⟨h1, h2⟩ := hw
  ext i
  rw [hV_apply]
  by_cases h : i = .inl 0 ∨ i = .inr (.inl 0)
  · rcases h with rfl | rfl <;> simp [h1, h2]
  · simp [dVec, h]

theorem polar_hV (u v : V3 F) : polar (Q3 F) (hV F u) (hV F v) = polar (Q3 F) u v := by
  unfold polar
  rw [← map_add, Q_hV, Q_hV, Q_hV]

theorem polar_hV_WS (u : V3 F) {w : V3 F} (hw : w ∈ WS F) :
    polar (Q3 F) (hV F u) w = polar (Q3 F) u w := by
  conv_lhs => rw [← hV_WS hw]
  exact polar_hV u w

theorem hV_eich {w : V3 F} (hw : w ∈ WS F) (v : V3 F) :
    hV F (eich w v) = eich (-w) (hV F v) := by
  have hf : hV F v (.inr (.inl 0)) = - v (.inr (.inl 0)) := by simp [hV_apply, dVec]
  have hQ : Q3 F (-w) = Q3 F w := QuadraticMap.map_neg _ _
  rw [eich_apply, eich_apply, hQ, hf, polar_neg_right, polar_hV_WS _ hw]
  simp only [map_add, map_sub, map_smul, hV_WS hw, hV_eV]
  module

theorem eV_e : (eV : V3 F) (.inl 0) = 1 := by simp [eV]

theorem eV_of_ne {i : Fin 3 ⊕ Fin 3 ⊕ Unit} (h : i ≠ .inl 0) : (eV : V3 F) i = 0 := by
  simp [eV, h]

theorem fV_f : (fV : V3 F) (.inr (.inl 0)) = 1 := by simp [fV]

theorem fV_of_ne {i : Fin 3 ⊕ Fin 3 ⊕ Unit} (h : i ≠ .inr (.inl 0)) : (fV : V3 F) i = 0 := by
  simp [fV, h]

end CFSG.HardMathSupport.Lang.E6Descent.RankB3
