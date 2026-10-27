module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4T
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4N2

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {F : Type} [Field F]

abbrev conjPre (I : Subgroup (StatedProj (StatedSp 2 F))) (g : StatedSp 2 F) :
    Subgroup (StatedSp 2 F) :=
  (I.map (MulAut.conj (proj 2 F g)⁻¹).toMonoidHom).comap (proj 2 F)

abbrev conjB (g : StatedSp 2 F) (B : GL (Fin 2 ⊕ Fin 2) F) : GL (Fin 2 ⊕ Fin 2) F :=
  ((g : GL (Fin 2 ⊕ Fin 2) F))⁻¹ * B * (g : GL (Fin 2 ⊕ Fin 2) F)

variable {I W : Subgroup (StatedProj (StatedSp 2 F))} {g : StatedSp 2 F}

theorem proj_conj_mem {x : StatedSp 2 F} (hx : x ∈ conjPre I g) :
    proj 2 F (g * x * g⁻¹) ∈ I := by
  obtain ⟨y, hy, hyx⟩ := hx
  have e : proj 2 F (g * x * g⁻¹) = y := by
    rw [map_mul, map_mul, map_inv, ← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [e]
  exact hy

theorem map_conjPre : (conjPre I g).map (proj 2 F) =
    I.map (MulAut.conj (proj 2 F g)⁻¹).toMonoidHom :=
  Subgroup.map_comap_eq_self_of_surjective proj_surjective _

theorem conjB_mul (B C : GL (Fin 2 ⊕ Fin 2) F) : conjB g B * conjB g C = conjB g (B * C) := by
  simp only [conjB]
  group

theorem conjB_sq {B : GL (Fin 2 ⊕ Fin 2) F} {l : F}
    (h : (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * B = l • 1) :
    (conjB g B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * conjB g B = l • 1 := by
  rw [← Units.val_mul, conjB_mul, conjB, Units.val_mul, Units.val_mul, Units.val_mul, h,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one]

theorem conjB_ne {B : GL (Fin 2 ⊕ Fin 2) F}
    (h : ∀ l : F, (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1) (l : F) :
    (conjB g B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) ≠ l • 1 := by
  intro hl
  apply h l
  have e : B = (g : GL (Fin 2 ⊕ Fin 2) F) * conjB g B * ((g : GL (Fin 2 ⊕ Fin 2) F))⁻¹ := by
    simp only [conjB]
    group
  rw [e, Units.val_mul, Units.val_mul, hl, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conjB_gsp (A : gsp 2 F) : ∃ μ : F, (conjB g (A : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * jJ * (conjB g (A : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = μ • jJ := by
  obtain ⟨μ, hμ⟩ := mem_gsp.mp (mul_mem (mul_mem (inv_mem (statedSp_le_gsp g.2)) A.2)
    (statedSp_le_gsp g.2))
  exact ⟨μ, hμ⟩

theorem conjB_central {A s : GL (Fin 2 ⊕ Fin 2) F} (hs : s ∈ center (GL (Fin 2 ⊕ Fin 2) F))
    {x : StatedSp 2 F}
    (h : A * ((g * x * g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * A⁻¹ =
      s * ((g * x * g⁻¹ : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)) :
    conjB g A * ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * (conjB g A)⁻¹ =
      s * ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
  have hc := Subgroup.mem_center_iff.mp hs
  simp only [conjB]
  set G := ((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) with hG
  set X := ((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) with hX
  calc G⁻¹ * A * G * X * (G⁻¹ * A * G)⁻¹ = G⁻¹ * (A * (G * X * G⁻¹) * A⁻¹) * G := by
        group
    _ = (G⁻¹ * s) * (G * X * G⁻¹) * G := by rw [h]; group
    _ = (s * G⁻¹) * (G * X * G⁻¹) * G := by rw [hc]
    _ = s * X := by group

variable [Finite F]

theorem conjPre_flag {N : Submodule F (Fin 2 ⊕ Fin 2 → F)} {d : ℕ}
    (hIW : I ≤ normalizer (W : Set (StatedProj (StatedSp 2 F))))
    (hN : ∀ A : GL (Fin 2 ⊕ Fin 2) F,
      A ∈ normalizer ((preGL W : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Set (GL (Fin 2 ⊕ Fin 2) F)) →
        ∀ v ∈ N, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ N)
    (hg : (flag 2 F d).map (spAct g) = N) {x : StatedSp 2 F} (hx : x ∈ conjPre I g) :
    ∀ v ∈ flag 2 F d, (((x : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v ∈ flag 2 F d := by
  have hy := proj_conj_mem hx
  refine mulVec_mem_flag_of_conj hg (hN _ (mem_normalizer_preGL_of_proj fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hIW hy) w).mp hw)) ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
