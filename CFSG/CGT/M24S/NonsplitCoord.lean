module

public import CFSG.LargeExtraspecial.DWModelMat
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.CGT.M24S

open Matrix CFSG.LargeExtraspecial.DW

abbrev tCent : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2)) :=
  Subgroup.centralizer ({CFSG.Quasithin.H13.transvection15} :
    Set (SpecialLinearGroup (Fin 5) (ZMod 2)))

namespace tCent

abbrev eZero : Fin 4 → ZMod 2 := Pi.single 0 1

@[simp] theorem eZero_zero : eZero 0 = 1 := Pi.single_eq_same _ _

@[expose] def wPart (x : ↥tCent) : Fin 4 → ZMod 2 :=
  fun i => ((x : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
    i.castSucc (Fin.last 4)

@[expose] def gPart (x : ↥tCent) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => ((x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
    Matrix (Fin 5) (Fin 5) (ZMod 2)) i.castSucc j.castSucc

theorem coe_transvection15 :
    ((CFSG.Quasithin.H13.transvection15 : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = affMat (m := 4) eZero 1 :=
  coe_cornerTransvection_eq_affMat (m := 4) (by norm_num)

theorem coe_eq_affMat (x : ↥tCent) :
    ((x : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      affMat (wPart x) (gPart x) := by
  have hdet : ((x : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)).det ≠ 0 := by
    rw [(x : SpecialLinearGroup (Fin 5) (ZMod 2)).2]
    exact one_ne_zero
  have hc : ((x : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      ((CFSG.Quasithin.H13.transvection15 : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      ((CFSG.Quasithin.H13.transvection15 : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      ((x : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
    congrArg (fun A : SpecialLinearGroup (Fin 5) (ZMod 2) => (A : Matrix (Fin 5) (Fin 5) (ZMod 2)))
      (Subgroup.mem_centralizer_singleton_iff.mp x.2)
  obtain ⟨w, g, hwg⟩ := exists_eq_affMat_of_commute (m := 4) (by norm_num) hdet hc
  have hw : wPart x = w := by
    funext i
    change ((x : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
      i.castSucc (Fin.last 4) = w i
    rw [hwg, affMat_castSucc_last]
  have hg : gPart x = g := by
    ext i j
    change ((x : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
      i.castSucc j.castSucc = g i j
    rw [hwg, affMat_castSucc_castSucc]
  rw [hw, hg, hwg]

@[expose] def affSL (w : Fin 4 → ZMod 2) (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg : g.det ≠ 0) :
    SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨affMat w g, by rw [det_affMat]; exact det_eq_one_of_ne_zero_zmod_two hg⟩

theorem affSL_mem (w : Fin 4 → ZMod 2) (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg : g.det ≠ 0)
    (hg0 : g *ᵥ eZero = eZero) : affSL w g hg ∈ tCent := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change affMat w g * _ = _ * affMat w g
  rw [coe_transvection15, affMat_mul, affMat_mul, hg0, mul_one, one_mul, one_mulVec, add_comm]

@[expose] def mk (w : Fin 4 → ZMod 2) (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg : g.det ≠ 0)
    (hg0 : g *ᵥ eZero = eZero) : ↥tCent :=
  ⟨affSL w g hg, affSL_mem w g hg hg0⟩

theorem coe_mk (w : Fin 4 → ZMod 2) (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg : g.det ≠ 0)
    (hg0 : g *ᵥ eZero = eZero) :
    (((mk w g hg hg0 : ↥tCent) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = affMat w g :=
  rfl

theorem wPart_mk (w : Fin 4 → ZMod 2) (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg : g.det ≠ 0)
    (hg0 : g *ᵥ eZero = eZero) : wPart (mk w g hg hg0) = w := by
  have h := coe_eq_affMat (mk w g hg hg0)
  rw [coe_mk] at h
  exact (affMat_injective h).1.symm

theorem gPart_mk (w : Fin 4 → ZMod 2) (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hg : g.det ≠ 0)
    (hg0 : g *ᵥ eZero = eZero) : gPart (mk w g hg hg0) = g := by
  have h := coe_eq_affMat (mk w g hg hg0)
  rw [coe_mk] at h
  exact (affMat_injective h).2.symm

theorem one_coord : wPart (1 : ↥tCent) = 0 ∧ gPart (1 : ↥tCent) = 1 := by
  have h := coe_eq_affMat 1
  have h' : (((1 : ↥tCent) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := rfl
  rw [h', ← affMat_zero_one (m := 4)] at h
  exact ⟨(affMat_injective h).1.symm, (affMat_injective h).2.symm⟩

@[simp] theorem wPart_one : wPart (1 : ↥tCent) = 0 := one_coord.1

@[simp] theorem gPart_one : gPart (1 : ↥tCent) = 1 := one_coord.2

@[expose] def transl (v : Fin 4 → ZMod 2) : ↥tCent :=
  mk v 1 (by rw [det_one]; exact one_ne_zero) (one_mulVec _)

@[simp] theorem wPart_transl (v : Fin 4 → ZMod 2) : wPart (transl v) = v := wPart_mk _ _ _ _

@[simp] theorem gPart_transl (v : Fin 4 → ZMod 2) : gPart (transl v) = 1 := gPart_mk _ _ _ _

@[expose] def levi (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hh : h.det ≠ 0)
    (hh0 : h *ᵥ eZero = eZero) : ↥tCent :=
  mk 0 h hh hh0

@[simp] theorem wPart_levi (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hh : h.det ≠ 0)
    (hh0 : h *ᵥ eZero = eZero) : wPart (levi h hh hh0) = 0 := wPart_mk _ _ _ _

@[simp] theorem gPart_levi (h : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hh : h.det ≠ 0)
    (hh0 : h *ᵥ eZero = eZero) : gPart (levi h hh hh0) = h := gPart_mk _ _ _ _

end tCent

end CFSG.CGT.M24S
