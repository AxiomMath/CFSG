module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TBlocks
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks
open scoped commutatorElement

section Central

variable {G : Type*} [Group G]

theorem chi_mul {g u : G} (v : G) (hu : u * g * u⁻¹ * g⁻¹ ∈ center G) :
    (v * u) * g * (v * u)⁻¹ * g⁻¹ = (u * g * u⁻¹ * g⁻¹) * (v * g * v⁻¹ * g⁻¹) := by
  set c := u * g * u⁻¹ * g⁻¹ with hc
  have hcv : v * c = c * v := (mem_center_iff.mp hu v)
  calc (v * u) * g * (v * u)⁻¹ * g⁻¹ = v * c * (g * v⁻¹ * g⁻¹) := by rw [hc]; group
    _ = c * v * (g * v⁻¹ * g⁻¹) := by rw [hcv]
    _ = c * (v * g * v⁻¹ * g⁻¹) := by group

theorem chi_inv {g u : G} (hu : u * g * u⁻¹ * g⁻¹ ∈ center G) :
    u⁻¹ * g * u⁻¹⁻¹ * g⁻¹ = (u * g * u⁻¹ * g⁻¹)⁻¹ := by
  set c := u * g * u⁻¹ * g⁻¹ with hc
  have hci : u⁻¹ * c⁻¹ = c⁻¹ * u⁻¹ := (mem_center_iff.mp (inv_mem hu) u⁻¹)
  calc u⁻¹ * g * u⁻¹⁻¹ * g⁻¹ = u⁻¹ * c⁻¹ * u := by rw [hc]; group
    _ = c⁻¹ * u⁻¹ * u := by rw [hci]
    _ = c⁻¹ := by group

theorem commutator_comm_of_central {g z w : G} (hz : z * g * z⁻¹ * g⁻¹ ∈ center G)
    (hw : w * g * w⁻¹ * g⁻¹ ∈ center G) : ⁅z, w⁆ * g = g * ⁅z, w⁆ := by
  set cz := z * g * z⁻¹ * g⁻¹ with hcz
  set cw := w * g * w⁻¹ * g⁻¹ with hcw
  have h1 := chi_inv hw
  have h2 := chi_inv hz
  have hw' : w⁻¹ * g * w⁻¹⁻¹ * g⁻¹ ∈ center G := by rw [h1]; exact inv_mem hw
  have hz' : z⁻¹ * g * z⁻¹⁻¹ * g⁻¹ ∈ center G := by rw [h2]; exact inv_mem hz
  have h3 := chi_mul z⁻¹ hw'
  have h3' : (z⁻¹ * w⁻¹) * g * (z⁻¹ * w⁻¹)⁻¹ * g⁻¹ ∈ center G := by
    rw [h3]; exact mul_mem hw' hz'
  have h4 := chi_mul w h3'
  have h4' : (w * (z⁻¹ * w⁻¹)) * g * (w * (z⁻¹ * w⁻¹))⁻¹ * g⁻¹ ∈ center G := by
    rw [h4]; exact mul_mem h3' hw
  have h5 := chi_mul z h4'
  have hone : ⁅z, w⁆ * g * ⁅z, w⁆⁻¹ * g⁻¹ = 1 := by
    have e : ⁅z, w⁆ = z * (w * (z⁻¹ * w⁻¹)) := by rw [commutatorElement_def]; group
    rw [e, h5, h4, h3, h1, h2]
    have hcomm : cz⁻¹ * cw = cw * cz⁻¹ := (mem_center_iff.mp (inv_mem hz) cw).symm
    calc cw⁻¹ * cz⁻¹ * cw * cz = cw⁻¹ * (cz⁻¹ * cw) * cz := by group
      _ = cw⁻¹ * (cw * cz⁻¹) * cz := by rw [hcomm]
      _ = 1 := by group
  calc ⁅z, w⁆ * g = (⁅z, w⁆ * g * ⁅z, w⁆⁻¹ * g⁻¹) * (g * ⁅z, w⁆) := by group
    _ = g * ⁅z, w⁆ := by rw [hone, one_mul]

theorem conj_comm_of_central {g z w : G} (hz : z * g * z⁻¹ * g⁻¹ ∈ center G)
    (hw : w * g = g * w) : (z * w * z⁻¹) * g = g * (z * w * z⁻¹) := by
  have h2 := chi_inv hz
  have hz' : z⁻¹ * g * z⁻¹⁻¹ * g⁻¹ ∈ center G := by rw [h2]; exact inv_mem hz
  set c := z⁻¹ * g * z⁻¹⁻¹ * g⁻¹ with hc
  set d := z * g * z⁻¹ * g⁻¹ with hd
  have hcd : c * d = 1 := by rw [h2, inv_mul_cancel]
  have hcm : ∀ h : G, h * c = c * h := fun h => mem_center_iff.mp hz' h
  have hzc : z⁻¹ * g * z = c * g := by rw [hc]; group
  have hdz : z * g * z⁻¹ = d * g := by rw [hd]; group
  calc (z * w * z⁻¹) * g = z * w * (z⁻¹ * g * z) * z⁻¹ := by group
    _ = z * w * (c * g) * z⁻¹ := by rw [hzc]
    _ = c * (z * (w * g) * z⁻¹) := by rw [← mul_assoc (z * w) c, hcm (z * w)]; group
    _ = c * (z * (g * w) * z⁻¹) := by rw [hw]
    _ = c * ((z * g * z⁻¹) * (z * w * z⁻¹)) := by group
    _ = c * (d * g * (z * w * z⁻¹)) := by rw [hdz]
    _ = g * (z * w * z⁻¹) := by rw [← mul_assoc c, ← mul_assoc c, hcd, one_mul]

end Central

variable (k : Type) [Field k]

@[expose] def bdL : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 4) k where
  toFun U := ⟨bd (U : Matrix (Fin 2) (Fin 2) k) 1, by rw [det_bd, U.2, det_one, one_mul]⟩
  map_one' := Subtype.ext (bd_one (F := k))
  map_mul' U V := Subtype.ext (by
    show bd ((U : Matrix (Fin 2) (Fin 2) k) * (V : Matrix (Fin 2) (Fin 2) k)) 1 =
      bd (U : Matrix (Fin 2) (Fin 2) k) 1 * bd (V : Matrix (Fin 2) (Fin 2) k) 1
    rw [bd_mul, mul_one])

@[expose] def bdR : SpecialLinearGroup (Fin 2) k →* SpecialLinearGroup (Fin 4) k where
  toFun W := ⟨bd 1 (W : Matrix (Fin 2) (Fin 2) k), by rw [det_bd, W.2, det_one, one_mul]⟩
  map_one' := Subtype.ext (bd_one (F := k))
  map_mul' U V := Subtype.ext (by
    show bd 1 ((U : Matrix (Fin 2) (Fin 2) k) * (V : Matrix (Fin 2) (Fin 2) k)) =
      bd 1 (U : Matrix (Fin 2) (Fin 2) k) * bd 1 (V : Matrix (Fin 2) (Fin 2) k)
    rw [bd_mul, mul_one])

@[expose] def factorL : Subgroup (projectiveSL 4 k) := ((proj 4 k).comp (bdL k)).range

@[expose] def factorR : Subgroup (projectiveSL 4 k) := ((proj 4 k).comp (bdR k)).range

variable {k}

theorem coe_bdL (U : SpecialLinearGroup (Fin 2) k) :
    ((bdL k U : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) =
      bd (U : Matrix (Fin 2) (Fin 2) k) 1 := rfl

theorem coe_bdR (W : SpecialLinearGroup (Fin 2) k) :
    ((bdR k W : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) =
      bd 1 (W : Matrix (Fin 2) (Fin 2) k) := rfl

theorem bdL_mul_bdR (U W : SpecialLinearGroup (Fin 2) k) :
    bdL k U * bdR k W = bdR k W * bdL k U := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_bdL, coe_bdR, bd_mul, mul_one, one_mul]

theorem proj_bdL_injective : Function.Injective ((proj 4 k).comp (bdL k)) := by
  rw [injective_iff_map_eq_one]
  intro U hU
  rw [MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hU
  obtain ⟨c, -, hc⟩ := hU
  rw [coe_bdL] at hc
  have hlr := congrArg lr hc
  have hul := congrArg ul hc
  rw [lr_bd] at hlr
  rw [ul_bd] at hul
  have h1 : (c : k) = 1 := by
    have := congrFun (congrFun hlr 0) 0
    simpa [lr, Matrix.scalar_apply, Matrix.diagonal_apply] using this.symm
  apply Subtype.ext
  rw [hul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ul, Matrix.scalar_apply, h1]

theorem proj_bdR_injective : Function.Injective ((proj 4 k).comp (bdR k)) := by
  rw [injective_iff_map_eq_one]
  intro U hU
  rw [MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hU
  obtain ⟨c, -, hc⟩ := hU
  rw [coe_bdR] at hc
  have hlr := congrArg lr hc
  have hul := congrArg ul hc
  rw [lr_bd] at hlr
  rw [ul_bd] at hul
  have h1 : (c : k) = 1 := by
    have := congrFun (congrFun hul 0) 0
    simpa [ul, Matrix.scalar_apply, Matrix.diagonal_apply] using this.symm
  apply Subtype.ext
  rw [hlr, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lr, Matrix.scalar_apply, h1]

theorem isBD_of_comm (htwo : (2 : k) ≠ 0) {g : SpecialLinearGroup (Fin 4) k} {b : k} (hb : b ≠ 0)
    (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) {Z : SpecialLinearGroup (Fin 4) k}
    (hZ : Z * g = g * Z) : IsBD (Z : Matrix (Fin 4) (Fin 4) k) := by
  have h := congrArg (fun M : SpecialLinearGroup (Fin 4) k => (M : Matrix (Fin 4) (Fin 4) k)) hZ
  simp only [Matrix.SpecialLinearGroup.coe_mul, hg] at h
  exact isBD_of_comm_X1 htwo hb h

theorem bd_ul_lr_mul {M N : Matrix (Fin 4) (Fin 4) k} (hM : IsBD M) (hN : IsBD N) :
    M * N = bd (ul M * ul N) (lr M * lr N) := by
  rw [eq_bd hM, eq_bd hN, bd_mul, ul_bd, ul_bd, lr_bd, lr_bd]

theorem ul_lr_mul_inv (htwo : (2 : k) ≠ 0) {g : SpecialLinearGroup (Fin 4) k} {b : k} (hb : b ≠ 0)
    (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) {Z : SpecialLinearGroup (Fin 4) k}
    (hZ : Z * g = g * Z) :
    ul (Z : Matrix (Fin 4) (Fin 4) k) * ul ((Z⁻¹ : SpecialLinearGroup (Fin 4) k) :
        Matrix (Fin 4) (Fin 4) k) = 1 ∧
      lr (Z : Matrix (Fin 4) (Fin 4) k) * lr ((Z⁻¹ : SpecialLinearGroup (Fin 4) k) :
        Matrix (Fin 4) (Fin 4) k) = 1 := by
  have hZi : Z⁻¹ * g = g * Z⁻¹ :=
    (Commute.inv_left (show Commute Z g from hZ)).eq
  have h1 := isBD_of_comm htwo hb hg hZ
  have h2 := isBD_of_comm htwo hb hg hZi
  have h := bd_ul_lr_mul h1 h2
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one] at h
  have hu := congrArg ul h
  have hl := congrArg lr h
  rw [ul_bd, ul_one] at hu
  rw [lr_bd] at hl
  refine ⟨hu.symm, ?_⟩
  rw [← hl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lr]

theorem comm_mem_sup (htwo : (2 : k) ≠ 0) {g : SpecialLinearGroup (Fin 4) k} {b : k}
    (hb : b ≠ 0) (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) {Z Z' : SpecialLinearGroup (Fin 4) k}
    (hZ : Z * g = g * Z) (hZ' : Z' * g = g * Z') :
    ⁅Z, Z'⁆ ∈ (bdL k).range ⊔ (bdR k).range := by
  have hZi : Z⁻¹ * g = g * Z⁻¹ :=
    (Commute.inv_left (show Commute Z g from hZ)).eq
  have hZi' : Z'⁻¹ * g = g * Z'⁻¹ :=
    (Commute.inv_left (show Commute Z' g from hZ')).eq
  have b1 := isBD_of_comm htwo hb hg hZ
  have b2 := isBD_of_comm htwo hb hg hZ'
  have b3 := isBD_of_comm htwo hb hg hZi
  have b4 := isBD_of_comm htwo hb hg hZi'
  obtain ⟨u1, l1⟩ := ul_lr_mul_inv htwo hb hg hZ
  obtain ⟨u2, l2⟩ := ul_lr_mul_inv htwo hb hg hZ'
  set M1 := (Z : Matrix (Fin 4) (Fin 4) k)
  set M2 := (Z' : Matrix (Fin 4) (Fin 4) k)
  set M3 := ((Z⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
  set M4 := ((Z'⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
  set u := ul M1 * ul M2 * ul M3 * ul M4 with hu
  set w := lr M1 * lr M2 * lr M3 * lr M4 with hw
  have hdu : u.det = 1 := by
    have e1 := congrArg Matrix.det u1
    have e2 := congrArg Matrix.det u2
    rw [det_mul, det_one] at e1 e2
    rw [hu, det_mul, det_mul, det_mul]
    linear_combination (ul M2).det * (ul M4).det * e1 + e2
  have hdw : w.det = 1 := by
    have e1 := congrArg Matrix.det l1
    have e2 := congrArg Matrix.det l2
    rw [det_mul, det_one] at e1 e2
    rw [hw, det_mul, det_mul, det_mul]
    linear_combination (lr M2).det * (lr M4).det * e1 + e2
  have hcomm : ⁅Z, Z'⁆ = bdL k ⟨u, hdu⟩ * bdR k ⟨w, hdw⟩ := by
    apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    change M1 * M2 * M3 * M4 = bd u 1 * bd 1 w
    rw [bd_mul, mul_one, one_mul]
    rw [eq_bd b1, eq_bd b2, eq_bd b3, eq_bd b4, bd_mul, bd_mul, bd_mul]
  rw [hcomm]
  exact mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩

theorem conj_bdL_mem (htwo : (2 : k) ≠ 0) {g : SpecialLinearGroup (Fin 4) k} {b : k}
    (hb : b ≠ 0) (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) {Z : SpecialLinearGroup (Fin 4) k}
    (hZ : Z * g = g * Z) (U : SpecialLinearGroup (Fin 2) k) :
    Z * bdL k U * Z⁻¹ ∈ (bdL k).range := by
  have hZi : Z⁻¹ * g = g * Z⁻¹ :=
    (Commute.inv_left (show Commute Z g from hZ)).eq
  have b1 := isBD_of_comm htwo hb hg hZ
  have b3 := isBD_of_comm htwo hb hg hZi
  obtain ⟨u1, l1⟩ := ul_lr_mul_inv htwo hb hg hZ
  set M1 := (Z : Matrix (Fin 4) (Fin 4) k)
  set M3 := ((Z⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
  set u := ul M1 * (U : Matrix (Fin 2) (Fin 2) k) * ul M3 with hu
  have hdu : u.det = 1 := by
    have e1 := congrArg Matrix.det u1
    rw [det_mul, det_one] at e1
    rw [hu, det_mul, det_mul, U.2, mul_one, e1]
  refine ⟨⟨u, hdu⟩, ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change bd u 1 = M1 * bd (U : Matrix (Fin 2) (Fin 2) k) 1 * M3
  rw [eq_bd b1, eq_bd b3, bd_mul, bd_mul, mul_one, l1]

theorem conj_bdR_mem (htwo : (2 : k) ≠ 0) {g : SpecialLinearGroup (Fin 4) k} {b : k}
    (hb : b ≠ 0) (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) {Z : SpecialLinearGroup (Fin 4) k}
    (hZ : Z * g = g * Z) (W : SpecialLinearGroup (Fin 2) k) :
    Z * bdR k W * Z⁻¹ ∈ (bdR k).range := by
  have hZi : Z⁻¹ * g = g * Z⁻¹ :=
    (Commute.inv_left (show Commute Z g from hZ)).eq
  have b1 := isBD_of_comm htwo hb hg hZ
  have b3 := isBD_of_comm htwo hb hg hZi
  obtain ⟨u1, l1⟩ := ul_lr_mul_inv htwo hb hg hZ
  set M1 := (Z : Matrix (Fin 4) (Fin 4) k)
  set M3 := ((Z⁻¹ : SpecialLinearGroup (Fin 4) k) : Matrix (Fin 4) (Fin 4) k)
  set w := lr M1 * (W : Matrix (Fin 2) (Fin 2) k) * lr M3 with hw
  have hdw : w.det = 1 := by
    have e1 := congrArg Matrix.det l1
    rw [det_mul, det_one] at e1
    rw [hw, det_mul, det_mul, W.2, mul_one, e1]
  refine ⟨⟨w, hdw⟩, ?_⟩
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change bd 1 w = M1 * bd 1 (W : Matrix (Fin 2) (Fin 2) k) * M3
  rw [eq_bd b1, eq_bd b3, bd_mul, bd_mul, mul_one, u1]

end Catalog7L4

end CFSG.ComponentClassification.GSThmB
