module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineAutomorphismMaps
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] (J : HermitianForm 3 K)

@[expose] def pglAut (θ : MulAut (GL (Fin 3) K)) : MulAut (ProjGenLinGroup (Fin 3) K) :=
  QuotientGroup.congr (Subgroup.center (GL (Fin 3) K)) (Subgroup.center (GL (Fin 3) K)) θ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance θ)

omit J in
theorem pglAut_mk (θ : MulAut (GL (Fin 3) K)) (g : GL (Fin 3) K) :
    pglAut θ (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk (θ g) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem map_pglAut (θ : MulAut (GL (Fin 3) K))
    (hθ : J.specialSubgroup.map θ.toMonoidHom = J.specialSubgroup) :
    (ProjectiveSpecialUnitaryMatrixGroup J).map (pglAut θ).toMonoidHom =
      ProjectiveSpecialUnitaryMatrixGroup J := by
  change (J.specialSubgroup.map ProjGenLinGroup.mk).map _ = J.specialSubgroup.map _
  conv_rhs => rw [← hθ]
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

@[expose] def psuAut (θ : MulAut (GL (Fin 3) K))
    (hθ : J.specialSubgroup.map θ.toMonoidHom = J.specialSubgroup) :
    MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  restrictMulAut (pglAut θ) _ (map_pglAut J θ hθ)

theorem coe_psuAut_mk (θ : MulAut (GL (Fin 3) K))
    (hθ : J.specialSubgroup.map θ.toMonoidHom = J.specialSubgroup) {g : GL (Fin 3) K}
    (hg : g ∈ J.specialSubgroup) :
    ((psuAut J θ hθ ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ :
      ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (θ g) :=
  pglAut_mk θ g

theorem mulAut_ext_mk {γ₁ γ₂ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (h : ∀ (g : GL (Fin 3) K) (hg : g ∈ J.specialSubgroup),
      (γ₁ ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ :
          ProjGenLinGroup (Fin 3) K) =
        γ₂ ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩) : γ₁ = γ₂ := by
  ext ⟨x, g, hg, rfl⟩
  exact h g hg

theorem psuAut_mul (θ₁ θ₂ : MulAut (GL (Fin 3) K))
    (h₁ : J.specialSubgroup.map θ₁.toMonoidHom = J.specialSubgroup)
    (h₂ : J.specialSubgroup.map θ₂.toMonoidHom = J.specialSubgroup)
    (h₁₂ : J.specialSubgroup.map (θ₁ * θ₂).toMonoidHom = J.specialSubgroup) :
    psuAut J (θ₁ * θ₂) h₁₂ = psuAut J θ₁ h₁ * psuAut J θ₂ h₂ := by
  refine mulAut_ext_mk J fun g hg => ?_
  have hg' : θ₂ g ∈ J.specialSubgroup := by
    rw [← h₂]
    exact Subgroup.mem_map_of_mem _ hg
  have h := coe_psuAut_mk J θ₂ h₂ hg
  have e : psuAut J θ₂ h₂ ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ =
      ⟨ProjGenLinGroup.mk (θ₂ g), Subgroup.mem_map_of_mem _ hg'⟩ := Subtype.ext h
  rw [coe_psuAut_mk J _ h₁₂ hg, MulAut.mul_apply, MulAut.mul_apply, e,
    coe_psuAut_mk J _ h₁ hg']

theorem psuAut_one (h : J.specialSubgroup.map (1 : MulAut (GL (Fin 3) K)).toMonoidHom =
    J.specialSubgroup) : psuAut J 1 h = 1 :=
  mulAut_ext_mk J fun g hg => by
    rw [coe_psuAut_mk J 1 h hg, MulAut.one_apply, MulAut.one_apply]

variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

theorem map_conj_unitary {A : GL (Fin 3) K} (hA : A ∈ J.unitarySubgroup) :
    J.specialSubgroup.map (MulAut.conj A).toMonoidHom = J.specialSubgroup := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    simpa [mul_assoc] using conj_mem_specialSubgroup hA h
  · intro h
    simpa using conj_mem_specialSubgroup (J.unitarySubgroup.inv_mem hA) h

include hJ in
theorem map_conj_diag3 (c : normOne J) :
    J.specialSubgroup.map (MulAut.conj (diag3 1 (c : Kˣ) 1)).toMonoidHom = J.specialSubgroup :=
  map_conj_unitary J (diag3_one_mem_unitary hJ c.2)

theorem glAut_conj_glAut_conj (g : GL (Fin 3) K) : glAut J.conj (glAut J.conj g) = g := by
  rw [← MulAut.mul_apply, ← map_mul, ← pow_two, conj_sq, map_one, MulAut.one_apply]

include hJ in
theorem map_glAut_conj :
    J.specialSubgroup.map (glAut J.conj : MulAut (GL (Fin 3) K)).toMonoidHom =
      J.specialSubgroup := by
  have hle : J.specialSubgroup.map (glAut J.conj : MulAut (GL (Fin 3) K)).toMonoidHom ≤
      J.specialSubgroup := by
    rintro _ ⟨g, hg, rfl⟩
    exact glAut_mem_specialSubgroup hJ (fun _ => rfl) hg
  refine le_antisymm hle fun g hg => ⟨glAut J.conj g, hle ⟨g, hg, rfl⟩, ?_⟩
  exact glAut_conj_glAut_conj J g

@[expose] def diagAut (c : normOne J) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  psuAut J (MulAut.conj (diag3 1 (c : Kˣ) 1)) (map_conj_diag3 J hJ c)

@[expose] def barAut : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  psuAut J (glAut J.conj) (map_glAut_conj J hJ)

@[expose] def diagHom : normOne J →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) where
  toFun := diagAut J hJ
  map_one' := by
    rw [diagAut]
    simp only [OneMemClass.coe_one, diag3_one, map_one]
    exact psuAut_one J _
  map_mul' c d := by
    change psuAut J _ _ = psuAut J _ _ * psuAut J _ _
    rw [← psuAut_mul J _ _ (map_conj_diag3 J hJ c) (map_conj_diag3 J hJ d)
      (by rw [← map_mul, ← diag3_one_mul]; exact map_conj_diag3 J hJ (c * d))]
    congr 1
    rw [← map_mul, ← diag3_one_mul]
    rfl

theorem diagHom_apply (c : normOne J) : diagHom J hJ c = diagAut J hJ c :=
  rfl

theorem barAut_mul_self : barAut J hJ * barAut J hJ = 1 := by
  rw [barAut, ← psuAut_mul J _ _ (map_glAut_conj J hJ) (map_glAut_conj J hJ)
    (by rw [← map_mul, ← pow_two, conj_sq, map_one]; exact Subgroup.map_id _)]
  have h : (glAut J.conj : MulAut (GL (Fin 3) K)) * glAut J.conj = 1 := by
    rw [← map_mul, ← pow_two, conj_sq, map_one]
  simp only [h]
  exact psuAut_one J _

theorem barAut_conj_diagAut (c : normOne J) :
    barAut J hJ * diagAut J hJ c * (barAut J hJ)⁻¹ = diagAut J hJ c⁻¹ := by
  have hτ : (barAut J hJ)⁻¹ = barAut J hJ := inv_eq_of_mul_eq_one_right (barAut_mul_self J hJ)
  rw [hτ]
  refine mulAut_ext_mk J fun g hg => ?_
  have hg₁ : glAut J.conj g ∈ J.specialSubgroup := by
    rw [← map_glAut_conj J hJ]
    exact Subgroup.mem_map_of_mem _ hg
  have hg₂ : MulAut.conj (diag3 1 (c : Kˣ) 1) (glAut J.conj g) ∈ J.specialSubgroup := by
    rw [← map_conj_diag3 J hJ c]
    exact Subgroup.mem_map_of_mem _ hg₁
  have e₁ : barAut J hJ ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ =
      ⟨ProjGenLinGroup.mk (glAut J.conj g), Subgroup.mem_map_of_mem _ hg₁⟩ :=
    Subtype.ext (coe_psuAut_mk J _ _ hg)
  have e₂ : diagAut J hJ c ⟨ProjGenLinGroup.mk (glAut J.conj g), Subgroup.mem_map_of_mem _ hg₁⟩ =
      ⟨ProjGenLinGroup.mk (MulAut.conj (diag3 1 (c : Kˣ) 1) (glAut J.conj g)),
        Subgroup.mem_map_of_mem _ hg₂⟩ :=
    Subtype.ext (coe_psuAut_mk J _ _ hg₁)
  rw [MulAut.mul_apply, MulAut.mul_apply, e₁, e₂]
  change ((psuAut J (glAut J.conj) (map_glAut_conj J hJ) _ :
    ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
      ((psuAut J _ (map_conj_diag3 J hJ c⁻¹) _ : ProjectiveSpecialUnitaryMatrixGroup J) :
        ProjGenLinGroup (Fin 3) K)
  rw [coe_psuAut_mk J _ _ hg₂, coe_psuAut_mk J _ _ hg]
  congr 1
  have hc : Units.mapEquiv J.conj.toMulEquiv (c : Kˣ) = ((c⁻¹ : normOne J) : Kˣ) := by
    apply Units.ext
    rw [InvMemClass.coe_inv, Units.val_inv_eq_inv_val]
    exact conj_eq_inv_of_mem_normOne J c.2
  simp only [MulAut.conj_apply, map_mul, map_inv, glAut_diag3_one, glAut_conj_glAut_conj, hc]

@[expose] def diagCoord (c : normOne J) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentCoord J :=
  ⟨(z.1.1 * J.conj ((c : Kˣ) : K), z.1.2), by
    have hc : ((c : Kˣ) : K) * J.conj ((c : Kˣ) : K) = 1 := c.2
    have hz := z.2
    dsimp only
    rw [map_mul, J.conj_involutive]
    linear_combination hz + z.1.1 * J.conj z.1.1 * hc⟩

omit hJ in
@[simp] theorem fst_diagCoord (c : normOne J) (z : hermitianUnipotentCoord J) :
    (diagCoord J c z).1.1 = z.1.1 * J.conj ((c : Kˣ) : K) :=
  rfl

omit hJ in
@[simp] theorem snd_diagCoord (c : normOne J) (z : hermitianUnipotentCoord J) :
    (diagCoord J c z).1.2 = z.1.2 :=
  rfl

include hJ in
theorem hermitianUnipotentGL_mem (z : hermitianUnipotentCoord J) :
    hermitianUnipotentGL J z ∈ J.specialSubgroup :=
  (hermitianUnipotentSU J hJ z).2

theorem hermitianUnipotentPSU_eq_mk (z : hermitianUnipotentCoord J) :
    hermitianUnipotentPSU J hJ z = ⟨ProjGenLinGroup.mk (hermitianUnipotentGL J z),
      Subgroup.mem_map_of_mem _ (hermitianUnipotentGL_mem J hJ z)⟩ :=
  Subtype.ext (hermitianUnipotentPSU_val J hJ z)

theorem diagAut_hermitianUnipotentPSU (c : normOne J) (z : hermitianUnipotentCoord J) :
    diagAut J hJ c (hermitianUnipotentPSU J hJ z) =
      hermitianUnipotentPSU J hJ (diagCoord J c z) := by
  apply Subtype.ext
  rw [hermitianUnipotentPSU_eq_mk J hJ z, diagAut,
    coe_psuAut_mk J _ _ (hermitianUnipotentGL_mem J hJ z), hermitianUnipotentPSU_val]
  congr 1
  apply Units.ext
  have hc := conj_eq_inv_of_mem_normOne J c.2
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, coe_diag3, coe_diag3_inv,
    hermitianUnipotentGL_val, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq,
    hermitianUnipotentMatrix_eq, fst_diagCoord, snd_diagCoord, hc]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, map_inv₀, hc, mul_comm]

theorem barAut_hermitianUnipotentPSU (z : hermitianUnipotentCoord J) :
    barAut J hJ (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ (rootTau J z) := by
  apply Subtype.ext
  rw [hermitianUnipotentPSU_eq_mk J hJ z, barAut,
    coe_psuAut_mk J _ _ (hermitianUnipotentGL_mem J hJ z), hermitianUnipotentPSU_val]
  congr 1
  apply Units.ext
  have hinv : ∀ x, J.conj (J.conj x) = x := J.conj_involutive
  rw [coe_glAut, hermitianUnipotentGL_val, hermitianUnipotentGL_val,
    hermitianUnipotentMatrix_eq, hermitianUnipotentMatrix_eq, fst_rootTau, snd_rootTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hinv]

end CFSG.ProperTwoGeneratedCore.RootCenter
