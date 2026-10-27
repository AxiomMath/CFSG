module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSp4

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Steinberg.Sp TauCeti.GLSymplecticFin
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem eq_top_of_elt_mem {n : ℕ} (H : Subgroup (StatedSp n F))
    (h : ∀ (r : RootSubgroupIndex n) (c : F), elt r c ∈ H) : H = ⊤ := by
  have hT : H.comap (CFSG.LieType.Universal.Symplectic.equivStatedSp n F).toMonoidHom = ⊤ :=
    eq_top_of_root_subgroups _ fun r c => h r c.toAdd
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (CFSG.LieType.Universal.Symplectic.equivStatedSp n F).surjective x
  have hy : y ∈ H.comap (CFSG.LieType.Universal.Symplectic.equivStatedSp n F).toMonoidHom := by
    rw [hT]
    exact Subgroup.mem_top y
  exact hy

theorem commute_longBlock_01 (a b : SL(2, F)) :
    Commute (longBlock F 2 0 a) (longBlock F 2 1 b) := by
  apply mat_injective
  rw [map_mul, map_mul, mat_longBlock, mat_longBlock]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]


@[expose] def upperM (S : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks 1 S 0 1

@[expose] def lowerM (S : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks 1 0 S 1

theorem mat_posLong (i : Fin 2) (c : F) :
    mat 2 F (elt (.positiveLong i) c) = upperM (c • Matrix.single i i 1) := by
  rw [mat_elt]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [E, upperM, Matrix.single_apply, Matrix.one_apply]

theorem mat_negLong (i : Fin 2) (c : F) :
    mat 2 F (elt (.negativeLong i) c) = lowerM (c • Matrix.single i i 1) := by
  rw [mat_elt]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [E, lowerM, Matrix.single_apply, Matrix.one_apply]

theorem mat_posSum (c : F) :
    mat 2 F (elt (.positiveSum 0 1 (by decide)) c) =
      upperM (c • (Matrix.single 0 1 1 + Matrix.single 1 0 1)) := by
  rw [mat_elt]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [E, upperM]

theorem mat_negSum (c : F) :
    mat 2 F (elt (.negativeSum 0 1 (by decide)) c) =
      lowerM (c • (Matrix.single 0 1 1 + Matrix.single 1 0 1)) := by
  rw [mat_elt]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [E, lowerM]

@[expose] noncomputable def phi4 (F : Type) [Field F] : SL(2, F) × SL(2, F) →* StatedSp 2 F :=
  MonoidHom.noncommCoprod (longBlock F 2 0) (longBlock F 2 1)
    (fun a b => commute_longBlock_01 a b)

theorem phi4_apply (a b : SL(2, F)) : phi4 F (a, b) = longBlock F 2 0 a * longBlock F 2 1 b := by
  simp [phi4, MonoidHom.noncommCoprod_apply]

noncomputable abbrev x0 (F : Type) [Field F] : StatedSp 2 F := longInv F 2 0

noncomputable abbrev ut (B B' : SL(2, F)) : StatedSp 2 F := phi4 F (B, B')

theorem x0_eq : x0 F = phi4 F (-1, 1) := by
  simp [phi4_apply, longInv]

theorem phi4_mem_centralizer_x0 (h : SL(2, F) × SL(2, F)) :
    phi4 F h ∈ Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, x0_eq, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp


theorem sup_centralizer_conj {G : Type*} [Group G] (g x₁ x₂ x₃ : G)
    (h : Subgroup.centralizer ({x₁} : Set G) ⊔ Subgroup.centralizer ({x₂} : Set G) ⊔
      Subgroup.centralizer ({x₃} : Set G) = ⊤) :
    Subgroup.centralizer ({g * x₁ * g⁻¹} : Set G) ⊔ Subgroup.centralizer ({g * x₂ * g⁻¹} : Set G) ⊔
      Subgroup.centralizer ({g * x₃ * g⁻¹} : Set G) = ⊤ := by
  have hle : ∀ y : G, (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
    intro y z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.mp hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
      _ = g * (y * w) * g⁻¹ := by rw [hw']
      _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group
  rw [eq_top_iff]
  intro y _
  have hy : g⁻¹ * y * g ∈ (⊤ : Subgroup G) := Subgroup.mem_top _
  rw [← h] at hy
  have hy' : y ∈ ((Subgroup.centralizer ({x₁} : Set G) ⊔ Subgroup.centralizer ({x₂} : Set G) ⊔
      Subgroup.centralizer ({x₃} : Set G)).map (MulAut.conj g).toMonoidHom) :=
    ⟨g⁻¹ * y * g, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  rw [Subgroup.map_sup, Subgroup.map_sup] at hy'
  exact (sup_le_sup (sup_le_sup (hle x₁) (hle x₂)) (hle x₃)) hy'

theorem sup_eq_top_of_conj (h h' B B' : SL(2, F))
    (key : Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({ut (h * B * h⁻¹) (h' * B' * h'⁻¹)} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x0 F * ut (h * B * h⁻¹) (h' * B' * h'⁻¹)} : Set (StatedSp 2 F)) = ⊤) :
    Subgroup.centralizer ({x0 F} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({ut B B'} : Set (StatedSp 2 F)) ⊔
      Subgroup.centralizer ({x0 F * ut B B'} : Set (StatedSp 2 F)) = ⊤ := by
  have hk := sup_centralizer_conj (phi4 F (h⁻¹, h'⁻¹)) _ _ _ key
  have e1 : phi4 F (h⁻¹, h'⁻¹) * x0 F * (phi4 F (h⁻¹, h'⁻¹))⁻¹ = x0 F := by
    have := (Subgroup.mem_centralizer_singleton_iff.mp (phi4_mem_centralizer_x0 (h⁻¹, h'⁻¹)))
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have e2 : phi4 F (h⁻¹, h'⁻¹) * ut (h * B * h⁻¹) (h' * B' * h'⁻¹) * (phi4 F (h⁻¹, h'⁻¹))⁻¹ =
      ut B B' := by
    simp only [ut, ← map_inv, ← map_mul]
    congr 1
    ext <;> simp [mul_assoc]
  have e3 : phi4 F (h⁻¹, h'⁻¹) * (x0 F * ut (h * B * h⁻¹) (h' * B' * h'⁻¹)) *
      (phi4 F (h⁻¹, h'⁻¹))⁻¹ = x0 F * ut B B' := by
    calc phi4 F (h⁻¹, h'⁻¹) * (x0 F * ut (h * B * h⁻¹) (h' * B' * h'⁻¹)) *
        (phi4 F (h⁻¹, h'⁻¹))⁻¹ =
        (phi4 F (h⁻¹, h'⁻¹) * x0 F * (phi4 F (h⁻¹, h'⁻¹))⁻¹) *
          (phi4 F (h⁻¹, h'⁻¹) * ut (h * B * h⁻¹) (h' * B' * h'⁻¹) * (phi4 F (h⁻¹, h'⁻¹))⁻¹) := by
          group
      _ = x0 F * ut B B' := by rw [e1, e2]
  rw [e1, e2, e3] at hk
  exact hk


theorem mat_ut (B B' : SL(2, F)) :
    mat 2 F (ut B B') = fromBlocks
      (Matrix.diagonal ![(B : Matrix (Fin 2) (Fin 2) F) 0 0, (B' : Matrix (Fin 2) (Fin 2) F) 0 0])
      (Matrix.diagonal ![(B : Matrix (Fin 2) (Fin 2) F) 0 1, (B' : Matrix (Fin 2) (Fin 2) F) 0 1])
      (Matrix.diagonal ![(B : Matrix (Fin 2) (Fin 2) F) 1 0, (B' : Matrix (Fin 2) (Fin 2) F) 1 0])
      (Matrix.diagonal ![(B : Matrix (Fin 2) (Fin 2) F) 1 1,
        (B' : Matrix (Fin 2) (Fin 2) F) 1 1]) := by
  rw [show ut B B' = longBlock F 2 0 B * longBlock F 2 1 B' from phi4_apply B B', map_mul,
    mat_longBlock, mat_longBlock]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [blockMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

end CFSG.ClassicalInvolution.RouteD.SCRSp4
