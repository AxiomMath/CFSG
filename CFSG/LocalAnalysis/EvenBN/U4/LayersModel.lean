module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutTorusOne
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Generation

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem miyamotoIParam_inv_eq_one (α : Kˣ) : miyamotoIParam h (α, α⁻¹) = 1 := by
  simp [miyamotoIParam]

theorem miyamotoIHom_inv_mem_N1 (α : Kˣ) : miyamotoIHom h (α, α⁻¹) ∈ miyamotoN1 h := by
  rw [mem_miyamotoN1]
  refine ⟨!![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two], ?_⟩
  rw [coe_miyamotoIHom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [miyamotoN1Mat, map_inv₀]

theorem eq_inv_of_miyamotoIHom_mem_N1 {p : Kˣ × Kˣ} (hp : miyamotoIHom h p ∈ miyamotoN1 h) :
    p.2 = p.1⁻¹ := by
  obtain ⟨m, hm, e⟩ := (mem_miyamotoN1 h).1 hp
  rw [coe_miyamotoIHom] at e
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e11 := congrFun (congrFun e 1) 1
  simp [miyamotoN1Mat] at e00 e01 e11
  rw [Matrix.det_fin_two, ← e00, ← e11, ← e01, zero_mul, sub_zero] at hm
  exact eq_inv_of_mul_eq_one_right (Units.ext (by simpa using hm))

theorem miyamotoWeightA_inv (α : Kˣ) : miyamotoWeightA (α, α⁻¹) = α ^ 2 := by
  simp [miyamotoWeightA, sq]

theorem miyamotoN1Hom_eq_rootA_mul (m : SpecialLinearGroup (Fin 2) K)
    (hm : (m : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) :
    ∃ α : Kˣ, miyamotoN1Hom h m = miyamotoXGL h ((m : Matrix (Fin 2) (Fin 2) K) 1 0 *
      (m : Matrix (Fin 2) (Fin 2) K) 1 1) 0 0 0 * miyamotoIHom h (α, α⁻¹) := by
  have hdet := m.2
  rw [Matrix.det_fin_two, hm, zero_mul, sub_zero] at hdet
  have h0 : (m : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : (m : Matrix (Fin 2) (Fin 2) K) 1 1 = ((m : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hdet).symm
  refine ⟨Units.mk0 _ h0, Units.ext ?_⟩
  rw [coe_miyamotoN1Hom, Units.val_mul, coe_miyamotoXGL, coe_miyamotoIHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoN1Mat, miyamotoX, Matrix.mul_diagonal, hm, h11, map_inv₀, h0]

theorem exists_eq_rootA_mul_of_conj_mem {n : GL (Fin 4) K} (hn : n ∈ miyamotoN1 h)
    (hu : n⁻¹ * miyamotoXGL h 1 0 0 0 * n ∈ miyamotoRootA h) :
    ∃ c : K, ∃ α : Kˣ, n = miyamotoXGL h c 0 0 0 * miyamotoIHom h (α, α⁻¹) := by
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨a, ha⟩ := hu
  have e : miyamotoXGL h 1 0 0 0 * miyamotoN1Hom h m =
      miyamotoN1Hom h m * miyamotoXGL h a 0 0 0 := by
    rw [← ha]
    change _ = miyamotoN1Hom h m * ((miyamotoN1Hom h m)⁻¹ * miyamotoXGL h 1 0 0 0 *
      miyamotoN1Hom h m)
    group
  have e11 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 1 1) e
  simp only [Units.val_mul, coe_miyamotoN1Hom, coe_miyamotoXGL] at e11
  simp [miyamotoN1Mat, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at e11
  obtain ⟨α, hα⟩ := miyamotoN1Hom_eq_rootA_mul h m e11
  exact ⟨_, α, hα⟩

theorem miyamotoXGL_rootA_comm [CharP K 2] (a c : K) :
    miyamotoXGL h a 0 0 0 * miyamotoXGL h c 0 0 0 =
      miyamotoXGL h c 0 0 0 * miyamotoXGL h a 0 0 0 := by
  rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
  refine ⟨add_comm a c, rfl, by simp, by simp⟩

theorem eq_refl_and_mem_rootA_of_fixes {i n : GL (Fin 4) K} (hi : i ∈ miyamotoI1 h)
    (hn : n ∈ miyamotoN1 h) {φ : K ≃+* K}
    (hfix : ∀ a : K,
      i * n * glAut φ (miyamotoXGL h a 0 0 0) * (i * n)⁻¹ = miyamotoXGL h a 0 0 0) :
    φ = RingEquiv.refl K ∧ n ∈ miyamotoRootA h := by
  have : CharP K 2 := h.charP
  have key : ∀ a : K, n⁻¹ * miyamotoXGL h a 0 0 0 * n = miyamotoXGL h (φ a) 0 0 0 := by
    intro a
    have e := hfix a
    rw [glAut_miyamotoXGL, map_zero] at e
    have hc : i * miyamotoXGL h a 0 0 0 = miyamotoXGL h a 0 0 0 * i :=
      miyamotoI1_commute_N1 h hi (miyamotoRootA_le_N1 h ⟨a, rfl⟩)
    have e2 : n * miyamotoXGL h (φ a) 0 0 0 * n⁻¹ = miyamotoXGL h a 0 0 0 := by
      calc n * miyamotoXGL h (φ a) 0 0 0 * n⁻¹ =
          i⁻¹ * (i * n * miyamotoXGL h (φ a) 0 0 0 * (i * n)⁻¹) * i := by group
        _ = i⁻¹ * (miyamotoXGL h a 0 0 0 * i) := by rw [e, mul_assoc]
        _ = miyamotoXGL h a 0 0 0 := by rw [← hc, inv_mul_cancel_left]
    calc n⁻¹ * miyamotoXGL h a 0 0 0 * n =
        n⁻¹ * (n * miyamotoXGL h (φ a) 0 0 0 * n⁻¹) * n := by rw [e2]
      _ = miyamotoXGL h (φ a) 0 0 0 := by group
  obtain ⟨c, α, rfl⟩ := exists_eq_rootA_mul_of_conj_mem h hn ⟨φ 1, key 1⟩
  have key2 : ∀ a : K, φ a = (α : K) ^ 2 * a := by
    intro a
    have e := key a
    have e2 : (miyamotoXGL h c 0 0 0 * miyamotoIHom h (α, α⁻¹))⁻¹ * miyamotoXGL h a 0 0 0 *
        (miyamotoXGL h c 0 0 0 * miyamotoIHom h (α, α⁻¹)) =
          (miyamotoIHom h (α, α⁻¹))⁻¹ * miyamotoXGL h a 0 0 0 * miyamotoIHom h (α, α⁻¹) := by
      have hca := miyamotoXGL_rootA_comm h a c
      calc (miyamotoXGL h c 0 0 0 * miyamotoIHom h (α, α⁻¹))⁻¹ * miyamotoXGL h a 0 0 0 *
          (miyamotoXGL h c 0 0 0 * miyamotoIHom h (α, α⁻¹)) =
            (miyamotoIHom h (α, α⁻¹))⁻¹ * (miyamotoXGL h c 0 0 0)⁻¹ *
              (miyamotoXGL h a 0 0 0 * miyamotoXGL h c 0 0 0) * miyamotoIHom h (α, α⁻¹) := by
            group
        _ = _ := by rw [hca]; group
    rw [e2, miyamotoIHom_conj_rootA, miyamotoWeightA_inv, miyamotoXGL_inj] at e
    rw [← e.1]
    simp
  have hα : (α : K) = 1 := by
    have := key2 1
    rw [map_one, mul_one] at this
    exact eq_of_sq_eq_sq (by rw [one_pow, this])
  have hα1 : α = 1 := Units.ext hα
  refine ⟨RingEquiv.ext fun a => by rw [key2, hα, one_pow, one_mul]; rfl, ?_⟩
  rw [hα1, inv_one, show ((1 : Kˣ), (1 : Kˣ)) = 1 from rfl, map_one, mul_one]
  exact ⟨c, rfl⟩

theorem glAut_refl (g : GL (Fin 4) K) : glAut (RingEquiv.refl K) g = g := by
  change glAut 1 g = g
  rw [map_one]
  rfl

theorem eq_refl_and_eq_one_of_fixes_N1 {i n : GL (Fin 4) K} (hi : i ∈ miyamotoI1 h)
    (hn : n ∈ miyamotoN1 h) {φ : K ≃+* K}
    (hfix : ∀ g ∈ miyamotoN1 h, i * n * glAut φ g * (i * n)⁻¹ = g) :
    φ = RingEquiv.refl K ∧ n = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨hφ, c, rfl⟩ := eq_refl_and_mem_rootA_of_fixes h hi hn
    fun a => hfix _ (miyamotoRootA_le_N1 h ⟨a, rfl⟩)
  refine ⟨hφ, ?_⟩
  set g := miyamotoN1Hom h (upperSL2 (1 : K)) with hg
  have hgN : g ∈ miyamotoN1 h := ⟨_, rfl⟩
  have e := hfix g hgN
  rw [hφ, glAut_refl] at e
  have hig : i * g = g * i := miyamotoI1_commute_N1 h hi hgN
  have e2 : miyamotoXGL h c 0 0 0 * g = g * miyamotoXGL h c 0 0 0 := by
    calc miyamotoXGL h c 0 0 0 * g =
        i⁻¹ * (i * miyamotoXGL h c 0 0 0 * g * (i * miyamotoXGL h c 0 0 0)⁻¹) *
          (i * miyamotoXGL h c 0 0 0) := by group
      _ = i⁻¹ * g * (i * miyamotoXGL h c 0 0 0) := by rw [e]
      _ = i⁻¹ * (g * i) * miyamotoXGL h c 0 0 0 := by group
      _ = i⁻¹ * (i * g) * miyamotoXGL h c 0 0 0 := by rw [hig]
      _ = g * miyamotoXGL h c 0 0 0 := by group
  have e00 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) e2
  simp only [Units.val_mul, coe_miyamotoXGL, hg, coe_miyamotoN1Hom_upperSL2] at e00
  simp [miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at e00
  rw [e00, miyamotoXGL_zero]

theorem conj_glAut_mem_N1 {i n : GL (Fin 4) K} (hi : i ∈ miyamotoI1 h) (hn : n ∈ miyamotoN1 h)
    (φ : K ≃+* K) {g : GL (Fin 4) K} (hg : g ∈ miyamotoN1 h) :
    i * n * glAut φ g * (i * n)⁻¹ ∈ miyamotoN1 h := by
  have hg' : n * glAut φ g * n⁻¹ ∈ miyamotoN1 h :=
    mul_mem (mul_mem hn (glAut_mem_miyamotoN1 h φ hg)) (inv_mem hn)
  have hc : i * (n * glAut φ g * n⁻¹) = (n * glAut φ g * n⁻¹) * i :=
    miyamotoI1_commute_N1 h hi hg'
  have e : i * n * glAut φ g * (i * n)⁻¹ = n * glAut φ g * n⁻¹ := by
    calc i * n * glAut φ g * (i * n)⁻¹ = i * (n * glAut φ g * n⁻¹) * i⁻¹ := by group
      _ = n * glAut φ g * n⁻¹ := by rw [hc, mul_inv_cancel_right]
  rw [e]
  exact hg'

end CFSG.LocalAnalysis.EvenBN.U4
