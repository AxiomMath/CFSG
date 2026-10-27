module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutTorus
public import CFSG.LocalAnalysis.EvenBN.U4.Model.Generation

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem miyamotoIParam_one_eq_one {β : Kˣ} (hβ : h.bar β = β) :
    miyamotoIParam h (1, β) = 1 := by
  apply Units.ext
  simp [miyamotoIParam, hβ]

theorem eq_of_miyamotoIHom_mem_N2 {p : Kˣ × Kˣ} (hp : miyamotoIHom h p ∈ miyamotoN2 h) :
    p.1 = 1 ∧ h.bar p.2 = p.2 := by
  obtain ⟨m, -, hbar, e⟩ := (mem_miyamotoN2 h).1 hp
  rw [coe_miyamotoIHom] at e
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  simp [miyamotoN2Mat] at e00 e11
  refine ⟨e00, ?_⟩
  rw [e11]
  exact hbar 0 0

theorem miyamotoWeightB_one {β : Kˣ} (hβ : h.bar β = β) : miyamotoWeightB h (1, β) = β ^ 2 := by
  apply Units.ext
  simp [hβ, sq]

theorem exists_eq_rootB_mul_of_conj_mem {n : GL (Fin 4) K} (hn : n ∈ miyamotoN2 h)
    (hu : n⁻¹ * miyamotoXGL h 0 1 0 0 * n ∈ miyamotoRootB h) :
    ∃ c : K, h.bar c = c ∧ ∃ β : Kˣ, h.bar β = β ∧
      n = miyamotoXGL h 0 c 0 0 * miyamotoIHom h (1, β) := by
  obtain ⟨m, hdet, hbar, hm⟩ := (mem_miyamotoN2 h).1 hn
  obtain ⟨b, -, hb⟩ := hu
  have e : miyamotoXGL h 0 1 0 0 * n = n * miyamotoXGL h 0 b 0 0 := by
    rw [← hb]
    group
  have e22 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 2 2) e
  simp only [Units.val_mul, hm, coe_miyamotoXGL] at e22
  simp [miyamotoN2Mat, miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at e22
  rw [Matrix.det_fin_two, e22, zero_mul, sub_zero] at hdet
  have h0 : m 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : m 1 1 = (m 0 0)⁻¹ := (inv_eq_of_mul_eq_one_right hdet).symm
  refine ⟨m 1 0 * m 1 1, by rw [map_mul, hbar, hbar], Units.mk0 _ h0, hbar 0 0, Units.ext ?_⟩
  rw [hm, Units.val_mul, coe_miyamotoXGL, coe_miyamotoIHom]
  have hb00 : h.bar (m 0 0) = m 0 0 := hbar 0 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miyamotoN2Mat, miyamotoX, Matrix.mul_diagonal, e22, h11, hb00, h0]

theorem miyamotoXGL_rootB_comm [CharP K 2] {b c : K} (hb : h.bar b = b) (hc : h.bar c = c) :
    miyamotoXGL h 0 b 0 0 * miyamotoXGL h 0 c 0 0 =
      miyamotoXGL h 0 c 0 0 * miyamotoXGL h 0 b 0 0 := by
  rw [miyamotoXGL_mul h hb, miyamotoXGL_mul h hc, miyamotoXGL_inj]
  refine ⟨rfl, add_comm b c, by simp, by simp⟩

theorem mem_rootB_of_fixes {i n : GL (Fin 4) K} (hi : i ∈ miyamotoI2 h)
    (hn : n ∈ miyamotoN2 h)
    (hfix : ∀ b : K, h.bar b = b →
      i * n * miyamotoXGL h 0 b 0 0 * (i * n)⁻¹ = miyamotoXGL h 0 b 0 0) :
    n ∈ miyamotoRootB h := by
  have : CharP K 2 := h.charP
  have key : ∀ b : K, h.bar b = b → n⁻¹ * miyamotoXGL h 0 b 0 0 * n = miyamotoXGL h 0 b 0 0 := by
    intro b hb
    have e := hfix b hb
    have hc : i * miyamotoXGL h 0 b 0 0 = miyamotoXGL h 0 b 0 0 * i :=
      miyamotoI2_commute_N2 h hi (miyamotoRootB_le_N2 h ⟨b, hb, rfl⟩)
    have e2 : n * miyamotoXGL h 0 b 0 0 * n⁻¹ = miyamotoXGL h 0 b 0 0 := by
      calc n * miyamotoXGL h 0 b 0 0 * n⁻¹ =
          i⁻¹ * (i * n * miyamotoXGL h 0 b 0 0 * (i * n)⁻¹) * i := by
            rw [show i * n * miyamotoXGL h 0 b 0 0 * (i * n)⁻¹ =
              i * (n * miyamotoXGL h 0 b 0 0 * n⁻¹) * i⁻¹ by group]
            group
        _ = i⁻¹ * (miyamotoXGL h 0 b 0 0 * i) := by rw [e, mul_assoc]
        _ = miyamotoXGL h 0 b 0 0 := by rw [← hc, inv_mul_cancel_left]
    calc n⁻¹ * miyamotoXGL h 0 b 0 0 * n =
        n⁻¹ * (n * miyamotoXGL h 0 b 0 0 * n⁻¹) * n := by rw [e2]
      _ = miyamotoXGL h 0 b 0 0 := by group
  obtain ⟨c, hc, β, hβ, rfl⟩ := exists_eq_rootB_mul_of_conj_mem h hn
    ⟨1, map_one _, key 1 (map_one _)⟩
  have e := key 1 (map_one _)
  have e2 : (miyamotoXGL h 0 c 0 0 * miyamotoIHom h (1, β))⁻¹ * miyamotoXGL h 0 1 0 0 *
      (miyamotoXGL h 0 c 0 0 * miyamotoIHom h (1, β)) =
        (miyamotoIHom h (1, β))⁻¹ * miyamotoXGL h 0 1 0 0 * miyamotoIHom h (1, β) := by
    have hcb := miyamotoXGL_rootB_comm h (map_one h.bar) hc
    calc (miyamotoXGL h 0 c 0 0 * miyamotoIHom h (1, β))⁻¹ * miyamotoXGL h 0 1 0 0 *
        (miyamotoXGL h 0 c 0 0 * miyamotoIHom h (1, β)) =
          (miyamotoIHom h (1, β))⁻¹ * (miyamotoXGL h 0 c 0 0)⁻¹ *
            (miyamotoXGL h 0 1 0 0 * miyamotoXGL h 0 c 0 0) * miyamotoIHom h (1, β) := by
          group
      _ = _ := by rw [hcb]; group
  rw [e2, miyamotoIHom_conj_rootB, miyamotoWeightB_one h hβ, miyamotoXGL_inj] at e
  have hβ1 : (β : K) = 1 := by
    have h1 : (β : K) ^ 2 = 1 := by simpa using e.2.1
    exact eq_of_sq_eq_sq (by rw [one_pow, h1])
  rw [show β = 1 from Units.ext hβ1, show ((1 : Kˣ), (1 : Kˣ)) = 1 from rfl, map_one, mul_one]
  exact ⟨c, hc, rfl⟩

theorem eq_one_of_fixes_N2 {i n : GL (Fin 4) K} (hi : i ∈ miyamotoI2 h)
    (hn : n ∈ miyamotoN2 h) (hfix : ∀ g ∈ miyamotoN2 h, i * n * g * (i * n)⁻¹ = g) :
    n = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨c, hc, rfl⟩ := mem_rootB_of_fixes h hi hn
    fun b hb => hfix _ (miyamotoRootB_le_N2 h ⟨b, hb, rfl⟩)
  set g := miyamotoN2Hom h (upperSL2 (1 : h.fixedField)) with hg
  have hgN : g ∈ miyamotoN2 h := ⟨_, rfl⟩
  have e := hfix g hgN
  have hig : i * g = g * i := miyamotoI2_commute_N2 h hi hgN
  have e2 : miyamotoXGL h 0 c 0 0 * g = g * miyamotoXGL h 0 c 0 0 := by
    calc miyamotoXGL h 0 c 0 0 * g =
        i⁻¹ * (i * miyamotoXGL h 0 c 0 0 * g * (i * miyamotoXGL h 0 c 0 0)⁻¹) *
          (i * miyamotoXGL h 0 c 0 0) := by group
      _ = i⁻¹ * g * (i * miyamotoXGL h 0 c 0 0) := by rw [e]
      _ = i⁻¹ * (g * i) * miyamotoXGL h 0 c 0 0 := by group
      _ = i⁻¹ * (i * g) * miyamotoXGL h 0 c 0 0 := by rw [hig]
      _ = g * miyamotoXGL h 0 c 0 0 := by group
  have e11 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 1 1) e2
  simp only [Units.val_mul, coe_miyamotoXGL, hg, coe_miyamotoN2Hom_upperSL2] at e11
  simp [miyamotoX, Matrix.mul_apply, Fin.sum_univ_four] at e11
  rw [e11, miyamotoXGL_zero]

end CFSG.LocalAnalysis.EvenBN.U4
