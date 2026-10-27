module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Torus

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem miyamotoP_one_zero_mul {g g' : GL (Fin 4) K} (hg : g ∈ miyamotoP h)
    (hg' : g' ∈ miyamotoP h) :
    ((g * g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 =
      (g : Matrix (Fin 4) (Fin 4) K) 1 0 + (g' : Matrix (Fin 4) (Fin 4) K) 1 0 := by
  obtain ⟨a, b, c, d, hb, -, rfl⟩ := (mem_P h).1 hg
  obtain ⟨a', b', c', d', -, -, rfl⟩ := (mem_P h).1 hg'
  rw [miyamotoXGL_mul h hb]
  simp

theorem mem_miyamotoA1_iff_one_zero {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    g ∈ miyamotoA1 h ↔ (g : Matrix (Fin 4) (Fin 4) K) 1 0 = 0 := by
  obtain ⟨a, b, c, d, hb, hd, rfl⟩ := (mem_P h).1 hg
  rw [miyamotoXGL_mem_A1, coe_miyamotoXGL, miyamotoX_one_zero]
  constructor
  · exact fun e => e.1
  · intro ha
    subst ha
    refine ⟨rfl, hb, (add_bar_eq_zero_iff h).1 ?_⟩
    simpa using hd

theorem miyamotoP_one_zero_inv {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 = (g : Matrix (Fin 4) (Fin 4) K) 1 0 := by
  have h1 := miyamotoP_one_zero_mul h (inv_mem hg) hg
  rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (by decide)] at h1
  have h2 : ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 =
      ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 +
        (((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 +
          (g : Matrix (Fin 4) (Fin 4) K) 1 0) := by
    rw [← h1, add_zero]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h2
  exact h2

omit [CharP K 2] in
theorem miyamotoIHom_conj_one_zero (p : Kˣ × Kˣ) {g : GL (Fin 4) K} (hg : g ∈ miyamotoP h) :
    (((miyamotoIHom h p)⁻¹ * g * miyamotoIHom h p : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) 1 0 =
      (p.1 : K) * (p.2 : K)⁻¹ * (g : Matrix (Fin 4) (Fin 4) K) 1 0 := by
  obtain ⟨a, b, c, d, -, -, rfl⟩ := (mem_P h).1 hg
  rw [miyamotoIHom_conj]
  simp

theorem exists_miyamotoI_conj_mul_inv_mem_A1 {g g' : GL (Fin 4) K} (hg : g ∈ miyamotoP h)
    (hgA : g ∉ miyamotoA1 h) (hg' : g' ∈ miyamotoP h) (hg'A : g' ∉ miyamotoA1 h) :
    ∃ D ∈ miyamotoI h, D⁻¹ * g * D * g'⁻¹ ∈ miyamotoA1 h := by
  have ha : (g : Matrix (Fin 4) (Fin 4) K) 1 0 ≠ 0 := fun e =>
    hgA ((mem_miyamotoA1_iff_one_zero h hg).2 e)
  have ha' : (g' : Matrix (Fin 4) (Fin 4) K) 1 0 ≠ 0 := fun e =>
    hg'A ((mem_miyamotoA1_iff_one_zero h hg').2 e)
  obtain ⟨p, hp, -, hpA⟩ := exists_miyamotoIParam_eq_one_weightB_eq_one h
    (Units.mk0 ((g' : Matrix (Fin 4) (Fin 4) K) 1 0 / (g : Matrix (Fin 4) (Fin 4) K) 1 0)
      (div_ne_zero ha' ha))
  have hD : miyamotoIHom h p ∈ miyamotoI h := (miyamotoIHom_mem_miyamotoI_iff h p).2 hp
  have hDN := miyamotoI_le_normalizer_unipotent h false false hD
  have hconjP : (miyamotoIHom h p)⁻¹ * g * miyamotoIHom h p ∈ miyamotoP h := by
    have := (mem_normalizer_iff.1 (inv_mem hDN) g).1 hg
    rwa [inv_inv] at this
  refine ⟨miyamotoIHom h p, hD, ?_⟩
  refine (mem_miyamotoA1_iff_one_zero h (mul_mem hconjP (inv_mem hg'))).2 ?_
  rw [miyamotoP_one_zero_mul h hconjP (inv_mem hg'), miyamotoP_one_zero_inv h hg',
    miyamotoIHom_conj_one_zero h p hg]
  have hw : (p.1 : K) * (p.2 : K)⁻¹ =
      (g' : Matrix (Fin 4) (Fin 4) K) 1 0 / (g : Matrix (Fin 4) (Fin 4) K) 1 0 := by
    have := congrArg Units.val hpA
    rwa [coe_miyamotoWeightA, Units.val_mk0] at this
  rw [hw, div_mul_cancel₀ _ ha, CharTwo.add_self_eq_zero]

theorem miyamotoIHom_conj_mul_inv_mem_Z2 (p : Kˣ × Kˣ) (hp : miyamotoWeightB h p = 1)
    {g : GL (Fin 4) K} (hg : g ∈ miyamotoA1 h) :
    (miyamotoIHom h p)⁻¹ * g * miyamotoIHom h p * g⁻¹ ∈ miyamotoZ2 h := by
  have hbb := h.bar_bar
  obtain ⟨b, c, d, hb, hd, rfl⟩ := (mem_A1 h).1 hg
  have hB : (p.2 : K) * h.bar p.2 = 1 := by
    have := congrArg Units.val hp
    rwa [coe_miyamotoWeightB, Units.val_one] at this
  rw [miyamotoIHom_conj, mul_zero, hB, one_mul, miyamotoXGL_inv h hb, miyamotoXGL_mul h hb,
    miyamotoXGL_mem_Z2]
  refine ⟨by ring, CharTwo.add_self_eq_zero b, ?_⟩
  simp only [map_add, map_mul, map_zero, hbb, hd, zero_mul, mul_zero, add_zero]
  ring

theorem miyamotoIHom_conj_mul_inv_mem_Z (p : Kˣ × Kˣ) (hp : miyamotoWeightC h p = 1)
    {g : GL (Fin 4) K} (hg : g ∈ miyamotoZ2 h) :
    (miyamotoIHom h p)⁻¹ * g * miyamotoIHom h p * g⁻¹ ∈ miyamotoZ h := by
  have hbb := h.bar_bar
  obtain ⟨c, d, hd, rfl⟩ := (mem_Z2 h).1 hg
  have hC : (p.1 : K) * h.bar p.2 = 1 := by
    have := congrArg Units.val hp
    rwa [coe_miyamotoWeightC, Units.val_one] at this
  rw [miyamotoIHom_conj, mul_zero, mul_zero, hC, one_mul, miyamotoXGL_inv h (map_zero _),
    miyamotoXGL_mul h (map_zero _), miyamotoXGL_mem_Z]
  refine ⟨by ring, by ring, ?_, ?_⟩
  · simp only [mul_zero, add_zero]
    exact CharTwo.add_self_eq_zero c
  · simp only [mul_zero, zero_mul, map_zero, add_zero, map_add, map_mul, hbb, hd]
    ring

end CFSG.LocalAnalysis.EvenBN.U4
