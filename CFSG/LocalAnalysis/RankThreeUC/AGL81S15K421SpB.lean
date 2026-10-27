module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpBd
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpBase
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpTorus
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CGProof K421BaseProof

section TallFacts

variable {F : Type} [Field F] [CharP F 2]

theorem tm_inj {α β α' β' : F} (h : tm F α β = tm F α' β') : α = α' ∧ β = β' := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [tm] at h00 h01
  exact ⟨h00, h01⟩

theorem tall_comm (g h : ↥(Tall F)) : g * h = h * g := by
  obtain ⟨α, β, -, hg⟩ := g.2
  obtain ⟨α', β', -, hh⟩ := h.2
  apply Subtype.ext
  apply Units.ext
  show (g.1 : Matrix (Fin 2) (Fin 2) F) * h.1 = h.1 * g.1
  rw [hg, hh, tm_mul, tm_mul]
  congr 1 <;> ring

instance instCommGroupTall : CommGroup ↥(Tall F) :=
  { (inferInstance : Group ↥(Tall F)) with mul_comm := tall_comm }

@[expose] def Cu : ↥(Tall F) :=
  ⟨⟨tm F 0 1, tm F 1 1,
    by
      have h2 := two_eq_zero_F F
      have e1 : (0 : F) * 1 + 1 * 1 = 1 := by ring
      have e2 : (0 : F) * 1 + 1 * 1 + 1 * 1 = 0 := by linear_combination h2
      rw [tm_mul, e2, e1, tm_one],
    by
      have h2 := two_eq_zero_F F
      have e1 : (1 : F) * 0 + 1 * 1 = 1 := by ring
      have e2 : (1 : F) * 1 + 1 * 0 + 1 * 1 = 0 := by linear_combination h2
      rw [tm_mul, e2, e1, tm_one]⟩,
    ⟨0, 1, by simp [Nrm], rfl⟩⟩

theorem Cu_val : (((Cu : ↥(Tall F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = tm F 0 1 := rfl

theorem Cu_pow_val (k : ℕ) :
    (((Cu ^ k : ↥(Tall F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (tm F 0 1) ^ k := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Cu_val]

theorem tall_cube (g : ↥(Tall F)) (h : g ^ 3 = 1) : ∃ z : ZMod 3, g = Cu ^ z.val := by
  obtain ⟨α, β, hn, hg⟩ := g.2
  have h2 := two_eq_zero_F F
  have hv : (g.1 : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    have := congrArg (fun x : ↥(Tall F) => ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  rw [hg, pow_succ, pow_two, tm_mul, tm_mul, ← tm_one] at hv
  obtain ⟨hA, hB⟩ := tm_inj hv
  have hB' : α * β * (α + β) = 0 := by
    linear_combination hB - (α ^ 2 * β + α * β ^ 2 + β ^ 3) * h2
  have hn' : α ^ 2 + α * β + β ^ 2 = 1 := hn
  have hgv : (g.1 : Matrix (Fin 2) (Fin 2) F) = tm F α β := hg
  have key : ∀ z : ZMod 3, tm F α β = (tm F 0 1) ^ z.val → g = Cu ^ z.val := fun z hz =>
    Subtype.ext (Units.ext (by rw [Cu_pow_val]; exact hgv.trans hz))
  have hsq : tm F 0 1 ^ 2 = tm F 1 1 := by
    rw [pow_two, tm_mul]
    congr 1 <;> ring
  rcases mul_eq_zero.1 hB' with h0 | h1
  · rcases mul_eq_zero.1 h0 with ha | hb
    ·
      subst ha
      have hb1 : β = 1 := sq_eq_one_F F (by linear_combination hn')
      subst hb1
      exact ⟨1, key 1 (by rw [show (1 : ZMod 3).val = 1 from rfl, pow_one])⟩
    ·
      subst hb
      have ha1 : α = 1 := sq_eq_one_F F (by linear_combination hn')
      subst ha1
      exact ⟨0, key 0 (by rw [show (0 : ZMod 3).val = 0 from rfl, pow_zero, tm_one])⟩
  ·
    have hβ : β = α := by linear_combination h1 - α * h2
    subst hβ
    have ha1 : β = 1 := sq_eq_one_F F (by linear_combination hn' - β ^ 2 * h2)
    subst ha1
    exact ⟨2, key 2 (by rw [show (2 : ZMod 3).val = 2 from rfl, hsq])⟩

end TallFacts

section Bhom

variable (F : Type) [Field F] [CharP F 2]

@[expose] def BhomGL : (Fin 3 → ↥(Tall F)) →* GL Idx F :=
  bdGL.comp (Pi.monoidHom fun j =>
    (Tall F).subtype.comp (Pi.evalMonoidHom (fun _ => ↥(Tall F)) j))

variable {F}

theorem BhomGL_val (y : Fin 3 → ↥(Tall F)) :
    ((BhomGL F y : GL Idx F) : Matrix Idx Idx F) =
      bd (fun j => (((y j : ↥(Tall F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := rfl

theorem BhomGL_mem (y : Fin 3 → ↥(Tall F)) : BhomGL F y ∈ SpI F := by
  rw [mem_SpI_iff, BhomGL_val, JF_eq_bd, bd_transpose, bd_mul, bd_mul]
  congr 1
  funext j
  obtain ⟨α, β, hn, hg⟩ := (y j).2
  show (((y j : ↥(Tall F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ * !![0, 1; 1, 0] *
    (((y j : ↥(Tall F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]
  rw [hg, tm_symp, hn, one_smul]

variable (F)

@[expose] def Bhom : (Fin 3 → ↥(Tall F)) →* ↥(SpI F) :=
  (BhomGL F).codRestrict (SpI F) BhomGL_mem

variable {F}

theorem Bhom_injective : Function.Injective (Bhom F) := by
  intro y y' h
  have h1 : BhomGL F y = BhomGL F y' := congrArg Subtype.val h
  have h2 := bdGL_injective h1
  funext j
  exact Subtype.ext (congrFun h2 j)

theorem cpow_map (z : ZMod 3) : (cpow z).map (ι2 F) = (tm F 0 1) ^ z.val := by
  have h1 : Cm.map (ι2 F) = tm F 0 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Cm, tm]
  have h2 := map_pow ((ι2 F).mapMatrix : Matrix (Fin 2) (Fin 2) F2 →+* Matrix (Fin 2) (Fin 2) F) Cm
    z.val
  simp only [RingHom.mapMatrix_apply] at h2
  rw [cpow, h2, h1]

theorem bc_aMat (x : V3) : bc F (aMat x) = bd (fun j => (tm F 0 1) ^ (x j).val) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [bc, aMat, bd, Matrix.map_apply, Matrix.of_apply]
  split_ifs with h
  · subst h
    have := congrFun (congrFun (cpow_map (F := F) (x i)) a) b
    simpa using this
  · simp

theorem av_eq_Bhom (x : V3) :
    (monoSp F).av x = Bhom F (fun j => (Cu : ↥(Tall F)) ^ (x j).val) := by
  apply Subtype.ext
  apply Units.ext
  show bc F (aMat x) = bd (fun j => ((((Cu : ↥(Tall F)) ^ (x j).val : ↥(Tall F)) : GL (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F))
  rw [bc_aMat]
  exact congrArg bd (funext fun j => (Cu_pow_val (x j).val).symm)

@[expose] def sB (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) (Matrix (Fin 2) (Fin 2) F) :=
  Matrix.of fun i j => if i = j + 1 then 1 else 0

theorem bc_sMat : bc F sMat = Matrix.compRingEquiv (Fin 3) (Fin 2) F (sB F) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [bc, sMat, sB, Matrix.map_apply, Matrix.of_apply, Matrix.compRingEquiv_apply,
    Matrix.comp_apply]
  by_cases h : i = j + 1
  · by_cases hab : a = b
    · subst hab
      simp [h]
    · simp [h, hab]
  · simp [h]

theorem bc_sMat_mul_bd (d : Fin 3 → Matrix (Fin 2) (Fin 2) F) :
    bc F sMat * bd d = bd (fun b => d (b - 1)) * bc F sMat := by
  rw [bc_sMat, bd_eq_comp, bd_eq_comp, ← map_mul, ← map_mul]
  congr 1
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [sB, Matrix.of_apply]
  by_cases h : i = j + 1
  · subst h
    simp
  · simp [h]

@[expose] def Bsub (F : Type) [Field F] [CharP F 2] : Subgroup ↥(SpI F) := (Bhom F).range

theorem s_Bhom (y : Fin 3 → ↥(Tall F)) :
    (monoSp F).s * Bhom F y * (monoSp F).s⁻¹ = Bhom F (fun b => y (b - 1)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  exact bc_sMat_mul_bd (F := F) (fun j => (((y j : ↥(Tall F)) : GL (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F))

theorem A0_le_Bsub : (monoSp F).A0 ≤ Bsub F := by
  intro g hg
  obtain ⟨x, rfl⟩ := (monoSp F).mem_A0_iff.1 hg
  exact ⟨_, (av_eq_Bhom x).symm⟩

theorem Bsub_comm : ∀ b ∈ Bsub F, ∀ b' ∈ Bsub F, b * b' = b' * b := by
  rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
  rw [← map_mul, ← map_mul, mul_comm y y']

theorem Bsub_sig : ∀ b ∈ Bsub F, (monoSp F).s * b * (monoSp F).s⁻¹ ∈ Bsub F := by
  rintro _ ⟨y, rfl⟩
  rw [s_Bhom]
  exact ⟨_, rfl⟩

theorem Bsub_exp3 : ∀ b ∈ Bsub F, b ^ 3 = 1 → b ∈ (monoSp F).A0 := by
  rintro _ ⟨y, rfl⟩ h3
  rw [← map_pow, ← map_one (Bhom F)] at h3
  have hy := Bhom_injective h3
  have hj : ∀ j, ∃ z : ZMod 3, y j = Cu ^ z.val := fun j =>
    tall_cube (y j) (by have := congrFun hy j; simpa using this)
  choose z hz using hj
  refine (monoSp F).mem_A0_iff.2 ⟨z, ?_⟩
  rw [av_eq_Bhom]
  exact congrArg (Bhom F) (funext hz)

theorem Bsub_hilbert : ∀ u ∈ Bsub F,
    u * ((monoSp F).s * u * (monoSp F).s⁻¹) *
      ((monoSp F).s * ((monoSp F).s * u * (monoSp F).s⁻¹) * (monoSp F).s⁻¹) = 1 →
    ∃ v ∈ Bsub F, u = v * ((monoSp F).s * v * (monoSp F).s⁻¹)⁻¹ := by
  rintro _ ⟨y, rfl⟩ h
  rw [s_Bhom, s_Bhom, ← map_mul, ← map_mul, ← map_one (Bhom F)] at h
  have hy := Bhom_injective h
  have hb : ∀ b, y b * y (b - 1) * y (b - 1 - 1) = 1 := fun b => congrFun hy b
  have h2 := hb 2
  have e1 : (2 : Fin 3) - 1 = 1 := by decide
  have e2 : (1 : Fin 3) - 1 = 0 := by decide
  rw [e1, e2] at h2
  refine ⟨Bhom F ![y 0, y 0 * y 1, 1], ⟨_, rfl⟩, ?_⟩
  rw [s_Bhom, ← map_inv, ← map_mul]
  refine congrArg (Bhom F) (funext fun b => ?_)
  fin_cases b
  · show y 0 = y 0 * (1 : ↥(Tall F))⁻¹
    simp
  · show y 1 = y 0 * y 1 * (y 0)⁻¹
    rw [mul_comm (y 0) (y 1), mul_assoc, mul_inv_cancel, mul_one]
  · show y 2 = 1 * (y 0 * y 1)⁻¹
    rw [one_mul]
    apply eq_inv_of_mul_eq_one_left
    calc y 2 * (y 0 * y 1) = y 2 * y 1 * y 0 := by rw [mul_comm (y 0) (y 1), mul_assoc]
      _ = 1 := h2

variable (F) in
@[expose] noncomputable def monoBase : MonoBase (monoSp F) where
  B := Bsub F
  A0_le := A0_le_Bsub
  comm := Bsub_comm
  sig_mem := Bsub_sig
  exp3 := Bsub_exp3
  hilbert := Bsub_hilbert

end Bhom

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
