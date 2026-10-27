module

public import CFSG.GH74.Generic.BProg.Vocab
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutGraph
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutAbs
public import CFSG.GH74.Generic.BProg.B2.GenLocU4Dich

public section

namespace CFSG.GH74.Generic.BProg.B3.S1DiagActModel

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
open CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B2
open scoped MatrixGroups


@[expose] def MatForm {Kt : Type} [Group Kt] {F : Type} [Field F] (ι : Kt →* GL (Fin 4) F)
    (δ : MulAut Kt) : Prop :=
  (∃ (g : GL (Fin 4) F) (c : F), c ≠ 0 ∧ (∀ x, ι (δ x) = g * ι x * g⁻¹) ∧
      ((g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = c • 1)) ∨
    (∃ B : GL (Fin 4) F, ∀ x, ((ι (δ x) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (B : Matrix (Fin 4) (Fin 4) F) * ((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
        (B : Matrix (Fin 4) (Fin 4) F))

theorem matrix_dichotomy_lin {Kt : Type} [Group Kt] {F : Type} [Field F] [Finite F]
    (hF4 : Nat.card F % 4 = 3) (e : Kt ≃* StatedSL 4 F) (δ : MulAut Kt) (hδ : δ * δ = 1) :
    ∃ ι : Kt →* GL (Fin 4) F, Function.Injective ι ∧ (2 : F) ≠ 0 ∧
      (∀ x, ((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1) ∧ MatForm ι δ := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 := two_ne_zero_of_odd_card hodd
  let ι : Kt →* GL (Fin 4) F := (StatedSL 4 F).subtype.comp e.toMonoidHom
  let φ : Kt ≃* SL(4, F) := e.trans (specialLinearGroupEquivStatedSL 4 F).symm
  have hφι : ∀ x, ((φ x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      ((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    intro x
    have := specialLinearGroupEquivStatedSL_coe 4 F (φ x)
    have h3 : specialLinearGroupEquivStatedSL 4 F (φ x) = e x := by simp [φ]
    rw [h3] at this
    exact this.symm
  let u : MulAut SL(4, F) := MulAut.congr φ δ
  have hu : u * u = 1 := by rw [← map_mul, hδ, map_one]
  have huφ : ∀ y, u (φ y) = φ (δ y) := fun y => by simp [u, MulAut.congr_apply]
  have hinj : Function.Injective ι := fun x y hxy => by
    apply e.injective
    exact Subtype.ext hxy
  have hdet : ∀ x, ((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := fun x => by
    rw [← hφι]
    exact (φ x).2
  refine ⟨ι, hinj, h2, hdet, ?_⟩
  unfold MatForm
  by_cases hin : GenLocL4Out.IsInnerDiag4 u
  · obtain ⟨x, hx⟩ := hin
    obtain ⟨c, hc0, hc⟩ := GenLocL4Out.innerLift_sq (t := u) (g := x) hx hu
    refine Or.inl ⟨x, c, hc0, fun y => ?_, hc⟩
    apply Units.ext
    have h1 := hx (φ y)
    rw [huφ, hφι, hφι] at h1
    rw [Units.val_mul, Units.val_mul]
    exact h1
  · obtain ⟨B, hB, -⟩ := GenLocL4Out.exists_graph_form hF4 u hu hin
    refine Or.inr ⟨B, fun y => ?_⟩
    have h1 := hB (φ y)
    rw [huφ, hφι] at h1
    have hXi : ((φ y : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
        (((φ y)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hBBi : ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [h1, ← hφι y]
    calc (B : Matrix (Fin 4) (Fin 4) F) * (((φ y)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ *
          ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F) *
          ((φ y : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ
        = (B : Matrix (Fin 4) (Fin 4) F) * (((φ y)⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ *
          (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F)) *
          ((φ y : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ := by simp only [Matrix.mul_assoc]
      _ = (B : Matrix (Fin 4) (Fin 4) F) := by
        rw [hBBi, Matrix.mul_one, Matrix.mul_assoc, ← Matrix.transpose_mul, hXi, Matrix.transpose_one,
          Matrix.mul_one]

theorem matrix_dichotomy_uni {Kt : Type} [Group Kt] {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) (e : Kt ≃* StatedSU 4 q F) (δ : MulAut Kt)
    (hδ : δ * δ = 1) :
    ∃ ι : Kt →* GL (Fin 4) F, Function.Injective ι ∧ (2 : F) ≠ 0 ∧
      (∀ x, ((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1) ∧ MatForm ι δ := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have h2 := two_ne_zero_of_odd_card hodd
  have hp2 : p ≠ 2 := prime_ne_two_of_odd_card hodd
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
    GenLocDiagU.unitaryFieldData_of_card hp.out hF
  let ι : Kt →* GL (Fin 4) F := (StatedSU 4 (p ^ f) F).subtype.comp e.toMonoidHom
  let φ : MulAut ↥(StatedSU 4 (p ^ f) F) := MulAut.congr e δ
  have hφ : φ * φ = 1 := by rw [← map_mul, hδ, map_one]
  have hφe : ∀ y, φ (e y) = e (δ y) := fun y => by simp [φ, MulAut.congr_apply]
  have hinj : Function.Injective ι := fun x y hxy => by
    apply e.injective
    exact Subtype.ext hxy
  have hmem := fun x => (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hU).1 (e x).2
  have hdet : ∀ x, ((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := fun x => (hmem x).1
  refine ⟨ι, hinj, h2, hdet, ?_⟩
  unfold MatForm
  have hbar : ∀ x, (((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f)))ᵀ *
      ((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    intro x
    have h1 := (hmem x).2
    rw [GenLocU4Basic.bar_eq_pow hU] at h1
    exact h1
  rcases GenLocU4Basic.inner_or_graph hp.out hp2 hF φ hφ with hin | ⟨A, ⟨hAu, hA⟩, -⟩
  · obtain ⟨x, hxu, hx⟩ := hin
    have hconj : ∀ y : Kt, ι (δ y) = x * ι y * x⁻¹ := fun y => by
      apply Units.ext
      have h1 := hx (e y)
      rw [hφe] at h1
      rw [Units.val_mul, Units.val_mul]
      exact h1
    obtain ⟨c, hc0, hc⟩ := GenLocU4Basic.proportional_of_conj_eq hU hp2 (u := x * x) (v := 1)
      (fun g hg => by
        have h1 := hconj (e.symm ⟨g, hg⟩)
        have h3 := hconj (δ (e.symm ⟨g, hg⟩))
        have h4 : δ (δ (e.symm ⟨g, hg⟩)) = e.symm ⟨g, hg⟩ := by
          have := congrArg (fun a : MulAut Kt => a (e.symm ⟨g, hg⟩)) hδ
          simpa using this
        rw [h4, h1] at h3
        have h5 : ι (e.symm ⟨g, hg⟩) = g := by simp [ι]
        rw [h5] at h3
        rw [one_mul, inv_one, mul_one]
        calc x * x * g * (x * x)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by group
          _ = g := h3.symm)
    refine Or.inl ⟨x, c, hc0, hconj, ?_⟩
    rw [← Units.val_mul]
    simpa using hc
  · refine Or.inr ⟨A, fun y => ?_⟩
    have h1 := hA (e y)
    rw [hφe] at h1
    have hX : ((ι y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (((ι y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f)))ᵀ = 1 :=
      mul_eq_one_comm.1 (hbar y)
    have hAAi : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hXt : (((ι y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f))) *
        ((ι y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      have := congrArg Matrix.transpose hX
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    show ((e (δ y) : StatedSU 4 (p ^ f) F) : GL (Fin 4) F).1 * _ * _ = _
    rw [h1]
    calc (A : Matrix (Fin 4) (Fin 4) F) * ((ι y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f)) *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) *
          ((ι y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ
        = (A : Matrix (Fin 4) (Fin 4) F) * ((ι y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f)) *
          (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F)) *
          ((ι y : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by simp only [Matrix.mul_assoc]
      _ = (A : Matrix (Fin 4) (Fin 4) F) := by
        rw [hAAi, Matrix.mul_one, Matrix.mul_assoc, hXt, Matrix.mul_one]

theorem matrix_dichotomy {Kt : Type} [Group Kt] (hK : QShape1 Kt) (δ : MulAut Kt) (hδ : δ * δ = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ι : Kt →* GL (Fin 4) F),
      Function.Injective ι ∧ (2 : F) ≠ 0 ∧
      (∀ x, ((ι x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1) ∧ MatForm ι δ := by
  rcases hK with ⟨F, _, _, hF4, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · exact ⟨F, inferInstance, inferInstance, matrix_dichotomy_lin hF4 e δ hδ⟩
  · exact ⟨F, inferInstance, inferInstance, matrix_dichotomy_uni hF hq e δ hδ⟩

end CFSG.GH74.Generic.BProg.B3.S1DiagActModel
