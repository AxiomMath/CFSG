module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GF2Type.SmithTypeE.L9Cent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.SLnFamily

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

open CFSG.GF2Type.SmithTypeE CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.Models.SymplecticPairs (inclMat inclMat_transpose_mul)
open scoped MatrixGroups Matrix

section Lin

variable {L : Type} [Field L] {ν m : ℕ}

@[expose] def projDiag (L : Type) [Field L] (X : Finset (Fin ν)) : Matrix (Fin ν) (Fin ν) L :=
  Matrix.diagonal fun k => if k ∈ X then 1 else 0

theorem projDiag_mul_self (X : Finset (Fin ν)) : projDiag L X * projDiag L X = projDiag L X := by
  unfold projDiag
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  split_ifs <;> simp

theorem incl_mul_transpose {X : Finset (Fin ν)} (e : Fin m → Fin ν) (he : Function.Injective e)
    (hX : ∀ k, k ∈ X ↔ ∃ a, e a = k) :
    inclMat (K := L) e * (inclMat (K := L) e)ᵀ = projDiag L X := by
  classical
  ext k l
  simp only [Matrix.mul_apply, inclMat, Matrix.transpose_apply, Matrix.of_apply, projDiag,
    Matrix.diagonal_apply]
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl]
    by_cases hk : k ∈ X
    · rw [if_pos hk]
      obtain ⟨a, rfl⟩ := (hX _).1 hk
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        have : e a ≠ e b := fun h => hb (he h).symm
        simp [this]
      · simp
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun a _ => ?_
      have : k ≠ e a := fun h => hk ((hX _).2 ⟨a, h.symm⟩)
      simp [this]
  · rw [if_neg hkl]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases h1 : k = e a
    · have : l ≠ e a := fun h2 => hkl (h1.trans h2.symm)
      simp [this]
    · simp [h1]

theorem mem_range_slEmbed_iff {X : Finset (Fin ν)} (e : Fin m → Fin ν) (he : Function.Injective e)
    (hX : ∀ k, k ∈ X ↔ ∃ a, e a = k) (Z : SL(ν, L)) :
    Z ∈ (slEmbed e he).range ↔
      (Z : Matrix (Fin ν) (Fin ν) L) - 1 =
        projDiag L X * ((Z : Matrix (Fin ν) (Fin ν) L) - 1) * projDiag L X := by
  classical
  set P : Matrix (Fin ν) (Fin m) L := inclMat e with hPdef
  have hPP : Pᵀ * P = 1 := inclMat_transpose_mul he
  have hp : P * Pᵀ = projDiag L X := incl_mul_transpose e he hX
  have hpp : projDiag L X * projDiag L X = projDiag L X := projDiag_mul_self X
  constructor
  · rintro ⟨A, rfl⟩
    have hco : ((slEmbed e he A : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        slEmbedMat e (A : Matrix (Fin m) (Fin m) L) := rfl
    rw [hco]
    unfold slEmbedMat
    rw [← hp]
    set B : Matrix (Fin m) (Fin m) L := (A : Matrix (Fin m) (Fin m) L) - 1 with hB
    have e1 : (1 : Matrix (Fin ν) (Fin ν) L) + P * B * Pᵀ - 1 = P * B * Pᵀ := by
      abel
    rw [e1]
    have e2 : P * Pᵀ * (P * B * Pᵀ) * (P * Pᵀ) = P * (Pᵀ * P) * B * (Pᵀ * P) * Pᵀ := by
      simp only [Matrix.mul_assoc]
    rw [e2, hPP]
    simp
  · intro hZ
    set A₀ : Matrix (Fin m) (Fin m) L := Pᵀ * (Z : Matrix (Fin ν) (Fin ν) L) * P with hA₀
    have hZ' : (Z : Matrix (Fin ν) (Fin ν) L) = slEmbedMat e A₀ := by
      unfold slEmbedMat
      rw [hA₀]
      have e3 : P * (Pᵀ * (Z : Matrix (Fin ν) (Fin ν) L) * P - 1) * Pᵀ =
          projDiag L X * (Z : Matrix (Fin ν) (Fin ν) L) * projDiag L X - projDiag L X := by
        rw [← hp]
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      rw [e3]
      have e4 : projDiag L X * ((Z : Matrix (Fin ν) (Fin ν) L) - 1) * projDiag L X =
          projDiag L X * (Z : Matrix (Fin ν) (Fin ν) L) * projDiag L X - projDiag L X := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hpp]
      rw [← e4, ← hZ]
      abel
    have hdet : A₀.det = 1 := by
      have := det_slEmbedMat he A₀
      rw [← hZ', Z.2] at this
      exact this.symm
    refine ⟨⟨A₀, hdet⟩, ?_⟩
    apply Subtype.ext
    exact hZ'.symm

theorem conj_mem_range_slEmbed {X : Finset (Fin ν)} (e : Fin m → Fin ν) (he : Function.Injective e)
    (hX : ∀ k, k ∈ X ↔ ∃ a, e a = k) {Y : SL(ν, L)}
    (hY : projDiag L X * (Y : Matrix (Fin ν) (Fin ν) L) =
      (Y : Matrix (Fin ν) (Fin ν) L) * projDiag L X) {Z : SL(ν, L)}
    (hZ : Z ∈ (slEmbed e he).range) : Y * Z * Y⁻¹ ∈ (slEmbed e he).range := by
  classical
  rw [mem_range_slEmbed_iff e he hX] at hZ ⊢
  set p : Matrix (Fin ν) (Fin ν) L := projDiag L X with hp
  set Ym : Matrix (Fin ν) (Fin ν) L := (Y : Matrix (Fin ν) (Fin ν) L) with hYm
  set Yi : Matrix (Fin ν) (Fin ν) L := ((Y⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) with hYi
  have hYYi : Ym * Yi = 1 := by
    rw [hYm, hYi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  have hYiY : Yi * Ym = 1 := by
    rw [hYm, hYi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  have hYi' : Yi * p = p * Yi := by
    calc Yi * p = Yi * p * (Ym * Yi) := by rw [hYYi, Matrix.mul_one]
      _ = Yi * (p * Ym) * Yi := by simp only [Matrix.mul_assoc]
      _ = Yi * (Ym * p) * Yi := by rw [hY]
      _ = (Yi * Ym) * p * Yi := by simp only [Matrix.mul_assoc]
      _ = p * Yi := by rw [hYiY, Matrix.one_mul]
  have hcoe : ((Y * Z * Y⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      Ym * (Z : Matrix (Fin ν) (Fin ν) L) * Yi := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [hcoe]
  have e1 : Ym * (Z : Matrix (Fin ν) (Fin ν) L) * Yi - 1 =
      Ym * ((Z : Matrix (Fin ν) (Fin ν) L) - 1) * Yi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hYYi]
  rw [e1]
  calc Ym * ((Z : Matrix (Fin ν) (Fin ν) L) - 1) * Yi
      = Ym * (p * ((Z : Matrix (Fin ν) (Fin ν) L) - 1) * p) * Yi := by rw [← hZ]
    _ = (Ym * p) * ((Z : Matrix (Fin ν) (Fin ν) L) - 1) * (p * Yi) := by
        simp only [Matrix.mul_assoc]
    _ = (p * Ym) * ((Z : Matrix (Fin ν) (Fin ν) L) - 1) * (Yi * p) := by rw [← hY, hYi']
    _ = p * (Ym * ((Z : Matrix (Fin ν) (Fin ν) L) - 1) * Yi) * p := by
        simp only [Matrix.mul_assoc]

theorem two_mul_card_le_of_zero_block (Y : Matrix (Fin ν) (Fin ν) L) (hY : Y.det ≠ 0)
    (X : Finset (Fin ν)) (h0 : ∀ k ∈ X, ∀ l ∈ X, Y k l = 0) : 2 * X.card ≤ ν := by
  classical
  have hind : LinearIndependent L (fun k : X => Y k) :=
    (Matrix.linearIndependent_rows_of_det_ne_zero hY).comp (Subtype.val : X → Fin ν)
      Subtype.val_injective
  set f : (Fin ν → L) →ₗ[L] (↥(Xᶜ : Finset (Fin ν)) → L) :=
    LinearMap.funLeft L L (Subtype.val : ↥(Xᶜ : Finset (Fin ν)) → Fin ν) with hf
  have hdisj : Disjoint (Submodule.span L (Set.range fun k : X => Y k)) (LinearMap.ker f) := by
    rw [Submodule.disjoint_def]
    intro v hv hvf
    have hvX : ∀ l ∈ X, v l = 0 := by
      have hle : Submodule.span L (Set.range fun k : X => Y k) ≤
          ⨅ l ∈ X, LinearMap.ker (LinearMap.proj l : (Fin ν → L) →ₗ[L] L) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
        intro l hl
        exact h0 k k.2 l hl
      have := hle hv
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply] at this
      exact this
    funext l
    by_cases hl : l ∈ X
    · exact hvX l hl
    · have : f v ⟨l, by simpa using hl⟩ = 0 := by rw [LinearMap.mem_ker.1 hvf]; rfl
      simpa [hf, LinearMap.funLeft] using this
  have hind2 : LinearIndependent L (f ∘ fun k : X => Y k) := hind.map hdisj
  have hcard := hind2.fintype_card_le_finrank
  simp only [Fintype.card_coe, Module.finrank_fintype_fun_eq_card, Finset.card_compl,
    Fintype.card_fin] at hcard
  omega

theorem conjDiagn_apply (d : Fin ν → Lˣ) (A : SL(ν, L)) (k l : Fin ν) :
    ((conjDiagn d A : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) k l =
      (d k : L) * (A : Matrix (Fin ν) (Fin ν) L) k l * (((d l)⁻¹ : Lˣ) : L) := by
  rw [coe_conjDiagn]
  have h1 : ((diagGLn d : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
      Matrix.diagonal fun i => (d i : L) := rfl
  have h2 : (((diagGLn d)⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
      Matrix.diagonal fun i => (((d i)⁻¹ : Lˣ) : L) := rfl
  rw [h1, h2, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem commute_diag_of_center {D : Fin ν → Lˣ} (X : Finset (Fin ν)) {d₀ : Lˣ}
    (hX : ∀ k, k ∈ X ↔ D k = d₀) (h2 : ν < 2 * X.card) {Y : SL(ν, L)}
    (hc : conjDiagn D Y * Y⁻¹ ∈ Subgroup.center SL(ν, L)) :
    ∀ k l, D k ≠ D l → (Y : Matrix (Fin ν) (Fin ν) L) k l = 0 := by
  classical
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hE : ∀ k l, (D k : L) * (Y : Matrix (Fin ν) (Fin ν) L) k l * (D l : L)⁻¹ =
      r * (Y : Matrix (Fin ν) (Fin ν) L) k l := by
    intro k l
    have h1 : ((conjDiagn D Y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        Matrix.scalar (Fin ν) r * (Y : Matrix (Fin ν) (Fin ν) L) := by
      have h3 : conjDiagn D Y = (conjDiagn D Y * Y⁻¹) * Y := by group
      have h4 := congrArg (fun A : SL(ν, L) => (A : Matrix (Fin ν) (Fin ν) L)) h3
      rw [Matrix.SpecialLinearGroup.coe_mul] at h4
      rw [h4, ← hr]
    have h5 := congrArg (fun A : Matrix (Fin ν) (Fin ν) L => A k l) h1
    simp only [conjDiagn_apply] at h5
    rw [Units.val_inv_eq_inv_val] at h5
    rw [h5, Matrix.scalar_apply, Matrix.diagonal_mul]
  by_cases hr1 : r = 1
  · subst hr1
    intro k l hkl
    have h1 := hE k l
    rw [one_mul] at h1
    by_contra hne
    apply hkl
    have hl0 : (D l : L) ≠ 0 := Units.ne_zero _
    field_simp at h1
    exact Units.ext h1
  · exfalso
    have hz : ∀ k ∈ X, ∀ l ∈ X, (Y : Matrix (Fin ν) (Fin ν) L) k l = 0 := by
      intro k hk l hl
      have h1 := hE k l
      rw [(hX k).1 hk, (hX l).1 hl] at h1
      have h5 : (d₀ : L) ≠ 0 := Units.ne_zero _
      have h6 : (d₀ : L) * (Y : Matrix (Fin ν) (Fin ν) L) k l * (d₀ : L)⁻¹ =
          (Y : Matrix (Fin ν) (Fin ν) L) k l := by
        rw [mul_comm (d₀ : L) _, mul_assoc, mul_inv_cancel₀ h5, mul_one]
      rw [h6] at h1
      have h7 : (1 - r) * (Y : Matrix (Fin ν) (Fin ν) L) k l = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h7 with h8 | h8
      · exact absurd (sub_eq_zero.1 h8).symm hr1
      · exact h8
    have hdet : (Y : Matrix (Fin ν) (Fin ν) L).det ≠ 0 := by
      rw [Y.2]; exact one_ne_zero
    have := two_mul_card_le_of_zero_block (Y : Matrix (Fin ν) (Fin ν) L) hdet X hz
    omega

end Lin

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6.T

end
