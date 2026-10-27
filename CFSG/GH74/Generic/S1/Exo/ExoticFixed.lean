module

public import CFSG.GH74.Generic.S1.Exo.UniDescent
public import CFSG.GH74.Generic.S1.Exo.OmegaSplit
public import CFSG.GH74.Generic.S1.Defs

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module QuadraticMap CFSG.Open CFSG.GH74.L5U5
open scoped Matrix

section Fixed

variable {Γ : Type} [Group Γ]

@[expose] def fixedSub (β : MulAut Γ) : Subgroup Γ := MonoidHom.eqLocus β.toMonoidHom (MonoidHom.id Γ)

def fixedSubEquiv (S : Subgroup Γ) (β : MulAut ↥S) (f : Γ →* Γ)
    (hβ : ∀ k : ↥S, ((β k : ↥S) : Γ) = f k) :
    ↥(fixedSub β) ≃* ↥(S ⊓ MonoidHom.eqLocus f (MonoidHom.id Γ)) where
  toFun x := ⟨(x.1 : Γ), x.1.2, by
    have h1 : β x.1 = x.1 := x.2
    have h2 := hβ x.1
    rw [h1] at h2
    exact h2.symm⟩
  invFun y := ⟨⟨(y.1 : Γ), y.2.1⟩, by
    apply Subtype.ext
    have h1 := hβ ⟨(y.1 : Γ), y.2.1⟩
    have h2 : f (y.1 : Γ) = (y.1 : Γ) := y.2.2
    exact h1.trans h2⟩
  left_inv x := rfl
  right_inv y := rfl
  map_mul' x y := rfl

end Fixed

section Ambient

variable {Γ : Type} [Group Γ]

@[expose] def ExoticFixedGroup (β : MulAut Γ) (z : Γ) (q : ℕ) : Prop :=
  ∃ Ω : Subgroup Γ, (∀ k ∈ Ω, β k = k) ∧ IsSimpleGroup ↥Ω ∧ Group.IsPerfect ↥Ω ∧
    Nat.card ↥Ω * 2 = q ^ 2 * (q ^ 4 - 1) ∧
    (∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = q ^ 2 ∧
      Nonempty (↥Ω ≃* StatedProj (StatedSL 2 E))) ∧
    β z = z ∧ z ∉ Ω ∧ ∀ k : Γ, β k = k → k ∈ Ω ∨ z * k ∈ Ω

theorem ExoticFixedGroup.of_omegaSplit {β : MulAut Γ} {z : Γ} (hz : β z = z) {q : ℕ}
    (h : OmegaSplit ↥(fixedSub β) ⟨z, hz⟩ q) : ExoticFixedGroup β z q := by
  obtain ⟨E, _, _, hE, Ω₀, hs, hp, hc, ⟨hi⟩, hzΩ, hall⟩ := h
  have e1 : ↥Ω₀ ≃* ↥(Ω₀.map (fixedSub β).subtype) :=
    Subgroup.equivMapOfInjective Ω₀ (fixedSub β).subtype (Subgroup.subtype_injective _)
  refine ⟨Ω₀.map (fixedSub β).subtype, ?_, e1.symm.isSimpleGroup, ?_, ?_, ⟨E, inferInstance, inferInstance, hE,
    ⟨e1.symm.trans hi⟩⟩, hz, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · exact Group.IsPerfect.ofSurjective (f := e1.toMonoidHom) e1.surjective
  · rw [Nat.card_congr e1.symm.toEquiv]
    exact hc
  · rintro ⟨k, hk, hkz⟩
    apply hzΩ
    have : k = ⟨z, hz⟩ := Subtype.ext hkz
    rw [← this]
    exact hk
  · intro k hk
    rcases hall ⟨k, hk⟩ with h1 | h1
    · exact Or.inl ⟨⟨k, hk⟩, h1, rfl⟩
    · exact Or.inr ⟨⟨z, hz⟩ * ⟨k, hk⟩, h1, rfl⟩

end Ambient

section Lin

variable {F : Type} [Field F]

theorem mem_linFixed_iff (g k : GL (Fin 4) F) :
    k ∈ linFixed g ↔ (k : Matrix (Fin 4) (Fin 4) F).det = 1 ∧
      g * Matrix.GeneralLinearGroup.inverseTranspose k * g⁻¹ = k := by
  have hS : k ∈ StatedSL 4 F ↔ (k : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    change k ∈ CFSG.Assembly.LowTwoRank.StatedSL 4 F ↔ _
    rw [statedSL_eq_detOne, mem_detOne]
  rw [linFixed, Subgroup.mem_inf, hS]
  rfl

theorem linFixed_eq_soMat (g : GL (Fin 4) F) :
    linFixed g = soMat ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  ext k
  rw [mem_linFixed_iff, mem_soMat_iff]
  suffices key : g * Matrix.GeneralLinearGroup.inverseTranspose k * g⁻¹ = k ↔
      (k : Matrix (Fin 4) (Fin 4) F)ᵀ * ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (k : Matrix (Fin 4) (Fin 4) F) = ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨key.1 h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, key.2 h1⟩
  have hAB : (k : Matrix (Fin 4) (Fin 4) F) * ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBA : ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (k : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGG : (g : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGG' : ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBA' : ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * (k : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  have hAB' : (k : Matrix (Fin 4) (Fin 4) F)ᵀ * ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one]
  set A := (k : Matrix (Fin 4) (Fin 4) F) with hA
  set B := ((k⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hB
  set Gm := (g : Matrix (Fin 4) (Fin 4) F) with hGm
  set Gi := ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hGi
  have hunits : g * Matrix.GeneralLinearGroup.inverseTranspose k * g⁻¹ = k ↔ Gm * Bᵀ * Gi = A := by
    constructor
    · intro h
      have := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) h
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose] at this
      exact this
    · intro h
      apply Units.ext
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose]
      exact h
  rw [hunits]
  constructor
  · intro h
    have h1 : Bᵀ = Gi * A * Gm := by
      calc Bᵀ = (Gi * Gm) * Bᵀ * (Gi * Gm) := by rw [hGG']; simp
        _ = Gi * (Gm * Bᵀ * Gi) * Gm := by simp only [Matrix.mul_assoc]
        _ = Gi * A * Gm := by rw [h]
    have h2 : Aᵀ * (Gi * A * Gm) = 1 := by rw [← h1]; exact hAB'
    calc Aᵀ * Gi * A = Aᵀ * Gi * A * (Gm * Gi) := by rw [hGG]; simp
      _ = (Aᵀ * (Gi * A * Gm)) * Gi := by simp only [Matrix.mul_assoc]
      _ = Gi := by rw [h2]; simp
  · intro h
    have h2 : Aᵀ * (Gi * A * Gm) = 1 := by
      calc Aᵀ * (Gi * A * Gm) = (Aᵀ * Gi * A) * Gm := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h, hGG']
    have h1 : Bᵀ = Gi * A * Gm := by
      calc Bᵀ = Bᵀ * (Aᵀ * (Gi * A * Gm)) := by rw [h2]; simp
        _ = (Bᵀ * Aᵀ) * (Gi * A * Gm) := by simp only [Matrix.mul_assoc]
        _ = Gi * A * Gm := by rw [hBA']; simp
    calc Gm * Bᵀ * Gi = Gm * (Gi * A * Gm) * Gi := by rw [h1]
      _ = (Gm * Gi) * A * (Gm * Gi) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [hGG]; simp

end Lin

section LinMain

variable {F : Type} [Field F]

theorem inverseTranspose_neg_one :
    Matrix.GeneralLinearGroup.inverseTranspose (-1 : GL (Fin 4) F) = -1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.coe_inverseTranspose]

theorem exotic_gram_facts {g : GL (Fin 4) F}
    (hgs : (g : Matrix (Fin 4) (Fin 4) F)ᵀ = (g : Matrix (Fin 4) (Fin 4) F))
    (hdet : ¬ IsSquare (g : Matrix (Fin 4) (Fin 4) F).det) :
    ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) ∧
      ¬ IsSquare ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hgs]
  · rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rwa [isSquare_inv]

theorem exoticFixedGroup_lin [Finite F] (hF : Nat.card F % 4 = 3)
    {β : MulAut ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F)}
    (hβ : IsExoticLin (CFSG.Assembly.LowTwoRank.StatedSL 4 F) β)
    (z : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F)) (hz : (z : GL (Fin 4) F) = -1) :
    ExoticFixedGroup β z (Nat.card F) := by
  obtain ⟨g, hgs, hdet, hact⟩ := hβ
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hβ' : ∀ k : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F),
      ((β k : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F)) : GL (Fin 4) F) = linAut g k := hact
  have hzfix : β z = z := by
    apply Subtype.ext
    rw [hact z, hz, inverseTranspose_neg_one]
    simp
  obtain ⟨hGs, hGdet⟩ := exotic_gram_facts hgs hdet
  refine ExoticFixedGroup.of_omegaSplit hzfix ?_
  let e1 : ↥(fixedSub β) ≃* ↥(linFixed g) := fixedSubEquiv _ β (linAut g) hβ'
  let e2 : ↥(linFixed g) ≃* ↥(soMat ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) :=
    MulEquiv.subgroupCongr (linFixed_eq_soMat g)
  refine (omegaSplit_soMat h2 _ hGs hGdet).of_mulEquiv (e1.trans e2).symm ?_
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext hz.symm

end LinMain

section UniMain

variable {F : Type} [Field F]

theorem map_neg_one_gl (bar : F →+* F) :
    Matrix.GeneralLinearGroup.map bar (-1 : GL (Fin 4) F) = -1 := by
  apply Units.ext
  show (RingHom.mapMatrix bar) ((-1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

theorem exoticFixedGroup_uni [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1)
    {β : MulAut ↥(CFSG.Assembly.LowTwoRank.StatedSU 4 q F)}
    (hβ : IsExoticUni (CFSG.Assembly.LowTwoRank.StatedSU 4 q F) q β)
    (z : ↥(CFSG.Assembly.LowTwoRank.StatedSU 4 q F)) (hz : (z : GL (Fin 4) F) = -1) :
    ExoticFixedGroup β z q := by
  obtain ⟨bar, g, hbar, hgu, hgs, hdet, hact⟩ := hβ
  have hβ' : ∀ k : ↥(CFSG.Assembly.LowTwoRank.StatedSU 4 q F),
      ((β k : ↥(CFSG.Assembly.LowTwoRank.StatedSU 4 q F)) : GL (Fin 4) F) = uniAut bar g k := hact
  have hzfix : β z = z := by
    apply Subtype.ext
    rw [hact z, hz, map_neg_one_gl]
    simp
  obtain ⟨K₀, _, _, G₀, hK₀, hG₀s, hG₀d, ψ, hψ⟩ := uniFixed_mulEquiv_soMat hF hq bar hbar g hgs hgu hdet
  have hodd : Odd (Nat.card K₀) := by
    rw [hK₀]
    exact Nat.odd_iff.2 (by omega)
  have h2 : (2 : K₀) ≠ 0 := two_ne_zero_of_odd_card hodd
  refine ExoticFixedGroup.of_omegaSplit hzfix ?_
  let e1 : ↥(fixedSub β) ≃* ↥(uniFixed q bar g) := fixedSubEquiv _ β (uniAut bar g) hβ'
  have hs := omegaSplit_soMat h2 G₀ hG₀s hG₀d
  rw [hK₀] at hs
  refine hs.of_mulEquiv (e1.trans ψ).symm ?_
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (hψ (e1 ⟨z, hzfix⟩) hz).symm

end UniMain

section Conj

variable {F : Type} [Field F]

theorem det_eq_one_of_mem_statedSL (w : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F)) :
    ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have : (w : GL (Fin 4) F) ∈ detOne F 4 := by
    rw [← statedSL_eq_detOne]
    exact w.2
  exact this

theorem det_mul_gl (a b : GL (Fin 4) F) :
    ((a * b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      (a : Matrix (Fin 4) (Fin 4) F).det * (b : Matrix (Fin 4) (Fin 4) F).det := by
  rw [Units.val_mul, Matrix.det_mul]

theorem IsExoticLin.conj_mul {β : MulAut ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F)}
    (hβ : IsExoticLin (CFSG.Assembly.LowTwoRank.StatedSL 4 F) β)
    {w : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F)} (hw2 : w * w = 1) (hwf : β w = w) :
    IsExoticLin (CFSG.Assembly.LowTwoRank.StatedSL 4 F) (MulAut.conj w * β) := by
  obtain ⟨g, hgs, hdet, hact⟩ := hβ
  have hWW : (w : GL (Fin 4) F) * (w : GL (Fin 4) F) = 1 := congrArg Subtype.val hw2
  have hWinv : (w : GL (Fin 4) F)⁻¹ = (w : GL (Fin 4) F) := inv_eq_of_mul_eq_one_right hWW
  have hfix : (w : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.inverseTranspose (w : GL (Fin 4) F) * g⁻¹ := by
    have := hact w
    rw [hwf] at this
    exact this
  have h1 : ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) * ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
    have h2 : (w : GL (Fin 4) F) * g = g * Matrix.GeneralLinearGroup.inverseTranspose (w : GL (Fin 4) F) := by
      calc (w : GL (Fin 4) F) * g
          = (g * Matrix.GeneralLinearGroup.inverseTranspose (w : GL (Fin 4) F) * g⁻¹) * g := by rw [← hfix]
        _ = g * Matrix.GeneralLinearGroup.inverseTranspose (w : GL (Fin 4) F) := by group
    have h3 := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) h2
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose, hWinv] at h3
    exact h3
  refine ⟨(w : GL (Fin 4) F) * g, ?_, ?_, ?_⟩
  · rw [Units.val_mul, Matrix.transpose_mul, hgs, h1]
  · rw [det_mul_gl, det_eq_one_of_mem_statedSL w, one_mul]
    exact hdet
  · intro k
    have hk := hact k
    calc (((MulAut.conj w * β) k : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F)) : GL (Fin 4) F)
        = (w : GL (Fin 4) F) * ((β k : ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 F)) : GL (Fin 4) F) *
            (w : GL (Fin 4) F)⁻¹ := rfl
      _ = (w : GL (Fin 4) F) * (g * Matrix.GeneralLinearGroup.inverseTranspose (k : GL (Fin 4) F) * g⁻¹) *
            (w : GL (Fin 4) F)⁻¹ := by rw [hk]
      _ = ((w : GL (Fin 4) F) * g) * Matrix.GeneralLinearGroup.inverseTranspose (k : GL (Fin 4) F) *
            ((w : GL (Fin 4) F) * g)⁻¹ := by group

end Conj

section ConjUni

variable {F : Type} [Field F]

theorem coe_glMap (bar : F →+* F) (A : GL (Fin 4) F) :
    ((Matrix.GeneralLinearGroup.map bar A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F).map bar := rfl

theorem IsExoticUni.conj_mul [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1)
    {β : MulAut ↥(CFSG.Assembly.LowTwoRank.StatedSU 4 q F)}
    (hβ : IsExoticUni (CFSG.Assembly.LowTwoRank.StatedSU 4 q F) q β)
    {w : ↥(CFSG.Assembly.LowTwoRank.StatedSU 4 q F)} (hw2 : w * w = 1) (hwf : β w = w) :
    IsExoticUni (CFSG.Assembly.LowTwoRank.StatedSU 4 q F) q (MulAut.conj w * β) := by
  obtain ⟨bar, g, hbar, hgu, hgs, hdet, hact⟩ := hβ
  obtain ⟨hbb, -, -, -⟩ := uniDesc_field_facts hF hq bar hbar
  obtain ⟨hWdet, hWunit⟩ := (uniDesc_mem_statedSU_iff bar hbar hbb (w : GL (Fin 4) F)).1 w.2
  have hWW : (w : GL (Fin 4) F) * (w : GL (Fin 4) F) = 1 := congrArg Subtype.val hw2
  have hWWm : ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, hWW, Units.val_one]
  have hWunit' : (((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ *
      ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := hWunit
  have hadjW : (((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ =
      ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    calc (((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ
        = (((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ *
            (((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by rw [hWWm, Matrix.mul_one]
      _ = ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [← Matrix.mul_assoc, hWunit', Matrix.one_mul]
  have hmapW : ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar =
      ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
    calc ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar
        = ((((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
      _ = ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [hadjW]
  have hfix : (w : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.map bar (w : GL (Fin 4) F) * g⁻¹ := by
    have := hact w
    rw [hwf] at this
    exact this
  have h1 : ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) * ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
    have h2 : (w : GL (Fin 4) F) * g = g * Matrix.GeneralLinearGroup.map bar (w : GL (Fin 4) F) := by
      calc (w : GL (Fin 4) F) * g
          = (g * Matrix.GeneralLinearGroup.map bar (w : GL (Fin 4) F) * g⁻¹) * g := by rw [← hfix]
        _ = g * Matrix.GeneralLinearGroup.map bar (w : GL (Fin 4) F) := by group
    have h3 := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F)) h2
    simp only [Units.val_mul, coe_glMap] at h3
    rw [hmapW] at h3
    exact h3
  refine ⟨bar, (w : GL (Fin 4) F) * g, hbar, ?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((g : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ *
          (((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ *
          (((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F))
        = ((g : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ *
            ((((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map bar)ᵀ *
              ((w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * (g : Matrix (Fin 4) (Fin 4) F) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hWunit', Matrix.mul_one, hgu]
  · rw [Units.val_mul, Matrix.transpose_mul, hgs, h1]
  · rw [det_mul_gl, hWdet, one_mul]
    exact hdet
  · intro k
    have hk := hact k
    calc (((MulAut.conj w * β) k : ↥(CFSG.Assembly.LowTwoRank.StatedSU 4 q F)) : GL (Fin 4) F)
        = (w : GL (Fin 4) F) * ((β k : ↥(CFSG.Assembly.LowTwoRank.StatedSU 4 q F)) : GL (Fin 4) F) *
            (w : GL (Fin 4) F)⁻¹ := rfl
      _ = (w : GL (Fin 4) F) * (g * Matrix.GeneralLinearGroup.map bar (k : GL (Fin 4) F) * g⁻¹) *
            (w : GL (Fin 4) F)⁻¹ := by rw [hk]
      _ = ((w : GL (Fin 4) F) * g) * Matrix.GeneralLinearGroup.map bar (k : GL (Fin 4) F) *
            ((w : GL (Fin 4) F) * g)⁻¹ := by group

end ConjUni

section Abstract

variable {K : Type} [Group K]

theorem ExoticFixedGroup.of_congr {S : Type} [Group S] (e : K ≃* S) {β : MulAut K} {z : K} {q : ℕ}
    (h : ExoticFixedGroup (MulAut.congr e β) (e z) q) : ExoticFixedGroup β z q := by
  obtain ⟨Ω, hfix, hs, hp, hc, ⟨E, _, _, hE, ⟨hi⟩⟩, hzf, hzΩ, hall⟩ := h
  have e1 : ↥Ω ≃* ↥(Ω.map e.symm.toMonoidHom) := e.symm.subgroupMap Ω
  have hmem : ∀ k : K, k ∈ Ω.map e.symm.toMonoidHom ↔ e k ∈ Ω := fun k => by
    rw [Subgroup.mem_map_equiv]
    simp
  have hcongr : ∀ k : K, MulAut.congr e β (e k) = e (β k) := fun k => by
    simp [MulAut.congr_apply]
  refine ⟨Ω.map e.symm.toMonoidHom, ?_, e1.symm.isSimpleGroup, ?_, ?_, ⟨E, inferInstance, inferInstance, hE,
    ⟨e1.symm.trans hi⟩⟩, ?_, ?_, ?_⟩
  · intro k hk
    have := hfix (e k) ((hmem k).1 hk)
    rw [hcongr] at this
    exact e.injective this
  · exact Group.IsPerfect.ofSurjective (f := e1.toMonoidHom) e1.surjective
  · rw [Nat.card_congr e1.symm.toEquiv]
    exact hc
  · have := hzf
    rw [hcongr] at this
    exact e.injective this
  · rw [hmem]
    exact hzΩ
  · intro k hk
    have hk' : MulAut.congr e β (e k) = e k := by rw [hcongr, hk]
    rcases hall (e k) hk' with h1 | h1
    · exact Or.inl ((hmem k).2 h1)
    · refine Or.inr ((hmem _).2 ?_)
      rw [map_mul]
      exact h1

theorem congr_conj_mul {S : Type} [Group S] (e : K ≃* S) (w : K) (α : MulAut K) :
    MulAut.congr e (MulAut.conj w * α) = MulAut.conj (e w) * MulAut.congr e α := by
  apply MulEquiv.ext
  intro x
  simp [MulAut.congr_apply, MulAut.conj_apply]

end Abstract

section Consequences

variable {Γ : Type} [Group Γ]

theorem sixteen_dvd_pow_four_sub_one {q : ℕ} (hq : Odd q) : 16 ∣ q ^ 4 - 1 := by
  have hq' : q % 2 = 1 := Nat.odd_iff.1 hq
  have hpos : 0 < q := hq.pos
  have h16 : q ^ 4 % 16 = 1 := by
    have key : ∀ r : Fin 16, r.val % 2 = 1 → r.val ^ 4 % 16 = 1 := by decide
    have := key ⟨q % 16, Nat.mod_lt _ (by norm_num)⟩ (by simp only; omega)
    rw [Nat.pow_mod]
    exact this
  have h1 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hpos
  omega

theorem natCard_pos_aux {q c : ℕ} (hq1 : 1 < q) (hc : c * 2 = q ^ 2 * (q ^ 4 - 1)) : c ≠ 0 := by
  rintro rfl
  have h1 : 1 < q ^ 4 := Nat.one_lt_pow (by norm_num) hq1
  have h2 : 0 < q ^ 2 := by positivity
  have : 0 < q ^ 2 * (q ^ 4 - 1) := Nat.mul_pos h2 (by omega)
  omega

end Consequences

end CFSG.GH74.Generic.S1.Exo
