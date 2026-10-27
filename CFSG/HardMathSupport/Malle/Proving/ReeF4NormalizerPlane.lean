module

public import CFSG.HardMathSupport.Malle.Proving.ReeF4ElemAbelianCoords
public import CFSG.HardMathSupport.Malle.Proving.ReeF4SolvableY0

public section

namespace CFSG.HardMathSupport.Malle.Proving

open CFSG.Open

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem phi_one_eq_zero {Z : Subgroup Y} (φ : Z ≃ Vec5)
    (hφ : ∀ a b : Z, φ (a * b) = φ a + φ b) : φ 1 = 0 := by
  have h := hφ 1 1
  rw [mul_one] at h
  simpa using h

omit [Finite Y] in
theorem symm_zero_eq_one {Z : Subgroup Y} (φ : Z ≃ Vec5)
    (hφ : ∀ a b : Z, φ (a * b) = φ a + φ b) : φ.symm 0 = 1 :=
  φ.symm_apply_eq.mpr (phi_one_eq_zero φ hφ).symm

omit [Finite Y] in
theorem symm_add_eq_mul {Z : Subgroup Y} (φ : Z ≃ Vec5)
    (hφ : ∀ a b : Z, φ (a * b) = φ a + φ b) (v w : Vec5) :
    φ.symm (v + w) = φ.symm v * φ.symm w := by
  rw [Equiv.symm_apply_eq, hφ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[expose] def addHomOf {Z : Subgroup Y} (φ : Z ≃ Vec5) (hφ : ∀ a b : Z, φ (a * b) = φ a + φ b)
    (σ : MulAut Z) : Vec5 →+ Vec5 where
  toFun v := φ (σ (φ.symm v))
  map_zero' := by
    simp only [symm_zero_eq_one φ hφ, map_one, phi_one_eq_zero φ hφ]
  map_add' v w := by
    simp only [symm_add_eq_mul φ hφ, map_mul, hφ]

@[expose] def linOfAdd (f : Vec5 →+ Vec5) : Vec5 →ₗ[ZMod 5] Vec5 where
  toFun := f
  map_add' := f.map_add
  map_smul' c v := by
    show f (c • v) = c • f v
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

@[expose] def linOf {Z : Subgroup Y} (φ : Z ≃ Vec5) (hφ : ∀ a b : Z, φ (a * b) = φ a + φ b)
    (σ : MulAut Z) : Vec5 ≃ₗ[ZMod 5] Vec5 where
  toLinearMap := linOfAdd (addHomOf φ hφ σ)
  invFun v := φ (σ.symm (φ.symm v))
  left_inv v := by simp [linOfAdd, addHomOf]
  right_inv v := by simp [linOfAdd, addHomOf]

omit [Finite Y] in
theorem linOf_apply {Z : Subgroup Y} (φ : Z ≃ Vec5) (hφ : ∀ a b : Z, φ (a * b) = φ a + φ b)
    (σ : MulAut Z) (v : Vec5) : linOf φ hφ σ v = φ (σ (φ.symm v)) := rfl

@[expose] def linHom {Z : Subgroup Y} (φ : Z ≃ Vec5) (hφ : ∀ a b : Z, φ (a * b) = φ a + φ b) :
    MulAut Z →* (Vec5 ≃ₗ[ZMod 5] Vec5) where
  toFun := linOf φ hφ
  map_one' := LinearEquiv.ext fun v => by simp [linOf_apply]
  map_mul' σ τ := LinearEquiv.ext fun v => by simp [linOf_apply]

omit [Finite Y] in
theorem linHom_eq_one_iff {Z : Subgroup Y} (φ : Z ≃ Vec5)
    (hφ : ∀ a b : Z, φ (a * b) = φ a + φ b) (σ : MulAut Z) :
    linHom φ hφ σ = 1 ↔ σ = 1 := by
  constructor
  · intro h
    refine MulEquiv.ext fun z => ?_
    have hv := congrArg (fun e : Vec5 ≃ₗ[ZMod 5] Vec5 => e (φ z)) h
    simp [linHom, linOf_apply] at hv
    simp only [MulAut.one_apply]
    exact hv
  · rintro rfl
    simp

theorem card_linEquiv : Nat.card (Vec5 ≃ₗ[ZMod 5] Vec5) = 480 := by
  have e1 := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) (Fin 2 → ZMod 5)
  have e2 := Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod 5)
  calc Nat.card (Vec5 ≃ₗ[ZMod 5] Vec5)
      = Nat.card (LinearMap.GeneralLinearGroup (ZMod 5) (Fin 2 → ZMod 5)) :=
        (Nat.card_congr e1.symm.toEquiv)
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) :=
        (Nat.card_congr e2.symm.toEquiv)
    _ = 480 := by
        rw [Matrix.card_GL_field]
        simp [ZMod.card, Fin.prod_univ_two]

theorem isSolvable_normalizer_plane {Z T : Subgroup Y} {k : ℕ}
    (hZe : IsElemAbelian 5 Z) (hZc : Nat.card Z = 5 ^ 2)
    (hTc : Nat.card T = 5 ^ k) (hTi : ¬ 5 ∣ T.index)
    (hTN : T ≤ Subgroup.normalizer (Z : Set Y))
    (hTC : T ≤ Subgroup.centralizer (Z : Set Y))
    (hker : Subgroup.normalizer (Z : Set Y) ⊓ Subgroup.centralizer (Z : Set Y) ≤ T) :
    Group.IsSolvable (Subgroup.normalizer (Z : Set Y)) := by
  obtain ⟨φ, hφ⟩ := exists_coord_of_isElemAbelian hZe hZc
  set N := Subgroup.normalizer (Z : Set Y) with hNdef
  let ρ : N →* (Vec5 ≃ₗ[ZMod 5] Vec5) := (linHom φ hφ).comp Z.normalizerMonoidHom
  have hkerρ : ρ.ker = T.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show linHom φ hφ (Z.normalizerMonoidHom x) = 1 ↔ _
    rw [linHom_eq_one_iff, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker,
      Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hker ⟨x.2, h⟩
    · intro h
      exact hTC h
  have hcardRange : Nat.card ↥ρ.range = T.relIndex N := by
    calc Nat.card ↥ρ.range = Nat.card (N ⧸ ρ.ker) :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).symm.toEquiv
      _ = (T.subgroupOf N).index := by rw [← hkerρ]; rfl
      _ = T.relIndex N := rfl
  have hdvdT : T.relIndex N ∣ T.index := ⟨N.index, (Subgroup.relIndex_mul_index hTN).symm⟩
  have hnd5 : ¬ 5 ∣ Nat.card ↥ρ.range := by
    rw [hcardRange]
    exact fun h => hTi (dvd_trans h hdvdT)
  have : Finite (Vec5 ≃ₗ[ZMod 5] Vec5) :=
    Finite.of_injective (fun e : Vec5 ≃ₗ[ZMod 5] Vec5 => (e : Vec5 → Vec5))
      LinearEquiv.coe_injective
  have hsub96 : Nat.card ↥ρ.range ∣ 96 := by
    have h1 : Nat.card ↥ρ.range ∣ 96 * 5 := by
      have h480 := Subgroup.card_subgroup_dvd_card ρ.range
      rw [card_linEquiv] at h480
      rw [show (96 : ℕ) * 5 = 480 by norm_num]
      exact h480
    have hcop : Nat.Coprime (Nat.card ↥ρ.range) 5 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hnd5).symm
    exact hcop.dvd_of_dvd_mul_right h1
  have hsolRange : Group.IsSolvable ↥ρ.range :=
    isSolvable_of_card_dvd (by rw [show (2 : ℕ) ^ 5 * 3 = 96 by norm_num]; exact hsub96)
  have hsolQ : Group.IsSolvable (N ⧸ ρ.ker) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange ρ).symm.surjective
  have hsolT : Group.IsSolvable (T.subgroupOf N) := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hp : IsPGroup 5 (T.subgroupOf N) := by
      apply IsPGroup.of_card (n := k)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hTc]
    have := hp.isNilpotent
    infer_instance
  have hsolK : Group.IsSolvable ↥ρ.ker :=
    Group.isSolvable_of_surjective (f := (MulEquiv.subgroupCongr hkerρ).symm.toMonoidHom)
      (MulEquiv.subgroupCongr hkerρ).symm.surjective
  exact Group.isSolvable_of_subgroup_quotient ρ.ker

end CFSG.HardMathSupport.Malle.Proving
