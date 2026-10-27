module

public import CFSG.GH74.Generic.S1.RAutLin
public import CFSG.GH74.Generic.S1.ROutAbs

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix CFSG.GH74.L5U5 CFSG.GH74.Generic
  CFSG.GH74.Filter.ClassicalOdd Subgroup CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem rinvT_sq : (Matrix.GeneralLinearGroup.inverseTranspose : MulAut (GL (Fin 4) F)) *
    Matrix.GeneralLinearGroup.inverseTranspose = 1 :=
  MulEquiv.ext fun A => Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose A

noncomputable def linAct (F : Type) [Field F] : ℤˣ →* MulAut (GL (Fin 4) F) :=
  MonoidHom.mk' (fun ε => if ε = 1 then 1 else Matrix.GeneralLinearGroup.inverseTranspose) (by
    intro a b
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
      simp [rinvT_sq])

theorem linAct_one : linAct F 1 = 1 := by simp [linAct]

theorem linAct_neg : linAct F (-1) = Matrix.GeneralLinearGroup.inverseTranspose := by
  simp [linAct]

noncomputable def z2Aut (F : Type) [Field F] : ℤˣ →* MulAut SL(4, F) :=
  MonoidHom.mk' (fun ε => if ε = 1 then 1 else CatalogueBGraphForm.slGraphAut 4 F) (by
    intro a b
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
      simp [slGraph_sq])

theorem z2Aut_one : z2Aut F 1 = 1 := by simp [z2Aut]

theorem z2Aut_neg : z2Aut F (-1) = CatalogueBGraphForm.slGraphAut 4 F := by simp [z2Aut]

abbrev LinG (F : Type) [Field F] : Type := GL (Fin 4) F ⋊[linAct F] ℤˣ

theorem linRho_compat [Finite F] (ε : ℤˣ) :
    (CatalogueBHigherLinearAction.slConjugation 4 F).comp (linAct F ε).toMonoidHom =
      (MulAut.conj (z2Aut F ε)).toMonoidHom.comp
        (CatalogueBHigherLinearAction.slConjugation 4 F) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · ext A : 1
    simp [linAct_one, z2Aut_one]
  · ext A : 1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, linAct_neg, z2Aut_neg,
      MulAut.conj_apply]
    have h := slGraph_slConj_slGraph (F := F) A
    have hinv : (CatalogueBGraphForm.slGraphAut 4 F)⁻¹ = CatalogueBGraphForm.slGraphAut 4 F :=
      inv_eq_of_mul_eq_one_right (slGraph_sq 4)
    rw [hinv, ← h]

noncomputable def linRho (F : Type) [Field F] [Finite F] : LinG F →* MulAut SL(4, F) :=
  SemidirectProduct.lift (CatalogueBHigherLinearAction.slConjugation 4 F) (z2Aut F) linRho_compat


theorem linRho_inl [Finite F] (A : GL (Fin 4) F) :
    linRho F (SemidirectProduct.inl A) = CatalogueBHigherLinearAction.slConjugation 4 F A :=
  SemidirectProduct.lift_inl _ _ _ _

theorem linRho_inr [Finite F] (ε : ℤˣ) : linRho F (SemidirectProduct.inr ε) = z2Aut F ε :=
  SemidirectProduct.lift_inr _ _ _ _

theorem linRho_mk [Finite F] (A : GL (Fin 4) F) (ε : ℤˣ) :
    linRho F (⟨A, ε⟩ : LinG F) = CatalogueBHigherLinearAction.slConjugation 4 F A * z2Aut F ε := by
  have : (⟨A, ε⟩ : LinG F) = SemidirectProduct.inl A * SemidirectProduct.inr ε := by
    ext <;> simp
  rw [this, map_mul, linRho_inl, linRho_inr]

noncomputable def quadHom (F : Type) [Field F] [Finite F] : Fˣ →* ℤˣ :=
  @MulChar.toUnitHom F _ ℤ _ (@quadraticChar F _ (Fintype.ofFinite F) (Classical.decEq F))

theorem quadHom_eq_one_iff [Finite F] (u : Fˣ) : quadHom F u = 1 ↔ IsSquare (u : F) := by
  have h1 : ((quadHom F u : ℤˣ) : ℤ) =
      @quadraticChar F _ (Fintype.ofFinite F) (Classical.decEq F) (u : F) := rfl
  rw [← Units.val_eq_one, h1]
  exact @quadraticChar_one_iff_isSquare F _ (Fintype.ofFinite F) (Classical.decEq F) (u : F) u.ne_zero

theorem det_inverseTranspose (A : GL (Fin 4) F) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.inverseTranspose A) =
      (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_inverseTranspose,
    Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem linChi_compat [Finite F] (ε : ℤˣ) :
    ((1 : GL (Fin 4) F →* ℤˣ).prod ((quadHom F).comp Matrix.GeneralLinearGroup.det)).comp
        (linAct F ε).toMonoidHom =
      (MulAut.conj (((MonoidHom.id ℤˣ).prod 1 : ℤˣ →* ℤˣ × ℤˣ) ε)).toMonoidHom.comp
        ((1 : GL (Fin 4) F →* ℤˣ).prod ((quadHom F).comp Matrix.GeneralLinearGroup.det)) := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · ext A : 1
    simp [linAct_one]
  · ext A : 1
    simp [linAct_neg, det_inverseTranspose, Int.units_inv_eq_self]


noncomputable def linChi (F : Type) [Field F] [Finite F] : LinG F →* ℤˣ × ℤˣ :=
  SemidirectProduct.lift
    ((1 : GL (Fin 4) F →* ℤˣ).prod ((quadHom F).comp Matrix.GeneralLinearGroup.det))
    ((MonoidHom.id ℤˣ).prod 1) linChi_compat

theorem linChi_mk [Finite F] (A : GL (Fin 4) F) (ε : ℤˣ) :
    linChi F (⟨A, ε⟩ : LinG F) = (ε, quadHom F (Matrix.GeneralLinearGroup.det A)) := by
  have : (⟨A, ε⟩ : LinG F) = SemidirectProduct.inl A * SemidirectProduct.inr ε := by
    ext <;> simp
  rw [this, map_mul]
  simp [linChi]

noncomputable def rhoK [Finite F] {K : Type} [Group K] (e : K ≃* SL(4, F)) : LinG F →* MulAut K :=
  (MulAut.congr e.symm).toMonoidHom.comp (linRho F)

theorem congr_conj_eq {C : Type} [Group C] (K : Subgroup C) [K.Normal] (e : ↥K ≃* SL(4, F))
    (s : SL(4, F)) :
    MulAut.congr e.symm (MulAut.conj s) = MulAut.conjNormal ((e.symm s : ↥K) : C) := by
  ext k
  have h1 : (MulAut.congr e.symm (MulAut.conj s)) k = e.symm s * k * (e.symm s)⁻¹ := by
    show e.symm (s * e k * s⁻¹) = _
    rw [map_mul, map_mul, map_inv, e.symm_apply_apply]
  rw [h1, MulAut.conjNormal_apply]
  rfl

theorem card_le_two_of_notMem (I : Subgroup (ℤˣ × ℤˣ)) (h : ((-1 : ℤˣ), (1 : ℤˣ)) ∉ I) :
    Nat.card I ≤ 2 := by
  have hY : Nat.card (ℤˣ × ℤˣ) = 2 ^ 2 := by
    rw [Nat.card_prod]
    have : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_two_iff]
      exact ⟨1, -1, by decide, by ext x; rcases Int.units_eq_one_or x with rfl | rfl <;> simp⟩
    rw [this]
    norm_num
  have hd : Nat.card I ∣ 2 ^ 2 := hY ▸ Subgroup.card_subgroup_dvd_card I
  obtain ⟨i, hi, hIi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  by_contra hlt
  push Not at hlt
  have hi2 : i = 2 := by
    by_contra hne
    have : i ≤ 1 := by omega
    have : 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  subst hi2
  have : I = ⊤ := (Subgroup.card_eq_iff_eq_top I).1 (by rw [hIi, hY])
  exact h (this ▸ Subgroup.mem_top _)


theorem det_toGL_jsl : Matrix.GeneralLinearGroup.det
    (Matrix.SpecialLinearGroup.toGL (Jsl : SL(4, F))) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp

theorem outBound_lin [Finite F] (hF : Nat.card F % 4 = 3) {C : Type} [Group C] [Finite C]
    (hC : Gen4 C) (K : Subgroup C) [K.Normal] (e : ↥K ≃* SL(4, F))
    (hcent : centralizer (K : Set C) ≤ K) (T : Subgroup C) (hT : IsPGroup 2 T) :
    (K.subgroupOf T).index ≤ 2 := by
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_mod_four hF
  obtain ⟨a, b, hab⟩ := (odd_field_two_dimensional_quaternion_matrices hF2).1
  let q : Q8 →* SL(2, F) := quatHom hab
  have hq : Function.Injective q := quatHom_injective hF2 hab
  let frameSL : Q8 × Q8 →* SL(4, F) :=
    { toFun := fun p => blkSL4 (q p.1) (q p.2)
      map_one' := by simp [blkSL4_one]
      map_mul' := fun p p' => by simp [blkSL4_mul] }
  have hfr : Function.Injective frameSL := by
    intro p p' h
    have := blkSL4_inj h
    exact Prod.ext (hq this.1) (hq this.2)
  let φ : Q8 × Q8 →* C := K.subtype.comp (e.symm.toMonoidHom.comp frameSL)
  have hφ : Function.Injective φ := K.subtype_injective.comp (e.symm.injective.comp hfr)
  have hφK : ∀ p, φ p ∈ K := fun p => (e.symm (frameSL p)).2
  let g₀ : LinG F := ⟨Matrix.SpecialLinearGroup.toGL (Jsl : SL(4, F)), -1⟩
  have hρg₀ : linRho F g₀ = tauJ F := by
    rw [linRho_mk, slConj_toGL, z2Aut_neg]
    rfl
  have hχg₀ : linChi F g₀ = (-1, 1) := by
    rw [linChi_mk, det_toGL_jsl, map_one]
  have hcover : ∀ t : C, (∃ n : ℕ, t ^ (2 ^ n) = 1) → ∃ g : LinG F,
      rhoK e g = MulAut.conjNormal t := by
    rintro t ⟨n, hn⟩
    set β : MulAut SL(4, F) := MulAut.congr e (MulAut.conjNormal t) with hβ
    have hβn : β ^ (2 ^ n) = 1 := by
      rw [hβ, ← map_pow, ← map_pow, hn, map_one, map_one]
    obtain ⟨A, e', he', hβe⟩ := aut2_lin_form hF β n hβn
    have hback : ∀ f : MulAut ↥K, MulAut.congr e.symm (MulAut.congr e f) = f := by
      intro f
      ext k
      simp [MulAut.congr_apply]
    rcases (by omega : e' = 0 ∨ e' = 1) with rfl | rfl
    · refine ⟨⟨A, 1⟩, ?_⟩
      have : linRho F (⟨A, 1⟩ : LinG F) = β := by
        rw [linRho_mk, z2Aut_one, mul_one, hβe, pow_zero, mul_one]
      show MulAut.congr e.symm (linRho F ⟨A, 1⟩) = _
      rw [this, hβ, hback]
    · refine ⟨⟨A, -1⟩, ?_⟩
      have : linRho F (⟨A, -1⟩ : LinG F) = β := by
        rw [linRho_mk, z2Aut_neg, hβe, pow_one]
      show MulAut.congr e.symm (linRho F ⟨A, -1⟩) = _
      rw [this, hβ, hback]
  have hker : ∀ g : LinG F, linChi F g = 1 → ∃ k : ↥K, rhoK e g = MulAut.conjNormal (k : C) := by
    rintro ⟨A, ε⟩ hg
    rw [linChi_mk] at hg
    simp only [Prod.ext_iff, Prod.fst_one, Prod.snd_one] at hg
    obtain ⟨hε, hd⟩ := hg
    subst hε
    have hsq : IsSquare ((A : Matrix (Fin 4) (Fin 4) F).det) := by
      have := (quadHom_eq_one_iff _).1 hd
      rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
    obtain ⟨s, hs⟩ := slConj_eq_conj_of_isSquare hF A hsq
    refine ⟨e.symm s, ?_⟩
    show MulAut.congr e.symm (linRho F ⟨A, 1⟩) = _
    rw [linRho_mk, z2Aut_one, mul_one, hs, congr_conj_eq]
  have hg₀sq : rhoK e g₀ ^ (2 ^ 1) = 1 := by
    show (MulAut.congr e.symm (linRho F g₀)) ^ (2 ^ 1) = 1
    rw [hρg₀, ← map_pow, pow_one, pow_two, tauJ_sq, map_one]
  have hfix : ∀ p, rhoK e g₀ ⟨φ p, hφK p⟩ = ⟨φ p, hφK p⟩ := by
    intro p
    have h1 : (⟨φ p, hφK p⟩ : ↥K) = e.symm (frameSL p) := rfl
    show MulAut.congr e.symm (linRho F g₀) ⟨φ p, hφK p⟩ = ⟨φ p, hφK p⟩
    rw [hρg₀, h1]
    show e.symm (tauJ F (e (e.symm (frameSL p)))) = e.symm (frameSL p)
    rw [e.apply_symm_apply, show frameSL p = blkSL4 (q p.1) (q p.2) from rfl, blkSL4_fix]
  have hninn : ∀ k : ↥K, rhoK e g₀ ≠ MulAut.conjNormal (k : C) := by
    intro k hk
    apply tauJ_ne_conj (e k)
    have h1 : rhoK e g₀ = MulAut.congr e.symm (tauJ F) := by
      show MulAut.congr e.symm (linRho F g₀) = _
      rw [hρg₀]
    have h2' : MulAut.conjNormal (k : C) = MulAut.congr e.symm (MulAut.conj (e k)) := by
      rw [congr_conj_eq]
      simp
    rw [h1, h2'] at hk
    exact (MulAut.congr e.symm).injective hk
  have hZ : ∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
    intro z hz hzc
    have hcen : e ⟨z, hz⟩ ∈ Subgroup.center SL(4, F) := by
      rw [Subgroup.mem_center_iff]
      intro s
      have := hzc (e.symm s : C) (e.symm s).2
      have h3 : e.symm s * (⟨z, hz⟩ : ↥K) = ⟨z, hz⟩ * e.symm s := Subtype.ext this.symm
      have h4 := congrArg e h3
      simpa using h4
    have h5 := center_pow_four _ hcen
    refine ⟨2, ?_⟩
    have h6 : (⟨z, hz⟩ : ↥K) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h5, map_one]
    have h7 := congrArg Subtype.val h6
    simpa using h7
  have hgrp : ∀ I : Subgroup (ℤˣ × ℤˣ), (∀ y ∈ I, ∃ n : ℕ, y ^ (2 ^ n) = 1) →
      linChi F g₀ ∉ I → Nat.card I ≤ 2 := by
    intro I _ hy
    rw [hχg₀] at hy
    exact card_le_two_of_notMem I hy
  exact index_le_two_of_frame_type hC K hcent (rhoK e) (fun a b => mul_comm a b) (linChi F) hcover hker φ hφ hφK g₀
    ⟨1, hg₀sq⟩ hfix hninn hZ hgrp T hT

end CFSG.GH74.Generic.S1
