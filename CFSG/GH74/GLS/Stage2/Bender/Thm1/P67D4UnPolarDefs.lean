module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnSys
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnGamma
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Main

public noncomputable section


namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair

section Defs

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

@[expose] def A2Core.unM2 : twistedGroup σ.toRingHom :=
  Classical.choose ((a2_foldData h φ hφ).exists_fixed_lift₂)

@[expose, reducible] def unM2
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : twistedGroup σ.toRingHom :=
  A2Core.unM2 h.toCore φ hφ

theorem A2Core.unM2_spec :
    a2Phi h φ (unM2 h φ hφ) = unM2 h φ hφ ∧
      ((nHat σ.toRingHom (0 : Fin 2)) * nHat σ.toRingHom (1 : Fin 2) *
        (nHat σ.toRingHom (0 : Fin 2))⁻¹)⁻¹ * unM2 h φ hφ ∈ ⨆ i, hHat σ.toRingHom i :=
  Classical.choose_spec ((a2_foldData h φ hφ).exists_fixed_lift₂)

theorem unM2_spec
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    :
    a2Phi h φ (unM2 h φ hφ) = unM2 h φ hφ ∧
      ((nHat σ.toRingHom (0 : Fin 2)) * nHat σ.toRingHom (1 : Fin 2) *
        (nHat σ.toRingHom (0 : Fin 2))⁻¹)⁻¹ * unM2 h φ hφ ∈ ⨆ i, hHat σ.toRingHom i :=
  A2Core.unM2_spec h.toCore φ hφ

structure A2Core.UnDSpec (D : RankTwoSystem ↥(foldFix (a2Phi h φ)) 3) : Prop where
  root : ∀ k, CFSG.GH74.BNPair.IsRoot 3 k → ∀ x : ↥(foldFix (a2Phi h φ)), x ∈ D.root k ↔
    (x : twistedGroup σ.toRingHom) ∈ foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)) k
  U : ∀ x : ↥(foldFix (a2Phi h φ)), x ∈ D.U ↔
    (x : twistedGroup σ.toRingHom) ∈ posUnipotent (g2Shape (twistedX σ.toRingHom))
  BN : ∀ x : ↥(foldFix (a2Phi h φ)), x ∈ D.B ⊓ D.N ↔
    (x : twistedGroup σ.toRingHom) ∈ ⨆ i, hHat σ.toRingHom i
  B : ∀ x : ↥(foldFix (a2Phi h φ)), x ∈ D.B ↔
    (x : twistedGroup σ.toRingHom) ∈
      (⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))
  lifts : ∃ n₁ n₂ : D.N, (n₁ : D.Weyl) = D.w₁ ∧ (n₂ : D.Weyl) = D.w₂ ∧
    (((n₁ : ↥(foldFix (a2Phi h φ))) : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) =
      nHat σ.toRingHom (1 : Fin 2) ∧
    (((n₂ : ↥(foldFix (a2Phi h φ))) : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) =
      unM2 h φ hφ

abbrev UnDSpec
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (D : RankTwoSystem ↥(foldFix (a2Phi h φ)) 3) : Prop :=
  A2Core.UnDSpec h.toCore φ hφ D

theorem A2Core.unD_exists : ∃ D : RankTwoSystem ↥(foldFix (a2Phi h φ)) 3, UnDSpec h φ hφ D := by
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom h.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom h.cube_apply)
  have h1 := a2_weyl_one_fix h φ hφ
  obtain ⟨D, h₁, h₂, h₃, h₄, h₅⟩ := (a2_foldData h φ hφ).exists_system hgen
    (fun g _ hcomm => a2_hZ h hcomm) (fun x hx => a2_hz h φ hφ x hx) (a2_hC h φ hφ)
    (m₁ := nHat σ.toRingHom (1 : Fin 2)) (m₂ := unM2 h φ hφ) h1
    (by rw [inv_mul_cancel]; exact one_mem _) (unM2_spec h φ hφ).1 (unM2_spec h φ hφ).2
  exact ⟨D, ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

theorem unD_exists
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : ∃ D : RankTwoSystem ↥(foldFix (a2Phi h φ)) 3, UnDSpec h φ hφ D :=
  A2Core.unD_exists h.toCore φ hφ

@[expose] def A2Core.unD : RankTwoSystem ↥(foldFix (a2Phi h φ)) 3 :=
  Classical.choose (unD_exists h φ hφ)

@[expose, reducible] def unD
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : RankTwoSystem ↥(foldFix (a2Phi h φ)) 3 :=
  A2Core.unD h.toCore φ hφ

theorem A2Core.unD_spec : UnDSpec h φ hφ (unD h φ hφ) := Classical.choose_spec (unD_exists h φ hφ)

theorem unD_spec
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : UnDSpec h φ hφ (unD h φ hφ) :=
  A2Core.unD_spec h.toCore φ hφ

end Defs

section Field

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

abbrev UnK (σ : K ≃+* K) : Type := ↥(fixedField σ.toRingHom)

@[expose] def unEps (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c)) : UnK σ ≃+* UnK σ :=
  RingEquiv.ofBijective
    ((ε.toRingHom).restrict (fixedField σ.toRingHom) (fixedField σ.toRingHom) (fun x hx => by
      have hx' : σ x = x := hx
      show σ (ε x) = ε x
      rw [← hεσ, hx']))
    (Finite.injective_iff_bijective.1 (fun a b hab => Subtype.ext (ε.injective (congrArg
      Subtype.val hab))))

theorem coe_unEps (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c)) (a : UnK σ) :
    ((unEps ε hεσ a : UnK σ) : K) = ε (a : K) := rfl

end Field

section SlFix

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

@[expose] def A2Core.unSl : Matrix.SpecialLinearGroup (Fin 2) (UnK σ) →* twistedGroup σ.toRingHom :=
  (slShort σ.toRingHom h.cube_apply).comp
    (Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype)

@[expose, reducible] def unSl
    (h : A2Std σ d q)
    : Matrix.SpecialLinearGroup (Fin 2) (UnK σ) →* twistedGroup σ.toRingHom :=
  A2Core.unSl h.toCore

theorem A2Core.unSl_upper (c : UnK σ) :
    unSl h (sl2Upper c) = slShort σ.toRingHom h.cube_apply (sl2Upper (c : K)) := by
  simp only [unSl, MonoidHom.comp_apply, a2sl_map_upper]

theorem unSl_upper
    (h : A2Std σ d q)
    (c : UnK σ) :
    unSl h (sl2Upper c) = slShort σ.toRingHom h.cube_apply (sl2Upper (c : K)) :=
  A2Core.unSl_upper h.toCore c

theorem A2Core.unSl_lower (c : UnK σ) :
    unSl h (sl2Lower c) = slShort σ.toRingHom h.cube_apply (sl2Lower (c : K)) := by
  simp only [unSl, MonoidHom.comp_apply, a2sl_map_lower]

theorem unSl_lower
    (h : A2Std σ d q)
    (c : UnK σ) :
    unSl h (sl2Lower c) = slShort σ.toRingHom h.cube_apply (sl2Lower (c : K)) :=
  A2Core.unSl_lower h.toCore c

include hφ in
theorem A2Core.unSl_fixed (A : Matrix.SpecialLinearGroup (Fin 2) (UnK σ)) :
    a2Phi h φ (unSl h A) = unSl h A := by
  have hu : ∀ c : UnK σ, a2Phi h φ (unSl h (sl2Upper c)) = unSl h (sl2Upper c) := fun c => by
    rw [unSl_upper, a2Phi_eq_iff h φ hφ]
    exact a2sl_upper_fixed h c.2
  have hl : ∀ c : UnK σ, a2Phi h φ (unSl h (sl2Lower c)) = unSl h (sl2Lower c) := fun c => by
    rw [unSl_lower, a2Phi_eq_iff h φ hφ]
    exact a2sl_lower_fixed h c.2
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod A
  simp only [map_mul]
  rw [hl, hu, hl, hu]

theorem unSl_fixed
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (A : Matrix.SpecialLinearGroup (Fin 2) (UnK σ)) :
    a2Phi h φ (unSl h A) = unSl h A :=
  A2Core.unSl_fixed h.toCore φ hφ A

@[expose] def A2Core.unSlFix :
    Matrix.SpecialLinearGroup (Fin 2) (UnK σ) →* ↥(foldFix (a2Phi h φ)) :=
  (unSl h).codRestrict (foldFix (a2Phi h φ)) (fun A => unSl_fixed h φ hφ A)

@[expose, reducible] def unSlFix
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : Matrix.SpecialLinearGroup (Fin 2) (UnK σ) →* ↥(foldFix (a2Phi h φ)) :=
  A2Core.unSlFix h.toCore φ hφ

theorem A2Core.coe_unSlFix (A : Matrix.SpecialLinearGroup (Fin 2) (UnK σ)) :
    ((unSlFix h φ hφ A : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) = unSl h A := rfl

theorem coe_unSlFix
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (A : Matrix.SpecialLinearGroup (Fin 2) (UnK σ)) :
    ((unSlFix h φ hφ A : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) = unSl h A :=
  A2Core.coe_unSlFix h.toCore φ hφ A

end SlFix

section Aut

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

theorem A2Core.unTau_preserves_fix (ε : K ≃+* K)
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) (x : twistedGroup σ.toRingHom) :
    x ∈ foldFix (a2Phi h φ) ↔ a2Phi h (unTau σ ε) x ∈ foldFix (a2Phi h φ) := by
  rw [mem_foldFix, mem_foldFix]
  have hc := un_tauGamma_comm h ε φ hcomm x
  constructor
  · intro hx
    rw [← hc, hx]
  · intro hx
    exact (a2Phi h (unTau σ ε)).injective (hc.trans hx)

theorem unTau_preserves_fix
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (ε : K ≃+* K)
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) (x : twistedGroup σ.toRingHom) :
    x ∈ foldFix (a2Phi h φ) ↔ a2Phi h (unTau σ ε) x ∈ foldFix (a2Phi h φ) :=
  A2Core.unTau_preserves_fix h.toCore φ ε hcomm x

@[expose] def A2Core.unTauX (ε : K ≃+* K) (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ↥(foldFix (a2Phi h φ)) ≃* ↥(foldFix (a2Phi h φ)) :=
  unRestrictAut (a2Phi h (unTau σ ε)) (foldFix (a2Phi h φ)) (unTau_preserves_fix h φ ε hcomm)

@[expose, reducible] def unTauX
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (ε : K ≃+* K) (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ↥(foldFix (a2Phi h φ)) ≃* ↥(foldFix (a2Phi h φ)) :=
  A2Core.unTauX h.toCore φ ε hcomm

theorem A2Core.coe_unTauX (ε : K ≃+* K) (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (x : ↥(foldFix (a2Phi h φ))) :
    ((unTauX h φ ε hcomm x : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) =
      a2Phi h (unTau σ ε) (x : twistedGroup σ.toRingHom) := rfl

theorem coe_unTauX
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (ε : K ≃+* K) (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y))
    (x : ↥(foldFix (a2Phi h φ))) :
    ((unTauX h φ ε hcomm x : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) =
      a2Phi h (unTau σ ε) (x : twistedGroup σ.toRingHom) :=
  A2Core.coe_unTauX h.toCore φ ε hcomm x

theorem A2Core.unEField_preserves_fix (δ : K ≃+* K)
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) = φ (fieldActor (t := TwistTag.D4) σ δ y))
    (x : twistedGroup σ.toRingHom) :
    x ∈ foldFix (a2Phi h φ) ↔
      a2Phi h (fieldActor (t := TwistTag.D4) σ δ) x ∈ foldFix (a2Phi h φ) := by
  rw [mem_foldFix, mem_foldFix]
  have hc : a2Phi h (fieldActor (t := TwistTag.D4) σ δ) (a2Phi h φ x) =
      a2Phi h φ (a2Phi h (fieldActor (t := TwistTag.D4) σ δ) x) := by
    simp only [a2Phi, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hcomm]
  constructor
  · intro hx
    rw [← hc, hx]
  · intro hx
    exact (a2Phi h (fieldActor (t := TwistTag.D4) σ δ)).injective (hc.trans hx)

theorem unEField_preserves_fix
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (δ : K ≃+* K)
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) = φ (fieldActor (t := TwistTag.D4) σ δ y))
    (x : twistedGroup σ.toRingHom) :
    x ∈ foldFix (a2Phi h φ) ↔
      a2Phi h (fieldActor (t := TwistTag.D4) σ δ) x ∈ foldFix (a2Phi h φ) :=
  A2Core.unEField_preserves_fix h.toCore φ δ hcomm x

@[expose] def A2Core.unFieldX (δ : K ≃+* K)
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ δ y)) :
    ↥(foldFix (a2Phi h φ)) ≃* ↥(foldFix (a2Phi h φ)) :=
  unRestrictAut (a2Phi h (fieldActor (t := TwistTag.D4) σ δ)) (foldFix (a2Phi h φ))
    (unEField_preserves_fix h φ δ hcomm)

@[expose, reducible] def unFieldX
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (δ : K ≃+* K)
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ δ y)) :
    ↥(foldFix (a2Phi h φ)) ≃* ↥(foldFix (a2Phi h φ)) :=
  A2Core.unFieldX h.toCore φ δ hcomm

theorem A2Core.coe_unFieldX (δ : K ≃+* K)
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) = φ (fieldActor (t := TwistTag.D4) σ δ y))
    (x : ↥(foldFix (a2Phi h φ))) :
    ((unFieldX h φ δ hcomm x : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) =
      a2Phi h (fieldActor (t := TwistTag.D4) σ δ) (x : twistedGroup σ.toRingHom) := rfl

theorem coe_unFieldX
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (δ : K ≃+* K)
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) = φ (fieldActor (t := TwistTag.D4) σ δ y))
    (x : ↥(foldFix (a2Phi h φ))) :
    ((unFieldX h φ δ hcomm x : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) =
      a2Phi h (fieldActor (t := TwistTag.D4) σ δ) (x : twistedGroup σ.toRingHom) :=
  A2Core.coe_unFieldX h.toCore φ δ hcomm x

end Aut

end CFSG.GH74.GLS.Stage2.Bender.Thm1
