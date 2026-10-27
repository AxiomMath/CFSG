module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnPolarDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnG1
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnSL2

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair

section Aux

theorem unM1_foldIdx_one : foldIdx 1 = 1 := by decide

theorem unM1_foldIdx_neg_one : foldIdx (-1) = -1 := by decide

variable {k l : Type*} [Field k] [Field l]

theorem unM1_sl2W_eq :
    (unSL2W : Matrix.SpecialLinearGroup (Fin 2) k) = sl2Upper 1 * sl2Lower (-1) * sl2Upper 1 := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LieType.Steinberg.coe_sl2Lower,
    CFSG.LieType.Steinberg.coe_sl2Upper, coe_unSL2W, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem unM1_slMap_W (f : k →+* l) :
    Matrix.SpecialLinearGroup.map f (unSL2W : Matrix.SpecialLinearGroup (Fin 2) k) = unSL2W := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unSL2W]

theorem unM1_slMap_diag (f : k →+* l) (u : kˣ) :
    Matrix.SpecialLinearGroup.map f (unSL2Diag u) = unSL2Diag (Units.map f.toMonoidHom u) := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unSL2Diag]

theorem unM1_slMap_injective {f : k →+* l} (hf : Function.Injective f) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := fun A B hAB => by
  refine Subtype.ext (Matrix.ext fun i j => hf ?_)
  have := congrFun (congrFun (congrArg Subtype.val hAB) i) j
  simpa using this

end Aux

section Short

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem unM1_slShort_W : slShort σ hσ unSL2W = nHat σ (1 : Fin 2) := by
  apply Subtype.ext
  rw [unM1_sl2W_eq, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, slShort_upper,
    slShort_lower]
  change _ = ((nHatE K (ng 1) : adjointGroup d4 K))
  rw [nHatE_one_eq]
  simp only [map_one, map_neg]

theorem unM1_slShort_diag (t : Kˣ) :
    ((slShort σ hσ (unSL2Diag t) : twistedGroup σ) : adjointGroup d4 K) = hShortHom σ t := by
  have hmem := torusElement_mem_rankOne (K := K) (nd 0) t
  have hy : restrictEquiv (rootOperatorFamily d4) cartan_zero_two
      ⟨torusElement d4 K (nd 0) t, hmem⟩ = unSL2Diag t := by
    apply Subtype.ext
    show ((restrictHom (rootOperatorFamily d4) cartan_zero_two ⟨_, hmem⟩ :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
    rw [restrictHom_torusElement cartan_zero_two, coe_unSL2Diag]
  have hs : (restrictEquiv (rootOperatorFamily d4) cartan_zero_two).symm (unSL2Diag t) =
      ⟨torusElement d4 K (nd 0) t, hmem⟩ := by
    rw [MulEquiv.symm_apply_eq, hy]
  simp only [slShort, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hs, phiShortTw_val]
  exact phiShort_torusElement σ t

end Short

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

include hφ in
theorem A2Core.unSlFix_injective : Function.Injective (unSlFix h φ hφ) := by
  intro A B hAB
  have h1 : unSl h A = unSl h B := congrArg Subtype.val hAB
  have h2 := slShort_injective h.cube_apply h1
  exact unM1_slMap_injective Subtype.val_injective h2

include hφ in
theorem A2Core.unSlFix_upper_mem (a : UnK σ) :
    unSlFix h φ hφ (sl2Upper a) ∈ (unD h φ hφ).root 1 := by
  rw [(unD_spec h φ hφ).root 1 ⟨one_ne_zero, by decide⟩, mem_foldRoot, unM1_foldIdx_one]
  exact (un_hex_one_iff h φ hφ _).2 ⟨(a : K), a.2, by rw [coe_unSlFix, unSl_upper]⟩

include hφ in
theorem A2Core.unSlFix_upper_surj {y : ↥(foldFix (a2Phi h φ))} (hy : y ∈ (unD h φ hφ).root 1) :
    ∃ a : UnK σ, y = unSlFix h φ hφ (sl2Upper a) := by
  rw [(unD_spec h φ hφ).root 1 ⟨one_ne_zero, by decide⟩, mem_foldRoot, unM1_foldIdx_one] at hy
  obtain ⟨c, hc, hyc⟩ := (un_hex_one_iff h φ hφ _).1 hy
  exact ⟨⟨c, hc⟩, Subtype.ext (by rw [coe_unSlFix, unSl_upper]; exact hyc)⟩

include hφ in
theorem A2Core.unSlFix_lower_mem (a : UnK σ) :
    unSlFix h φ hφ (sl2Lower a) ∈ (unD h φ hφ).root (-1) := by
  rw [(unD_spec h φ hφ).root (-1) ⟨by norm_num, by decide⟩, mem_foldRoot, unM1_foldIdx_neg_one]
  exact (un_hex_neg_one_iff h φ hφ _).2 ⟨(a : K), a.2, by rw [coe_unSlFix, unSl_lower]⟩

include hφ in
theorem A2Core.unSlFix_w : ((unSlFix h φ hφ unSL2W : ↥(foldFix (a2Phi h φ))) :
    twistedGroup σ.toRingHom) = nHat σ.toRingHom (1 : Fin 2) := by
  rw [coe_unSlFix]
  change slShort σ.toRingHom h.cube_apply (Matrix.SpecialLinearGroup.map
    (fixedField σ.toRingHom).subtype unSL2W) = _
  rw [unM1_slMap_W]
  exact unM1_slShort_W h.cube_apply

theorem unSlFix_w
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : ((unSlFix h φ hφ unSL2W : ↥(foldFix (a2Phi h φ))) :
    twistedGroup σ.toRingHom) = nHat σ.toRingHom (1 : Fin 2) :=
  A2Core.unSlFix_w h.toCore φ hφ

include hφ in
theorem A2Core.unSlFix_diag (u : (UnK σ)ˣ) :
    unSlFix h φ hφ (unSL2Diag u) ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N := by
  rw [(unD_spec h φ hφ).BN, coe_unSlFix]
  refine Subgroup.mem_iSup_of_mem (ng 1) ?_
  rw [hHat, Subgroup.mem_subgroupOf]
  refine ⟨Units.map (fixedField σ.toRingHom).subtype.toMonoidHom u, ?_⟩
  change hShortHom σ.toRingHom _ = ((slShort σ.toRingHom h.cube_apply (Matrix.SpecialLinearGroup.map
    (fixedField σ.toRingHom).subtype (unSL2Diag u)) : twistedGroup σ.toRingHom) :
      adjointGroup d4 K)
  rw [unM1_slMap_diag, unM1_slShort_diag]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
