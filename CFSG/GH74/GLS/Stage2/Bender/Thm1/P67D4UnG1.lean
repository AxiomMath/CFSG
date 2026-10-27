module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Phi
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnS1

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

section Hex

theorem un_hexPos_one : hexPos 1 = Pi.single (ng 1) 1 := by
  funext i
  fin_cases i <;> rfl

theorem un_hexPos_neg_one : hexPos (-1) = -Pi.single (ng 1) 1 := by
  funext i
  fin_cases i <;> rfl

theorem A2Core.un_hex_pm_iff (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {s : ℤ} (hs : s = 1 ∨ s = -1) (x : twistedGroup σ.toRingHom) :
    (x ∈ hexGroup (twistedX σ.toRingHom) s ∧ a2Phi h φ x = x) ↔
      ∃ c : K, σ c = c ∧ ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
        xOuter s c (σ.toRingHom c) (σ.toRingHom (σ.toRingHom c)) := by
  have hσ := h.cube_apply
  have hα := isRoot_smul_single hs (nd 0)
  have hp : proj (s • Pi.single (nd 0) 1 : Fin d4.rank → ℤ) = hexPos s := by
    rcases hs with rfl | rfl
    · rw [one_smul, proj_single_zero, un_hexPos_one]
    · rw [neg_one_smul, proj_neg_single_zero, un_hexPos_neg_one]
  have hne := rho_smul_single_ne hs (i := nd 0) (by decide)
  have hχ : a2Char d (s • Pi.single (nd 0) 1) = 1 := a2sl_char_outer d (by decide)
  have hmem := mem_twistedRootSubgroupD4_iff_of_orbit (σ := σ.toRingHom) hσ hα hp hne
  constructor
  · rintro ⟨hx, hfix⟩
    obtain ⟨c, hc⟩ := (hmem ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K)).1 hx
    have hfix' := (a2Phi_eq_iff h φ hφ x).1 hfix
    rw [hc, a2Conj_xOrbit h hα hne, hχ, one_mul] at hfix'
    have hσc := xOrbit_injective σ.toRingHom hα hne (Subtype.ext hfix')
    refine ⟨c, hσc, ?_⟩
    rw [hc, xOrbit_smul_single σ.toRingHom hs]
  · rintro ⟨c, hc, hxc⟩
    have hc' : σ.toRingHom c = c := hc
    have hxc' : ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K) =
        xOrbit σ.toRingHom (s • Pi.single (nd 0) 1) c := by
      rw [xOrbit_smul_single σ.toRingHom hs]
      exact hxc
    refine ⟨(hmem ((x : twistedGroup σ.toRingHom) : adjointGroup d4 K)).2 ⟨c, hxc'⟩, ?_⟩
    rw [a2Phi_eq_iff h φ hφ, hxc', a2Conj_xOrbit h hα hne, hχ, one_mul, hc]

theorem A2Core.un_hex_one_iff (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (x : twistedGroup σ.toRingHom) :
    (x ∈ hexGroup (twistedX σ.toRingHom) 1 ∧ a2Phi h φ x = x) ↔
      ∃ c : K, σ c = c ∧ x = slShort σ.toRingHom h.cube_apply (sl2Upper c) := by
  rw [un_hex_pm_iff h φ hφ (Or.inl rfl) x]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [← slShort_upper h.cube_apply c]
  exact Subtype.ext_iff.symm

theorem A2Core.un_hex_neg_one_iff (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (x : twistedGroup σ.toRingHom) :
    (x ∈ hexGroup (twistedX σ.toRingHom) (-1) ∧ a2Phi h φ x = x) ↔
      ∃ c : K, σ c = c ∧ x = slShort σ.toRingHom h.cube_apply (sl2Lower c) := by
  rw [un_hex_pm_iff h φ hφ (Or.inr rfl) x]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [← slShort_lower h.cube_apply c]
  exact Subtype.ext_iff.symm

end Hex

section Torus

omit
  [Finite K] in
theorem un_rootDiag_conj_xUnit (c : Fin d4.rank → Kˣ) (j : Fin d4.rank) (u : K) :
    rootDiagUnit TwistTag.D4.tag c * xUnit TwistTag.D4.tag K j u *
      (rootDiagUnit TwistTag.D4.tag c)⁻¹ = xUnit TwistTag.D4.tag K j ((c j : K) * u) := by
  have h := rootDiagUnit_conj_pinnedX c (isRoot_single TwistTag.D4.tag j) u
  rwa [pinnedX_single, pinnedX_single, a2_rootChar_single] at h

omit
  [Finite K] in
theorem un_rootDiag_conj_yUnit (c : Fin d4.rank → Kˣ) (j : Fin d4.rank) (u : K) :
    rootDiagUnit TwistTag.D4.tag c * yUnit TwistTag.D4.tag K j u *
      (rootDiagUnit TwistTag.D4.tag c)⁻¹ = yUnit TwistTag.D4.tag K j (((c j)⁻¹ : Kˣ) * u) := by
  have h := rootDiagUnit_conj_pinnedX c (isRoot_neg_single TwistTag.D4.tag j) u
  have e : rootChar (τ := TwistTag.D4.tag) c (-Pi.single j 1) = (c j)⁻¹ := by
    have h1 := rootChar_add c (Pi.single j 1) (-Pi.single j 1)
    rw [add_neg_cancel, rootChar_zero, a2_rootChar_single] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  rwa [pinnedX_neg_single, pinnedX_neg_single, e] at h

theorem A2Core.un_torus_slShort (h : A2Core σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {t : twistedGroup σ.toRingHom} (ht : t ∈ ⨆ i, hHat σ.toRingHom i) (htf : a2Phi h φ t = t) :
    ∃ χ : K, σ χ = χ ∧ χ ≠ 0 ∧ ∀ c : K, σ c = c →
      t * slShort σ.toRingHom h.cube_apply (sl2Upper c) * t⁻¹ =
        slShort σ.toRingHom h.cube_apply (sl2Upper (χ * c)) ∧
      t * slShort σ.toRingHom h.cube_apply (sl2Lower c) * t⁻¹ =
        slShort σ.toRingHom h.cube_apply (sl2Lower (χ⁻¹ * c)) := by
  have hσ := h.cube_apply
  obtain ⟨b, hbt, b1, b3, -, -⟩ := a2_torus_coord h (a2_mem_hHatE_iSup t ht)
  have hfix : ∀ i, Units.map σ.toRingHom.toMonoidHom (b i) = b i := by
    have h1 := (a2Phi_eq_iff h φ hφ t).1 htf
    rw [hbt, a2tor_conj_rootDiagUnit] at h1
    exact fun i => congrFun (rootDiagUnit_injective h1) i
  have e1 : b (nd 1) = b (nd 0) := b1.trans (hfix _)
  have e3 : b (nd 3) = b (nd 0) := by rw [b3, e1, hfix]
  have hσχ : σ.toRingHom ((b (nd 0) : Kˣ) : K) = ((b (nd 0) : Kˣ) : K) :=
    congrArg Units.val (hfix _)
  refine ⟨((b (nd 0) : Kˣ) : K), hσχ, (b (nd 0)).ne_zero, fun c hc => ?_⟩
  have hc' : σ.toRingHom c = c := hc
  have key : ∀ x y z : ModGL TwistTag.D4.tag K,
      rootDiagUnit TwistTag.D4.tag b * (x * y * z) * (rootDiagUnit TwistTag.D4.tag b)⁻¹ =
        (rootDiagUnit TwistTag.D4.tag b * x * (rootDiagUnit TwistTag.D4.tag b)⁻¹) *
        (rootDiagUnit TwistTag.D4.tag b * y * (rootDiagUnit TwistTag.D4.tag b)⁻¹) *
        (rootDiagUnit TwistTag.D4.tag b * z * (rootDiagUnit TwistTag.D4.tag b)⁻¹) :=
    fun x y z => by group
  constructor
  · refine Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hbt, un_coe_slShort_upper hσ, un_coe_slShort_upper hσ, key, un_rootDiag_conj_xUnit,
      un_rootDiag_conj_xUnit, un_rootDiag_conj_xUnit, e1, e3]
    simp only [map_mul, hσχ, hc']
  · refine Subtype.ext (Subtype.ext ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hbt, un_coe_slShort_lower hσ, un_coe_slShort_lower hσ, key, un_rootDiag_conj_yUnit,
      un_rootDiag_conj_yUnit, un_rootDiag_conj_yUnit, e1, e3]
    simp only [map_mul, map_inv₀, hσχ, hc', Units.val_inv_eq_inv_val]

end Torus

end CFSG.GH74.GLS.Stage2.Bender.Thm1
