module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux10

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section Torus

variable {L : Type} [Field L] [CharP L 2]

theorem HSL_word {ζ : L} (h0 : ζ ≠ 0) :
    (HSL (Units.mk0 ζ h0) : SL2 L) = uSL ζ * vSL ζ⁻¹ * uSL ζ * (uSL 1 * vSL 1 * uSL 1) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_HSL, coe_uSL, coe_vSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, mul_inv_cancel₀ h0, inv_mul_cancel₀ h0, CharTwo.add_self_eq_zero]


theorem torus_word {ζ : L} (h0 : ζ ≠ 0) :
    rootTorusSL2 Tag.F4 L (highRoot Tag.F4) (Units.mk0 ζ h0) =
      pinnedX Tag.F4 L (highRoot Tag.F4) ζ * pinnedX Tag.F4 L (-highRoot Tag.F4) ζ⁻¹ *
        pinnedX Tag.F4 L (highRoot Tag.F4) ζ *
        (pinnedX Tag.F4 L (highRoot Tag.F4) 1 * pinnedX Tag.F4 L (-highRoot Tag.F4) 1 *
          pinnedX Tag.F4 L (highRoot Tag.F4) 1) := by
  rw [rootTorusSL2, HSL_word h0]
  simp only [map_mul, CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo (isRoot_highRoot Tag.F4),
    CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo (isRoot_highRoot Tag.F4)]

theorem hasAct_scalar {ζ : L} (h0 : ζ ≠ 0) :
    HasAct (rootTorusSL2 Tag.F4 L (highRoot Tag.F4) (Units.mk0 ζ h0)) (fun v => ζ • v) := by
  have hθ := isRoot_highRoot Tag.F4
  refine Qθ_map_good
    (φ := (MulAut.conj (rootTorusSL2 Tag.F4 L (highRoot Tag.F4) (Units.mk0 ζ h0))).toMonoidHom)
    (f := fun v => ζ • v) (fun a b => smul_add ζ a b) ?_
  intro α hα c
  have hQ : ∀ w : L, pinnedX Tag.F4 L α w ∈ Qθ Tag.F4 L := fun w => pinnedX_mem_rootSpan hα w
  rcases (CoordAux.mem_radRoots_iff α).1 hα with h | h
  · have hconj := ScalarTorusAux.torus_conj_pinnedX hθ (CoordAux.mem_Deg1.1 h).1
      (Units.mk0 ζ h0) c
    rw [ScalarTorusAux.exponent_of_Deg1 h, zpow_one] at hconj
    have e : (MulAut.conj (rootTorusSL2 Tag.F4 L (highRoot Tag.F4)
        (Units.mk0 ζ h0))).toMonoidHom (pinnedX Tag.F4 L α c) =
        pinnedX Tag.F4 L α (((Units.mk0 ζ h0 : Lˣ) : L) * c) := hconj
    rw [e, Units.val_mk0]
    refine ⟨hQ _, ?_⟩
    rw [(heisCoord_spec Tag.F4 L).pinnedX_deg1 α h, (heisCoord_spec Tag.F4 L).pinnedX_deg1 α h]
    ext β
    by_cases hβ : β = α
    · subst hβ
      simp
    · simp [Pi.single_apply, hβ]
  · subst h
    have hconj := ScalarTorusAux.torus_conj_pinnedX hθ hθ (Units.mk0 ζ h0) c
    have e : (MulAut.conj (rootTorusSL2 Tag.F4 L (highRoot Tag.F4)
        (Units.mk0 ζ h0))).toMonoidHom (pinnedX Tag.F4 L (highRoot Tag.F4) c) =
        pinnedX Tag.F4 L (highRoot Tag.F4) (((Units.mk0 ζ h0 ^
          (2 * CFSG.LieType.Steinberg.Adjoint.iform (highRoot Tag.F4) (highRoot Tag.F4) /
            CFSG.LieType.Steinberg.Adjoint.iform (highRoot Tag.F4) (highRoot Tag.F4)) : Lˣ) : L)
          * c) := hconj
    rw [e]
    refine ⟨hQ _, ?_⟩
    rw [(heisCoord_spec Tag.F4 L).pinnedX_highRoot, (heisCoord_spec Tag.F4 L).pinnedX_highRoot,
      smul_zero]

end Torus

section Main

open CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K] [Finite K] [CharP K 2] (D : LangLevi Tag.F4 K wF4)

theorem eth_mem {H : Subgroup (ModGL Tag.F4 K)} (h1 : D.frame TwClass.f4Six.S₁ ≤ H) {c : D.L}
    (hc : D.Fr c = c) : pinnedX Tag.F4 D.L (highRoot Tag.F4) c ∈ H.map (Θ D) :=
  mem_map_Θ D h1 (pinnedX_mem_rootSpan θ_mem_S₁ c) (sig_th hc)

theorem ethn_mem {H : Subgroup (ModGL Tag.F4 K)} (h1 : D.frame TwClass.f4Six.S₁ ≤ H) {c : D.L}
    (hc : D.Fr c = c) : pinnedX Tag.F4 D.L (-highRoot Tag.F4) c ∈ H.map (Θ D) :=
  mem_map_Θ D h1 (pinnedX_mem_rootSpan negθ_mem_S₁ c) (sig_thn hc)

theorem escal_mem {H : Subgroup (ModGL Tag.F4 K)} (h1 : D.frame TwClass.f4Six.S₁ ≤ H)
    {ζ : D.L} (hζ : D.Fr ζ = ζ) (h0 : ζ ≠ 0) :
    ∃ h ∈ H.map (Θ D), sigHom D.Fr h = h ∧ HasAct h (fun v => ζ • v) := by
  have hζi : D.Fr ζ⁻¹ = ζ⁻¹ := by rw [map_inv₀, hζ]
  have h1' : D.Fr (1 : D.L) = 1 := map_one _
  refine ⟨rootTorusSL2 Tag.F4 D.L (highRoot Tag.F4) (Units.mk0 ζ h0), ?_, ?_, hasAct_scalar h0⟩
  · rw [torus_word h0]
    exact mul_mem (mul_mem (mul_mem (eth_mem D h1 hζ) (ethn_mem D h1 hζi)) (eth_mem D h1 hζ))
      (mul_mem (mul_mem (eth_mem D h1 h1') (ethn_mem D h1 h1')) (eth_mem D h1 h1'))
  · rw [torus_word h0]
    simp only [map_mul, sig_th hζ, sig_thn hζi, sig_th h1', sig_thn h1']

theorem elts {H : Subgroup (ModGL Tag.F4 K)} (h1 : D.frame TwClass.f4Six.S₁ ≤ H)
    (h2 : D.frame TwClass.f4Six.S₂ ≤ H) : Elts D.Fr (H.map (Θ D)) where
  eg5 := fun c hc => mem_map_Θ D h2 (pinnedX_mem_rootSpan g5_mem_S₂ c) (sig_g5 hc)
  eg5n := fun c hc => mem_map_Θ D h2 (pinnedX_mem_rootSpan g5n_mem_S₂ c) (sig_g5n hc)
  eu := fun s c hs hc => mem_map_Θ D h2 (mul_mem (mul_mem (pinnedX_mem_rootSpan a3_mem_S₂ s)
    (pinnedX_mem_rootSpan a4_mem_S₂ _)) (pinnedX_mem_rootSpan g5_mem_S₂ c)) (sig_u hs hc)
  eth := fun c hc => eth_mem D h1 hc
  ethn := fun c hc => ethn_mem D h1 hc
  er := fun b z hb hz => mem_map_Θ D h1 (mul_mem (mul_mem (pinnedX_mem_rootSpan rS_mem_S₁ b)
    (pinnedX_mem_rootSpan pS_mem_S₁ _)) (pinnedX_mem_rootSpan θ_mem_S₁ z)) (sig_r hb hz)
  escal := fun _ hζ h0 => escal_mem D h1 hζ h0

theorem sf_of_sig {L : Type} [Field L] [CharP L 2] {Fr : L →+* L} {q : ModGL Tag.F4 L}
    (hq : q ∈ Qθ Tag.F4 L) (hs : sigHom Fr q = q) :
    ∀ ν, heisCoord Tag.F4 L q ν = Fr (heisCoord Tag.F4 L q (wF4⁻¹ • ν)) := by
  intro ν
  have h1 := (sig_Qθ Fr q hq).2
  rw [hs] at h1
  exact congrFun h1 ν

theorem supp_of_Qθ {L : Type} [Field L] [CharP L 2] {q : ModGL Tag.F4 L}
    (hq : q ∈ Qθ Tag.F4 L) : Supp (heisCoord Tag.F4 L q) :=
  fun ν hν => (heisCoord_spec Tag.F4 L).support q hq ν hν

theorem exists_r {L : Type} [Field L] [CharP L 2] {Fr : L →+* L}
    (hsurj : ∀ n : L, ∃ z, z + Fr z = n) {b : L} (hb : InE Fr b) :
    ∃ y : ModGL Tag.F4 L, y ∈ Qθ Tag.F4 L ∧ heisCoord Tag.F4 L y = fv Fr rS b ∧
      sigHom Fr y = y ∧ y ∈ rootSpan Tag.F4 L TwClass.f4Six.S₁ := by
  obtain ⟨zz, hzz⟩ := hsurj (b * Fr b)
  obtain ⟨hyQ, hyc⟩ := heisCoord_r (Fr := Fr) b zz
  exact ⟨_, hyQ, hyc, sig_r hb hzz, mul_mem (mul_mem (pinnedX_mem_rootSpan rS_mem_S₁ b)
    (pinnedX_mem_rootSpan pS_mem_S₁ _)) (pinnedX_mem_rootSpan θ_mem_S₁ zz)⟩

theorem exists_same_coords {L : Type} [Field L] [CharP L 2] {Fr : L →+* L}
    (hsurj : ∀ n : L, ∃ z, z + Fr z = n) {q : ModGL Tag.F4 L} (hq : q ∈ Qθ Tag.F4 L)
    (hs : sigHom Fr q = q)
    (h1 : (crd (heisCoord Tag.F4 L q)).a1 = 0) (h2 : (crd (heisCoord Tag.F4 L q)).a2 = 0)
    (h3 : (crd (heisCoord Tag.F4 L q)).a3 = 0) (h4 : (crd (heisCoord Tag.F4 L q)).b12 = 0)
    (h5 : (crd (heisCoord Tag.F4 L q)).b13 = 0) (h6 : (crd (heisCoord Tag.F4 L q)).b23 = 0) :
    ∃ y : ModGL Tag.F4 L, y ∈ Qθ Tag.F4 L ∧ y ∈ rootSpan Tag.F4 L TwClass.f4Six.S₁ ∧
      heisCoord Tag.F4 L y = heisCoord Tag.F4 L q := by
  have hsf := sf_of_sig hq hs
  obtain ⟨hE0, -⟩ := crd_E hsf
  obtain ⟨y, hyQ, hyc, hys, hyS⟩ := exists_r hsurj hE0
  refine ⟨y, hyQ, hyS, ?_⟩
  refine eq_of_crd (Fr := Fr) (supp_of_Qθ hyQ) (supp_of_Qθ hq) (sf_of_sig hyQ hys) hsf ?_
  have hc : crd (heisCoord Tag.F4 L q) = ⟨(crd (heisCoord Tag.F4 L q)).s, 0, 0, 0, 0, 0, 0⟩ :=
    T7.ext rfl h1 h2 h3 h4 h5 h6
  rw [hyc, crd_fv_rS]
  exact hc.symm

theorem mul_inv_mem_Uθ {L : Type} [Field L] {z y : ModGL Tag.F4 L} (hz : z ∈ Qθ Tag.F4 L)
    (hy : y ∈ Qθ Tag.F4 L) (h : heisCoord Tag.F4 L z = heisCoord Tag.F4 L y) :
    z * y⁻¹ ∈ Uθ Tag.F4 L := by
  have hd : z * y⁻¹ ∈ Qθ Tag.F4 L := mul_mem hz (inv_mem hy)
  have hd0 : heisCoord Tag.F4 L (z * y⁻¹) = 0 := by
    rw [(heisCoord_spec Tag.F4 L).mul _ hz _ (inv_mem hy), heisCoord_inv hy, h, add_neg_cancel]
  exact ((heisCoord_spec Tag.F4 L).eq_zero_iff _ hd).1 hd0

theorem mem_rootSpan_of_Uθ {L : Type} [Field L] {S : Set (Fin Tag.F4.rank → ℤ)}
    (hθ : highRoot Tag.F4 ∈ S) {z y : ModGL Tag.F4 L} (hdU : z * y⁻¹ ∈ Uθ Tag.F4 L)
    (hy : y ∈ rootSpan Tag.F4 L S) : z ∈ rootSpan Tag.F4 L S := by
  have h : (z * y⁻¹) * y ∈ rootSpan Tag.F4 L S :=
    mul_mem (rootSubgroup_le_rootSpan_of_mem hθ hdU) hy
  simpa using h

theorem six_coords (hsurj : ∀ n : D.L, ∃ z, z + D.Fr z = n) {H : Subgroup (ModGL Tag.F4 K)}
    (hHG : H ≤ adjointGroup Tag.F4 K) {m : ModGL Tag.F4 K} (hmH : m ∈ H)
    (hmQ : m ∈ Qθ Tag.F4 K) (hmX : m ∉ D.frame TwClass.f4Six.S₁) :
    (crd (heisCoord Tag.F4 D.L (Θ D m))).a1 ≠ 0 ∨ (crd (heisCoord Tag.F4 D.L (Θ D m))).a2 ≠ 0 ∨
      (crd (heisCoord Tag.F4 D.L (Θ D m))).a3 ≠ 0 ∨
      (crd (heisCoord Tag.F4 D.L (Θ D m))).b12 ≠ 0 ∨
      (crd (heisCoord Tag.F4 D.L (Θ D m))).b13 ≠ 0 ∨
      (crd (heisCoord Tag.F4 D.L (Θ D m))).b23 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha1, ha2, ha3, hb12, hb13, hb23⟩ := hcon
  have hzQ := Θ_mem_Qθ D hmQ
  obtain ⟨y, hyQ, hyS, hyc⟩ := exists_same_coords hsurj hzQ (sig_Θ D m) ha1 ha2 ha3 hb12 hb13 hb23
  exact hmX ((mem_frame_iff' D _ m).2 ⟨hHG hmH,
    mem_rootSpan_of_Uθ θ_mem_S₁ (mul_inv_mem_Uθ hzQ hyQ hyc.symm) hyS⟩)

theorem Qθ_le_of_notmem (hK3 : 3 ≤ Nat.card K) {H : Subgroup (ModGL Tag.F4 K)}
    (hHG : H ≤ adjointGroup Tag.F4 K) (h1 : D.frame TwClass.f4Six.S₁ ≤ H)
    (h2 : D.frame TwClass.f4Six.S₂ ≤ H) {m : ModGL Tag.F4 K} (hmH : m ∈ H)
    (hmQ : m ∈ Qθ Tag.F4 K) (hmX : m ∉ D.frame TwClass.f4Six.S₁) : Qθ Tag.F4 K ≤ H := by
  obtain ⟨AD⟩ := exists_actData D.L
  have hsurj := hsurj_L D (by omega)
  have hcore := core AD (elts D h1 h2) hsurj (exists_zeta D hK3)
    ⟨Θ D m, ⟨m, hmH, rfl⟩, Θ_mem_Qθ D hmQ, sig_Θ D m, six_coords D hsurj hHG hmH hmQ hmX⟩
  intro q hq
  obtain ⟨h, hh, hΘ⟩ := hcore (Θ D q) (Θ_mem_Qθ D hq) (sig_Θ D q)
  rw [← Θ_injective D hΘ]
  exact hh

end Main

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

