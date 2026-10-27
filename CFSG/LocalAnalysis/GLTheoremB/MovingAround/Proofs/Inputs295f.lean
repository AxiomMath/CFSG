module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295f

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false

section Matrices

open Matrix

variable {L : Type} [Field L]

@[expose] noncomputable def kysDiagSL (r : L) (hr : r ^ 3 = 1) : SL(3, L) :=
  ⟨Matrix.diagonal ![1, r, r ^ 2], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_mul]
    rw [← pow_succ']
    exact hr⟩

@[expose] noncomputable def kysCycSL : SL(3, L) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem coe_kysDiagSL (r : L) (hr : r ^ 3 = 1) :
    ((kysDiagSL r hr : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![1, r, r ^ 2] :=
  rfl

theorem coe_kysCycSL :
    ((kysCycSL : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = !![0, 0, 1; 1, 0, 0; 0, 1, 0] :=
  rfl

theorem kys_commutator_diag_cyc (r : L) (hr : r ^ 3 = 1) {X : SL(3, L)}
    (hX : (X : Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) r) :
    ⁅kysDiagSL r hr, kysCycSL⁆ = X := by
  have h : kysDiagSL r hr * kysCycSL = X * (kysCycSL * kysDiagSL r hr) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hX, coe_kysDiagSL, coe_kysCycSL]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp <;>
      first | ring1 | linear_combination hr | linear_combination (-1 : L) * hr
  rw [commutatorElement_def, h]
  group

theorem kys_stdUnitary_eq_self (σ : L →+* L) {ν : ℕ} (X : SL(ν, L))
    (hX : ((X : Matrix (Fin ν) (Fin ν) L).map σ)ᵀ * (X : Matrix (Fin ν) (Fin ν) L) = 1) :
    stdUnitary σ X = X := by
  apply Subtype.ext
  rw [coe_stdUnitary]
  have h1 : ((X : Matrix (Fin ν) (Fin ν) L).map σ)⁻¹ = (X : Matrix (Fin ν) (Fin ν) L)ᵀ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.transpose_transpose ((X : Matrix (Fin ν) (Fin ν) L).map σ),
      ← Matrix.transpose_mul, hX, Matrix.transpose_one]
  rw [h1, Matrix.transpose_transpose]

theorem kys_stdUnitary_kysDiagSL (σ : L →+* L) (r : L) (hr : r ^ 3 = 1) (hσr : σ r * r = 1) :
    stdUnitary σ (kysDiagSL r hr) = kysDiagSL r hr := by
  refine kys_stdUnitary_eq_self σ _ ?_
  rw [coe_kysDiagSL, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext k
  fin_cases k
  · simp
  · simpa using hσr
  · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.reduceFinMk,
      Fin.isValue, map_pow]
    rw [← mul_pow, hσr, one_pow]

theorem kys_stdUnitary_kysCycSL (σ : L →+* L) : stdUnitary σ (kysCycSL : SL(3, L)) = kysCycSL := by
  refine kys_stdUnitary_eq_self σ _ ?_
  have hmap : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) L).map σ =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [coe_kysCycSL, hmap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end Matrices

section LangFrame

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem kys_exists_lang_frame_conj (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ σQ : L ≃+* L,
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)))) ∧
      ∃ z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom ta)),
        ∀ X : SL(ν, L), iterHom S.D.step
            (componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) (z * ψ X * z⁻¹) =
          z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := hchar
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ a b) c) = pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := CFSG.SectionRank.OddCover.diagHom ν d *
    (CFSG.RankThree.Classical.permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) =
          (CFSG.SectionRank.OddCover.diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) *
            Y * ((CFSG.RankThree.Classical.permGL π : GL (Fin ν) L) :
              Matrix (Fin ν) (Fin ν) L)) *
              (↑(CFSG.SectionRank.OddCover.diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(ν, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      field_simp
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S hs0
    (fun γ hγ => outer_iterate_mem_kernelRoots S hT s hγ) (Subgroup.mem_sup_right hy₁)
  refine ⟨σQ, hσc, z, hzZ, fun X => ?_⟩
  change Fs (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹
  rw [← hstd X, map_mul, map_mul, map_inv, hz]
  group

end LangFrame

section Stable


theorem kys_rootDiagUnit_mem_Gamma_of_stable
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)
    {ta : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus)
    (hap : ∀ j, ta j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 ta ≠ 1)
    (i : KernelComponent (rootCharHom ta))
    (hi6 : (componentRoots (rootCharHom ta) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin 3))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1)
    (h3q : 3 ∣ S.D.q + 1) :
    rootDiagUnit Tag.E6 ta ∈ S.Γ := by
  classical
  obtain ⟨σQ, hσc, z, hzZ, hconj⟩ :=
    kys_exists_lang_frame_conj S hT i le_rfl hψ hΨ π hπ hr hchar he hq
  rw [hs1, Nat.mul_one] at hσc
  have hFs1 : ∀ x, iterHom S.D.step
      (componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) x = S.D.step x := fun x => by
    rw [hs1]
    rfl
  have hd : rootDiagUnit Tag.E6 ta ∈ (Subgroup.center SL(3, L)).map ψ := by
    rw [map_center_frame_eq_zpowers_rootDiagUnit hap h1 i hi6 hψ hΨ]
    exact Subgroup.mem_zpowers _
  obtain ⟨X₀, hX₀c, hX₀d⟩ := Subgroup.mem_map.1 hd
  obtain ⟨r₀, hr₀3, hr₀X⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hX₀c
  rw [Fintype.card_fin] at hr₀3
  have hσr : σQ.toRingHom r₀ * r₀ = 1 := by
    obtain ⟨k, hk⟩ := h3q
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσc, ← pow_succ, ← hq, hk, pow_mul,
      hr₀3, one_pow]
  have hψS : ∀ X, ψ X ∈ rootSpan Tag.E6 L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hnorm := mem_componentRootSpan_iff_conj_of_mem hzZ
  have hθM : ∀ X : SL(3, L), stdUnitary σQ.toRingHom X = X → z * ψ X * z⁻¹ ∈ S.D.model := by
    intro X hX
    refine (S.D.mem_model).2 ⟨rootSpan_le_adjointGroup L _ ((hnorm i _).1 (hψS X)), ?_⟩
    have h2 := hconj X
    rw [hFs1, hX] at h2
    exact h2
  have hx := hθM _ (kys_stdUnitary_kysDiagSL _ r₀ hr₀3 hσr)
  have hy := hθM _ (kys_stdUnitary_kysCycSL σQ.toRingHom)
  have hmem := Subgroup.commutator_mem_commutator hx hy
  have e1 : ⁅z * ψ (kysDiagSL r₀ hr₀3) * z⁻¹, z * ψ kysCycSL * z⁻¹⁆ =
      z * ψ ⁅kysDiagSL r₀ hr₀3, kysCycSL⁆ * z⁻¹ := by
    simp only [commutatorElement_def, map_mul, map_inv]
    group
  rw [e1, kys_commutator_diag_cyc r₀ hr₀3 hr₀X.symm, hX₀d] at hmem
  have hzd : rootDiagUnit Tag.E6 ta * z = z * rootDiagUnit Tag.E6 ta :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.CubeCentre.rootDiagUnit_mul_comm_of_mem_Z
      ta hzZ
  have e2 : z * rootDiagUnit Tag.E6 ta * z⁻¹ = rootDiagUnit Tag.E6 ta := by
    rw [← hzd, mul_inv_cancel_right]
  rw [e2] at hmem
  exact hmem

end Stable

section A2Out


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ} {h : twistedE6InndiagGL K σ}

theorem kys_orbit_three_of_outer (D : TwE6LineLang K σ q h) (hdim : twE6MatFixDim K σ h = 24)
    (hq3 : 3 ∣ q + 1) (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ) :
    (∀ i : KernelComponent (rootCharHom D.a),
      (componentRoots (rootCharHom D.a) i).ncard = 6) ∧
    ∀ i : KernelComponent (rootCharHom D.a),
      componentOrbitLength D.S.ρ (componentRoots (rootCharHom D.a) i) = 3 ∧
        rationalRoots D.S.ρ (rootCharHom D.a) i = kernelRoots (rootCharHom D.a) := by
  classical
  obtain ⟨c, hc, hc6⟩ :=
    kernel_classes_of_ncard_eighteen D.hL3 D.hap (D.ncard_kernelRoots_a2out hdim)
  have hi6 : ∀ i : KernelComponent (rootCharHom D.a),
      (componentRoots (rootCharHom D.a) i).ncard = 6 := by
    intro i
    obtain ⟨k, rfl⟩ := hc.2 i
    exact hc6 k
  refine ⟨hi6, ?_⟩
  rcases orbit_dichotomy D.S D.hT hc with ⟨i, hi⟩ | hall
  · exfalso
    obtain ⟨ψ, σ', π, hψ, hΨ, hπ⟩ := exists_unitary_frame_of_odd_orbit D.S D.hL3 D.hT D.hap
      D.h1 i (hi6 i) (by rw [hi]) (D.three_dvd_sq hq3)
    have hΓ : rootDiagUnit Tag.E6 D.a ∈ D.S.Γ :=
      kys_rootDiagUnit_mem_Gamma_of_stable D.S D.hT D.hap D.h1 i (hi6 i) hψ hΨ π hπ D.hℓ D.hchar
        D.he D.hSq hi (D.three_dvd_sq hq3)
    exact hout (D.conj_mem_inner_of_mem_Gamma hΓ)
  · exact hall

theorem kys_rationalComponent_psu_model (D : TwE6LineLang K σ q h)
    (hdim : twE6MatFixDim K σ h = 24) (hq3 : 3 ∣ q + 1)
    (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ)
    (i : KernelComponent (rootCharHom D.a)) :
    StatedClassicalModel (↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) ⧸
        Subgroup.center ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i)) .PSU 3
      (ringChar K) (D.e * 3) := by
  classical
  obtain ⟨hi6, hall⟩ := kys_orbit_three_of_outer D hdim hq3 hout
  have h3q := D.three_dvd_sq hq3
  have hs3 := (hall i).1
  obtain ⟨ψ, σ', π, hψ, hΨ, hπ⟩ := exists_unitary_frame_of_odd_orbit D.S D.hL3 D.hT D.hap D.h1 i
    (hi6 i) (by rw [hs3]) h3q
  have hQ : ((3 : ℕ), ringChar K ^ (D.e * componentOrbitLength D.S.ρ
      (componentRoots (rootCharHom D.a) i))) ≠ (3, 2) := by
    intro hc
    have h2 : ringChar K ^ (D.e * componentOrbitLength D.S.ρ
        (componentRoots (rootCharHom D.a) i)) = 2 := (Prod.mk.inj hc).2
    rw [hs3] at h2
    have h3 : ringChar K ^ 3 ≤ ringChar K ^ (D.e * 3) :=
      Nat.pow_le_pow_right D.hℓ.pos (by have := D.he; omega)
    have h4 : 2 ^ 3 ≤ ringChar K ^ 3 := Nat.pow_le_pow_left D.hℓ.two_le 3
    omega
  have hmodel := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact.rationalComponent_suN_model
    D.S D.hT i (le_refl 3) hψ hΨ π hπ D.hℓ D.hchar D.he D.hSq hQ
  rw [hs3] at hmodel
  exact hmodel

end A2Out

section PSolvable

open CFSG.HallHigman
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal (isPSolvable_of_mulEquiv)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_le isPSolvable_map)

theorem kys_not_isMulCommutative_of_simple {G : Type} [Group G] (hs : IsSimpleGroup G)
    (h9 : 9 ∣ Nat.card G) : ¬ IsMulCommutative G := by
  intro hc
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc.is_comm.comm }
  have hp : (Nat.card G).Prime := IsSimpleGroup.prime_card
  rcases hp.eq_one_or_self_of_dvd 9 h9 with h | h
  · norm_num at h
  · rw [← h] at hp
    norm_num at hp

theorem kys_not_isPSolvable_of_simple {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (h9 : 9 ∣ Nat.card G) : ¬ IsPSolvable 3 G :=
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hs
    (kys_not_isMulCommutative_of_simple hs h9) (dvd_trans (by norm_num) h9)

theorem kys_isPSolvable_of_surjective {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (h : IsPSolvable 3 A) : IsPSolvable 3 B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : IsPSolvable 3 ↥(⊤ : Subgroup A) := isPSolvable_of_mulEquiv Subgroup.topEquiv.symm h
  have h2 := isPSolvable_map f h1
  rw [Subgroup.map_top_of_surjective f hf] at h2
  exact isPSolvable_of_mulEquiv Subgroup.topEquiv h2

theorem kys_not_isPSolvable_of_quotient {G : Type} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (h : ¬ IsPSolvable 3 (G ⧸ N)) : ¬ IsPSolvable 3 G := fun hs =>
  h (kys_isPSolvable_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hs)

theorem kys_isPSolvable_of_le {X : Type} [Group X] {N Y : Subgroup X} [Finite N]
    (hN : IsPSolvable 3 ↥N) (hYN : Y ≤ N) : IsPSolvable 3 ↥Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : IsPSolvable 3 ↥(⊤ : Subgroup ↥N) := isPSolvable_of_mulEquiv Subgroup.topEquiv.symm hN
  have h2 : IsPSolvable 3 ↥(Y.subgroupOf N) := isPSolvable_of_le h1 le_top
  exact isPSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYN) h2

theorem kys_not_isPSolvable_psu_three_eight {X : Type} [Group X] [Finite X]
    (h : StatedClassicalModel X .PSU 3 2 3) : ¬ IsPSolvable 3 X := by
  refine kys_not_isPSolvable_of_simple (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h)
    ?_
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_eight h]
  norm_num

theorem kys_not_isPSolvable_pomegaPlus_four_two {X : Type} [Group X] [Finite X]
    (h : StatedClassicalModel X .POmegaPlus 4 2 1) : ¬ IsPSolvable 3 X := by
  refine kys_not_isPSolvable_of_simple (CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel h)
    ?_
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.2.1 rfl]
  decide

end PSolvable

section Triality


theorem kys_not_isPSolvable_of_equiv_trialityD4 {G : Type} [Group G] {q : TauCeti.PrimePower}
    (hq2 : q.p = 2) (hq1 : q.exponent = 1) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    ¬ CFSG.HallHigman.IsPSolvable 3 G := by
  have hm := CFSG.LieType.SeitzGeneration.chevalleyModel_cat_trialityD4 hv
  rw [hq2, hq1] at hm
  have hcard : Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩) =
      CFSG.Open.ordTrialityD4 (2 ^ 1) := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  obtain ⟨hfin, hsimp⟩ := CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_trialityD4 hv
  haveI := hfin
  haveI := hsimp
  haveI : Finite G := Finite.of_equiv _ e.symm.toEquiv
  refine kys_not_isPSolvable_of_simple e.isSimpleGroup ?_
  rw [Nat.card_congr e.toEquiv]
  change 9 ∣ Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.trialityD4 q, hv⟩)
  rw [hcard]
  decide

end Triality

section Finite


theorem kys_finite_of_le_Gamma {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {H : Subgroup (ModGL τ L)} (hH : H ≤ S.Γ) : Finite H := by
  haveI := S.finite
  have hΓM : S.Γ ≤ S.D.model := by
    change ⁅S.D.model, S.D.model⁆ ≤ S.D.model
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  exact Finite.of_injective (Subgroup.inclusion (hH.trans hΓM)) (Subgroup.inclusion_injective _)

end Finite

section D4Line

open CFSG.Blueprint CFSG.HardMathSupport.Solomon.Coordinator.LieComp


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ} {h : twistedE6InndiagGL K σ}

theorem kys_char_two_of_q_two (D : TwE6LineLang K σ q h) (hq2 : q = 2) :
    ringChar K = 2 ∧ D.e = 1 := by
  have h1 : ringChar K ^ D.e = 2 := by rw [← D.hqe, hq2]
  have he : D.e ≤ 1 := by
    by_contra hlt
    have h2 : ringChar K ^ 2 ≤ ringChar K ^ D.e := Nat.pow_le_pow_right D.hℓ.pos (by omega)
    have h4 : 2 ^ 2 ≤ ringChar K ^ 2 := Nat.pow_le_pow_left D.hℓ.two_le 2
    omega
  have he1 : D.e = 1 := by have := D.he; omega
  rw [he1, pow_one] at h1
  exact ⟨h1, he1⟩

theorem kys_finite_rationalComponent (D : TwE6LineLang K σ q h)
    (i : KernelComponent (rootCharHom D.a)) :
    Finite ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) :=
  kys_finite_of_le_Gamma D.S ((langSubnormal_of_mem_torus D.S D.hT i).1.trans inf_le_left)

theorem kys_not_isPSolvable_rationalComponent_d4 (D : TwE6LineLang K σ q h)
    (hdim : twE6MatFixDim K σ h = 30) (hq2 : q = 2) (i : KernelComponent (rootCharHom D.a)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) := by
  classical
  obtain ⟨hℓ2, he1⟩ := kys_char_two_of_q_two D hq2
  haveI := kys_finite_rationalComponent D i
  have hall : (kernelRoots (rootCharHom D.a)).ncard = 24 := by
    have := D.hker
    omega
  obtain ⟨hr, hc⟩ := d4t2_class_of_card D.hL3 D.hap hall i
  have hker := d4t2_class_eq_kernel D.hL3 D.hap hall i
  have hρ : ∀ γ ∈ componentRoots (rootCharHom D.a) i,
      D.S.ρ γ ∈ componentRoots (rootCharHom D.a) i := by
    intro γ hγ
    rw [hker] at hγ ⊢
    exact outer_rho_mem_kernelRoots D.S D.hT hγ
  haveI : Fact (ringChar K).Prime := ⟨D.hℓ⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) := D.hchar
  have h3q : 3 ∣ ringChar K ^ D.e + 1 := by
    rw [hℓ2, he1]
    norm_num
  by_cases hin : twistInner (componentRoots (rootCharHom D.a) i)
      (D.S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
  ·
    obtain ⟨_, w, m0, m1, m2, m3, m4, m5, -, hsum, -, hcl⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs.kac_class_data D.hL3 D.hap
    obtain ⟨x, hx, hroots, hncard, -, -⟩ := hcl i
    have hD4 := d4t2in_cmpF_eq_sD4 hsum hx (hncard.symm.trans hc)
    have hfam : componentRoots (rootCharHom D.a) i = rootsOfFam (fun y => w⁻¹ • kacE6.extRoot y)
        (Set.range CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.lD4) := by
      rw [hroots, hD4, ← CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.range_lD4]
      exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.image_rootsOf_eq_rootsOfFam
        kacE6 w⁻¹ _
    have hfin : (componentRoots (rootCharHom D.a) i).Finite :=
      (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
    have hs1 : componentOrbitLength D.S.ρ (componentRoots (rootCharHom D.a) i) = 1 :=
      componentOrbitLength_eq_one hfin hρ
    have hinner : twistInner (componentRoots (rootCharHom D.a) i)
        ((D.S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength D.S.ρ
          (componentRoots (rootCharHom D.a) i)]) := by
      rw [hs1, Function.iterate_one]
      exact hin
    obtain ⟨hmodel, -⟩ := d4t2in_dModel_center D.S (Or.inr (Or.inl rfl)) D.hT i hinner
      (n := 4) le_rfl (fun y => w⁻¹ • kacE6.extRoot y)
      (fun y => IsRoot.smul (kacE6.isRoot_extRoot y) w⁻¹)
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.lD4 hfam
      (fun c d hcd h1 h2 => by
        show iform (w⁻¹ • kacE6.extRoot
            (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.lD4 c))
          (w⁻¹ • kacE6.extRoot
            (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.lD4 d)) = 0
        rw [iform_smul, kacE6_extRoot]
        exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.d4_hgram c d hcd h1 h2)
      (fun {F} _ c d h =>
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerAbs.d4_frames w⁻¹ c d h)
      D.hℓ D.he D.hSq
    rw [hs1, Nat.mul_one, hℓ2, he1] at hmodel
    exact kys_not_isPSolvable_of_quotient _ (kys_not_isPSolvable_pomegaPlus_four_two hmodel)
  ·
    have hTp : rootDiagUnit Tag.E6 D.a ^ 3 = 1 := by
      have h1 : rootDiagUnit Tag.E6 (D.a ^ 3) = rootDiagUnit Tag.E6 D.a ^ 3 :=
        (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)).map_pow D.a 3
      have h2 : D.a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, D.hap j, Pi.one_apply]
      rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]
    obtain ⟨v, hv, -⟩ := D.S.d4_pinnedT_of_prime Nat.prime_three D.hL3 facts_E6 kacCount_E6_four
      (by decide) (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) D.hT hTp i hr hc
    obtain ⟨⟨e⟩, -⟩ := d4t2out_rationalComponent_equiv D.S D.hS D.he D.hSq h3q D.hT D.hap i v hv
      hker.symm.le hρ hin
    exact kys_not_isPSolvable_of_equiv_trialityD4 hℓ2 he1 _ e

theorem kys_not_isPSolvable_rationalComponent_a2out (D : TwE6LineLang K σ q h)
    (hdim : twE6MatFixDim K σ h = 24) (hq2 : q = 2)
    (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ)
    (i : KernelComponent (rootCharHom D.a)) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i) := by
  obtain ⟨hℓ2, he1⟩ := kys_char_two_of_q_two D hq2
  haveI := kys_finite_rationalComponent D i
  have hmodel := kys_rationalComponent_psu_model D hdim (by rw [hq2]) hout i
  rw [hℓ2, he1, one_mul] at hmodel
  exact kys_not_isPSolvable_of_quotient _ (kys_not_isPSolvable_psu_three_eight hmodel)

end D4Line

section A5T1

open CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.Blueprint.Chevalley.RootCertificate
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3


theorem kys_e6A5T1Check :
    (e6ThreeStabs.all fun S => decide (e6KerCount (vec3 (τ := .E6) S.vec) ≠ 30) ||
      (S.passing e6Certificate).all fun t => t == List.range Tag.E6.rank) = true := by
  decide +kernel

theorem kys_e6KerCount_eq_of_pairing {b b' : Fin Tag.E6.rank → ZMod 3} (t : WeylGroup .E6)
    (h : ∀ v, triPairing b v = triPairing b' (t⁻¹ • v)) : e6KerCount b = e6KerCount b' := by
  classical
  unfold e6KerCount
  refine Finset.card_bij (fun α _ => t⁻¹ • α) ?_ ?_ ?_
  · intro α hα
    rw [Finset.mem_filter, mem_rootFinset] at hα ⊢
    refine ⟨IsRoot.smul hα.1 t⁻¹, ?_⟩
    have h1 : triPairing b' (t⁻¹ • α) = 0 := by rw [← h α]; exact hα.2
    exact h1
  · intro α₁ _ α₂ _ he
    exact smul_left_cancel t⁻¹ he
  · intro β hβ
    rw [Finset.mem_filter, mem_rootFinset] at hβ
    refine ⟨t • β, ?_, inv_smul_smul t β⟩
    rw [Finset.mem_filter, mem_rootFinset]
    refine ⟨IsRoot.smul hβ.1 t, ?_⟩
    have h1 : triPairing b (t • β) = 0 := by rw [h, inv_smul_smul]; exact hβ.2
    exact h1

theorem kys_mem_kernelWeylGroup_of_ker30
    (b : Fin Tag.E6.rank → ZMod 3) (hb : e6KerCount b = 30) {w : WeylGroup .E6}
    (hw : w ∈ charStabilizer (triChar b)) : w ∈ kernelWeylGroup (triChar b) := by
  obtain ⟨horbit, hstab⟩ := e6ThreeScCheck_spec
  have hvec := e6ThreeStabs_vec
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 horbit (triChar b)
  have hlen : ρ < e6ThreeStabs.length := by
    rw [← List.length_map StabCert3.vec, hvec]
    exact hρ
  set S := e6ThreeStabs[ρ] with hSdef
  have hSv : S.vec = e6ThreeReps.getD ρ [] := by
    rw [List.getD_eq_getElem _ _ hρ, hSdef]
    have := congrArg (fun l => l[ρ]?) hvec
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem hρ,
      Option.map_some, Option.some.injEq] at this
    exact this
  obtain ⟨hScheck, -⟩ := hstab S (List.getElem_mem hlen)
  rw [← hSv] at ht
  set bρ := vec3 (τ := .E6) S.vec with hbρ
  have hw₀ : t⁻¹ * w * t ∈ charStabilizer (triChar bρ) :=
    (charStabilizer_iff_of_isCharConj ht).1 hw
  have hpair : ∀ v, triPairing b v = triPairing bρ (t⁻¹ • v) := fun v => by
    have h := ht v
    rw [triChar_apply, triChar_apply] at h
    exact Z3.ofAdd_eq_ofAdd_iff.1 h
  have hbρ30 : e6KerCount bρ = 30 := by
    rw [← kys_e6KerCount_eq_of_pairing t hpair]
    exact hb
  have hcert := kys_e6A5T1Check
  rw [List.all_eq_true] at hcert
  have hS := hcert S (List.getElem_mem hlen)
  rw [Bool.or_eq_true, decide_eq_true_eq] at hS
  have hpass : ∀ t' ∈ S.passing e6Certificate, t' = List.range Tag.E6.rank := by
    rcases hS with h | h
    · exact absurd hbρ30 h
    · rw [List.all_eq_true] at h
      exact fun t' ht' => by simpa using h t' ht'
  obtain ⟨u, hu, hwu⟩ := exists_mul_mem_kernelPosStabilizer hw₀
  obtain ⟨t', ht', hrep⟩ := StabCert3.exists_passing_of_mem e6Certificate_check hScheck hwu
  rw [hpass t' ht'] at hrep
  have h1 : t⁻¹ * w * t * u = 1 := represents_unique hrep (represents_one e6Certificate_check)
  have hk : t⁻¹ * w * t ∈ kernelWeylGroup (triChar bρ) := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_mem hu
  rw [kernelWeylGroup_eq_map ht]
  exact ⟨t⁻¹ * w * t, hk, by simp [mul_assoc]⟩

theorem kys_kernelReflectionGroup_of_ker30 {L : Type} [Field L]
    {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (x : Fin Tag.E6.rank → ZMod 3)
    (hx : e6KerCount x = 30) :
    rootCharStabilizerSubgroup (torV ω x) ≤ kernelReflectionGroup (torV ω x) := by
  intro w hw
  have hker : ∀ v, rootCharHom3 (torV ω x) v = 1 ↔ triChar x v = 1 := by
    intro v
    change rootChar (torV ω x) (Multiplicative.toAdd v) = 1 ↔
      Z3.ofAdd (triPairing x (Multiplicative.toAdd v)) = 1
    rw [rootChar_torV_eq_one_iff hω3 hω1, Z3.ofAdd_eq_one]
    rfl
  have hS : rootCharStabilizerSubgroup (torV ω x) = charStabilizer (rootCharHom3 (torV ω x)) :=
    Subgroup.ext fun w => Iff.rfl
  have hW : kernelReflectionGroup (torV ω x) = kernelWeylGroup (rootCharHom3 (torV ω x)) := rfl
  rw [hS, charStabilizer_congr_ker hker] at hw
  rw [hW, kernelWeylGroup_congr_ker hker]
  exact kys_mem_kernelWeylGroup_of_ker30 x hx hw

end A5T1

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295f
