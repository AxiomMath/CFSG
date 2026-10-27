module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoModel
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoLang
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoRefl
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoKind
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoUnit
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoSep
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoClass
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

section Aux

theorem not_isSolvable_of_isQuasisimple' {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hs
  obtain ⟨-, hsimple, a, b, hab⟩ := hQ
  have : Group.IsSolvable (Q ⧸ Subgroup.center Q) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective _)
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := Q ⧸ Subgroup.center Q)).2 this a b)

theorem three_dvd_card_of_orderOf {G : Type*} [Group G] {R : Subgroup G} {g : G} (hg : g ∈ R)
    (h3 : orderOf g = 3) : 3 ∣ Nat.card R := by
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : R)
  rwa [Subgroup.orderOf_mk, h3] at h

theorem exists_primitive_root_odd {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {N : ℕ}
    (hN : Odd N) : ∃ ζ : Lˣ, ∀ n : ℤ, ζ ^ n = 1 ↔ (N : ℤ) ∣ n := by
  have hN0 : 0 < N := hN.pos
  haveI : NeZero (N : L) := by
    refine ⟨fun h => ?_⟩
    obtain ⟨m, hm⟩ := hN
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    rw [hm] at h
    push_cast at h
    have : (1 : L) = 0 := by linear_combination h - (m : L) * h2
    exact one_ne_zero this
  obtain ⟨ζ, hζ⟩ := (IsSepClosed.hasEnoughRootsOfUnity L N).prim
  refine ⟨(hζ.isUnit hN0.ne').unit, fun n => ?_⟩
  have := hζ.zpow_eq_one_iff_dvd n
  rw [← this, ← Units.val_inj, Units.val_zpow_eq_zpow_val, Units.val_one]
  rfl

theorem commute_conj_of_commute {M : Type*} [Group M] {z g w : M}
    (h : g * (z * w * z⁻¹) = (z * w * z⁻¹) * g) : (z⁻¹ * g * z) * w = w * (z⁻¹ * g * z) := by
  calc (z⁻¹ * g * z) * w = z⁻¹ * (g * (z * w * z⁻¹)) * z := by group
    _ = z⁻¹ * ((z * w * z⁻¹) * g) * z := by rw [h]
    _ = w * (z⁻¹ * g * z) := by group

end Aux

set_option linter.unusedSectionVars false


section Orth

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem false_of_orth_root {C : Type} [Group C] {x : C} {J : Subgroup C}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ} (ι : C →* ModGL Tag.F4 L)
    (hrange : ι.range = S.Γ) (hx : ι x = rootDiagUnit Tag.F4 a) (hap : ∀ i, a i ^ 3 = 1)
    (hJ : J ≤ Subgroup.centralizer {x}) (hperf : ⁅J, J⁆ = J) (hxJ : x ∈ J) {ω : Lˣ}
    {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i)
    {e : V4} (he : IsRoot Tag.F4 e)
    (horth : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → ipF4 γ e = 0) : False := by
  classical
  have hΓ : S.Γ ≤ adjointGroup Tag.F4 L :=
    (Subgroup.commutator_le_self S.D.model).trans inf_le_left
  have hPX : J.map ι ≤ toralCentralizer Tag.F4 L a := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hΓ (hrange ▸ ⟨y, rfl⟩), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hx, ← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJ hy)
  have hperfmap : ⁅J.map ι, J.map ι⁆ = J.map ι := by
    rw [← Subgroup.map_commutator, hperf]
  have hU := perfect_le_rootSpan_kernel Nat.prime_three a hap hPX hperfmap
  have hd : rootDiagUnit Tag.F4 a ∈ rootSpan Tag.F4 L (rootCharKernel a) := hU ⟨x, hxJ, hx⟩
  have hkdot : ∀ γ : V4, rootChar a γ = 1 ↔ kdot k γ % 3 = 0 := fun γ =>
    rootChar_eq_one_iff hω3 hω1 hak γ
  have h1 := rootChar_eq_one_of_mem_rootSpan_of_orth a (rootCharKernel a)
    (fun γ hγ => hγ.1) hd he (fun γ hγ => by
      rw [iform_F4]
      exact horth γ hγ.1 ((hkdot γ).1 hγ.2))
  have h2 := horth e he ((hkdot e).1 h1)
  have h3 := iform_self_cases noG2_F4 he
  rw [iform_F4, h2] at h3
  omega

end Orth

section Pair

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem exists_pair_frames (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) {ω : Lˣ}
    {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i)
    (hk : KernelA2A2 k) :
    ∃ (σ τ : Fin 3 → Fin 3 → V4) (κ κ' : ℤ) (ψ ψ' : SL(3, L) →* ModGL Tag.F4 L)
      (iΛ iΘ : KernelComponent (rootCharHom a)),
      A2Pair σ τ κ κ' ∧ IsA2Frame ψ σ ∧ IsA2Frame ψ' τ ∧
      componentRoots (rootCharHom a) iΛ = frameRoots σ ∧
      componentRoots (rootCharHom a) iΘ = frameRoots τ ∧
      (∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 → γ ∈ frameRoots σ ∨ γ ∈ frameRoots τ) ∧
      (∀ j : KernelComponent (rootCharHom a), j = iΛ ∨ j = iΘ) ∧
      (S.ρ : V4 → V4) '' frameRoots σ = frameRoots σ ∧
      (S.ρ : V4 → V4) '' frameRoots τ = frameRoots τ := by
  classical
  have hker : ∀ γ : V4, γ ∈ kernelRoots (rootCharHom a) ↔ IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 :=
    fun γ => and_congr_right fun _ => rootChar_eq_one_iff hω3 hω1 hak γ
  have hkd : ∀ γ ∈ kernelRoots (rootCharHom a), kdot k γ % 3 = 0 := fun γ hγ => ((hker γ).1 hγ).2
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    intro h
    have h3 : ((3 : ℕ) : L) = 3 := by norm_num
    rw [h3] at h
    have : (1 : L) = 0 := by linear_combination h - h2
    exact one_ne_zero this
  have hTp : rootDiagUnit Tag.F4 a ^ 3 = 1 := by
    have h : rootDiagUnit Tag.F4 a ^ 3 = rootDiagUnit Tag.F4 (a ^ 3) :=
      ((rootDiagUnitHom Tag.F4 L).map_pow a 3).symm
    rw [h, show a ^ 3 = 1 from funext fun i => by simpa using hap i, rootDiagUnit_one]
  have hnorm2 : ∀ γ : V4, IsRoot Tag.F4 γ → ipF4 γ γ = 2 ∨ ipF4 γ γ = 4 := fun γ hγ => by
    have := iform_self_cases noG2_F4 hγ
    rwa [iform_F4] at this
  obtain ⟨γL, hγL, hLen⟩ : ∃ γ, γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = 4 := by
    obtain ⟨γ, hγ⟩ := Set.nonempty_of_ncard_ne_zero (s := {γ : V4 | IsRoot Tag.F4 γ ∧
      kdot k γ % 3 = 0 ∧ ipF4 γ γ = 4}) (by rw [hk.card_long]; norm_num)
    exact ⟨γ, (hker γ).2 ⟨hγ.1, hγ.2.1⟩, hγ.2.2⟩
  obtain ⟨γS, hγS, hShort⟩ : ∃ γ, γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = 2 := by
    obtain ⟨γ, hγ⟩ := Set.nonempty_of_ncard_ne_zero (s := {γ : V4 | IsRoot Tag.F4 γ ∧
      kdot k γ % 3 = 0 ∧ ipF4 γ γ = 2}) (by rw [hk.card_short]; norm_num)
    exact ⟨γ, (hker γ).2 ⟨hγ.1, hγ.2.1⟩, hγ.2.2⟩
  obtain ⟨iΛ, hiΛ⟩ : ∃ i : KernelComponent (rootCharHom a), i = ⟦⟨γL, hγL⟩⟧ := ⟨_, rfl⟩
  obtain ⟨iΘ, hiΘ⟩ : ∃ i : KernelComponent (rootCharHom a), i = ⟦⟨γS, hγS⟩⟧ := ⟨_, rfl⟩
  have hΛset : componentRoots (rootCharHom a) iΛ =
      {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = 4} := by
    rw [hiΛ, componentRoots_eq_sameLength hω3 hω1 hak hk hγL, hLen]
  have hΘset : componentRoots (rootCharHom a) iΘ =
      {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = 2} := by
    rw [hiΘ, componentRoots_eq_sameLength hω3 hω1 hak hk hγS, hShort]
  have hΛ6 : (componentRoots (rootCharHom a) iΛ).ncard = 6 := by
    rw [hΛset]
    have : {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = 4} =
        {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 ∧ ipF4 γ γ = 4} :=
      Set.ext fun γ => by simp only [Set.mem_setOf_eq, hker, and_assoc]
    rw [this]
    exact hk.card_long
  have hΘ6 : (componentRoots (rootCharHom a) iΘ).ncard = 6 := by
    rw [hΘset]
    have : {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = 2} =
        {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 ∧ ipF4 γ γ = 2} :=
      Set.ext fun γ => by simp only [Set.mem_setOf_eq, hker, and_assoc]
    rw [this]
    exact hk.card_short
  obtain ⟨ψ, σ, κ, hψ, hκ, hnormσ, hΛroots⟩ :=
    exists_a2frame_of_class S Nat.prime_three h3L hTp iΛ hΛ6
  obtain ⟨ψ', τ, κ', hψ', hκ', hnormτ, hΘroots⟩ :=
    exists_a2frame_of_class S Nat.prime_three h3L hTp iΘ hΘ6
  have hmemΛ : ∀ x y : Fin 3, x ≠ y →
      σ x y ∈ kernelRoots (rootCharHom a) ∧ ipF4 (σ x y) (σ x y) = 4 := by
    intro x y hxy
    have h : σ x y ∈ componentRoots (rootCharHom a) iΛ := by
      rw [hΛroots]
      exact ⟨x, y, hxy, rfl⟩
    rwa [hΛset] at h
  have hmemΘ : ∀ x y : Fin 3, x ≠ y →
      τ x y ∈ kernelRoots (rootCharHom a) ∧ ipF4 (τ x y) (τ x y) = 2 := by
    intro x y hxy
    have h : τ x y ∈ componentRoots (rootCharHom a) iΘ := by
      rw [hΘroots]
      exact ⟨x, y, hxy, rfl⟩
    rwa [hΘset] at h
  have hκ2 : κ = 2 := by
    have h1 := hnormσ 0 1 (by decide)
    rw [iform_F4, (hmemΛ 0 1 (by decide)).2] at h1
    omega
  have hκ1 : κ' = 1 := by
    have h1 := hnormτ 0 1 (by decide)
    rw [iform_F4, (hmemΘ 0 1 (by decide)).2] at h1
    omega
  have hρΛ : (S.ρ : V4 → V4) '' frameRoots σ = frameRoots σ := by
    have hfin : {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 γL γL}.Finite := by
      apply Set.finite_of_ncard_ne_zero
      rw [← componentRoots_eq_sameLength hω3 hω1 hak hk hγL, ← hiΛ, hΛ6]
      norm_num
    rw [← hΛroots, hiΛ, componentRoots_eq_sameLength hω3 hω1 hak hk hγL]
    exact rho_image_sameLength S hT hfin
  have hρΘ : (S.ρ : V4 → V4) '' frameRoots τ = frameRoots τ := by
    have hfin : {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 γS γS}.Finite := by
      apply Set.finite_of_ncard_ne_zero
      rw [← componentRoots_eq_sameLength hω3 hω1 hak hk hγS, ← hiΘ, hΘ6]
      norm_num
    rw [← hΘroots, hiΘ, componentRoots_eq_sameLength hω3 hω1 hak hk hγS]
    exact rho_image_sameLength S hT hfin
  refine ⟨σ, τ, κ, κ', ψ, ψ', iΛ, iΘ, ?_, hψ, hψ', hΛroots, hΘroots, ?_, ?_, hρΛ, hρΘ⟩
  · exact
      { kappa := Or.inr ⟨hκ2, hκ1⟩
        σ_root := hψ.isRoot
        τ_root := hψ'.isRoot
        σ_add := hψ.add
        τ_add := hψ'.add
        σ_norm := fun x y hxy => by rw [(hmemΛ x y hxy).2, hκ2]; norm_num
        τ_norm := fun x y hxy => by rw [(hmemΘ x y hxy).2, hκ1]; norm_num
        orth := fun x y x' y' hxy hxy' =>
          hk.diff (σ x y) (τ x' y') (hψ.isRoot x y hxy) (hψ'.isRoot x' y' hxy')
            (hkd _ (hmemΛ x y hxy).1) (hkd _ (hmemΘ x' y' hxy').1)
            (by rw [(hmemΛ x y hxy).2, (hmemΘ x' y' hxy').2]; norm_num) }
  · intro γ hγ hk3
    have hγk : γ ∈ kernelRoots (rootCharHom a) := (hker γ).2 ⟨hγ, hk3⟩
    rcases hnorm2 γ hγ with h2 | h4
    · right
      rw [← hΘroots, hΘset]
      exact ⟨hγk, h2⟩
    · left
      rw [← hΛroots, hΛset]
      exact ⟨hγk, h4⟩
  · intro j
    induction j using Quotient.inductionOn with
    | _ γ' =>
      obtain ⟨γ, hγ⟩ := γ'
      rcases hnorm2 γ hγ.1 with h2 | h4
      · right
        rw [hiΘ]
        exact mk_eq_of_iform_ne_zero (α := ⟨γ, hγ⟩) (β := ⟨γS, hγS⟩) (by
          show iform γ γS ≠ 0
          rw [iform_F4]
          exact hk.same γ γS hγ.1 hγS.1 (hkd γ hγ) (hkd γS hγS) (by rw [h2, hShort]))
      · left
        rw [hiΛ]
        exact mk_eq_of_iform_ne_zero (α := ⟨γ, hγ⟩) (β := ⟨γL, hγL⟩) (by
          show iform γ γL ≠ 0
          rw [iform_F4]
          exact hk.same γ γL hγ.1 hγL.1 (hkd γ hγ) (hkd γL hγL) (by rw [h4, hLen]))

end Pair

section Unitary

variable {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem exists_sigmaQ (S : LangSetup Tag.F4 L p₀) :
    ∃ σQ : L ≃+* L, ∀ c, σQ c = c ^ S.D.q := by
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r e
  refine ⟨σ, fun c => ?_⟩
  have h1 : σ c = iterateFrobenius L r e c := by
    rw [← hσ]
    rfl
  rw [h1, iterateFrobenius_def, hq]

theorem fix_perfect (S : LangSetup Tag.F4 L p₀) {σQ : L ≃+* L} (hσc : ∀ c, σQ c = c ^ S.D.q)
    (hq2 : S.D.q ≠ 2) : Group.IsPerfect (fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) := by
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have h := (stdUnitary_fixSubgroup (L := L) (ν := 3) hr he σQ (fun c => by rw [hσc, hq])
    (le_refl 3)).2.1 (by
      intro h
      apply hq2
      rw [hq]
      exact (Prod.mk.inj h).2)
  exact h.1

theorem scalar_unitary {σQ : L ≃+* L} {q : ℕ} (hσc : ∀ c, σQ c = c ^ q) (u : Lˣ)
    (hu : u ^ (q + 1) = 1) : σQ.toRingHom (u : L) * (u : L) = 1 := by
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσc, ← pow_succ,
    ← Units.val_pow_eq_pow_val, hu, Units.val_one]

theorem omega_det {ω : Lˣ} (hω3 : ω ^ 3 = 1) :
    (fun _ : Fin 3 => ω) 0 * (fun _ : Fin 3 => ω) 1 * (fun _ : Fin 3 => ω) 2 = 1 := by
  show ω * ω * ω = 1
  rw [← pow_three']
  exact hω3

theorem orderOf_conj_frame_omega {ψ : SL(3, L) →* ModGL Tag.F4 L} (hψ : Function.Injective ψ)
    {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (z : ModGL Tag.F4 L) :
    orderOf (z * ψ (diagSL3 (fun _ => ω) (omega_det hω3)) * z⁻¹) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X₀ := diagSL3 (fun _ : Fin 3 => ω) (omega_det hω3) with hX₀
  have hX3 : X₀ ^ 3 = 1 := by
    have h := diagSL3_cube (fun _ : Fin 3 => ω) (omega_det hω3) (fun _ => 1) (by simp)
      (fun i => hω3.symm)
    rw [← h]
    apply Subtype.ext
    simp [coe_diagSL3]
  have hX1 : X₀ ≠ 1 := by
    intro h
    have h00 := congrArg (fun X : SL(3, L) => (X : Matrix (Fin 3) (Fin 3) L) 0 0) h
    simp only [hX₀, coe_diagSL3, Matrix.diagonal_apply_eq, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h00
    exact hω1 (Units.ext h00)
  apply orderOf_eq_prime
  · rw [conj_pow, ← map_pow, hX3, map_one]
    group
  · intro h
    apply hX1
    apply hψ
    rw [map_one]
    have h' : ψ X₀ = z⁻¹ * (z * ψ X₀ * z⁻¹) * z := by group
    rw [h', h]
    group

end Unitary

section A2A2

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem false_of_a2a2 {C : Type} [Group C] [Finite C] {x g y : C} {J : Subgroup C}
    (hcfg : InnerHeisCfg x g y J) (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (ι : C →* ModGL Tag.F4 L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ)
    (hx : ι x = rootDiagUnit Tag.F4 a) (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit Tag.F4 a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hqn : ∃ n : ℕ, Odd n ∧ S.D.q = 2 ^ n) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3) (hk0 : ∃ i, k i ≠ 0)
    (hak : ∀ i, a i = ω ^ k i) (hk : KernelA2A2 k) : False := by
  classical
  obtain ⟨n, hn, hqn'⟩ := hqn
  have hqmod : S.D.q % 3 = 2 := by
    rw [hqn']
    obtain ⟨m, rfl⟩ := hn
    have h4 : 4 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [pow_succ, pow_mul]
    norm_num
    omega
  obtain ⟨σ, τ, κ, κ', ψ, ψ', iΛ, iΘ, hP, hψ, hψ', hΛ, hΘ, hSig, hall, hρΛ, hρΘ⟩ :=
    exists_pair_frames S hT hap hω3 hω1 hak hk
  have hSig' : ∀ γ : V4, IsRoot Tag.F4 γ → kdot k γ % 3 = 0 →
      γ ∈ frameRoots τ ∨ γ ∈ frameRoots σ := fun γ h1 h2 => (hSig γ h1 h2).symm
  obtain ⟨π₁, hπ₁⟩ := exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP hψ hSig hqmod hρΛ
  obtain ⟨π₂, hπ₂⟩ := exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP.symm hψ' hSig' hqmod hρΘ
  have hψSL := IsSLFrame.of_isA2Frame hψ
  have hψSL' := IsSLFrame.of_isA2Frame hψ'
  have hs1Λ : componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΛ) = 1 :=
    componentOrbitLength_eq_one S hT iΛ (by rw [hΛ]; exact hρΛ)
  have hs1Θ : componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΘ) = 1 :=
    componentOrbitLength_eq_one S hT iΘ (by rw [hΘ]; exact hρΘ)
  have hπ₁' : ∀ x y : Fin 3, x ≠ y →
      (S.ρ : V4 → V4)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΛ)] (σ x y) =
        σ (π₁ y) (π₁ x) := by
    intro x y hxy
    rw [hs1Λ, Function.iterate_one]
    exact hπ₁ x y hxy
  have hπ₂' : ∀ x y : Fin 3, x ≠ y →
      (S.ρ : V4 → V4)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) iΘ)] (τ x y) =
        τ (π₂ y) (π₂ x) := by
    intro x y hxy
    rw [hs1Θ, Function.iterate_one]
    exact hπ₂ x y hxy
  have hRU := rationalComponent_of_unitary_frame_T S hT iΛ (le_refl 3) hψSL hΛ π₁ hπ₁'
  have hRU' := rationalComponent_of_unitary_frame_T S hT iΘ (le_refl 3) hψSL' hΘ π₂ hπ₂'
  have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hcfg.comp
  obtain ⟨hJX, -, -, -⟩ := hcfg.comp
  by_cases hq2 : S.D.q = 2
  ·
    have hsolv : ∀ j : KernelComponent (rootCharHom a),
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) j) := by
      intro j
      rcases hall j with rfl | rfl
      · exact isSolvable_of_card_dvd_216 (hRU.2 (by rw [hs1Λ, pow_one, hq2]))
      · exact isSolvable_of_card_dvd_216 (hRU'.2 (by rw [hs1Θ, pow_one, hq2]))
    have hPmap : J.map ι ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.F4 a} := by
      rintro _ ⟨y', hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨hrange ▸ ⟨y', rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hx, ← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_centralizer_singleton_iff.1 (hJX hy)
    have hperfmap : ⁅J.map ι, J.map ι⁆ = J.map ι := by
      rw [← Subgroup.map_commutator, hperfJ]
    have h2 := perfect_le_iSup_rationalComponent_of_prime S Nat.prime_three hT hap h1 hTame
      (J.map ι) hPmap hperfmap
    haveI : IsEmpty {i : KernelComponent (rootCharHom a) //
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)} :=
      ⟨fun ⟨i, hi⟩ => not_isSolvable_of_isQuasisimple' hi (hsolv i)⟩
    rw [iSup_of_empty] at h2
    have hd : rootDiagUnit Tag.F4 a ∈ (⊥ : Subgroup (ModGL Tag.F4 L)) := h2 ⟨x, hcfg.mem, hx⟩
    exact h1 (Subgroup.mem_bot.1 hd)
  ·
    have hn3 : 3 ≤ n := by
      by_contra hlt
      obtain ⟨m, hm⟩ := hn
      have : n = 1 := by omega
      subst this
      apply hq2
      rw [hqn']
      norm_num
    have hq8 : 8 ≤ S.D.q := by
      rw [hqn']
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    have hN9 : 9 ≤ S.D.q + 1 := by omega
    have hNodd : Odd (S.D.q + 1) := by
      have : Even S.D.q := by
        rw [hqn']
        exact Nat.even_pow.2 ⟨even_two, by omega⟩
      exact this.add_one
    obtain ⟨ζ, hζ⟩ := exists_primitive_root_odd (L := L) hNodd
    have hζN : ζ ^ (S.D.q + 1) = 1 := by
      have h := (hζ (((S.D.q + 1 : ℕ)) : ℤ)).2 dvd_rfl
      rwa [zpow_natCast] at h
    obtain ⟨σQ, hσc⟩ := exists_sigmaQ S
    obtain ⟨B₁, hB₁⟩ := exists_unitary_pinning S (le_refl 3) hψSL π₁ hπ₁ σQ hσc
    obtain ⟨B₂, hB₂⟩ := exists_unitary_pinning S (le_refl 3) hψSL' π₂ hπ₂ σQ hσc
    have hψS : ∀ X : SL(3, L), ψ X ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) iΛ) :=
      fun X => by
        rw [hΛ, ← hψSL.range]
        exact ⟨X, rfl⟩
    have hψS' : ∀ X : SL(3, L), ψ' X ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) iΘ) :=
      fun X => by
        rw [hΘ, ← hψSL'.range]
        exact ⟨X, rfl⟩
    have hy₁ : ψ B₁ * ψ' B₂ ∈ rootSpan Tag.F4 L (kernelRoots (rootCharHom a)) :=
      mul_mem (rootSpan_mono (fun γ hγ => hγ.1) (hψS B₁))
        (rootSpan_mono (fun γ hγ => hγ.1) (hψS' B₂))
    obtain ⟨z, hzZ, hnorm, hc₁, hc₂⟩ :=
      exists_common_lang S hT B₁ B₂ σQ hB₁ hB₂ (hP.commute_frames hψ hψ') hy₁
    have hperf := fix_perfect S hσc hq2
    have hmemΛ : ∀ X : SL(3, L), stdUnitary σQ.toRingHom X = X →
        z * ψ X * z⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) iΛ := fun X hX =>
      conj_mem_rationalComponent S iΛ hψSL hΛ (fun g hg => (hnorm iΛ g).1 hg) hc₁ hperf hX
    have hmemΘ : ∀ X : SL(3, L), stdUnitary σQ.toRingHom X = X →
        z * ψ' X * z⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) iΘ := fun X hX =>
      conj_mem_rationalComponent S iΘ hψSL' hΘ (fun g hg => (hnorm iΘ g).1 hg) hc₂ hperf hX
    have hqΛ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) iΛ) := by
      refine hRU.1 ?_
      rw [hs1Λ, pow_one]
      intro h
      exact hq2 (Prod.mk.inj h).2
    have hqΘ : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) iΘ) := by
      refine hRU'.1 ?_
      rw [hs1Θ, pow_one]
      intro h
      exact hq2 (Prod.mk.inj h).2
    have hωu : ω ^ (S.D.q + 1) = 1 := by
      obtain ⟨t, ht⟩ : 3 ∣ S.D.q + 1 := by omega
      rw [ht, pow_mul, hω3, one_pow]
    have hωC : stdUnitary σQ.toRingHom (diagSL3 (fun _ => ω) (omega_det hω3)) =
        diagSL3 (fun _ => ω) (omega_det hω3) :=
      stdUnitary_diagSL3_eq_self _ _ _ (fun i => scalar_unitary hσc ω hωu)
    have h3Λ : 3 ∣ Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) iΛ) :=
      three_dvd_card_of_orderOf (hmemΛ _ hωC) (orderOf_conj_frame_omega hψ.injective hω3 hω1 z)
    have h3Θ : 3 ∣ Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) iΘ) :=
      three_dvd_card_of_orderOf (hmemΘ _ hωC) (orderOf_conj_frame_omega hψ'.injective hω3 hω1 z)
    have hcompΛ := glaPComponent_of_rational S hT ι hι hrange hx iΛ hqΛ h3Λ
    have hcompΘ := glaPComponent_of_rational S hT ι hι hrange hx iΘ hqΘ h3Θ
    have hcent : ∀ i : KernelComponent (rootCharHom a),
        GLAPComponent 3 (Subgroup.centralizer ({x} : Set C))
          ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι) →
        ∀ r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
          ι g * r = r * ι g ∧ ι y * r = r * ι y := by
      intro i hi r hr
      have hrΓ : r ∈ S.Γ := (Subgroup.mem_inf.1 ((langSubnormal_of_mem_torus S hT i).1 hr)).1
      rw [← hrange] at hrΓ
      obtain ⟨l, rfl⟩ := hrΓ
      obtain ⟨h1', h2'⟩ := hcfg.centralizes _ hi l (Subgroup.mem_comap.2 hr)
      exact ⟨by rw [← map_mul, ← map_mul, h1'], by rw [← map_mul, ← map_mul, h2']⟩
    have hunit : ∀ e₀ e₁ : ℤ, stdUnitary σQ.toRingHom
        (diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁)) =
          diagSL3 (lvec ζ e₀ e₁) (lvec_det ζ e₀ e₁) := fun e₀ e₁ =>
      stdUnitary_diagSL3_eq_self _ _ _ (fun i => scalar_unitary hσc _ (lvec_pow hζN e₀ e₁ i))
    have hGΛ := fun e₀ e₁ => hcent iΛ hcompΛ _ (hmemΛ _ (hunit e₀ e₁))
    have hGΘ := fun e₀ e₁ => hcent iΘ hcompΘ _ (hmemΘ _ (hunit e₀ e₁))
    have hcommd : rootDiagUnit Tag.F4 a * z = z * rootDiagUnit Tag.F4 a :=
      commute_of_mem_torus_sup_kernel S hzZ
    have hGY : (z⁻¹ * ι g * z) * (z⁻¹ * ι y * z) * (z⁻¹ * ι g * z)⁻¹ * (z⁻¹ * ι y * z)⁻¹ =
        rootDiagUnit Tag.F4 a := by
      have e1 : (z⁻¹ * ι g * z) * (z⁻¹ * ι y * z) * (z⁻¹ * ι g * z)⁻¹ * (z⁻¹ * ι y * z)⁻¹ =
          z⁻¹ * (ι g * ι y * (ι g)⁻¹ * (ι y)⁻¹) * z := by group
      have e2 : ι g * ι y * (ι g)⁻¹ * (ι y)⁻¹ = rootDiagUnit Tag.F4 a := by
        rw [← hx, ← hcfg.comm]
        simp only [map_mul, map_inv]
      rw [e1, e2]
      calc z⁻¹ * rootDiagUnit Tag.F4 a * z = z⁻¹ * (rootDiagUnit Tag.F4 a * z) := by group
        _ = z⁻¹ * (z * rootDiagUnit Tag.F4 a) := by rw [hcommd]
        _ = rootDiagUnit Tag.F4 a := by group
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply h1
      rw [show a = 1 from funext hcon, rootDiagUnit_one]
    exact hP.commutator_contradiction hψ hψ' hN9 hζ
      (fun e₀ e₁ => commute_conj_of_commute (hGΛ e₀ e₁).1)
      (fun e₀ e₁ => commute_conj_of_commute (hGΘ e₀ e₁).1)
      (fun e₀ e₁ => commute_conj_of_commute (hGΛ e₀ e₁).2)
      (fun e₀ e₁ => commute_conj_of_commute (hGΘ e₀ e₁).2) hGY
      (isRoot_single Tag.F4 i) (by rw [rootChar_single']; exact hi)

end A2A2

section Final

theorem not_innerHeisCfg_F4 (n : ℕ) (hn : Odd n) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (x g y : ↥(adjointGroup Tag.F4 F))
    (J : Subgroup ↥(adjointGroup Tag.F4 F)) : ¬ InnerHeisCfg x g y J := by
  intro hcfg
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  have hpK : ¬ 3 ∣ Nat.card F := by
    rw [hF]
    intro h
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1 h3
    omega
  obtain ⟨p₀, S, a, ι, hSq, hT, hap, h1, hinj, hrange, hxι, -, hTame⟩ :=
    exists_langSetup_F4_of_orderOf_eq_three hpK x hcfg.order
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param (L := AlgebraicClosure F) hap
  have hk0 : ∃ i, k i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h1
    rw [show a = 1 from funext fun i => by rw [hak i, hcon i, pow_zero]; rfl, rootDiagUnit_one]
  have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hcfg.comp
  obtain ⟨hJX, -, -, -⟩ := hcfg.comp
  rcases classify_kernel k hk3 hk0 with ⟨e, he, horth⟩ | hk
  · exact false_of_orth_root S ι hrange hxι hap hJX hperfJ hcfg.mem hω3 hω1 hak he horth
  · exact false_of_a2a2 hcfg S ι hinj hrange hxι hT hap h1 hTame ⟨n, hn, by rw [hSq, hF]⟩ hω3 hω1
      hk3 hk0 hak hk

end Final

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
