module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeCentreFrame
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace CubeCentre

section Norm

theorem iterHom_eq_self_of_fixed {G : Type*} [Group G] {F : G →* G} {y : G} (hy : F y = y)
    (n : ℕ) : iterHom F n y = y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterHom_succ, ih, hy]

theorem norm_eq_pow_of_fixed {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]
    (P : CycFamily F s) (y : P.S 0) (hy : F (y : G) = y) : P.norm y = (y : G) ^ s := by
  classical
  unfold CycFamily.norm CycFamily.mu
  rw [MonoidHom.comp_apply, Subgroup.noncommPiCoprod_apply]
  refine (Finset.noncommProd_eq_pow_card _ _ _ (y : G) ?_).trans ?_
  · intro k _
    simp [CycFamily.coe_diag_apply, iterHom_eq_self_of_fixed hy]
  · simp [ZMod.card]

theorem exists_cube_root_ne_one {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0) :
    ∃ ω : Lˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  haveI : NeZero ((3 : ℕ) : L) := ⟨h3⟩
  obtain ⟨x, hx⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  refine ⟨Units.mk0 x (hx.ne_zero (by norm_num)), Units.ext ?_, fun h => ?_⟩
  · rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact hx.pow_eq_one
  · exact hx.ne_one (by norm_num) (by simpa using congrArg Units.val h)

end Norm

section Hom

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem step_rootDiagUnit (hT : rootDiagUnit τ ta ∈ S.D.torus) :
    S.D.step (rootDiagUnit τ ta) = rootDiagUnit τ ta :=
  (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hT).2

theorem rootDiagUnit_pow_three_eq_one {a : Fin τ.rank → Lˣ} (ha : ∀ j, a j ^ 3 = 1) :
    rootDiagUnit τ a ^ 3 = 1 := by
  have h : a ^ 3 = 1 := funext ha
  calc rootDiagUnit τ a ^ 3 = rootDiagUnit τ (a ^ 3) :=
        (map_pow (CFSG.LieType.Chevalley.rootDiagUnitHom τ L) a 3).symm
    _ = 1 := by rw [h, CFSG.LieType.Chevalley.rootDiagUnit_one]

theorem rootDiagUnit_mul_comm_of_mem_Z (a : Fin τ.rank → Lˣ) {z : ModGL τ L}
    (hz : z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    rootDiagUnit τ a * z = z * rootDiagUnit τ a := by
  have hle : torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) ≤
      Subgroup.centralizer {rootDiagUnit τ a} := by
    refine sup_le (fun h hh => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (rootDiagUnit_mul_comm_of_mem_torusGroup a hh).symm
    · refine iSup₂_le fun γ hγ => ?_
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have h1 := rootDiagUnit_conj_pinnedX (K := L) (a := a) hγ.1 c
      have h2 : (rootChar a γ : L) = 1 := by
        have := hγ.2
        change rootChar a γ = 1 at this
        rw [this]
        rfl
      rw [h2, one_mul] at h1
      symm
      calc rootDiagUnit τ a * pinnedX τ L γ c
          = (rootDiagUnit τ a * pinnedX τ L γ c * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by
            group
        _ = pinnedX τ L γ c * rootDiagUnit τ a := by rw [h1]
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem rationalComponent_eq_range_of_hom_norm (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom ta) i =
      componentRoots (rootCharHom ta) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom ta) i ≠
        componentRoots (rootCharHom ta) i)
    {C : Type*} [Group C] (θ : C →* ModGL τ L)
    (hθS : ∀ c, θ c ∈ rootSpan τ L (componentRoots (rootCharHom ta) i))
    (hθfix : ∀ c, iterHom S.D.step s (θ c) = θ c)
    (hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      iterHom S.D.step s g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      iterHom S.D.step s g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z → ⁅g, g'⁆ ∈ θ.range)
    (hθZ : ∀ c, θ c ∈ (outerOrbitFamily S hT i hs hmin).Z → c ∈ Subgroup.center C) :
    ∃ f : C →* ModGL τ L, rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤ f.range ∧
      f.ker ≤ Subgroup.center C ∧
      (Group.IsPerfect C → f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom ta) i) ∧
      ∀ c, S.D.step (θ c) = θ c → f c = θ c ^ s := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  set Ψ := componentRoots (rootCharHom ta) i with hΨ
  have hP0 : P.S 0 = rootSpan τ L Ψ := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
    rfl
  let θ₀ : C →* P.S 0 := θ.codRestrict (P.S 0) fun c => by
    rw [hP0]
    exact hθS c
  have hθ₀ : ∀ c, ((θ₀ c : P.S 0) : ModGL τ L) = θ c := fun c => rfl
  let f : C →* ModGL τ L := P.norm.comp θ₀
  have hfix : ∀ c, iterHom S.D.step s ((θ₀ c : P.S 0) : ModGL τ L) = θ₀ c := fun c => by
    rw [hθ₀]; exact hθfix c
  have hYW : ⁅P.Y, P.Y⁆ ≤ θ.range := by
    rw [Subgroup.commutator_le]
    intro u hu u' hu'
    obtain ⟨hu0, huZ⟩ := P.mem_Y.1 hu
    obtain ⟨hu0', huZ'⟩ := P.mem_Y.1 hu'
    rw [hP0] at hu0 hu0'
    exact hθY u u' hu0 hu0' huZ huZ'
  have hΓM : S.Γ ≤ S.D.model := commutator_le_self' _
  have hrsA : rationalSpan S.ρ S.Γ (rootCharHom ta) i ≤ P.Afix := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine ⟨?_, (hΓM hx2).2⟩
    rw [hP, outerOrbitFamily_A]
    exact hx1
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have h1 := P.commutator_Afix_le (Subgroup.commutator_mono hrsA hrsA hg)
    obtain ⟨y, hyY, rfl⟩ := P.mem_normImage.1 h1
    obtain ⟨c, hc⟩ := hYW hyY
    refine ⟨c, ?_⟩
    change P.norm (θ₀ c) = P.norm y
    congr 1
    exact Subtype.ext hc
  · intro c hc
    have h1 : P.norm (θ₀ c) = 1 := hc
    exact hθZ c (P.mem_Z_of_norm_eq_one h1)
  · intro hperf
    rintro _ ⟨x, rfl⟩
    exact outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hfix x
  · intro c hc
    exact norm_eq_pow_of_fixed P (θ₀ c) hc

theorem exists_suN_hom_norm (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ σQ : L ≃+* L,
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)))) ∧
      ∃ z : ModGL τ L, rootDiagUnit τ ta * z = z * rootDiagUnit τ ta ∧
      ∃ f : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →* ModGL τ L,
        rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤ f.range ∧
        f.ker ≤ Subgroup.center
          ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) ∧
        (Group.IsPerfect
            ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →
          f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom ta) i) ∧
        ∀ c : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)),
          S.D.step (z * ψ c * z⁻¹) = z * ψ c * z⁻¹ →
            f c = (z * ψ c * z⁻¹) ^ componentOrbitLength S.ρ
              (componentRoots (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
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
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom ta) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
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
  have hnorm := mem_componentRootSpan_iff_conj_of_mem hzZ
  have hconj : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
    intro X
    rw [← hstd X, map_mul, map_mul, map_inv, hz]
    group
  have hzA : ∀ y ∈ P.A, z * y * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) := by rw [hj]; exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun y hy => h hy
  have hZconj : ∀ x : ModGL τ L, z * x * z⁻¹ ∈ P.Z → x ∈ P.Z := by
    intro x hx
    rw [CycFamily.mem_Z] at hx ⊢
    intro y hy
    have := hx _ (hzA y hy)
    have e1 : z * y * z⁻¹ * (z * x * z⁻¹) = z * (y * x) * z⁻¹ := by group
    have e2 : z * x * z⁻¹ * (z * y * z⁻¹) = z * (x * y) * z⁻¹ := by group
    rw [e1, e2] at this
    simpa using this
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε _ _ h01, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hcentral : ∀ X : SL(ν, L), ψ X ∈ P.Z → X ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker fun Y => ?_
    have hYA : ψ Y ∈ P.A := P.S_le_A 0 (by rw [hP0]; exact hψS Y)
    exact ((CycFamily.mem_Z P).1 hX (ψ Y) hYA).symm
  set C := CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  let θ : C →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ c * z⁻¹ := fun c => rfl
  have hθS : ∀ c : C, θ c ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun c => by
    rw [hθ]
    exact (hnorm i _).1 (hψS c)
  have hθfix : ∀ c : C, Fs (θ c) = θ c := fun c => by
    rw [hθ, hconj, (hCmem c).1 c.2]
  have hpre : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i),
      ∃ X : SL(ν, L), g = z * ψ X * z⁻¹ := by
    intro g hg
    have h1 : z⁻¹ * g * z ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
      rw [e]
      exact hg)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    exact ⟨X, by rw [hX]; group⟩
  have hfixmod : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ ∈ P.Z →
      stdUnitary σQ.toRingHom X * X⁻¹ ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    have e : Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ =
        z * ψ (stdUnitary σQ.toRingHom X * X⁻¹) * z⁻¹ := by
      rw [hconj, map_mul, map_inv]
      group
    rw [e] at hX
    exact hcentral _ (hZconj _ hX)
  have hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) → Fs g * g⁻¹ ∈ P.Z →
        Fs g' * g'⁻¹ ∈ P.Z → ⁅g, g'⁆ ∈ θ.range := by
    intro g g' hg hg' hgZ hg'Z
    obtain ⟨X, rfl⟩ := hpre g hg
    obtain ⟨X', rfl⟩ := hpre g' hg'
    have hc := hfixmod X hgZ
    have hc' := hfixmod X' hg'Z
    set c := stdUnitary σQ.toRingHom X * X⁻¹ with hcdef
    set c' := stdUnitary σQ.toRingHom X' * X'⁻¹ with hc'def
    have hX : stdUnitary σQ.toRingHom X = c * X := by rw [hcdef, inv_mul_cancel_right]
    have hX' : stdUnitary σQ.toRingHom X' = c' * X' := by rw [hc'def, inv_mul_cancel_right]
    have hcomm : ∀ (w : SL(ν, L)) (hw : w ∈ Subgroup.center SL(ν, L)) (y : SL(ν, L)),
        Commute w y := fun w hw y => (Subgroup.mem_center_iff.1 hw y).symm
    have hfixc : stdUnitary σQ.toRingHom ⁅X, X'⁆ = ⁅X, X'⁆ := by
      rw [map_commutatorElement, hX, hX']
      exact CycFamily.commutatorElement_central_mul (hcomm c hc X) (hcomm c hc X')
        (hcomm c hc c') (hcomm c' hc' X) (hcomm c' hc' X')
    refine ⟨⟨⁅X, X'⁆, (hCmem _).2 hfixc⟩, ?_⟩
    rw [hθ]
    simp only [commutatorElement_def, map_mul, map_inv]
    group
  have hθZ : ∀ c : C, θ c ∈ P.Z → c ∈ Subgroup.center C := by
    intro c hc
    rw [hθ] at hc
    have h := hcentral _ (hZconj _ hc)
    rw [Subgroup.mem_center_iff]
    intro d'
    exact Subtype.ext (Subgroup.mem_center_iff.1 h d')
  obtain ⟨f, hf1, hfker, hf2, hfs⟩ :=
    rationalComponent_eq_range_of_hom_norm S hT i hs hmin θ hθS hθfix hθY hθZ
  exact ⟨σQ, hσc, z, rootDiagUnit_mul_comm_of_mem_Z ta hzZ, f, hf1, hfker, hf2, hfs⟩

theorem stdUnitary_scalar_eq_self (σ : L →+* L) {X : SL(3, L)} {r : L}
    (hX : (X : Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) r) (hr : σ r * r = 1) :
    stdUnitary σ X = X := by
  apply Subtype.ext
  rw [coe_stdUnitary, hX, Matrix.scalar_apply, Matrix.diagonal_map (map_zero σ)]
  have hinv : (Matrix.diagonal fun _ : Fin 3 => σ r)⁻¹ = Matrix.diagonal fun _ : Fin 3 => r := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, hr, Matrix.diagonal_one]
  rw [hinv, Matrix.diagonal_transpose]

theorem center_le_fixSubgroup {Q : ℕ} (σQ : L ≃+* L) (hσc : ∀ c, σQ c = c ^ Q) (h3 : 3 ∣ Q + 1) :
    Subgroup.center SL(3, L) ≤
      CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ) := by
  intro X hX
  obtain ⟨r, hr, hrX⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hX
  rw [Fintype.card_fin] at hr
  rw [CFSG.RankThree.Classical2.mem_fixSubgroup, stdUnitaryEquiv_apply]
  refine stdUnitary_scalar_eq_self σQ.toRingHom hrX.symm ?_
  obtain ⟨k, hk⟩ := h3
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσc, ← pow_succ, hk, pow_mul, hr,
    one_pow]

theorem card_center_fixSubgroup_three {r f : ℕ} (hr : r.Prime) [CharP L r] (hf : 1 ≤ f)
    (σQ : L ≃+* L) (hσc : ∀ c, σQ c = c ^ (r ^ f)) (h3 : 3 ∣ r ^ f + 1) :
    Nat.card (Subgroup.center
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ))) = 3 := by
  obtain ⟨F, hFcard, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Exc.two_suN_exists_equiv (ν := 3) hr hf σQ hσc le_rfl
  haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hr.pos _) 2).ne')
  rw [← Nat.card_congr (Subgroup.centerCongr eC).toEquiv]
  exact CFSG.Open.StatedCenterThree.card_center_statedSU_three hFcard h3

end Hom

end CubeCentre

section Centre


theorem center_rationalComponent_eq_bot_of_orbit_three
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)
    {ta : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 ta ∈ S.D.torus)
    (hap : ∀ j, ta j ^ 3 = 1) (i : KernelComponent (rootCharHom ta))
    (hi6 : (componentRoots (rootCharHom ta) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    (π : Equiv.Perm (Fin 3))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hs3 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 3)
    (h3q : 3 ∣ S.D.q + 1) :
    Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) = ⊥ := by
  classical
  have hr3 : r ≠ 3 := by
    rintro rfl
    rw [hq] at h3q
    exact absurd ((Nat.dvd_add_right (dvd_pow_self 3 he.ne')).1 h3q) (by norm_num)
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff L r]
    exact fun h => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)
  obtain ⟨σQ, hσc, z, hzd, f, hf1, hfker, hf2, hfs⟩ :=
    CubeCentre.exists_suN_hom_norm S hT i le_rfl hψ hΨ π hπ hr hchar he hq
  rw [hs3] at hσc hfs
  have hes : 1 ≤ e * 3 := by omega
  have hQ3 : 3 ∣ r ^ (e * 3) + 1 := by
    have hq3 : S.D.q % 3 = 2 := by omega
    have h' : S.D.q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hq3]
    rw [pow_mul, ← hq]
    generalize S.D.q ^ 3 = Q at h' ⊢
    omega
  have hνQ : ((3 : ℕ), r ^ (e * 3)) ≠ (3, 2) := by
    intro h
    have h2 : r ^ (e * 3) = 2 := (Prod.mk.inj h).2
    have h8 : 2 ^ 3 ≤ r ^ (e * 3) :=
      (Nat.pow_le_pow_left hr.two_le 3).trans (Nat.pow_le_pow_right hr.pos (by omega))
    rw [h2] at h8
    norm_num at h8
  have hCperf := ((stdUnitary_fixSubgroup (ν := 3) hr hes σQ hσc le_rfl).2.1 hνQ).1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  let g : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center
      ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  obtain ⟨c₀, hc₀Z, hc₀1, hfc₀⟩ : ∃ c₀ : ↥(CFSG.RankThree.Classical2.fixSubgroup
      (stdUnitaryEquiv (ν := 3) σQ)), c₀ ∈ Subgroup.center _ ∧ c₀ ≠ 1 ∧ f c₀ = 1 := by
    obtain ⟨ω, hω3, hω1⟩ := CubeCentre.exists_cube_root_ne_one h3L
    obtain ⟨X₀, hX₀⟩ : ∃ X₀ : SL(3, L),
        (X₀ : Matrix (Fin 3) (Fin 3) L) = Matrix.scalar (Fin 3) (ω : L) :=
      ⟨blockTorusProd (m := 2) ω 2, coe_blockTorusProd_eq_scalar (m := 2) ω hω3⟩
    have hX₀c : X₀ ∈ Subgroup.center SL(3, L) :=
      Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨(ω : L), by
        rw [Fintype.card_fin, ← Units.val_pow_eq_pow_val, hω3, Units.val_one], hX₀.symm⟩
    have hX₀1 : X₀ ≠ 1 := by
      intro h
      apply hω1
      have h1 : Matrix.scalar (Fin 3) (ω : L) = Matrix.scalar (Fin 3) 1 := by
        rw [← hX₀, h, Matrix.SpecialLinearGroup.coe_one, (Matrix.scalar (Fin 3)).map_one]
      exact Units.val_eq_one.1 (Matrix.scalar_inj.1 h1)
    have hX₀C := CubeCentre.center_le_fixSubgroup σQ hσc hQ3 hX₀c
    refine ⟨⟨X₀, hX₀C⟩, Subgroup.mem_center_iff.2 fun d' => Subtype.ext
      (Subgroup.mem_center_iff.1 hX₀c d'), fun h => hX₀1 (congrArg Subtype.val h), ?_⟩
    have hψX : ψ X₀ ∈ Subgroup.zpowers (rootDiagUnit Tag.E6 ta) :=
      map_center_frame_le_zpowers_rootDiagUnit hap i hi6 hψ hΨ (Subgroup.mem_map_of_mem ψ hX₀c)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hψX
    have hzd' : Commute (rootDiagUnit Tag.E6 ta) z := hzd
    have hzX : z * ψ X₀ * z⁻¹ = ψ X₀ := by
      rw [← hk, ← (hzd'.zpow_left k).eq, mul_inv_cancel_right]
    have hstepX : S.D.step (z * ψ X₀ * z⁻¹) = z * ψ X₀ * z⁻¹ := by
      rw [hzX, ← hk, map_zpow, CubeCentre.step_rootDiagUnit S hT]
    have hfX : f ⟨X₀, hX₀C⟩ = (z * ψ X₀ * z⁻¹) ^ 3 := hfs ⟨X₀, hX₀C⟩ hstepX
    rw [hfX, hzX, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast,
      CubeCentre.rootDiagUnit_pow_three_eq_one hap, one_zpow]
  have hZ3 := CubeCentre.card_center_fixSubgroup_three hr hes σQ hσc hQ3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_center_of_surjective
    (Group.isPerfect_def.1 hCperf) g hgsurj hgker, Subgroup.map_eq_bot_iff]
  intro c hc
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  show f c = 1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_prime_card hZ3 (g := ⟨c₀, hc₀Z⟩) (g' := ⟨c, hc⟩)
      (fun h => hc₀1 (congrArg Subtype.val h)))
  have hck : c = c₀ ^ k := by
    have h := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h
    exact h.symm
  rw [hck, map_zpow, hfc₀, one_zpow]

theorem rootDiagUnit_mem_rationalComponent_of_stable
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
    (h3q : 3 ∣ S.D.q + 1) (hq2 : S.D.q ≠ 2) :
    rootDiagUnit Tag.E6 ta ∈ rationalComponent S.ρ S.Γ (rootCharHom ta) i := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, hσc, z, hzd, f, -, -, hf2, hfs⟩ :=
    CubeCentre.exists_suN_hom_norm S hT i le_rfl hψ hΨ π hπ hr hchar he hq
  rw [hs1] at hσc hfs
  rw [mul_one] at hσc
  have hQ3 : 3 ∣ r ^ e + 1 := by
    rw [← hq]
    exact h3q
  have hνQ : ((3 : ℕ), r ^ e) ≠ (3, 2) := by
    rw [← hq]
    intro h
    exact hq2 (Prod.mk.inj h).2
  have hCperf := ((stdUnitary_fixSubgroup (ν := 3) hr he σQ hσc le_rfl).2.1 hνQ).1
  have hd : rootDiagUnit Tag.E6 ta ∈ (Subgroup.center SL(3, L)).map ψ := by
    rw [map_center_frame_eq_zpowers_rootDiagUnit hap h1 i hi6 hψ hΨ]
    exact Subgroup.mem_zpowers _
  obtain ⟨X, hXc, hXd⟩ := Subgroup.mem_map.1 hd
  have hXC := CubeCentre.center_le_fixSubgroup σQ hσc hQ3 hXc
  have hzX : z * ψ X * z⁻¹ = ψ X := by
    rw [hXd, ← hzd, mul_inv_cancel_right]
  have hstepX : S.D.step (z * ψ X * z⁻¹) = z * ψ X * z⁻¹ := by
    rw [hzX, hXd]
    exact CubeCentre.step_rootDiagUnit S hT
  have hfX : f ⟨X, hXC⟩ = (z * ψ X * z⁻¹) ^ 1 := hfs ⟨X, hXC⟩ hstepX
  refine hf2 hCperf (MonoidHom.mem_range.2 ⟨⟨X, hXC⟩, ?_⟩)
  rw [hfX, pow_one, hzX, hXd]

end Centre

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
