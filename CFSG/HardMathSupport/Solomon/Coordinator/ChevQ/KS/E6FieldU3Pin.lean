module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentComp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement MatrixGroups

section Order

variable {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ}

theorem two_suN_exists_equiv_pinned {ℓ f : ℕ} (hℓ : ℓ.Prime) [CharP L ℓ] (hf : 1 ≤ f) (σ : L ≃+* L)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hν : 3 ≤ ν) :
    ∃ (F : Subfield L) (e : StatedSU ν (ℓ ^ f) F ≃* fixSubgroup (stdUnitaryEquiv (ν := ν) σ)),
      Nat.card F = (ℓ ^ f) ^ 2 ∧
      ∀ Y, ((e Y : fixSubgroup (stdUnitaryEquiv (ν := ν) σ)) : SL(ν, L)) =
        statedSUToSL F ν (ℓ ^ f) Y := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set Φ := stdUnitaryEquiv (ν := ν) σ with hΦ
  set F : Subfield L := (iterateFrobenius L ℓ (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hσmap : ∀ M : Matrix (Fin ν) (Fin ν) L, M.map σ.toRingHom = M.map (· ^ ℓ ^ f) := by
    intro M
    ext i j
    simp [hσ]
  have hfix : ∀ X : SL(ν, L), X ∈ fixSubgroup Φ ↔
      Matrix.SpecialLinearGroup.toGL X ∈ unitarySet (ℓ ^ f) ν := by
    intro X
    rw [mem_fixSubgroup, hΦ, stdUnitaryEquiv_apply]
    have hdetX : IsUnit ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)).det := by
      rw [← hσmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, X.2, map_one]
      exact isUnit_one
    constructor
    · intro h
      have hstd : stdUnitary σ.toRingHom X = X := h
      have h1 : (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ =
          (X : Matrix (Fin ν) (Fin ν) L) := by
        rw [← hσmap, ← coe_stdUnitary, hstd]
      have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = 1 := by
        have e1 : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
            (X : Matrix (Fin ν) (Fin ν) L) = ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
              (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ := by rw [h1]
        rw [e1, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdetX, Matrix.transpose_one]
      refine ⟨fun i j => ?_, X.2, hu⟩
      have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom X = invTransposeSL X := by
        have := congrArg invTransposeSL hstd
        rwa [stdUnitary, MonoidHom.comp_apply, invTransposeSL_invTransposeSL] at this
      have h2 : Matrix.SpecialLinearGroup.map σ.toRingHom
          (Matrix.SpecialLinearGroup.map σ.toRingHom X) = X := by
        rw [hmap, slMap_invTransposeSL, ← MonoidHom.comp_apply invTransposeSL, ← stdUnitary, hstd]
      have h3 := congrArg (fun Y : SL(ν, L) => (Y : Matrix (Fin ν) (Fin ν) L) i j) h2
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ] at h3
      rw [← pow_mul, ← sq] at h3
      exact h3
    · rintro ⟨-, -, hu'⟩
      have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = 1 := hu'
      apply Subtype.ext
      rw [coe_stdUnitary, hσmap]
      have : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹ =
          (X : Matrix (Fin ν) (Fin ν) L)ᵀ := by
        refine Matrix.inv_eq_left_inv ?_
        rw [← Matrix.transpose_transpose ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)),
          ← Matrix.transpose_mul, hu, Matrix.transpose_one]
      rw [this, Matrix.transpose_transpose]
  let Ψ : StatedSU ν (ℓ ^ f) F →* SL(ν, L) := statedSUToSL F ν (ℓ ^ f)
  have hΨmem : ∀ Y, Ψ Y ∈ fixSubgroup Φ := fun Y =>
    (hfix _).2 ((mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩)
  let e : StatedSU ν (ℓ ^ f) F ≃* fixSubgroup Φ := MulEquiv.ofBijective (Ψ.codRestrict _ hΨmem)
    ⟨fun Y Z h => statedSUToSL_injective F ν (ℓ ^ f) (congrArg Subtype.val h), fun X => by
      obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) X).mpr
        ((hfix X).1 X.2)
      exact ⟨Y, Subtype.ext hY⟩⟩
  exact ⟨F, e, hFcard, fun Y => rfl⟩

end Order

section Construction

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem two_suN_exists_pinned (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1)
    (hνQ : (ν, r ^ e) ≠ (3, 2)) :
    ∃ (σQ : L ≃+* L) (z : ModGL τ L), (∀ c, σQ c = c ^ (r ^ e)) ∧
      CFSG.IsQuasisimple ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) ∧
      rationalComponent S.ρ S.Γ (rootCharHom ta) i =
        ((MulAut.conj z).toMonoidHom.comp
          (ψ.comp (fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)).subtype)).range ∧
      ((MulAut.conj z).toMonoidHom.comp
          (ψ.comp (fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)).subtype)).ker ≤
        Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
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
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
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
  obtain ⟨z, hz, hnorm⟩ := exists_lang_mul_T S hT hs0 hy₁
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
  set C := fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, mem_fixSubgroup, stdUnitaryEquiv_apply]
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
  have hes : 0 < e * s := Nat.mul_pos he hs0
  have hFs1 : ∀ x, Fs x = S.D.step x := fun x => by
    rw [hFs, hs1]
    rfl
  have hstepfix : ∀ g ∈ S.Γ, S.D.step g = g := fun g hg =>
    ((S.D.mem_model).1 (commutator_le_self_of_subgroup S.D.model hg)).2
  have hνQ' : (ν, r ^ (e * s)) ≠ (3, 2) := by
    rw [hs1, Nat.mul_one]
    exact hνQ
  obtain ⟨-, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  have hCQ : CFSG.IsQuasisimple ↥C := hqsC hνQ'
  have hperfC : Group.IsPerfect ↥C := hCQ.1
  have hmodel : ∀ c : C, θ c ∈ S.D.model := fun c => by
    refine (S.D.mem_model).2 ⟨?_, ?_⟩
    · exact rootSpan_le_adjointGroup L _ (hθS c)
    · have := hθfix c
      rw [hFs1] at this
      exact this
  have hθΓ : ∀ c : C, θ c ∈ S.Γ := fun c =>
    map_mem_commutator_of_perfect hperfC θ S.D.model hmodel c
  have hρΨ : ∀ γ ∈ componentRoots (rootCharHom ta) i,
      S.ρ γ ∈ componentRoots (rootCharHom ta) i := by
    intro γ hγ
    have h1 : (S.ρ : (Fin τ.rank → ℤ) → _) γ ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom ta) i := by
      rw [hs1]
      exact ⟨γ, hγ, rfl⟩
    rwa [hs] at h1
  have hrr : rationalRoots S.ρ (rootCharHom ta) i = componentRoots (rootCharHom ta) i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k with
      | zero => exact hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hρΨ _ ih
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  have hrsΨ : rationalSpan S.ρ S.Γ (rootCharHom ta) i =
      rootSpan τ L (componentRoots (rootCharHom ta) i) ⊓ S.Γ := by
    unfold rationalSpan
    rw [hrr]
  have hθrs : ∀ c : C, θ c ∈ rationalSpan S.ρ S.Γ (rootCharHom ta) i := fun c => by
    rw [hrsΨ]
    exact ⟨hθS c, hθΓ c⟩
  refine ⟨σQ, z, fun c => by rw [hσc c, hs1, Nat.mul_one], hCQ, ?_, ?_⟩
  · apply le_antisymm
    · unfold rationalComponent
      rw [Subgroup.commutator_le]
      intro g hg g' hg'
      rw [hrsΨ] at hg hg'
      refine hθY g g' hg.1 hg'.1 ?_ ?_
      · have : Fs g = g := by rw [hFs1]; exact hstepfix g hg.2
        rw [this, mul_inv_cancel]
        exact P.Z.one_mem
      · have : Fs g' = g' := by rw [hFs1]; exact hstepfix g' hg'.2
        rw [this, mul_inv_cancel]
        exact P.Z.one_mem
    · rintro _ ⟨c, rfl⟩
      unfold rationalComponent
      exact map_mem_commutator_of_perfect hperfC θ _ hθrs c
  · intro c hc
    apply hθZ
    rw [MonoidHom.mem_ker] at hc
    rw [hc]
    exact P.Z.one_mem

end Construction


section E6


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem Std8.exists_pinned_su3
    (D : Std8 L) {ω : Lˣ} (hω : orderOf ω = 3) (i : KernelComponent (rootCharHom (a0 ω))) :
    ∃ (F : Subfield L) (ψ : SL(3, L) →* ModGL Tag.E6 L)
      (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ) (z : ModGL Tag.E6 L),
      Nat.card F = (2 ^ 3) ^ 2 ∧ IsSLFrame ψ σ ∧ (∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2) ∧
      componentRoots (rootCharHom (a0 ω)) i = frameRoots σ ∧
      CFSG.Open.IsQuasisimple ↥(StatedSU 3 (2 ^ 3) F) ∧
      rationalComponent D.S.ρ D.S.Γ (rootCharHom (a0 ω)) i =
        ((MulAut.conj z).toMonoidHom.comp (ψ.comp (statedSUToSL F 3 (2 ^ 3)))).range ∧
      ((MulAut.conj z).toMonoidHom.comp (ψ.comp (statedSUToSL F 3 (2 ^ 3)))).ker ≤
        Subgroup.center ↥(StatedSU 3 (2 ^ 3) F) := by
  obtain ⟨ψ, σ, hψ, hnorm, hΨ⟩ := exists_frames_a0 hω i
  have hs1 := D.orbitLength_eq_one i
  have hπ : ∀ a' b : Fin 3, a' ≠ b → (D.S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength
      D.S.ρ (componentRoots (rootCharHom (a0 ω)) i)] (σ a' b) =
        σ ((Equiv.refl (Fin 3)) b) ((Equiv.refl (Fin 3)) a') := by
    intro a' b _
    rw [hs1, Function.iterate_one, D.hρ]
    exact (hψ.neg a' b).symm
  have hq8 : D.S.D.q = 2 ^ 3 := D.hq.trans (by norm_num)
  have hνQ : ((3 : ℕ), 2 ^ 3) ≠ (3, 2) := by decide
  obtain ⟨σQ, z, hσc, hCQ, hR, hker⟩ := two_suN_exists_pinned D.S (D.a0_mem_torus hω) i
    (by norm_num : 3 ≤ 3) hψ hΨ (Equiv.refl _) hπ Nat.prime_two inferInstance
    (by norm_num : 0 < 3) hq8 hs1 hνQ
  obtain ⟨F, eC, hFcard, heC⟩ := two_suN_exists_equiv_pinned (L := L) Nat.prime_two (f := 3)
    (by norm_num) σQ hσc (by norm_num : 3 ≤ 3)
  have hπ₀ : ∀ g, ((MulAut.conj z).toMonoidHom.comp (ψ.comp (statedSUToSL F 3 (2 ^ 3)))) g =
      ((MulAut.conj z).toMonoidHom.comp
        (ψ.comp (fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)).subtype)) (eC g) := by
    intro g
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [heC g]
  refine ⟨F, ψ, σ, z, hFcard, hψ, hnorm, hΨ, ?_, ?_, ?_⟩
  · exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv eC.symm hCQ)
  · rw [hR]
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨g, rfl⟩ := eC.surjective c
      exact ⟨g, hπ₀ g⟩
    · rintro ⟨g, rfl⟩
      exact ⟨eC g, (hπ₀ g).symm⟩
  · intro g hg
    rw [MonoidHom.mem_ker, hπ₀] at hg
    have h1 : eC g ∈ Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := 3) σQ)) :=
      hker (MonoidHom.mem_ker.2 hg)
    rw [← Subgroup.map_center_eq eC] at h1
    obtain ⟨g', hg', hgg'⟩ := h1
    have : g' = g := eC.injective hgg'
    rw [← this]
    exact hg'

end E6

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
