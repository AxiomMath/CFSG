module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthFactor
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLCellSpBlock
import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict

public section

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.AGLEmbedding.ToralCensus

open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

theorem not_isSolvable_commutator_subgroup {G : Type*} [Group G] {H : Subgroup G}
    (hH : ¬ Group.IsSolvable H) : ¬ Group.IsSolvable ↥⁅H, H⁆ := by
  intro hs
  have hmap : (commutator H).map H.subtype = ⁅H, H⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hmem : ∀ c : commutator H, H.subtype c.1 ∈ ⁅H, H⁆ := fun c => by
    rw [← hmap]; exact ⟨c.1, c.2, rfl⟩
  let f : commutator H →* ↥⁅H, H⁆ := (H.subtype.comp (commutator H).subtype).codRestrict _ hmem
  have hf : Function.Injective f := fun a b hab => by
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have h1 : Group.IsSolvable (commutator H) := Group.isSolvable_of_isSolvable_injective hf
  exact hH (Group.isSolvable_commutator_iff.mp h1)

theorem not_isSolvable_inf_derived_of_embed {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {x : V ≃ₗ[K] V} {M : Type*} [Group M] (hM : ¬ Group.IsSolvable M)
    (ι : M →* (V ≃ₗ[K] V)) (hι : Function.Injective ι) (hle : ι.range ≤ isometryCentralizer Q x) :
    ¬ Group.IsSolvable ↥(isometryCentralizer Q x ⊓ orthDerived Q) := by
  have hO : ι.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hle.trans (inf_le_left : isometryCentralizer Q x ≤ _)
  have hH : ¬ Group.IsSolvable ι.range := fun hs =>
    hM (Group.isSolvable_of_isSolvable_injective (f := ι.rangeRestrict)
      (fun a b hab => hι (congrArg Subtype.val hab)))
  have hc := not_isSolvable_commutator_subgroup hH
  have hle2 : ⁅ι.range, ι.range⁆ ≤ isometryCentralizer Q x ⊓ orthDerived Q :=
    le_inf ((Subgroup.commutator_le_self _).trans hle) (Subgroup.commutator_mono hO hO)
  intro hs
  exact hc (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle2)
    (Subgroup.inclusion_injective hle2))

section Block

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

omit [Finite K] [FiniteDimensional K V] in
theorem not_isSolvable_of_block_embed {h : K[X]} {M : Type*} [Group M]
    (hM : ¬ Group.IsSolvable M) (ι : M →* ↥(supportedBlock Q x h)) (hι : Function.Injective ι) :
    ¬ Group.IsSolvable ↥(isometryCentralizer Q x ⊓ orthDerived Q) := by
  refine not_isSolvable_inf_derived_of_embed hM ((supportedBlock Q x h).subtype.comp ι)
    ((Subgroup.subtype_injective _).comp hι) ?_
  rintro _ ⟨g, rfl⟩
  exact (inf_le_left : supportedBlock Q x h ≤ _) (ι g).2

theorem exists_selfDual_unitary_odd {p : ℕ} (hp2 : Odd p) (hx : OddOrderIsometry Q p x) {h : K[X]}
    [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hX : h ≠ X - 1) (hself : h = reciprocalPolynomial h) :
    ∃ (ℓ f d : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar] primaryComponent x.toLinearMap h
        →ₗ[AdjoinRoot h] AdjoinRoot h),
      h.natDegree = 2 * d ∧ Nat.card K = ℓ ^ f ∧ B.IsSymm ∧ B.SeparatingLeft ∧
        Nonempty (↥(supportedBlock Q x h) ≃* ↥(sesqUnitaryGroup B)) := by
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hX hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (CFSG.RankThree.PartOne.KCOrthogonal.blockGL Q x h).range = sesqUnitaryGroup B := by
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hX hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  refine ⟨ℓ, f, d, hU, B, hdeg, hq, hBsymm, hBl, ⟨?_⟩⟩
  exact (MonoidHom.ofInjective (hx.blockGL_injective hh)).trans (MulEquiv.subgroupCongr hrange)

theorem not_isSolvable_isometryCentralizer_of_mult [CharP K 2] {p : ℕ}
    (hx : OddOrderIsometry Q p x) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hm : 5 ≤ primaryMultiplicity x.toLinearMap h) :
    ¬ Group.IsSolvable ↥(isometryCentralizer Q x ⊓ orthDerived Q) := by
  classical
  have hp2 : Odd p := by
    rcases Nat.even_or_odd p with he | ho
    · exfalso
      apply hx.cast_ne_zero
      rw [CharP.cast_eq_zero_iff K 2]
      exact even_iff_two_dvd.mp he
    · exact ho
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  by_cases hX : h = X - 1
  ·
    subst hX
    have hdim := finrank_primaryComponent x.toLinearMap (X - 1 : K[X])
    have hnat : (X - 1 : K[X]).natDegree = 1 := natDegree_X_sub_C 1
    rw [hnat, one_mul] at hdim
    have hd5 : 5 ≤ finrank K (fixedSpace x) := by
      rw [fixedSpace_eq_primaryComponent, hdim]; exact hm
    obtain ⟨s, hs⟩ := exists_finrank_eq_two_mul hx.polarBilin_fixed_nondegenerate
    have hd6 : 6 ≤ finrank K (fixedSpace x) := by omega
    obtain ⟨W, hWle, hWperf, T, hTW, hT3, hTnc⟩ :=
      perfectNoncycThreeIn_orth_six hx.polarBilin_fixed_nondegenerate hd6
    have hWne : W ≠ ⊥ := by
      intro hbot
      apply hTnc
      have : T = ⊥ := le_bot_iff.mp (hbot ▸ hTW)
      rw [this]
      infer_instance
    have hperf : Group.IsPerfect ↥W := Subgroup.isPerfect_iff.mpr hWperf
    have hnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hWne
    exact not_isSolvable_of_block_embed (h := X - 1) (Group.IsPerfect.not_isSolvable _)
      ((fixedBlockEquiv hx).symm.toMonoidHom.comp (Subgroup.inclusion hWle))
      ((fixedBlockEquiv hx).symm.injective.comp (Subgroup.inclusion_injective hWle))
  · by_cases hself : reciprocalPolynomial h = h
    ·
      obtain ⟨ℓ, f, d, hU, B, -, -, hBs, hBl, ⟨φ⟩⟩ :=
        exists_selfDual_unitary_odd hp2 hx hh hX hself.symm
      have : Finite (AdjoinRoot h) := hU.finite
      obtain ⟨e, he⟩ := hU.exists_orthonormal_basis hBs hBl
      let E := AdjoinRoot h
      let W := primaryComponent x.toLinearMap h
      let m := primaryMultiplicity x.toLinearMap h
      let gl := LinearMap.GeneralLinearGroup.generalLinearEquiv E W
      have hcoe : ∀ (δ : W ≃ₗ[E] W) u,
          (((gl.symm δ : LinearMap.GeneralLinearGroup E W) : Module.End E W) u) = δ u :=
        fun δ u => congrArg (fun f => f u) (gl.apply_symm_apply δ)
      let pe : Equiv.Perm (Fin m) →* (W ≃ₗ[E] W) :=
        { toFun := CFSG.RankThree.PartOne.KCSymplectic.permEquiv e
          map_one' := by
            refine LinearEquiv.toLinearMap_injective (e.ext fun j => ?_)
            change CFSG.RankThree.PartOne.KCSymplectic.permEquiv e 1 (e j) = e j
            rw [CFSG.RankThree.PartOne.KCSymplectic.permEquiv_apply_basis]
            rfl
          map_mul' := fun τ σ' => by
            refine LinearEquiv.toLinearMap_injective (e.ext fun j => ?_)
            change CFSG.RankThree.PartOne.KCSymplectic.permEquiv e (τ * σ') (e j) =
              CFSG.RankThree.PartOne.KCSymplectic.permEquiv e τ
                (CFSG.RankThree.PartOne.KCSymplectic.permEquiv e σ' (e j))
            rw [CFSG.RankThree.PartOne.KCSymplectic.permEquiv_apply_basis,
              CFSG.RankThree.PartOne.KCSymplectic.permEquiv_apply_basis,
              CFSG.RankThree.PartOne.KCSymplectic.permEquiv_apply_basis]
            rfl }
      have hmem : ∀ τ, gl.symm (pe τ) ∈ sesqUnitaryGroup B := by
        intro τ
        refine mem_sesqUnitaryGroup.2 fun u v => ?_
        rw [hcoe, hcoe]
        exact CFSG.RankThree.PartOne.KCSymplectic.herm_perm e B he τ u v
      let ι0 : Equiv.Perm (Fin m) →* sesqUnitaryGroup B :=
        (gl.symm.toMonoidHom.comp pe).codRestrict _ hmem
      have hι0 : Function.Injective ι0 := by
        intro τ τ' hττ
        have h3 : gl.symm (pe τ) = gl.symm (pe τ') := congrArg Subtype.val hττ
        have h4 : pe τ = pe τ' := gl.symm.injective h3
        have h5 : ∀ j, e (τ j) = e (τ' j) := by
          intro j
          have := congrArg (fun δ : W ≃ₗ[E] W => δ (e j)) h4
          simpa [pe, CFSG.RankThree.PartOne.KCSymplectic.permEquiv_apply_basis] using this
        exact Equiv.ext fun j => e.injective (h5 j)
      exact not_isSolvable_of_block_embed (h := h)
        (Equiv.Perm.not_isSolvable (Fin m) (by rw [Cardinal.mk_fin]; exact_mod_cast hm))
        (φ.symm.toMonoidHom.comp ι0) (φ.symm.injective.comp hι0)
    ·
      have hne : h ≠ reciprocalPolynomial h := fun e => hself e.symm
      have := finite_adjoinRoot (K := K) (h := h)
      set b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
        (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
      exact not_isSolvable_of_block_embed (h := h)
        (not_isSolvable_gl (by omega) (AdjoinRoot h))
        ((pairedBlockEquiv hx hh hne).symm.toMonoidHom.comp
          (Matrix.GeneralLinearGroup.toLin' b).toMonoidHom)
        ((pairedBlockEquiv hx hh hne).symm.injective.comp
          (Matrix.GeneralLinearGroup.toLin' b).injective)

end Block

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell
