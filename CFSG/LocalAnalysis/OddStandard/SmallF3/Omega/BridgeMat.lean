module

public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

private lemma mem_commutator_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 3) (ι → ZMod 3)) (g : OGroup Q) :
    g ∈ commutator (OGroup Q) ↔
      (g : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [← Subgroup.map_subtype_commutator (TauCeti.QuadraticMap.orthogonalGroup Q)]
  constructor
  · intro h
    simpa using Subgroup.mem_map_of_mem (TauCeti.QuadraticMap.orthogonalGroup Q).subtype h
  · rintro ⟨y, hy, hxy⟩
    have hy' : y = g := Subtype.ext hxy
    rwa [hy'] at hy

theorem nonempty_statedProj_statedOmega_mulEquiv_omegaProj {ι : Type} [Fintype ι]
    [DecidableEq ι] (Q : QuadraticForm (ZMod 3) (ι → ZMod 3)) (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Module.finrank (ZMod 3) (ι → ZMod 3)) :
    Nonempty (StatedProj (StatedOmega ⇑Q) ≃* omegaProj hQ) := by
  classical
  let e := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 3)
  let H : Subgroup (GL ι (ZMod 3)) := StatedOmega ⇑Q
  have hH : H = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆.comap e.toMonoidHom := by
    show StatedOmega ⇑Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆.comap e.toMonoidHom
    exact CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Q) rfl
  have hmem : ∀ A : H, e (A : GL ι (ZMod 3)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro A
    have hA : e (A : GL ι (ZMod 3)) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
      have := (le_of_eq hH) A.2
      simpa using this
    exact Subgroup.commutator_le_self _ hA
  let f : H →* OGroup Q := MonoidHom.codRestrict (e.toMonoidHom.comp H.subtype)
    (TauCeti.QuadraticMap.orthogonalGroup Q) hmem
  let ψ : H →* ProjOrth Q := (toProj Q).comp f
  have hf_apply : ∀ A : H,
      (f A : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) = e (A : GL ι (ZMod 3)) :=
    fun _ => rfl
  have hker : ψ.ker = (StatedScalars ι (ZMod 3)).subgroupOf H := by
    ext A
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      CFSG.ClassicalGroups.Orthogonal.mem_statedScalars_iff]
    constructor
    · intro hψ
      have hmem_ker : f A ∈ (toProj Q).ker := MonoidHom.mem_ker.mpr hψ
      rw [QuotientGroup.ker_mk'] at hmem_ker
      rcases mem_piGroup_iff.mp hmem_ker with h | h
      · rw [CFSG.ClassicalGroups.Orthogonal.mem_scalars]
        refine ⟨1, fun v => ?_⟩
        have hf1 : (f A : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) = 1 := by
          have := congrArg (fun z : OGroup Q =>
            (z : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))) h
          simpa using this
        rw [← hf_apply A, hf1]
        simp
      · rw [CFSG.ClassicalGroups.Orthogonal.mem_scalars]
        refine ⟨-1, fun v => ?_⟩
        have hfpi : (f A : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) =
            (piOrth Q : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) := by
          have := congrArg (fun z : OGroup Q =>
            (z : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))) h
          simpa using this
        rw [← hf_apply A, hfpi, coe_piOrth_apply]
        simp
    · intro hscal
      rw [CFSG.ClassicalGroups.Orthogonal.mem_scalars] at hscal
      obtain ⟨c, hc⟩ := hscal
      obtain ⟨v₀, hv₀⟩ := exists_eq_unit_of_two_le_finrank hQ h2 (1 : (ZMod 3)ˣ)
      have hv₀ne : Q v₀ ≠ 0 := by rw [hv₀]; exact one_ne_zero
      have hO : ∀ v, Q (e (A : GL ι (ZMod 3)) v) = Q v := by
        intro v
        have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (f A).2 v
        simpa [hf_apply A] using this
      have h1 : (c * c) • Q v₀ = Q v₀ := by
        rw [← QuadraticMap.map_smul, ← hc v₀, hO v₀]
      have hmul : c * c * Q v₀ = Q v₀ := by simpa using h1
      have hcc : c * c = 1 :=
        mul_right_cancel₀ hv₀ne (by rw [hmul, one_mul])
      have hcases : c = 1 ∨ c = -1 :=
        (by decide : ∀ x : ZMod 3, x * x = 1 → x = 1 ∨ x = -1) c hcc
      have hfA : f A ∈ piGroup Q := by
        rw [mem_piGroup_iff]
        rcases hcases with hc1 | hcm1
        · left
          apply Subtype.ext
          show e (A : GL ι (ZMod 3)) = 1
          ext v
          rw [hc v, hc1, one_smul]
          simp
        · right
          apply Subtype.ext
          show e (A : GL ι (ZMod 3)) =
            (piOrth Q : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))
          ext v
          rw [hc v, hcm1, coe_piOrth_apply]
          simp
      change toProj Q (f A) = 1
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hfA
  have hrange : ψ.range = omegaProj hQ := by
    ext x
    constructor
    · rintro ⟨A, rfl⟩
      rw [omegaProj, Subgroup.mem_map]
      refine ⟨f A, ?_, rfl⟩
      rw [omegaGroup_eq_commutator hQ h2]
      exact (mem_commutator_iff Q (f A)).mpr (by
        have hA : e (A : GL ι (ZMod 3)) ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
            TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
          have := (le_of_eq hH) A.2
          simpa using this
        simpa [hf_apply A] using hA)
    · intro hx
      rw [omegaProj, Subgroup.mem_map] at hx
      obtain ⟨g, hg, hgx⟩ := hx
      have hg' : (g : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) ∈
          ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
            TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
        (mem_commutator_iff Q g).mp (by rwa [omegaGroup_eq_commutator hQ h2] at hg)
      let A : H := ⟨e.symm (g : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)), by
        rw [hH]
        exact Subgroup.mem_comap.mpr (by simpa using hg')⟩
      refine ⟨A, ?_⟩
      have hfA : f A = g := by
        apply Subtype.ext
        show e (e.symm (g : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))) =
          (g : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))
        exact e.apply_symm_apply _
      rw [← hgx]
      change toProj Q (f A) = toProj Q g
      rw [hfA]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange))⟩

end CFSG.OddStandard.SmallF3.Omega
