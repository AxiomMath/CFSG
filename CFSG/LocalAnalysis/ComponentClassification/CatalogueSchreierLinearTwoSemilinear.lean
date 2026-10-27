module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter
open scoped commutatorElement

universe u v

theorem fieldAut_isCyclic (K : Type u) [Field K] [Finite K] :
    IsCyclic (K ≃+* K) := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpchar, n, hp, _hcard⟩ := FiniteField.card' K
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := hpchar
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) := {
    toFun := fun sigma =>
      AlgEquiv.ofRingEquiv (f := sigma) (by
        intro x
        have h :
            (sigma.toRingHom.comp (algebraMap (ZMod p) K) : ZMod p →+* K) =
              algebraMap (ZMod p) K := RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h x)
    invFun := fun sigma => sigma.toRingEquiv
    left_inv := by intro sigma; ext x; rfl
    right_inv := by intro sigma; ext x; rfl
    map_mul' := by intro sigma tau; ext x; rfl }
  exact e.isCyclic.mpr inferInstance

theorem pglPSLRange_normal (K : Type u) [Field K] :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.Normal := by
  let q : Matrix.GeneralLinearGroup (Fin 2) K →* PGL2 K :=
    Matrix.ProjGenLinGroup.mk
  let s : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.GeneralLinearGroup (Fin 2) K := Matrix.SpecialLinearGroup.toGL
  have hs : s.range.Normal := by
    rw [show s.range = Matrix.GeneralLinearGroup.det.ker from
      Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    infer_instance
  have heq : s.range.map q =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk a, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk a⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) a
      exact ⟨s b, ⟨b, rfl⟩, (Matrix.ProjectiveSpecialLinearGroup.toPGL_mk b).symm⟩
  rw [← heq]
  exact hs.map q Matrix.ProjGenLinGroup.mk_surjective

theorem semilinearPSLRange_normal (K : Type u) [Field K] :
    (pGammaL2PSLRange K).Normal := by
  let t : PSL2 K →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have ht : t.range.Normal := pglPSLRange_normal K
  constructor
  intro x hx g
  obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K x).mp hx
  have hfield : (pgl2FieldAut K g.right) (t y) ∈ t.range :=
    ⟨psl2FieldAut K g.right y, psl2FieldAut_toPGL g.right y⟩
  obtain ⟨z, hz⟩ := ht.conj_mem _ hfield g.left
  apply (mem_pGammaL2PSLRange_iff K _).mpr
  refine ⟨z, ?_⟩
  apply SemidirectProduct.ext
  · simpa [t] using hz
  · simp

noncomputable instance semilinearPSLRangeNormal (K : Type u) [Field K] :
    (pGammaL2PSLRange K).Normal := semilinearPSLRange_normal K

abbrev SemilinearQuotient (K : Type u) [Field K] :=
  PGammaL2 K ⧸ pGammaL2PSLRange K

@[expose] def quotientFieldProjection (K : Type u) [Field K] :
    SemilinearQuotient K →* (K ≃+* K) :=
  QuotientGroup.lift (pGammaL2PSLRange K) SemidirectProduct.rightHom (by
    rintro x ⟨y, rfl⟩
    simp [MonoidHom.mem_ker])

@[expose] def diagonalHom (K : Type u) [Field K] :
    PGL2 K →* SemilinearQuotient K :=
  (QuotientGroup.mk' (pGammaL2PSLRange K)).comp SemidirectProduct.inl

theorem quotientFieldProjection_ker (K : Type u) [Field K] :
    (quotientFieldProjection K).ker = (diagonalHom K).range := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pGammaL2PSLRange K) x
  constructor
  · intro hg
    have hright : g.right = 1 := hg
    refine ⟨g.left, ?_⟩
    change QuotientGroup.mk' (pGammaL2PSLRange K)
      (SemidirectProduct.inl g.left) = QuotientGroup.mk' (pGammaL2PSLRange K) g
    congr 1
    exact SemidirectProduct.ext rfl hright.symm
  · rintro ⟨y, hy⟩
    rw [← hy]
    change SemidirectProduct.rightHom (SemidirectProduct.inl y : PGammaL2 K) = 1
    simp

theorem quotientFieldProjection_surjective (K : Type u) [Field K] :
    Function.Surjective (quotientFieldProjection K) := by
  intro sigma
  refine ⟨QuotientGroup.mk' (pGammaL2PSLRange K) (SemidirectProduct.inr sigma), ?_⟩
  change SemidirectProduct.rightHom (SemidirectProduct.inr sigma : PGammaL2 K) = sigma
  simp

theorem diagonal_commutator_eq_bot (K : Type u) [Field K] [Finite K] :
    ⁅(diagonalHom K).range, (diagonalHom K).range⁆ = ⊥ := by
  rw [← map_commutator_eq]
  apply ((commutator (PGL2 K)).map_eq_bot_iff).mpr
  intro g hg
  obtain ⟨y, hy⟩ := pgl2_commutator_le_psl2_range K hg
  rw [MonoidHom.mem_ker]
  change QuotientGroup.mk' (pGammaL2PSLRange K) (SemidirectProduct.inl g) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (mem_pGammaL2PSLRange_iff K _).mpr ⟨y, congrArg SemidirectProduct.inl hy⟩

theorem quotient_commutator_le_diagonal (K : Type u) [Field K] [Finite K] :
    commutator (SemilinearQuotient K) ≤ (diagonalHom K).range := by
  let : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  rw [← quotientFieldProjection_ker]
  exact Abelianization.commutator_subset_ker (quotientFieldProjection K)

theorem semilinearQuotient_secondDerived_eq_bot
    (K : Type u) [Field K] [Finite K] :
    derivedSeries (SemilinearQuotient K) 2 = ⊥ := by
  apply le_bot_iff.mp
  change ⁅commutator (SemilinearQuotient K), commutator (SemilinearQuotient K)⁆ ≤ ⊥
  exact (Subgroup.commutator_mono (quotient_commutator_le_diagonal K)
    (quotient_commutator_le_diagonal K)).trans (diagonal_commutator_eq_bot K).le

theorem semilinearQuotient_solvable (K : Type u) [Field K] [Finite K] :
    Group.IsSolvable (SemilinearQuotient K) :=
  ⟨⟨2, semilinearQuotient_secondDerived_eq_bot K⟩⟩

theorem secondDerived_eq_bot_of_surjective
    {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hG : derivedSeries G 2 = ⊥) : derivedSeries H 2 = ⊥ := by
  rw [← map_derivedSeries_eq hf, hG, Subgroup.map_bot]

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
