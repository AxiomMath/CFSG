module

public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.CatalogueSchreierLinearTwoNormalized
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter OuterAutomorphisms

universe u v

theorem semilinearAction_surjective (K : Type u) [Field K] [Finite K] :
    Function.Surjective (semilinearAction K) := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨p, _hchar, f, hp, hcard⟩ := FiniteField.card' K
  let : Fact p.Prime := ⟨hp⟩
  have hKcard : Nat.card K = p ^ (f : ℕ) := by rwa [Nat.card_eq_fintype_card]
  intro alpha
  let g : PGL2 K := psl2MulAutNormalizerPGL K hKcard alpha
  let sigma : K ≃+* K := normalizedAffineRingEquiv K hKcard alpha
  refine ⟨SemidirectProduct.inl g⁻¹ * SemidirectProduct.inr sigma, ?_⟩
  rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  have hn := normalizedAut_eq_fieldAut K hKcard alpha
  change pglAction K g * alpha = psl2FieldAut K sigma at hn
  rw [map_inv, ← hn]
  group

theorem semilinearAction_injective (K : Type u) [Field K] [Finite K] :
    Function.Injective (semilinearAction K) := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨p, _hchar, f, hp, hcard⟩ := FiniteField.card' K
  let : Fact p.Prime := ⟨hp⟩
  have hKcard : Nat.card K = p ^ (f : ℕ) := by rwa [Nat.card_eq_fintype_card]
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hact : pglAction K g.left * psl2FieldAut K g.right = 1 := by
    have h := congrArg (semilinearAction K) (SemidirectProduct.inl_left_mul_inr_right g)
    rw [map_mul, semilinearAction_inl, semilinearAction_inr] at h
    exact h.trans hg
  have hfix (x : PSL2ProjectiveLine K)
      (hx : psl2MulAutProjectiveLine K hKcard (psl2FieldAut K g.right) x = x) :
      g.left • x = x := by
    have h := congrArg (fun a : MulAut (PSL2 K) =>
      psl2MulAutProjectiveLine K hKcard a x) hact
    simpa only [map_mul, Equiv.Perm.mul_apply, pglAction_projectiveLine, hx,
      map_one, Equiv.Perm.one_apply] using h
  have hInfinity := hfix (psl2ProjectiveInfinity K)
    (fieldAut_projectiveLine_infinity K hKcard g.right)
  have h0 := hfix (psl2ProjectiveZero K) (by
    simpa using fieldAut_projectiveLine_affine K hKcard g.right 0)
  have h1 := hfix (psl2ProjectiveOne K) (by
    simpa [psl2ProjectiveOne] using fieldAut_projectiveLine_affine K hKcard g.right 1)
  obtain ⟨a, _ha, hunique⟩ := existsUnique_pgl2_normalizes_projective_triple K
    (1 : Equiv.Perm (PSL2ProjectiveLine K))
  have hgleft : g.left = 1 :=
    (hunique g.left ⟨hInfinity, h0, h1⟩).trans (hunique 1 (by simp)).symm
  have hfield : psl2FieldAut K g.right = 1 := by simpa [hgleft] using hact
  have hgright : g.right = 1 := by
    apply psl2FieldAut_injective K
    simpa using hfield
  exact SemidirectProduct.ext hgleft hgright

@[expose] def semilinearEquivAut (K : Type u) [Field K] [Finite K] :
    PGammaL2 K ≃* MulAut (PSL2 K) :=
  MulEquiv.ofBijective (semilinearAction K)
    ⟨semilinearAction_injective K, semilinearAction_surjective K⟩

@[expose] def semilinearToOuter (K : Type u) [Field K] :
    PGammaL2 K →* Outer (PSL2 K) :=
  (QuotientGroup.mk' (inner (PSL2 K))).comp (semilinearAction K)

theorem semilinearToOuter_surjective (K : Type u) [Field K] [Finite K] :
    Function.Surjective (semilinearToOuter K) :=
  (QuotientGroup.mk'_surjective (inner (PSL2 K))).comp (semilinearAction_surjective K)

theorem semilinearToOuter_ker (K : Type u) [Field K] [Finite K] :
    (semilinearToOuter K).ker = pGammaL2PSLRange K := by
  ext g
  change (QuotientGroup.mk (semilinearAction K g) : Outer (PSL2 K)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨y, hy⟩
    apply (mem_pGammaL2PSLRange_iff K g).mpr
    refine ⟨y, ?_⟩
    apply semilinearAction_injective K
    rw [semilinearAction_inl, pglAction_toPGL]
    exact hy
  · intro hg
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K g).mp hg
    refine ⟨y, ?_⟩
    rw [semilinearAction_inl, pglAction_toPGL]

@[expose] def outerEquivSemilinearQuotient (K : Type u) [Field K] [Finite K] :
    SemilinearQuotient K ≃* Outer (PSL2 K) :=
  (QuotientGroup.quotientMulEquivOfEq (semilinearToOuter_ker K).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (semilinearToOuter K)
      (semilinearToOuter_surjective K))

theorem outer_secondDerived_eq_bot (K : Type u) [Field K] [Finite K] :
    derivedSeries (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (outerEquivSemilinearQuotient K).toMonoidHom
    (outerEquivSemilinearQuotient K).surjective (semilinearQuotient_secondDerived_eq_bot K)

theorem outer_solvable (K : Type u) [Field K] [Finite K] :
    Group.IsSolvable (Outer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
  ⟨⟨2, outer_secondDerived_eq_bot K⟩⟩

theorem outer_secondDerived_eq_bot_of_equiv {G : Type v} [Group G]
    (K : Type u) [Field K] [Finite K] (e : G ≃* PSL2 K) :
    derivedSeries (Outer G) 2 = ⊥ :=
  secondDerived_eq_bot_of_surjective (equivalence e).symm.toMonoidHom
    (equivalence e).symm.surjective (outer_secondDerived_eq_bot K)

theorem outer_solvable_of_equiv {G : Type v} [Group G]
    (K : Type u) [Field K] [Finite K] (e : G ≃* PSL2 K) :
    Group.IsSolvable (Outer G) :=
  ⟨⟨2, outer_secondDerived_eq_bot_of_equiv K e⟩⟩

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
