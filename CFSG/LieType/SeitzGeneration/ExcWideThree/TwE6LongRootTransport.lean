module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootDefs

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Abstract

variable {G G' : Type*} [Group G] [Group G']

theorem normalizer_map_equiv (φ : G ≃* G') (H : Subgroup G) :
    Subgroup.normalizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.normalizer (H : Set G)).map φ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  constructor
  · intro h h'
    have := h (φ h')
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
    exact this
  · intro h h'
    obtain ⟨h'', rfl⟩ := φ.surjective h'
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact h h''

theorem centralizer_map_equiv (φ : G ≃* G') (H : Subgroup G) :
    Subgroup.centralizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.centralizer (H : Set G)).map φ.toMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h h' hh'
    have := h (φ h') ((Subgroup.mem_map_equiv).2 (by simpa using hh'))
    rw [← map_mul, ← map_mul] at this
    exact φ.injective this
  · intro h h' hh'
    obtain ⟨h'', rfl⟩ := φ.surjective h'
    have hh : h'' ∈ H := by simpa using ((Subgroup.mem_map_equiv).1 hh')
    rw [← map_mul, ← map_mul, h h'' hh]

theorem pCore_map_subtype_equiv (p : ℕ) (φ : G ≃* G) (P P' : Subgroup G)
    (h : P' = P.map (φ : G →* G)) :
    (CFSG.pCore p P').map P'.subtype =
      ((CFSG.pCore p P).map P.subtype).map (φ : G →* G) := by
  subst h
  have hι : (CFSG.pCore p P).map (φ.subgroupMap P).toMonoidHom =
      CFSG.pCore p ↥(P.map (φ : G →* G)) := CFSG.pCore_map_iso p (φ.subgroupMap P)
  rw [← hι, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_conj_map_conj (g g' : G) (M : Subgroup G) :
    (M.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g').toMonoidHom =
      (M.map (MulAut.conj (g * g' * g⁻¹)).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
    inv_inv]
  group

theorem map_conj_map_conj_inv (g : G) (M : Subgroup G) :
    (M.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = M := by
  rw [Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [this]
    exact hy
  · intro hx
    exact ⟨x, hx, by group⟩

theorem map_conj_inv_map_conj (g : G) (M : Subgroup G) :
    (M.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = M := by
  have := map_conj_map_conj_inv g⁻¹ M
  rwa [inv_inv] at this

end Abstract

section Transport

variable
  {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem twE6LongRootSL2_map (φ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)
    (X Xm : Subgroup (twistedE6RootGroup K σ)) :
    twE6LongRootSL2 (X.map φ.toMonoidHom) (Xm.map φ.toMonoidHom) =
      (twE6LongRootSL2 X Xm).map φ.toMonoidHom := by
  unfold twE6LongRootSL2
  rw [MonoidHom.map_closure, Set.image_union]
  rfl

theorem twE6LongRootParabolic_map (φ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)
    (X : Subgroup (twistedE6RootGroup K σ)) :
    twE6LongRootParabolic (X.map φ.toMonoidHom) =
      (twE6LongRootParabolic X).map φ.toMonoidHom :=
  normalizer_map_equiv φ X

theorem twE6LongRootTorus_map (φ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)
    (X Xm : Subgroup (twistedE6RootGroup K σ)) :
    twE6LongRootTorus (X.map φ.toMonoidHom) (Xm.map φ.toMonoidHom) =
      (twE6LongRootTorus X Xm).map φ.toMonoidHom := by
  unfold twE6LongRootTorus
  rw [twE6LongRootSL2_map, normalizer_map_equiv φ X, normalizer_map_equiv φ Xm,
    Subgroup.map_inf _ _ _ φ.injective, Subgroup.map_inf _ _ _ φ.injective]

theorem twE6LongRootRadical_map (φ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)
    (X : Subgroup (twistedE6RootGroup K σ)) :
    twE6LongRootRadical (X.map φ.toMonoidHom) =
      (twE6LongRootRadical X).map φ.toMonoidHom := by
  unfold twE6LongRootRadical
  exact pCore_map_subtype_equiv _ φ _ _ (twE6LongRootParabolic_map φ X)

theorem twE6LongRootLevi_map (φ : twistedE6RootGroup K σ ≃* twistedE6RootGroup K σ)
    (X Xm : Subgroup (twistedE6RootGroup K σ)) :
    twE6LongRootLevi (X.map φ.toMonoidHom) (Xm.map φ.toMonoidHom) =
      (twE6LongRootLevi X Xm).map φ.toMonoidHom := by
  unfold twE6LongRootLevi
  rw [twE6LongRootSL2_map, centralizer_map_equiv, Subgroup.map_commutator]

end Transport

section Reduction

variable
  {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

abbrev stdX : Subgroup (twistedE6RootGroup K σ) := twE6RootSubgroup K σ e6HighestRoot

abbrev stdXm : Subgroup (twistedE6RootGroup K σ) := twE6RootSubgroup K σ (-e6HighestRoot)

theorem irreducible_of_standard
    (h : ∀ M : Subgroup (twistedE6RootGroup K σ), stdX σ ≤ M → M ≤ twE6LongRootRadical (stdX σ) →
      (∀ g ∈ twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ),
        M.map (MulAut.conj g).toMonoidHom = M) →
      M = stdX σ ∨ M = twE6LongRootRadical (stdX σ))
    (X Xm : Subgroup (twistedE6RootGroup K σ)) (hpair : IsTwE6LongRootPair K σ X Xm)
    (M : Subgroup (twistedE6RootGroup K σ)) (hXM : X ≤ M) (hMQ : M ≤ twE6LongRootRadical X)
    (hnorm : ∀ g ∈ twE6LongRootLevi X Xm ⊔ twE6LongRootTorus X Xm,
      M.map (MulAut.conj g).toMonoidHom = M) :
    M = X ∨ M = twE6LongRootRadical X := by
  obtain ⟨g, rfl, rfl⟩ := hpair
  have hQ := twE6LongRootRadical_map (MulAut.conj g) (stdX σ)
  have hJT : twE6LongRootLevi ((stdX σ).map (MulAut.conj g).toMonoidHom)
      ((stdXm σ).map (MulAut.conj g).toMonoidHom) ⊔
      twE6LongRootTorus ((stdX σ).map (MulAut.conj g).toMonoidHom)
        ((stdXm σ).map (MulAut.conj g).toMonoidHom) =
      (twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ)).map
        (MulAut.conj g).toMonoidHom := by
    rw [twE6LongRootLevi_map, twE6LongRootTorus_map, Subgroup.map_sup]
  set M₀ := M.map (MulAut.conj g⁻¹).toMonoidHom with hM₀
  have hback : M = M₀.map (MulAut.conj g).toMonoidHom := (map_conj_inv_map_conj g M).symm
  have h1 : stdX σ ≤ M₀ := by
    intro x hx
    refine Subgroup.mem_map.2 ⟨g * x * g⁻¹, hXM (Subgroup.mem_map.2 ⟨x, hx, rfl⟩), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have h2 : M₀ ≤ twE6LongRootRadical (stdX σ) := by
    rintro _ ⟨m, hm, rfl⟩
    have := hMQ hm
    rw [hQ] at this
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 this
    have e : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom q) = q := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact hq
  have h3 : ∀ g' ∈ twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ),
      M₀.map (MulAut.conj g').toMonoidHom = M₀ := by
    intro g' hg'
    have hmem : g * g' * g⁻¹ ∈ twE6LongRootLevi ((stdX σ).map (MulAut.conj g).toMonoidHom)
        ((stdXm σ).map (MulAut.conj g).toMonoidHom) ⊔
        twE6LongRootTorus ((stdX σ).map (MulAut.conj g).toMonoidHom)
          ((stdXm σ).map (MulAut.conj g).toMonoidHom) := by
      rw [hJT]
      exact Subgroup.mem_map.2 ⟨g', hg', by simp [MulAut.conj_apply]⟩
    rw [hM₀, map_conj_map_conj, hnorm _ hmem]
  rcases h M₀ h1 h2 h3 with h4 | h4
  · left
    rw [hback, h4]
  · right
    rw [hback, h4, hQ]

theorem generates_of_standard
    (h : ∃ n ∈ twE6LongRootSL2 (stdX σ) (stdXm σ),
      Subgroup.closure ((twE6LongRootRadical (stdX σ) : Set (twistedE6RootGroup K σ)) ∪
        ((twE6LongRootRadical (stdX σ)).map (MulAut.conj n).toMonoidHom :
          Set (twistedE6RootGroup K σ))) = ⊤)
    (X Xm : Subgroup (twistedE6RootGroup K σ)) (hpair : IsTwE6LongRootPair K σ X Xm) :
    ∃ n ∈ twE6LongRootSL2 X Xm,
      Subgroup.closure ((twE6LongRootRadical X : Set (twistedE6RootGroup K σ)) ∪
        ((twE6LongRootRadical X).map (MulAut.conj n).toMonoidHom :
          Set (twistedE6RootGroup K σ))) = ⊤ := by
  obtain ⟨g, rfl, rfl⟩ := hpair
  obtain ⟨n, hnS, hn⟩ := h
  refine ⟨g * n * g⁻¹, ?_, ?_⟩
  · rw [twE6LongRootSL2_map]
    exact Subgroup.mem_map.2 ⟨n, hnS, by simp [MulAut.conj_apply]⟩
  · rw [twE6LongRootRadical_map]
    have e : ((twE6LongRootRadical (stdX σ)).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj (g * n * g⁻¹)).toMonoidHom =
        ((twE6LongRootRadical (stdX σ)).map (MulAut.conj n).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
        inv_inv]
      group
    rw [e]
    have e2 : (Subgroup.closure ((twE6LongRootRadical (stdX σ) : Set (twistedE6RootGroup K σ)) ∪
        ((twE6LongRootRadical (stdX σ)).map (MulAut.conj n).toMonoidHom :
          Set (twistedE6RootGroup K σ)))).map (MulAut.conj g).toMonoidHom =
        Subgroup.closure ((((twE6LongRootRadical (stdX σ)).map
          (MulAut.conj g).toMonoidHom : Subgroup (twistedE6RootGroup K σ)) :
            Set (twistedE6RootGroup K σ)) ∪
          ((((twE6LongRootRadical (stdX σ)).map (MulAut.conj n).toMonoidHom).map
            (MulAut.conj g).toMonoidHom : Subgroup (twistedE6RootGroup K σ)) :
              Set (twistedE6RootGroup K σ))) := by
      rw [MonoidHom.map_closure, Set.image_union]
      rfl
    rw [← e2, hn]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

end Reduction

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
