module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Datum
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Tag
public import CFSG.LieType.Chevalley.GraphFixedParabolicSelfCentralizing
public import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.LieType.BorelTits
  CFSG.LieType.ChevTwo CFSG.LieType.Chevalley.EvenOddRadical

set_option linter.unusedSectionVars false

section Fixed


variable (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)

@[expose] noncomputable def radFix (J : Set (Fin t.foldedTag.rank)) :
    Subgroup ↥(graphFixedRootGroup t K σ.toRingHom) :=
  (graphFixedParabolicRadical t K σ.toRingHom J).subgroupOf (graphFixedRootGroup t K σ.toRingHom)

@[expose] noncomputable def parFix (J : Set (Fin t.foldedTag.rank)) :
    Subgroup ↥(graphFixedRootGroup t K σ.toRingHom) :=
  (graphFixedParabolic t K σ.toRingHom J).subgroupOf (graphFixedRootGroup t K σ.toRingHom)

variable {t K σ}

theorem normalizer_radFix (J : Set (Fin t.foldedTag.rank)) :
    Subgroup.normalizer ((radFix t K σ J : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)) :
      Set ↥(graphFixedRootGroup t K σ.toRingHom)) = parFix t K σ J := by
  ext x
  rw [radFix, mem_normalizer_subgroupOf_iff
    (graphFixedParabolicRadical_le_graphFixedRootGroup t K σ.toRingHom J) x, parFix,
    Subgroup.mem_subgroupOf]
  have h := diagram_fixed_parabolic_root_radical_normalizers t K σ J
  constructor
  · intro hx
    rw [← h]
    exact Subgroup.mem_inf.2 ⟨x.2, hx⟩
  · intro hx
    rw [← h] at hx
    exact (Subgroup.mem_inf.1 hx).2

theorem centralizer_radFix_le {J : Set (Fin t.foldedTag.rank)} (hJ : J ≠ Set.univ)
    (x : ↥(graphFixedRootGroup t K σ.toRingHom)) (hx : ∀ r ∈ radFix t K σ J, x * r = r * x) :
    x ∈ radFix t K σ J := by
  have hxN : x ∈ Subgroup.normalizer ((radFix t K σ J : Subgroup _) : Set _) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun r hr => (hx r hr).symm)
  rw [normalizer_radFix] at hxN
  have hxP : (x : ModGL t.tag K) ∈ graphFixedParabolic t K σ.toRingHom J :=
    Subgroup.mem_subgroupOf.1 hxN
  have hxC : (x : ModGL t.tag K) ∈
      Subgroup.centralizer (graphFixedParabolicRadical t K σ.toRingHom J : Set (ModGL t.tag K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := hx ⟨r, graphFixedParabolicRadical_le_graphFixedRootGroup t K σ.toRingHom J hr⟩ hr
    exact congrArg Subtype.val this.symm
  exact Subgroup.mem_subgroupOf.2
    ((diagram_fixed_proper_parabolic_root_radical_self_centralizing t K σ hJ).2
      (Subgroup.mem_inf.2 ⟨hxP, hxC⟩))

theorem isPGroup_radFix [Finite K] [CharP K 2] (J : Set (Fin t.foldedTag.rank)) :
    IsPGroup 2 (radFix t K σ J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (graphFixedParabolicRadical t K σ.toRingHom J) :=
    (isPGroup_posUnipotent 2 t.tag).to_le fun x hx =>
      parabolicRadical_le_posUnipotent _ (Subgroup.mem_inf.1 hx).1
  exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe
    (graphFixedParabolicRadical_le_graphFixedRootGroup t K σ.toRingHom J)).symm

theorem exists_std_position_fixed [Finite K] [CharP K 2] (hσ : σ ^ t.order = 1)
    {R : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)} (hR : IsRadical 2 R) :
    ∃ (g : ↥(graphFixedRootGroup t K σ.toRingHom)) (J : Set (Fin t.foldedTag.rank)),
      J ≠ Set.univ ∧ R.map (MulAut.conj g⁻¹).toMonoidHom = radFix t K σ J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  have hfinM : Finite (ModGL t.tag K) := finite_modGL
  have hQ₀ne : R.map (graphFixedRootGroup t K σ.toRingHom).subtype ≠ ⊥ := fun h =>
    h0 ((Subgroup.map_eq_bot_iff_of_injective R
      (graphFixedRootGroup t K σ.toRingHom).subtype_injective).1 h)
  obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_fixed t σ hσ (Subgroup.map_subtype_le R)
    (hp.map _) hQ₀ne
  have hPJ : parFix t K σ J ≤ Subgroup.normalizer ((radFix t K σ J : Subgroup _) : Set _) :=
    (normalizer_radFix J).ge
  have hN : ∀ x ∈ Subgroup.normalizer (R : Set ↥(graphFixedRootGroup t K σ.toRingHom)),
      (⟨g, hg⟩ : ↥(graphFixedRootGroup t K σ.toRingHom))⁻¹ * x * ⟨g, hg⟩ ∈ parFix t K σ J :=
    fun x hx => Subgroup.mem_subgroupOf.2 (hP x x.2 (mem_normalizer_map_subtype' hx))
  have hQ : ∀ q ∈ R, (⟨g, hg⟩ : ↥(graphFixedRootGroup t K σ.toRingHom))⁻¹ * q * ⟨g, hg⟩ ∈
      radFix t K σ J := fun q hq => Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)
  obtain ⟨hQ', hNQ⟩ := std_position (⟨g, hg⟩ : ↥(graphFixedRootGroup t K σ.toRingHom)) hc
    (isPGroup_radFix J) hPJ hN hQ
  refine ⟨⟨g, hg⟩, J, ?_, hQ'⟩
  rintro rfl
  apply hnt
  have hPtop : parFix t K σ Set.univ = ⊤ := by
    rw [parFix, (fixed_standard_parabolic_cells t K σ).2.2.2.2.2]
    exact Subgroup.subgroupOf_self _
  set γ : MulAut ↥(graphFixedRootGroup t K σ.toRingHom) :=
    MulAut.conj (⟨g, hg⟩ : ↥(graphFixedRootGroup t K σ.toRingHom))⁻¹ with hγ
  have hN' : Subgroup.normalizer ((R.map γ.toMonoidHom : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom)) :
      Set ↥(graphFixedRootGroup t K σ.toRingHom)) = ⊤ := by
    rw [hQ', hNQ, hPtop]
  rw [← Subgroup.map_equiv_normalizer_eq] at hN'
  rw [eq_top_iff]
  intro x _
  have hx : γ x ∈ (Subgroup.normalizer (R : Set ↥(graphFixedRootGroup t K σ.toRingHom))).map
      γ.toMonoidHom := by
    rw [hN']
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := γ.injective hyx
  rw [← this]
  exact hy

theorem closure_parFix_eq_top (hrank : 2 ≤ t.foldedTag.rank) :
    Subgroup.closure (⋃ i : Fin t.foldedTag.rank,
      (parFix t K σ {i}ᶜ : Set ↥(graphFixedRootGroup t K σ.toRingHom))) = ⊤ := by
  haveI : Nontrivial (Fin t.foldedTag.rank) := Fin.nontrivial_iff_two_le.2 hrank
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup ↥(graphFixedRootGroup t K σ.toRingHom),
      Y = Subgroup.closure (⋃ i : Fin t.foldedTag.rank,
        (parFix t K σ {i}ᶜ : Set ↥(graphFixedRootGroup t K σ.toRingHom))) := ⟨_, rfl⟩
  rw [← hY]
  have hPY : ∀ i : Fin t.foldedTag.rank, parFix t K σ {i}ᶜ ≤ Y := fun i x hx => by
    rw [hY]
    exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, hx⟩)
  obtain ⟨Y', hY'⟩ : ∃ Y' : Subgroup (ModGL t.tag K),
      Y' = Y.map (graphFixedRootGroup t K σ.toRingHom).subtype := ⟨_, rfl⟩
  have hYle : Y' ≤ graphFixedRootGroup t K σ.toRingHom := by
    rw [hY']
    exact Subgroup.map_subtype_le Y
  have hPle : ∀ (i : Fin t.foldedTag.rank) (x : ModGL t.tag K),
      x ∈ graphFixedParabolic t K σ.toRingHom {i}ᶜ → x ∈ Y' := by
    intro i x hx
    have hxC : x ∈ graphFixedRootGroup t K σ.toRingHom :=
      graphFixedParabolic_le t K σ.toRingHom _ hx
    rw [hY']
    exact ⟨⟨x, hxC⟩, hPY i (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  obtain ⟨i0, -⟩ := exists_pair_ne (Fin t.foldedTag.rank)
  have hB : graphFixedRootBorel t K σ.toRingHom ≤ Y' := fun b hb =>
    hPle i0 b (graphFixedRootBorel_le_graphFixedParabolic t K σ.toRingHom _ hb)
  obtain ⟨hcl, -⟩ := fixed_Borel_overgroup_classification t K σ Y' hB hYle
  have hJ' : ∀ a : Fin t.foldedTag.rank,
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ Y' := by
    intro a
    obtain ⟨i1, hi1⟩ := exists_ne a
    exact hPle i1 _ ((canonicalRep_orbitReflection_mem_graphFixedParabolic_iff σ.surjective).2
      (show a ∈ ({i1}ᶜ : Set (Fin t.foldedTag.rank)) from fun h => hi1 h.symm))
  have hY'top : Y' = graphFixedRootGroup t K σ.toRingHom := by
    rw [hcl]
    have : {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ Y'} = Set.univ :=
      Set.eq_univ_of_forall hJ'
    rw [this]
    exact (fixed_standard_parabolic_cells t K σ).2.2.2.2.2
  rw [eq_top_iff]
  intro x _
  have hxY' : (x : ModGL t.tag K) ∈ Y' := by
    rw [hY'top]
    exact x.2
  rw [hY'] at hxY'
  obtain ⟨y, hy, hyx⟩ := hxY'
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

noncomputable def stdDatumFixed [Finite K] [CharP K 2] (hσ : σ ^ t.order = 1)
    (hrank : 2 ≤ t.foldedTag.rank) :
    StdDatum 2 ↥(graphFixedRootGroup t K σ.toRingHom) (Fin t.foldedTag.rank) where
  Q := radFix t K σ
  P := parFix t K σ
  U := (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf (graphFixedRootGroup t K σ.toRingHom)
  U_sylow := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P, hP⟩ := (RootWeightDatum.fixed t σ hσ).exists_sylow_eq_unipotent 2
    exact ⟨P, hP⟩
  Q_pGroup := isPGroup_radFix
  Q_le_U := fun J x hx => Subgroup.mem_subgroupOf.2
    (graphFixedParabolicRadical_le_graphFixedPosUnipotent J (Subgroup.mem_subgroupOf.1 hx))
  normalizer_eq := normalizer_radFix
  centralizer_le := fun J hJ => centralizer_radFix_le hJ
  std_position := fun R hR => exists_std_position_fixed hσ hR
  generation := ⟨Set.range fun i : Fin t.foldedTag.rank => ({i}ᶜ : Set (Fin t.foldedTag.rank)),
    by
      rintro _ ⟨i, rfl⟩ h
      have h' : ({i}ᶜ : Set (Fin t.foldedTag.rank)) = Set.univ := h
      have : i ∈ ({i}ᶜ : Set (Fin t.foldedTag.rank)) := by rw [h']; exact Set.mem_univ i
      exact this rfl,
    by
      have := closure_parFix_eq_top (t := t) (K := K) (σ := σ) hrank
      simpa [Set.biUnion_range] using this⟩

end Fixed

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
