module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalKempf
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.ChevTwo.OppositeFixedExcBase

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.LieType.BorelTits
  CFSG.LieType.ChevTwo CFSG.LieType.Chevalley.EvenOddRadical

set_option linter.unusedSectionVars false

theorem mem_normalizer_subgroupOf_iff {G : Type*} [Group G] {C Q : Subgroup G} (hQ : Q ≤ C)
    (x : C) :
    x ∈ Subgroup.normalizer ((Q.subgroupOf C : Subgroup C) : Set C) ↔
      (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      have h1 := (h ⟨y, hQ hy⟩).1 (Subgroup.mem_subgroupOf.2 hy)
      exact Subgroup.mem_subgroupOf.1 h1
    · intro hy
      have hyC : y ∈ C := by
        have h2 : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) ∈ C :=
          C.mul_mem (C.mul_mem (C.inv_mem x.2) (hQ hy)) x.2
        have h3 : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) = y := by group
        rwa [h3] at h2
      have h1 : (⟨y, hyC⟩ : C) ∈ Q.subgroupOf C := by
        refine (h ⟨y, hyC⟩).2 ?_
        exact Subgroup.mem_subgroupOf.2 hy
      exact Subgroup.mem_subgroupOf.1 h1
  · intro h y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact h (y : G)

theorem mem_normalizer_map_subtype' {G : Type*} [Group G] {K' : Subgroup G} {Q : Subgroup K'}
    {x : K'} (hx : x ∈ Subgroup.normalizer (Q : Set K')) :
    (x : G) ∈ Subgroup.normalizer ((Q.map K'.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨x * q * x⁻¹, (hx q).1 hq, rfl⟩
  · rintro ⟨q', hq', hq'e⟩
    refine ⟨x⁻¹ * q' * x, (hx _).2 (by rw [show x * (x⁻¹ * q' * x) * x⁻¹ = q' by group]; exact hq'), ?_⟩
    have h1 : (q' : G) = (x : G) * h * (x : G)⁻¹ := hq'e
    change ((x⁻¹ * q' * x : K') : G) = h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1]
    group

section Tag


variable (τ : Tag) (K : Type) [Field K]

@[expose] noncomputable def radTag (J : Set (Fin τ.rank)) : Subgroup ↥(adjointGroup τ K) :=
  (parabolicRadical τ K J).subgroupOf (adjointGroup τ K)

@[expose] noncomputable def parTag (J : Set (Fin τ.rank)) : Subgroup ↥(adjointGroup τ K) :=
  (parabolicSubgroup τ K J).subgroupOf (adjointGroup τ K)

variable {τ K}

theorem parabolicRadical_le_adjointGroup' (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ≤ adjointGroup τ K :=
  (parabolicRadical_le_posUnipotent J).trans posUnipotent_le_adjointGroup

theorem normalizer_radTag (J : Set (Fin τ.rank)) :
    Subgroup.normalizer ((radTag τ K J : Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) =
      parTag τ K J := by
  ext x
  rw [radTag, mem_normalizer_subgroupOf_iff (parabolicRadical_le_adjointGroup' J) x, parTag,
    Subgroup.mem_subgroupOf]
  have h := (Chevalley_Borel_overgroups_and_radical_normalizers τ K).2 J
  constructor
  · intro hx
    rw [← h]
    exact Subgroup.mem_inf.2 ⟨x.2, hx⟩
  · intro hx
    rw [← h] at hx
    exact (Subgroup.mem_inf.1 hx).2

theorem centralizer_radTag_le {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ) (x : ↥(adjointGroup τ K))
    (hx : ∀ r ∈ radTag τ K J, x * r = r * x) : x ∈ radTag τ K J := by
  have hxN : x ∈ Subgroup.normalizer ((radTag τ K J : Subgroup ↥(adjointGroup τ K)) :
      Set ↥(adjointGroup τ K)) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun r hr => (hx r hr).symm)
  rw [normalizer_radTag] at hxN
  have hxP : (x : ModGL τ K) ∈ parabolicSubgroup τ K J := Subgroup.mem_subgroupOf.1 hxN
  have hxC : (x : ModGL τ K) ∈ Subgroup.centralizer (parabolicRadical τ K J : Set (ModGL τ K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have := hx ⟨r, parabolicRadical_le_adjointGroup' J hr⟩ hr
    exact congrArg Subtype.val this.symm
  exact Subgroup.mem_subgroupOf.2
    ((Chevalley_proper_parabolic_root_radical_self_centralizing τ K hJ).2
      (Subgroup.mem_inf.2 ⟨hxP, hxC⟩))


theorem isPGroup_radTag [Finite K] [CharP K 2] (J : Set (Fin τ.rank)) :
    IsPGroup 2 (radTag τ K J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (parabolicRadical τ K J) :=
    (isPGroup_posUnipotent 2 τ).to_le (parabolicRadical_le_posUnipotent J)
  exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe (parabolicRadical_le_adjointGroup' J)).symm

theorem exists_std_position [Finite K] [CharP K 2] {R : Subgroup ↥(adjointGroup τ K)}
    (hR : IsRadical 2 R) :
    ∃ (g : ↥(adjointGroup τ K)) (J : Set (Fin τ.rank)), J ≠ Set.univ ∧
      R.map (MulAut.conj g⁻¹).toMonoidHom = radTag τ K J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h0, hp, hc, hnt⟩ := hR
  have hfinM : Finite (ModGL τ K) := finite_modGL
  have hQ₀ne : R.map (adjointGroup τ K).subtype ≠ ⊥ := fun h =>
    h0 ((Subgroup.map_eq_bot_iff_of_injective R (adjointGroup τ K).subtype_injective).1 h)
  obtain ⟨g, hg, J, hP, hQJ⟩ := exists_optimal_radical_ordinary (Subgroup.map_subtype_le R)
    (hp.map _) hQ₀ne
  have hPJ : parTag τ K J ≤ Subgroup.normalizer ((radTag τ K J : Subgroup ↥(adjointGroup τ K)) :
      Set ↥(adjointGroup τ K)) := (normalizer_radTag J).ge
  have hN : ∀ x ∈ Subgroup.normalizer (R : Set ↥(adjointGroup τ K)),
      (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ * x * ⟨g, hg⟩ ∈ parTag τ K J := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hP x x.2 (mem_normalizer_map_subtype' hx))
  have hQ : ∀ q ∈ R, (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ * q * ⟨g, hg⟩ ∈ radTag τ K J :=
    fun q hq => Subgroup.mem_subgroupOf.2 (hQJ q ⟨q, hq, rfl⟩)
  obtain ⟨hQ', hNQ⟩ := std_position (⟨g, hg⟩ : ↥(adjointGroup τ K)) hc (isPGroup_radTag J) hPJ hN hQ
  refine ⟨⟨g, hg⟩, J, ?_, hQ'⟩
  rintro rfl
  apply hnt
  have hPtop : parTag τ K Set.univ = ⊤ := by
    rw [parTag, (standard_parabolic_cells τ K).2.2.2.2.2.1]
    exact Subgroup.subgroupOf_self _
  set γ : MulAut ↥(adjointGroup τ K) := MulAut.conj (⟨g, hg⟩ : ↥(adjointGroup τ K))⁻¹ with hγ
  have hN' : Subgroup.normalizer ((R.map γ.toMonoidHom : Subgroup ↥(adjointGroup τ K)) :
      Set ↥(adjointGroup τ K)) = ⊤ := by
    rw [hQ', hNQ, hPtop]
  rw [← Subgroup.map_equiv_normalizer_eq] at hN'
  rw [eq_top_iff]
  intro x _
  have hx : γ x ∈ (Subgroup.normalizer (R : Set ↥(adjointGroup τ K))).map γ.toMonoidHom := by
    rw [hN']
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := γ.injective hyx
  rw [← this]
  exact hy

theorem centralizer_le_of_isRadical [Finite K] [CharP K 2] {R : Subgroup ↥(adjointGroup τ K)}
    (hR : IsRadical 2 R) : ∀ x : ↥(adjointGroup τ K), (∀ r ∈ R, x * r = r * x) → x ∈ R := by
  obtain ⟨g, J, hJ, hRJ⟩ := exists_std_position hR
  intro x hx
  have hy : ∀ r ∈ radTag τ K J, (g⁻¹ * x * g) * r = r * (g⁻¹ * x * g) := by
    intro r hr
    rw [← hRJ] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    have hs' := hx s hs
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * s * g) = g⁻¹ * (x * s) * g := by group
      _ = g⁻¹ * (s * x) * g := by rw [hs']
      _ = g⁻¹ * s * g * (g⁻¹ * x * g) := by group
  have h1 := centralizer_radTag_le hJ (g⁻¹ * x * g) hy
  rw [← hRJ] at h1
  obtain ⟨s, hs, hse⟩ := h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hse
  have : x = s := by
    have h2 : g * (g⁻¹ * s * g) * g⁻¹ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hse]
    simpa using h2.symm
  rw [this]
  exact hs

theorem closure_parTag_eq_top (hrank : 2 ≤ τ.rank) :
    Subgroup.closure (⋃ i : Fin τ.rank, (parTag τ K {i}ᶜ : Set ↥(adjointGroup τ K))) = ⊤ := by
  haveI : Nontrivial (Fin τ.rank) := Fin.nontrivial_iff_two_le.2 hrank
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup ↥(adjointGroup τ K),
      Y = Subgroup.closure (⋃ i : Fin τ.rank, (parTag τ K {i}ᶜ : Set ↥(adjointGroup τ K))) :=
    ⟨_, rfl⟩
  rw [← hY]
  have hPY : ∀ i : Fin τ.rank, parTag τ K {i}ᶜ ≤ Y := fun i x hx => by
    rw [hY]
    exact Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, hx⟩)
  obtain ⟨Y', hY'⟩ : ∃ Y' : Subgroup (ModGL τ K), Y' = Y.map (adjointGroup τ K).subtype :=
    ⟨_, rfl⟩
  have hYle : Y' ≤ adjointGroup τ K := by
    rw [hY']
    exact Subgroup.map_subtype_le Y
  have hPle : ∀ (i : Fin τ.rank) (x : ModGL τ K), x ∈ parabolicSubgroup τ K {i}ᶜ → x ∈ Y' := by
    intro i x hx
    have hxC : x ∈ adjointGroup τ K := parabolicSubgroup_le_adjointGroup τ K _ hx
    rw [hY']
    exact ⟨⟨x, hxC⟩, hPY i (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  obtain ⟨i0, -⟩ := exists_pair_ne (Fin τ.rank)
  have hB : borelGroup τ K ≤ Y' := fun b hb =>
    hPle i0 b (borelGroup_le_parabolicSubgroup _ hb)
  obtain ⟨-, hcl⟩ := (Chevalley_Borel_overgroups_and_radical_normalizers τ K).1 Y' hB hYle
  have hJ' : ∀ j : Fin τ.rank, weylElt τ K j 1 ∈ Y' := by
    intro j
    obtain ⟨i1, hi1⟩ := exists_ne j
    exact hPle i1 _ (weylElt_mem_parabolicSubgroup (show j ∈ ({i1}ᶜ : Set (Fin τ.rank)) from
      fun h => hi1 h.symm))
  have hY'top : Y' = adjointGroup τ K := by
    rw [hcl]
    have : {i | weylElt τ K i 1 ∈ Y'} = Set.univ := Set.eq_univ_of_forall hJ'
    rw [this]
    exact (standard_parabolic_cells τ K).2.2.2.2.2.1
  rw [eq_top_iff]
  intro x _
  have hxY' : (x : ModGL τ K) ∈ Y' := by
    rw [hY'top]
    exact x.2
  rw [hY'] at hxY'
  obtain ⟨y, hy, hyx⟩ := hxY'
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem exists_sylow_posUnipotent [Finite K] [CharP K 2] :
    ∃ P : Sylow 2 ↥(adjointGroup τ K),
      (P : Subgroup ↥(adjointGroup τ K)) = (posUnipotent τ K).subgroupOf (adjointGroup τ K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (RootWeightDatum.ordinary (K := K) τ).exists_sylow_eq_unipotent 2

theorem radicalGen_posUnipotent [Finite K] [CharP K 2] (hrank : 2 ≤ τ.rank) :
    RadicalGen 2 ↥(adjointGroup τ K) ((posUnipotent τ K).subgroupOf (adjointGroup τ K)) := by
  unfold RadicalGen
  rw [eq_top_iff, ← closure_parTag_eq_top hrank]
  refine Subgroup.closure_mono ?_
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  have hJ : ({i}ᶜ : Set (Fin τ.rank)) ≠ Set.univ := fun h => by
    have : i ∈ ({i}ᶜ : Set (Fin τ.rank)) := by rw [h]; exact Set.mem_univ i
    exact this rfl
  refine ⟨radTag τ K {i}ᶜ, isPGroup_radTag _, ?_, centralizer_radTag_le hJ, ?_⟩
  · intro r hr
    exact Subgroup.mem_subgroupOf.2
      ((parabolicRadical_le_posUnipotent _) (Subgroup.mem_subgroupOf.1 hr))
  · rw [normalizer_radTag]
    exact hi

theorem radRigid_adjointGroup [Finite K] [CharP K 2] (hrank : 2 ≤ τ.rank) :
    RadRigid 2 ↥(adjointGroup τ K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_posUnipotent (τ := τ) (K := K)
  refine radRigid_of_gen ((holds_adjointGroup_tag τ K 2).holdsTits)
    (fun R hR => centralizer_le_of_isRadical hR) ?_
  exact RadicalGen.of_sylow U₀ (by rw [hU₀]; exact radicalGen_posUnipotent hrank)

end Tag

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
