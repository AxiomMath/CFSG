module

public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.LocalAnalysis.SectionRank.EvenCover.CoverMap
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit

public section

namespace CFSG.SectionRank.EvenCover

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.LieType.CentralExt
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalGroups.Orthogonal

variable {E : Type*} [Group E] [Finite E]

theorem even_spinPlus_central_odd_extension_splitting
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K 2] {π : E →* spinGroup (quadPlus n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadPlus n K) →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : spinGroup (quadPlus n K) →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := not_two_dvd_of_odd hodd
  refine exists_section_mulEquiv_of_existsUnique hcen
    (existsUnique_section_of_sl2_lift (p := 2) (SpinPlus.isCTGroupDatum hn)
      (plusDatum_steinbergExtras hn) (SpinPlus.isParametrization hn) (SpinPlus.rankOne hn) hπ
      hcen hC fun ρ => ?_)
  obtain ⟨ρ', hρ', -⟩ := sl2_existsUnique_lift hπ hcen hC ρ
  exact ⟨ρ', fun g => congrArg (· g) hρ'⟩

section Minus

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
  [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]

theorem shortRels_h_eq_one_of_charTwo [Finite K] [CharP K 2] (i : Fin (n - 1))
    {t : ShortField b c} (ht : t ≠ 0) (h1 : (shortRels n hirr i).h t = 1) : t = 1 := by
  set a := fieldCoord t with ha_def
  have ha : a ≠ 0 := fieldCoord_ne_zero ht
  rw [shortRels_h] at h1
  have hN : planeNorm b c a = 1 := by
    have he := spinAction_shortTorusElt_eVec n hirr i ha
    rw [h1, map_one] at he
    have := congrFun (congrArg (fun v => (v : Vm n K)) he) (.inl i)
    simpa [eVec] using this.symm
  have hrefl : ∀ q, planeRefl b c a q = planeRefl b c planeOne q := by
    intro q
    have hp := spinAction_shortTorusElt_planeVec n hirr i ha (planeRefl b c planeOne q)
    rw [h1, map_one, planeRefl_planeRefl planeNorm_planeOne_ne_zero] at hp
    exact (planeVec_injective n hp).symm
  have h0 := hrefl planeOne
  rw [planeRefl, hN, div_one] at h0
  have hs1 : planeRefl b c planeOne planeOne = planeOne := by
    ext k
    fin_cases k <;> simp [planeRefl, polarPlane, planeNorm, planeOne, CharTwo.two_eq_zero]
  rw [hs1, sub_eq_self] at h0
  have hB : polarPlane b c planeOne a = b * a 1 := by
    simp [polarPlane, planeOne, CharTwo.two_eq_zero]
  have hb : b ≠ 0 := by
    rintro rfl
    obtain ⟨s, hs⟩ := isSquare_of_charTwo' (-c)
    exact hirr s (by linear_combination -hs)
  have ha1 : a 1 = 0 := by
    have hB0 := (smul_eq_zero.1 h0).resolve_right ha
    rw [hB] at hB0
    exact (mul_eq_zero.1 hB0).resolve_left hb
  simp only [planeNorm, ha1] at hN
  have ha0 : a 0 = 1 := CharTwo.sq_inj.1 (by rw [one_pow]; linear_combination hN)
  have hre : t.re = a 0 := rfl
  have him : t.im = a 1 := rfl
  exact QuadraticAlgebra.ext (hre.trans (ha0.trans QuadraticAlgebra.re_one.symm))
    (him.trans (ha1.trans QuadraticAlgebra.im_one.symm))

end Minus

theorem even_spinMinus_central_odd_extension_splitting
    {n : ℕ} (hn : 4 ≤ n) {k : Type} [Field k]
    [Finite k] [CharP k 2] {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {π : E →* spinGroup (quadMinus n k b c)} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadMinus n k b c) →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : spinGroup (quadMinus n k b c) →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap k (ShortField b c)).injective _
  have hC := not_two_dvd_of_odd hodd
  refine exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_rankOne_lift
    (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
    (fun _ hγ => isPGroup_minusRootGroup hirr hγ) hπ hker hC fun i => ?_)
  by_cases hi : i.val + 1 < n - 1
  · obtain ⟨ρ', hρ', -⟩ := sl2_existsUnique_lift hπ hker hC
      ((minusFrame n b c).longSL2 (succ_ne_of_lt n hi) true false)
    exact exists_lift_of_injective (SpinFrame.longSL2_injective _ _ _ _)
      (rankOne_minusRootGroup_of_lt n hirr hi).le fun g => DFunLike.congr_fun hρ' g
  · exact exists_rankOne_lift_of_rankOneRels (minusDatum_steinbergExtras n hirr) i
      (shortRels n hirr i) (mem_minusRootGroup_single_iff hirr hi)
      (mem_minusRootGroup_neg_single_iff hirr hi) (shortRels_x_injective hirr i)
      (fun t ht h1 => shortRels_h_eq_one_of_charTwo hirr i ht h1) hπ hker hC

omit [Finite E] in
theorem existsUnique_section_of_mulEquiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H)
    {π : E →* H} (h : ∃! s : G →* E, ∀ x, Φ.symm (π (s x)) = x) :
    ∃! s : H →* E, ∀ x, π (s x) = x := by
  obtain ⟨s, hs, huniq⟩ := h
  refine ⟨s.comp Φ.symm.toMonoidHom, fun x => Φ.symm.injective (hs (Φ.symm x)), fun τ hτ => ?_⟩
  have h := huniq (τ.comp Φ.toMonoidHom) fun x => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hτ, MulEquiv.symm_apply_apply]
  ext x
  have := congrArg (· (Φ.symm x)) h
  simpa using this

omit [Finite E] in
theorem ker_symm_comp {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (π : E →* H) :
    (Φ.symm.toMonoidHom.comp π).ker = π.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

section Omega

variable {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
  {Q : QuadraticForm K (σ → K)} {Q₀ : (σ → K) → K}

@[expose] noncomputable def spinMatrixEquiv (hker : (spinMatrix Q).ker = ⊥)
    (hR : (spinMatrix Q).range = StatedOmega Q₀) : spinGroup Q ≃* StatedOmega Q₀ :=
  (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff _).1 hker)).trans (MulEquiv.subgroupCongr hR)

theorem statedScalars_subgroupOf_statedOmega_eq_bot [CharP K 2] (hQ₀ : ⇑Q = Q₀)
    (hv : ∃ v, Q v ≠ 0) : (StatedScalars σ K).subgroupOf (StatedOmega Q₀) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hmem : Matrix.GeneralLinearGroup.scalar σ c ∈ StatedOmega Q₀ := by
    rw [hc]
    exact g.2
  have hc1 : (c : K) = 1 :=
    CharTwo.sq_inj.1 (by rw [sq_eq_one_of_scalar_mem_statedOmega hQ₀ hv hmem, one_pow])
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, hc1, map_one]
  rfl

end Omega

theorem even_split_orthogonal_central_odd_extension_splitting
    {n : ℕ} (hn : 3 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] {π : E →* StatedOmega (StatedQuadPlus n K)}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : StatedOmega (StatedQuadPlus n K) →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : StatedOmega (StatedQuadPlus n K) →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  set Φ := spinMatrixEquiv (ker_spinMatrix_quadPlus_eq_bot (n := n) (K := K) CharTwo.two_eq_zero)
    (range_spinMatrix_quadPlus hn)
  have hker := ker_symm_comp Φ π
  obtain ⟨s, hs, huniq, -⟩ := even_spinPlus_central_odd_extension_splitting hn
    (Φ.symm.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hodd)
  exact exists_section_mulEquiv_of_existsUnique hcen
    (existsUnique_section_of_mulEquiv Φ ⟨s, hs, huniq⟩)

theorem even_nonsplit_orthogonal_central_odd_extension_splitting
    {n : ℕ} (hn : 4 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {π : E →* StatedOmega (StatedQuadMinus n K b c)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : StatedOmega (StatedQuadMinus n K b c) →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : StatedOmega (StatedQuadMinus n K b c) →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 := by
  set Φ := spinMatrixEquiv (ker_spinMatrix_quadMinus_eq_bot (n := n) hirr CharTwo.two_eq_zero)
    (range_spinMatrix_quadMinus hn hirr)
  have hker := ker_symm_comp Φ π
  obtain ⟨s, hs, huniq, -⟩ := even_spinMinus_central_odd_extension_splitting hn hirr
    (Φ.symm.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hodd)
  exact exists_section_mulEquiv_of_existsUnique hcen
    (existsUnique_section_of_mulEquiv Φ ⟨s, hs, huniq⟩)

theorem center_eq_bot_of_even_split_orthogonal
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 3 ≤ n) {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    Subgroup.center L = ⊥ := by
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := even_split_orthogonal_central_odd_extension_splitting hn hsurj hcen
    (Odd.of_dvd_nat hodd hdvd)
  obtain ⟨φ, -, -, hD⟩ := perfect_cover_map_of_section e σ hσ
  rw [← hD, statedScalars_subgroupOf_statedOmega_eq_bot (coe_quadPlus n K)
    (exists_map_ne_zero_of_hypPair _ (plusPair K (⟨0, by omega⟩ : Fin n))), Subgroup.map_bot]

theorem center_eq_bot_of_even_nonsplit_orthogonal
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {L : Type*}
    [Group L] [Finite L] [Group.IsPerfect L] (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    Subgroup.center L = ⊥ := by
  obtain ⟨hsurj, hcen, hdvd⟩ := pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ, -⟩ := even_nonsplit_orthogonal_central_odd_extension_splitting hn hirr hsurj
    hcen (Odd.of_dvd_nat hodd hdvd)
  obtain ⟨φ, -, -, hD⟩ := perfect_cover_map_of_section e σ hσ
  rw [← hD, statedScalars_subgroupOf_statedOmega_eq_bot (coe_quadMinus n K b c)
    (exists_map_ne_zero_of_hypPair _ (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1)))),
    Subgroup.map_bot]

theorem even_split_orthogonal_odd_cover_catalog_step
    {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L) (hodd : Odd (Nat.card (Subgroup.center L))) {n f : ℕ}
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus n 2 f) :
    Subgroup.center L = ⊥ ∧ (IsStronglyQuasithin L → CatalogStepConclusion L) := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ClassicalOdd.charP_of_card hK
  have : Group.IsPerfect L := hL.1
  have hZ := center_eq_bot_of_even_split_orthogonal (by omega) hodd e
  exact ⟨hZ, fun hSQT => catalogStepConclusion_of_center_eq_bot hSQT hZ⟩

theorem even_nonsplit_orthogonal_odd_cover_catalog_step
    {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L) (hodd : Odd (Nat.card (Subgroup.center L))) {n f : ℕ}
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaMinus n 2 f) :
    Subgroup.center L = ⊥ ∧ (IsStronglyQuasithin L → CatalogStepConclusion L) := by
  obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ClassicalOdd.charP_of_card hK
  have : Group.IsPerfect L := hL.1
  have hZ := center_eq_bot_of_even_nonsplit_orthogonal hn hirr hodd e
  exact ⟨hZ, fun hSQT => catalogStepConclusion_of_center_eq_bot hSQT hZ⟩

end CFSG.SectionRank.EvenCover
