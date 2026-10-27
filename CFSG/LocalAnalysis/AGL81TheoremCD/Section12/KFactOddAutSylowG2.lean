module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolicReduce
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGTwoModel
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12


private theorem inndiagGroup_g2_eq_adjointGroup (K : Type) [Field K] :
    CFSG.StandardType.RecipeExcLang.inndiagGroup .G2 K =
      CFSG.Blueprint.Chevalley.adjointGroup .G2 K := by
  refine le_antisymm ?_ CFSG.StandardType.RecipeExcLang.adjointGroup_le_inndiagGroup
  rintro w ⟨b, j, hj, rfl⟩
  obtain ⟨B, hB, -⟩ :=
    (CFSG.LieType.Chevalley.G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).1
  exact mul_mem
    ((CFSG.LieType.Chevalley.G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K).2
      B hB b).2.2.1 hj

private theorem mulAutCongr_inndiagFieldAut {K : Type} [Field K]
    {hΓ : CFSG.StandardType.RecipeExcLang.inndiagGroup .G2 K =
      CFSG.Blueprint.Chevalley.adjointGroup .G2 K}
    (T : K ≃+* K) :
    MulAut.congr (MulEquiv.subgroupCongr hΓ)
        (CFSG.StandardType.RecipeExcLang.inndiagFieldAut .G2 K T) =
      CFSG.LieType.Chevalley.entrywiseAdjointAut .G2 T := by
  refine MulEquiv.ext fun h => ?_
  apply Subtype.ext
  simp [MulAut.congr_apply, CFSG.StandardType.RecipeExcLang.coe_inndiagFieldAut,
    CFSG.LieType.Chevalley.coe_entrywiseAdjointAut]

private theorem exists_conj_g2FieldHom_of_lang {K : Type} [Field K] [Finite K] [CharP K 2]
    {f e p : ℕ} (hKf : Nat.card K = 2 ^ f) (hK4 : 4 ≤ Nat.card K)
    (he : 1 ≤ e) (hp : 1 ≤ p) (hep : e * p = f) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ (2 ^ e)) (g' : CFSG.Blueprint.Chevalley.adjointGroup .G2 K)
    (hY : (MulAut.conj g' *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T) ^ p = 1) :
    ∃ c : CFSG.Blueprint.Chevalley.adjointGroup .G2 K,
      MulAut.conj c * (MulAut.conj g' *
        CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T) *
        (MulAut.conj c)⁻¹ =
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T := by
  let w : CFSG.StandardType.RecipeExcLang.inndiagGroup .G2 K :=
    ⟨g', CFSG.StandardType.RecipeExcLang.adjointGroup_le_inndiagGroup g'.2⟩
  let X : MulAut (CFSG.StandardType.RecipeExcLang.inndiagGroup .G2 K) :=
    MulAut.conj w * CFSG.StandardType.RecipeExcLang.inndiagFieldAut .G2 K T
  let κ := MulAut.congr (MulEquiv.subgroupCongr (inndiagGroup_g2_eq_adjointGroup K))
  have hκF : κ (CFSG.StandardType.RecipeExcLang.inndiagFieldAut .G2 K T) =
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo.g2FieldHom_eq_entrywise]
    exact mulAutCongr_inndiagFieldAut T
  have hκX : κ X =
      MulAut.conj g' *
        CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T := by
    show κ (MulAut.conj w * CFSG.StandardType.RecipeExcLang.inndiagFieldAut .G2 K T) = _
    rw [map_mul, hκF]
    congr 1
  have hXp : X ^ p = 1 := by
    apply κ.injective
    rw [map_pow, hκX, map_one, hY]
  obtain ⟨cΓ, hcΓ⟩ :=
    CFSG.StandardType.RecipeExcLang.exists_conj_eq_inndiagFieldAut_frob
      hKf hK4 he hp hep T hT w hXp
  refine ⟨MulEquiv.subgroupCongr (inndiagGroup_g2_eq_adjointGroup K) cΓ, ?_⟩
  have h := congrArg κ hcΓ
  rw [map_mul, map_mul, map_inv, hκX, hκF,
    CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at h
  exact h

private theorem orderOf_g2FieldHom_dvd_orderOf {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 2 ≤ f) (hKf : Nat.card K = 2 ^ f)
    {α : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)}
    {g : CFSG.Blueprint.Chevalley.adjointGroup .G2 K} {σ : K ≃+* K}
    (hgσ : α = MulAut.conj g *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) :
    orderOf σ ∣ orderOf α := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK3 : ringChar K ≠ 3 := by
    have h := ringChar.eq K 2
    omega
  have hinner := (CFSG.RankThree.PartTwo.KFacts.g2_automorphism_normal_form hK3 hK4).2
  rw [orderOf_dvd_iff_pow_eq_one]
  set n := orderOf α with hn
  set g'' := ((List.range n).map fun i =>
    (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ ^ i) g).prod with hg''
  have hden : α ^ n = MulAut.conj g'' *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K (σ ^ n) := by
    rw [hgσ, CFSG.RankThree.PartOne.KE.conj_mul_pow_aut, ← map_pow]
  have hn1 : α ^ n = 1 := by rw [hn, pow_orderOf_eq_one]
  have hinner' : CFSG.RankThree.PartTwo.KFacts.IsInnerAut
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K (σ ^ n)) := by
    have h : MulAut.conj g'' *
        CFSG.RankThree.PartTwo.KFacts.g2FieldHom K (σ ^ n) = 1 := by
      rw [← hden]
      exact hn1
    have h2 : CFSG.RankThree.PartTwo.KFacts.g2FieldHom K (σ ^ n) =
        (MulAut.conj g'')⁻¹ :=
      eq_inv_of_mul_eq_one_right h
    rw [h2, ← map_inv]
    exact CFSG.RankThree.PartTwo.KFacts.isInnerAut_conj g''⁻¹
  exact hinner _ hinner'

private theorem orderOf_eq_orderOf_g2FieldHom {K : Type} [Field K] [Finite K] [CharP K 2]
    {f r k : ℕ} (hf : 2 ≤ f) (hKf : Nat.card K = 2 ^ f)
    {α : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)} (hα : orderOf α = r ^ k)
    (hinn : Subgroup.zpowers α ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) = ⊥)
    {g : CFSG.Blueprint.Chevalley.adjointGroup .G2 K} {σ : K ≃+* K}
    (hgσ : α = MulAut.conj g *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) :
    orderOf α = orderOf σ := by
  have hL3 : (MulAut.conj g *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) ^
      orderOf (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) = 1 :=
    pow_orderOf_eq_one_of_mul
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 K))
      (D := CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 K))
      (fun δ hδ _ _ => hδ) ⟨g, rfl⟩
      (fun x hx => by
        obtain ⟨y, rfl⟩ := hx
        exact ⟨(CFSG.RankThree.PartTwo.KFacts.g2FieldHom
          K σ) y, by
          ext z
          simp [MulAut.conj_apply, mul_assoc]⟩)
      (by rw [← hgσ, ← hα, pow_orderOf_eq_one])
      (by rw [← hgσ]; exact hinn)
  have hαdvd : orderOf α ∣
      orderOf (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) := by
    rw [hgσ]
    exact orderOf_dvd_of_pow_eq_one hL3
  have hEord : orderOf (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) ∣ orderOf σ :=
    orderOf_map_dvd (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K) σ
  exact Nat.dvd_antisymm (hαdvd.trans hEord)
    (orderOf_g2FieldHom_dvd_orderOf hf hKf hgσ)

private theorem exists_frobenius_pow_zpowers_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 2 ≤ f) (hKf : Nat.card K = 2 ^ f) (σ : K ≃+* K)
    (hp1 : 1 ≤ orderOf σ) :
    ∃ (e : ℕ) (T : K ≃+* K) (t u : ℕ), 1 ≤ e ∧ e * orderOf σ = f ∧
      (∀ c, T c = c ^ (2 ^ e)) ∧ σ ^ t = T ∧ T ^ u = σ := by
  obtain ⟨φ, hφ, hφord, hφtop, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (p := 2) Nat.prime_two (by omega) hKf
  let : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
  let : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  set p := orderOf σ with hpdef
  have hp1' : 1 ≤ p := hp1
  have hpdvd : p ∣ f := by
    rw [← hcardAut]
    exact orderOf_dvd_natCard σ
  set e := f / p with hedef
  have hep : e * p = f := Nat.div_mul_cancel hpdvd
  have he1 : 1 ≤ e := Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) (by omega)
  set T := φ ^ e with hTdef
  have hT : ∀ c, T c = c ^ (2 ^ e) := by
    intro c
    rw [hTdef, CFSG.LieType.Chevalley.ringEquiv_pow_apply]
    have hit : ∀ n : ℕ, (⇑φ)^[n] c = c ^ (2 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hφ, pow_two, pow_succ, pow_mul, pow_two]
    exact hit e
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow, hφord, Nat.gcd_eq_right ⟨p, hep.symm⟩]
    exact Nat.div_eq_of_eq_mul_left (by omega) (by rw [mul_comm]; exact hep.symm)
  have hTT : Subgroup.zpowers T = Subgroup.zpowers σ := by
    refine IsCyclic.subgroup_eq_iff_card_eq.2 ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hTord]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, σ ^ t = T := by
    have h : T ∈ Subgroup.zpowers σ := hTT ▸ Subgroup.mem_zpowers T
    rwa [← mem_powers_iff_mem_zpowers] at h
  obtain ⟨u, hu⟩ : ∃ u : ℕ, T ^ u = σ := by
    have h : σ ∈ Subgroup.zpowers T := hTT ▸ Subgroup.mem_zpowers σ
    rwa [← mem_powers_iff_mem_zpowers] at h
  exact ⟨e, T, t, u, he1, hep, hT, ht, hu⟩

private theorem pow_eq_one_and_pow_eq_of_zpowers {G H : Type*} [Group G] [Group H]
    {α : G} {σ T : H} {t u : ℕ} (hαord : orderOf α = orderOf σ)
    (ht : σ ^ t = T) (hu : T ^ u = σ) :
    (α ^ t) ^ u = α ∧ (α ^ t) ^ orderOf σ = 1 := by
  have htuα : (α ^ t) ^ u = α := by
    have htu_mod : t * u ≡ 1 [MOD orderOf σ] := by
      have h : σ ^ (t * u) = σ ^ 1 := by rw [pow_mul, ht, hu, pow_one]
      exact (pow_eq_pow_iff_modEq (x := σ)).mp h
    rw [← pow_mul]
    have h : α ^ (t * u) = α ^ 1 := by
      rw [pow_eq_pow_iff_modEq, hαord]
      exact htu_mod
    simpa using h
  have hαtp : (α ^ t) ^ orderOf σ = 1 := by
    have hdvd1 : orderOf (α ^ t) ∣ orderOf σ := by
      have := orderOf_pow_dvd (x := α) t
      rwa [hαord] at this
    have hdvd2 : orderOf σ ∣ orderOf (α ^ t) := by
      have := orderOf_pow_dvd (x := α ^ t) u
      rw [htuα] at this
      rwa [hαord] at this
    have hEq : orderOf (α ^ t) = orderOf σ := Nat.dvd_antisymm hdvd1 hdvd2
    rw [← hEq, pow_orderOf_eq_one]
  exact ⟨htuα, hαtp⟩

private theorem exists_conj_g2FieldHom_of_order {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) {f : ℕ} (hf : 2 ≤ f) (hKf : Nat.card K = 2 ^ f)
    {α : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)}
    {g : CFSG.Blueprint.Chevalley.adjointGroup .G2 K} {σ : K ≃+* K}
    (hgσ : α = MulAut.conj g *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ)
    (hαord : orderOf α = orderOf σ) (hp1 : 1 ≤ orderOf σ) :
    ∃ (γ : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) (τ : K ≃+* K),
      α = γ * CFSG.RankThree.PartTwo.KFacts.g2FieldHom K τ *
        γ⁻¹ := by
  obtain ⟨e, T, t, u, he1, hep, hT, ht, hu⟩ :=
    exists_frobenius_pow_zpowers_eq hf hKf σ hp1
  set g' : CFSG.Blueprint.Chevalley.adjointGroup .G2 K :=
    ((List.range t).map fun i =>
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ ^ i) g).prod
    with hg'def
  have hαt : α ^ t = MulAut.conj g' *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T := by
    rw [hgσ, CFSG.RankThree.PartOne.KE.conj_mul_pow_aut, ← map_pow, ht]
  obtain ⟨htuα, hαtp⟩ := pow_eq_one_and_pow_eq_of_zpowers hαord ht hu
  obtain ⟨c, hc⟩ :=
    exists_conj_g2FieldHom_of_lang (f := f) (e := e) (p := orderOf σ) hKf hK4 he1 hp1
      hep T hT g' (hαt ▸ hαtp)
  have hcinv : (MulAut.conj c⁻¹)⁻¹ = MulAut.conj c := by
    rw [map_inv, inv_inv]
  have hX : MulAut.conj g' *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T =
      MulAut.conj c⁻¹ * CFSG.RankThree.PartTwo.KFacts.g2FieldHom
        K T * MulAut.conj c := by
    have h := congrArg (fun y => MulAut.conj c⁻¹ * y * MulAut.conj c) hc
    simpa [mul_assoc] using h
  refine ⟨MulAut.conj c⁻¹, T ^ u, ?_⟩
  calc α = (α ^ t) ^ u := htuα.symm
    _ = (MulAut.conj c⁻¹ *
          CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T *
          (MulAut.conj c⁻¹)⁻¹) ^ u := by rw [hαt, hX, ← hcinv]
    _ = MulAut.conj c⁻¹ *
          (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K T) ^ u *
          (MulAut.conj c⁻¹)⁻¹ := conj_pow
    _ = MulAut.conj c⁻¹ *
          CFSG.RankThree.PartTwo.KFacts.g2FieldHom K (T ^ u) *
          (MulAut.conj c⁻¹)⁻¹ := by rw [← map_pow]

private theorem exists_card_eq_two_pow_of_four_le_card {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : 4 ≤ Nat.card K) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  refine ⟨(n : ℕ), ?_, hcard'⟩
  have h4 : 4 ≤ 2 ^ (n : ℕ) := by rw [← hcard']; exact hK
  have h2 : 2 ^ 2 ≤ 2 ^ (n : ℕ) := by
    calc 2 ^ 2 = 4 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := h4
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2

private theorem eq_one_of_eq_conj_mul_g2FieldHom_of_field_eq_one {K : Type} [Field K]
    {α : MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 K)}
    {g : CFSG.Blueprint.Chevalley.adjointGroup .G2 K} {σ : K ≃+* K}
    (hgσ : α = MulAut.conj g *
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ)
    (hσ1 : σ = 1)
    (hinn : Subgroup.zpowers α ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) = ⊥) :
    α = 1 := by
  have hαinner : α ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := by
    rw [hgσ, hσ1, map_one, mul_one]
    exact ⟨g, rfl⟩
  have hmem : α ∈ Subgroup.zpowers α ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers α, hαinner⟩
  rw [hinn] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem posUnipotent_map_g2FieldHom {K : Type} [Field K] [Finite K] (τ : K ≃+* K) :
    (CFSG.LieType.Steinberg.posUnipotent
        (CFSG.LieType.Steinberg.Adjoint.g2Datum K)).map
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K τ).toMonoidHom =
    CFSG.LieType.Steinberg.posUnipotent
      (CFSG.LieType.Steinberg.Adjoint.g2Datum K) := by
  let : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    CFSG.LieType.Chevalley.generated_group_finite .G2 K
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact
      CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo.g2FieldHom_mem_posUnipotent
        τ hy
  · rw [Subgroup.card_map_of_injective
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K τ).injective]

theorem oddAutSylowFixAt_g2 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* CFSG.Blueprint.AdjointQuotient .G2 K) {r : ℕ}
    (hr : r.Prime) (hr5 : 5 ≤ r) : OddAutSylowFixAt r Y := by
  classical
  obtain ⟨f, hf2, hKf⟩ := exists_card_eq_two_pow_of_four_le_card hK
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    CFSG.LieType.Chevalley.generated_group_finite .G2 K
  refine OddAutSylowFixAt.of_mulEquiv
    (e.trans (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K)).symm ?_
  have hB :=
    CFSG.AGLEmbedding.ParabHub.borelQuotient_g2
      (CFSG.AGLEmbedding.ParabAutIrr.adjointQuotientEquiv K).symm
  let S₀ : Sylow 2 ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    (CFSG.LieType.Steinberg.isPGroup_iSup_pos hB.extras hB.pGroup).toSylow hB.not_dvd_index
  refine OddAutSylowFixAt.of_conj S₀ ?_
  intro α k hα hinn
  obtain ⟨g, σ, hgσ⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.GTwo.exists_conj_mul_g2FieldHom
      hf2 hKf α
  have hαord : orderOf α = orderOf σ :=
    orderOf_eq_orderOf_g2FieldHom hf2 hKf hα hinn hgσ
  have hp1 : 1 ≤ orderOf σ := by
    have h2r : 2 ≤ r := by
      have h := hr.two_le
      omega
    have hpos : 0 < r := by omega
    have h : 0 < r ^ k := pow_pos hpos k
    rw [← hα] at h
    rwa [hαord] at h
  by_cases hσ1 : σ = 1
  · have hα1 : α = 1 :=
      eq_one_of_eq_conj_mul_g2FieldHom_of_field_eq_one hgσ hσ1 hinn
    exact ⟨1, 1, by rw [hα1]; simp, by
      rw [show (1 : MulAut ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)).toMonoidHom =
        MonoidHom.id _ from rfl, Subgroup.map_id]⟩
  · obtain ⟨γ, τ, hγτ⟩ :=
      exists_conj_g2FieldHom_of_order hK hf2 hKf hgσ hαord hp1
    refine ⟨γ, CFSG.RankThree.PartTwo.KFacts.g2FieldHom K τ,
      hγτ, ?_⟩
    have hS₀ : (S₀ : Subgroup ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K)) =
        CFSG.LieType.Steinberg.posUnipotent
          (CFSG.LieType.Steinberg.Adjoint.g2Datum K) := rfl
    rw [hS₀]
    exact posUnipotent_map_g2FieldHom τ

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
