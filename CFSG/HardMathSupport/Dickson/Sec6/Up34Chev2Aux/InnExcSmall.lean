module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcUniDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallRankOne
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.Goldschmidt.Steps.G37Quot
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.RankThree.Chevalley

namespace Up34Exc

section RankOne

theorem center_sl2_eq_bot_two (K : Type) [Field K] [CharP K 2] :
    Subgroup.center (SL2 K) = ⊥ := by
  ext A
  rw [Subgroup.mem_bot]
  constructor
  · intro hA
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have h2 : r ^ 2 = 1 := by simpa using hr
    have h3 : (r - 1) ^ 2 = 0 := by
      have : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination h2 + (1 - r) * this
    have h4 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff (two_ne_zero)).mp h3)
    apply Subtype.ext
    rw [← hrA, h4]
    simp
  · rintro rfl
    exact Subgroup.one_mem _

theorem card_sl2_eq (K : Type) [Field K] [Finite K] :
    Nat.card (SL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite K
  have hcard : Nat.card (SL2 K) =
      ((Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K)) /
        (Fintype.card K - 1) := by
    have := Matrix.card_SL_field (𝔽 := K) 2
    simpa [Fin.prod_univ_two] using this
  have h2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [hcard, Nat.card_eq_fintype_card]
  have e : Fintype.card K ^ 2 - Fintype.card K = Fintype.card K * (Fintype.card K - 1) := by
    rw [Nat.mul_sub, pow_two, mul_one]
  have hpos : 0 < Fintype.card K - 1 := by omega
  rw [e]
  generalize Fintype.card K ^ 2 - 1 = X
  generalize Fintype.card K - 1 = Y at hpos ⊢
  have : X * (Fintype.card K * Y) = (Fintype.card K * X) * Y := by ring
  rw [this]
  exact Nat.mul_div_cancel _ hpos


theorem componentRootSpan_eq_range_of_rank_one {τ : Tag} {M : Type} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) {K : Type} [Field K]
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i)
    (hrank : ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α) :
    componentRootSpan K χ i = (rootSL2 τ K α).range := by
  refine le_antisymm (componentRootSpan_le_range_of_rank_one i hα hrank) ?_
  have hαr : IsRoot τ α := (isRootComponent_componentRoots i).isRoot α hα
  rw [range_rootSL2_of_isRoot hαr]
  have hneg : -α ∈ componentRoots χ i := (isRootComponent_componentRoots i).neg_mem α hα
  exact sup_le (rootSubgroup_le_rootSpan hα) (rootSubgroup_le_rootSpan hneg)

theorem nonempty_mulEquiv_sl2_of_rank_one {τ : Tag} {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α)
    (K : Type) [Field K] : Nonempty (SL2 K ≃* ↥(componentRootSpan K χ i)) := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep i
  have hα : a.1 ∈ componentRoots χ i := ⟨a.2, ha⟩
  have hαr : IsRoot τ a.1 := (isRootComponent_componentRoots i).isRoot a.1 hα
  have hCeq := componentRootSpan_eq_range_of_rank_one (K := K) i hα (hrank a.1 hα)
  exact ⟨(MonoidHom.ofInjective (rootSL2_injective_of_field a.1)).trans
    (MulEquiv.subgroupCongr hCeq.symm)⟩

theorem card_componentRootSpan_rankOne_le_six {τ : Tag} {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(componentRootSpan K χ i) ≤ 6 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_sl2_of_rank_one χ i hrank K
  rw [← Nat.card_congr e.toEquiv, card_sl2_eq, hK]
  norm_num

theorem no_card_sl2_eq_20160 (q : ℕ) (h2 : 2 ≤ q) : q * (q ^ 2 - 1) ≠ 20160 := by
  intro h
  rcases le_or_gt q 27 with hq | hq
  · interval_cases q <;> omega
  · have h1 : 28 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have h3 : 28 * 783 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq (by omega)
    omega

theorem rankOne_not_isLThreeFour {τ : Tag} {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {R : Type} [Group R] (f : ↥(componentRootSpan K χ i) →* R)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center ↥(componentRootSpan K χ i))
    (hL34 : IsLThreeFour (R ⧸ Subgroup.center R)) : False := by
  classical
  obtain ⟨e⟩ := nonempty_mulEquiv_sl2_of_rank_one χ i hrank K
  have hZC : Subgroup.center ↥(componentRootSpan K χ i) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨A, rfl⟩ := e.surjective c
    have hA : A ∈ Subgroup.center (SL2 K) := by
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro B
      apply e.injective
      rw [map_mul, map_mul]
      exact hc (e B)
    rw [center_sl2_eq_bot_two, Subgroup.mem_bot] at hA
    rw [hA, map_one]
    exact Subgroup.one_mem _
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact eq_bot_iff.2 (hker.trans hZC.le)
  let g : ↥(componentRootSpan K χ i) ≃* R := MulEquiv.ofBijective f ⟨hinj, hf⟩
  have hZR : Subgroup.center R = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    obtain ⟨c, rfl⟩ := g.surjective r
    have hc : c ∈ Subgroup.center ↥(componentRootSpan K χ i) := by
      rw [Subgroup.mem_center_iff] at hr ⊢
      intro d
      apply g.injective
      rw [map_mul, map_mul]
      exact hr (g d)
    rw [hZC, Subgroup.mem_bot] at hc
    rw [hc, map_one]
    exact Subgroup.one_mem _
  have h1 : Nat.card (R ⧸ Subgroup.center R) = 20160 := card_eq_of_isLThreeFour hL34
  have h2 : Nat.card R = 20160 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
    rw [hZR, Subgroup.card_bot, mul_one] at this
    rw [this]
    rw [hZR] at h1
    exact h1
  have h3 : Nat.card (SL2 K) = 20160 := by
    rw [Nat.card_congr (e.toEquiv.trans g.toEquiv)]
    exact h2
  rw [card_sl2_eq] at h3
  exact no_card_sl2_eq_20160 (Nat.card K) Finite.one_lt_card h3

end RankOne

section Unipotent


theorem innexc_isLThreeFour_of_surjective_central {C R : Type*} [Group C] [Group R]
    (hC : Group.IsPerfect C) (f : C →* R) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center C) (h : IsLThreeFour (R ⧸ Subgroup.center R)) :
    IsLThreeFour (C ⧸ Subgroup.center C) := by
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hC f hf hker
  exact IsLThreeFour.of_mulEquiv e.symm h

theorem two_pow_dvd_20160 {n : ℕ} (h : 2 ^ n ∣ 20160) : n ≤ 6 := by
  have h1 : 2 ^ n ∣ 2 ^ 6 * 315 := by norm_num; exact h
  have h2 : 2 ^ n ∣ 2 ^ 6 :=
    Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 315)) h1
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2

theorem unipotent_not_isLThreeFour (hU : UniEmbed) {τ : Tag} {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    {R : Type} [Group R] (f : ↥(componentRootSpan K χ i) →* R)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center ↥(componentRootSpan K χ i))
    (hperf : Group.IsPerfect ↥(componentRootSpan K χ i))
    (hL34 : IsLThreeFour (R ⧸ Subgroup.center R))
    (hbig : 64 < Nat.card K ^ (posRoots (componentRoots χ i)).ncard) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVp, hVcard, hVZ⟩ := hU τ χ i K 2
  have hCL := innexc_isLThreeFour_of_surjective_central hperf f hf hker hL34
  let g : ↥V →* ↥(componentRootSpan K χ i) ⧸ Subgroup.center ↥(componentRootSpan K χ i) :=
    (QuotientGroup.mk' _).comp V.subtype
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : ↥(componentRootSpan K χ i)) ∈ Subgroup.center ↥(componentRootSpan K χ i) :=
      (QuotientGroup.eq_one_iff _).1 hx
    have hmem : (x : ↥(componentRootSpan K χ i)) ∈
        V ⊓ Subgroup.center ↥(componentRootSpan K χ i) := ⟨x.2, hx'⟩
    rw [hVZ, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hdvd : Nat.card V ∣ 20160 := by
    rw [← card_eq_of_isLThreeFour hCL]
    exact Subgroup.card_dvd_of_injective g hginj
  haveI : Finite ↥V := inferInstance
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥V)).1 hVp
  rw [hn] at hdvd
  have hn6 : n ≤ 6 := two_pow_dvd_20160 hdvd
  have h64 : Nat.card ↥V ≤ 64 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
      _ = 64 := by norm_num
  rw [hVcard] at h64
  omega

end Unipotent

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
