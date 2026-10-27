module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311r

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311s

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.RankThree.PartOne.CTP CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Seitz.Proving

section Abstract

variable {G : Type*} [Group G]

theorem fixedSubgroup_conj_eq_map_inputs2311s (ψ β : MulAut G) :
    fixedSubgroup (ψ * β * ψ⁻¹) = (fixedSubgroup β).map ψ.toMonoidHom := by
  ext y
  rw [mem_fixedSubgroup, Subgroup.mem_map]
  constructor
  · intro hy
    refine ⟨ψ⁻¹ y, ?_, MulAut.apply_inv_self G ψ y⟩
    have h1 : ψ (β (ψ⁻¹ y)) = y := hy
    show β (ψ⁻¹ y) = ψ⁻¹ y
    calc β (ψ⁻¹ y) = ψ⁻¹ (ψ (β (ψ⁻¹ y))) := (MulAut.inv_apply_self G ψ _).symm
      _ = ψ⁻¹ y := by rw [h1]
  · rintro ⟨z, hz, rfl⟩
    have hz' : β z = z := hz
    show ψ (β (ψ⁻¹ (ψ z))) = ψ z
    rw [MulAut.inv_apply_self G ψ z, hz']

theorem mem_normalizer_of_map_inputs2311s (ψ : MulAut G) {H : Subgroup G} {g : G}
    (hg : ψ g ∈ Subgroup.normalizer ((H.map ψ.toMonoidHom : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  have hmem : ∀ k : G, ψ k ∈ H.map ψ.toMonoidHom ↔ k ∈ H := fun k =>
    ⟨fun ⟨l, hl, hlk⟩ => by
      have hlk' : l = k := ψ.injective hlk
      rwa [← hlk'], fun hk => ⟨k, hk, rfl⟩⟩
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  have key := hg (ψ h)
  rw [show ψ g * ψ h * (ψ g)⁻¹ = ψ (g * h * g⁻¹) by rw [map_mul, map_mul, map_inv], hmem, hmem] at key
  exact key

theorem isSimpleGroup_fixedSubgroup_conj_inputs2311s (ψ β : MulAut G)
    [IsSimpleGroup ↥(fixedSubgroup β)] : IsSimpleGroup ↥(fixedSubgroup (ψ * β * ψ⁻¹)) := by
  rw [fixedSubgroup_conj_eq_map_inputs2311s]
  exact MulEquiv.isSimpleGroup
    (Subgroup.equivMapOfInjective (fixedSubgroup β) ψ.toMonoidHom ψ.injective).symm

theorem zpow_eq_pow_emod_three_inputs2311s {g : G} (hg : g ^ 3 = 1) (k : ℤ) :
    g ^ k = g ^ (k % 3).toNat := by
  have hk : k = (k % 3) + 3 * (k / 3) := by have := Int.mul_ediv_add_emod k 3; omega
  have hnn : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  conv_lhs => rw [hk]
  rw [zpow_add, zpow_mul, zpow_ofNat, hg, one_zpow, mul_one]

end Abstract

section Graph

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K]

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple in
theorem center_fixedSubgroup_d4Graph_one_inputs2311s (hK3 : 3 ≤ Nat.card K) :
    Subgroup.center ↥(fixedSubgroup (d4Graph K 1)) = ⊥ := by
  set Φ := (MulEquiv.subgroupCongr (show fixedSubgroup (d4Graph K 1) = fixSubgroup (d4Graph K 1) from
    Subgroup.ext fun _ => Iff.rfl)).trans (fixSubgroupEquivG2 K hK3)
  rw [eq_bot_iff]
  intro z hz
  have hΦ : Φ z ∈ Subgroup.center ↥(adjointGroup Tag.G2 K) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨v, rfl⟩ := Φ.surjective w
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) v]
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hΦ
  exact Φ.injective (hΦ.trans (map_one Φ).symm)

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple in
theorem isSimpleGroup_fixedSubgroup_d4Graph_one_inputs2311s (hK3 : 3 ≤ Nat.card K) :
    IsSimpleGroup ↥(fixedSubgroup (d4Graph K 1)) := by
  have heq : fixedSubgroup (d4Graph K 1) = fixSubgroup (d4Graph K 1) :=
    Subgroup.ext fun _ => Iff.rfl
  have hq : CFSG.IsQuasisimple ↥(fixedSubgroup (d4Graph K 1)) :=
    CFSG.IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr heq).symm
      (isQuasisimple_fixSubgroup_d4Graph_one hK3)
  exact CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
    ((QuotientGroup.quotientMulEquivOfEq (center_fixedSubgroup_d4Graph_one_inputs2311s hK3)).trans
      QuotientGroup.quotientBot).symm

theorem not_isA2Type_d4Graph_one_inputs2311s (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3) :
    ¬ IsA2Type (d4Graph K 1) := by
  rintro ⟨ψ, B, hB3, hB1, h⟩
  obtain ⟨hrp, hrK, hK5⟩ := Inputs2311q.ringChar_facts_inputs2311q hK2 hK3
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd.d4GraphA2FixIsoOdd_holds K hK2
    hK3 hK5 B hB3 hB1
  obtain ⟨-, -, hns⟩ := Inputs2311m.exists_rGen_escape_of_isPGLPiThree (x := 1) hK5 hfix hrp hK3 hrK
    (map_one _) (one_pow 3)
  apply hns
  haveI := isSimpleGroup_fixedSubgroup_d4Graph_one_inputs2311s (K := K) (by omega)
  have hs := isSimpleGroup_fixedSubgroup_conj_inputs2311s ψ (d4Graph K 1)
  rcases h with h | h
  · rwa [h] at hs
  · rwa [h, fixedSubgroup_inv] at hs

theorem gammaP_not_mem_innerAut_inputs2311s (hK4 : 4 ≤ Nat.card K) (B : SL2 K) :
    gammaP K B ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) := by
  rintro ⟨g, hg⟩
  set h := sl2At K ⟨2, by decide⟩ B
  set g' := h⁻¹ * g
  have hγ : d4Graph K 1 = MulAut.conj g' := by
    rw [map_mul, map_inv, hg, gammaP, ← mul_assoc, inv_mul_cancel, one_mul]
  have hfix : d4Graph K 1 g' = g' := by
    rw [hγ, MulAut.conj_apply, mul_inv_cancel_right]
  have hcen : (⟨g', hfix⟩ : ↥(fixedSubgroup (d4Graph K 1))) ∈
      Subgroup.center ↥(fixedSubgroup (d4Graph K 1)) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨yv, hyv⟩
    have hy : d4Graph K 1 yv = yv := hyv
    rw [hγ, MulAut.conj_apply] at hy
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    calc yv * g' = g' * yv * g'⁻¹ * g' := by rw [hy]
      _ = g' * yv := by group
  rw [center_fixedSubgroup_d4Graph_one_inputs2311s (by omega), Subgroup.mem_bot] at hcen
  have hg1 : g' = 1 := congrArg Subtype.val hcen
  rw [hg1, map_one] at hγ
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf t = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers ht
  have hcardU : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have hmove := d4Graph_one_torusSub (coe_torusElement (K := K) ⟨0, by decide⟩ t)
  rw [hγ, MulAut.one_apply, coe_torusElement, tupAct_permM] at hmove
  have h0 := congrFun (rootDiagUnit_injective_D4 hmove) ⟨0, by decide⟩
  have hc : Tag.D4.cartan ⟨0, by decide⟩ (rhoP.symm ⟨0, by decide⟩) = 0 ∧
      Tag.D4.cartan ⟨0, by decide⟩ ⟨0, by decide⟩ = 2 := by decide
  simp only [hc.1, hc.2, zpow_zero] at h0
  have h2 : t ^ 2 = 1 := by
    rw [← zpow_natCast]
    exact_mod_cast h0
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hord, hcardU] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem fixedSubgroup_le_normalizer_of_isA2Type_inputs2311s (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [hEa : CFSG.IsElementaryAbelian 3 ↥E]
    (hc : Nat.card E = 3 ^ 2) {β : MulAut ↥(adjointGroup Tag.D4 K)} (hβE : β ∈ E)
    (hβout : β ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K)) (hβ : IsA2Type β)
    {y : ↥(adjointGroup Tag.D4 K)} (hy1 : y ≠ 1) (hyE : MulAut.conj y ∈ E) :
    fixedSubgroup β ≤
      Subgroup.normalizer (uniPlaneClosure (ringChar K) E : Set ↥(adjointGroup Tag.D4 K)) := by
  classical
  obtain ⟨φ, B, hB3, hB1, hφ⟩ := hβ
  set E₁ := E.map (MulAut.congr φ).toMonoidHom with hE₁
  haveI hE₁a : CFSG.IsElementaryAbelian 3 ↥E₁ := CFSG.IsElementaryAbelian.map _
  have hc₁ : Nat.card E₁ = 3 ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.congr φ).injective, hc]
  have hβE₁ : φ * β * φ⁻¹ ∈ E₁ := ⟨β, hβE, Inputs2311q.mulAut_congr_self_inputs2311q φ β⟩
  have hγE₁ : gammaP K B ∈ E₁ := by
    rcases hφ with h | h
    · rwa [h] at hβE₁
    · rw [h] at hβE₁
      simpa using E₁.inv_mem hβE₁
  set y' := φ y with hy'
  have hy'E₁ : MulAut.conj y' ∈ E₁ := ⟨MulAut.conj y, hyE, by rw [mulAut_congr_conj]⟩
  have hinj : Function.Injective
      (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)) := conj_injective_adj
  have hy'1 : y' ≠ 1 := fun h => hy1 (φ.injective (h.trans (map_one φ).symm))
  have hy'3 : y' ^ 3 = 1 :=
    hinj (by rw [map_pow, map_one]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hy'E₁)
  have hγy' : gammaP K B y' = y' := by
    apply hinj
    have hcomm : gammaP K B * MulAut.conj y' = MulAut.conj y' * gammaP K B := by
      have := hE₁a.toIsMulCommutative.is_comm.comm (⟨_, hγE₁⟩ : E₁) ⟨_, hy'E₁⟩
      exact congrArg Subtype.val this
    rw [← Inputs2311r.conj_mulAut_conj_inputs2311r, hcomm, mul_inv_cancel_right]
  have hγout : gammaP K B ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) := by
    intro hin
    apply hβout
    rw [← Inputs2311r.conj_mem_innerAut_iff_inputs2311r φ β]
    rcases hφ with h | h
    · rw [h]
      exact hin
    · rw [h]
      exact Subgroup.inv_mem _ hin
  have hnot : gammaP K B ∉ Subgroup.zpowers (MulAut.conj y') := by
    intro hmem
    apply hγout
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact ⟨y' ^ k, by rw [map_zpow, hk]⟩
  have hct1 : MulAut.conj y' ≠ 1 := fun h => hy'1 (hinj (h.trans (map_one _).symm))
  have hct3 : MulAut.conj y' ^ 3 = 1 := by rw [← map_pow, hy'3, map_one]
  have hgen : Subgroup.closure {gammaP K B, MulAut.conj y'} = E₁ :=
    Inputs2311q.closure_pair_eq_of_card_inputs2311q Nat.prime_three hc₁ hγE₁ hy'E₁ hct3 hct1 hnot
  have hesc := Inputs2311q.fixedSubgroup_le_normalizer_inputs2311q hK2 hK3 hB3 hB1 hγy' hy'3
  rw [hgen, hE₁, uniPlaneClosure_map_congr] at hesc
  intro g hg
  apply mem_normalizer_of_map_inputs2311s φ
  apply hesc
  have hfg : φ g ∈ fixedSubgroup (φ * β * φ⁻¹) := by
    rw [fixedSubgroup_conj_eq_map_inputs2311s]
    exact ⟨g, hg, rfl⟩
  rcases hφ with h | h
  · rwa [h] at hfg
  · rwa [h, fixedSubgroup_inv] at hfg

end Graph

section Sylow

set_option linter.unusedSectionVars false

theorem exists_conj_normalForm_inputs2311s {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 2)
    (hK4 : 4 ≤ Nat.card K) {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K K₂]
    (hcard : Nat.card K₂ = Nat.card K ^ 2) (σ : K₂ →+* K₂) (hσ : ∀ x, σ x = x ^ Nat.card K)
    {x : ↥(adjointGroup Tag.D4 K)} (hαx : gammaP K (orderThreeSL K) x = x) (hx3 : x ^ 3 = 1) :
    ∃ (Q : SL2 K₂) (ω : K₂ˣ) (hω3 : ω ^ 3 = 1) (r : ↥(adjointGroup Tag.D4 K₂)) (a₁ a₂ : K₂ˣ),
      Q⁻¹ * orderThreeSL K₂ * Q = HSL ω ∧ orderOf ω = 3 ∧
      (r : ModGL Tag.D4 K₂) = rootDiagUnit Tag.D4 (tupXZ a₁ a₂) ∧
      ∃ c : ↥(adjointGroup Tag.D4 K), gammaP K (orderThreeSL K) c = c ∧
        ∃ (t : ↥(adjointGroup Tag.D4 K₂)) (b : Fin Tag.D4.rank → K₂ˣ) (k : ℕ), k < 3 ∧
          (t : ModGL Tag.D4 K₂) = rootDiagUnit Tag.D4 b ∧ tupAct permM b = b ∧
          ιTw K Q (c⁻¹ * x * c) = t * (r * yP hω3) ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, ω, c₀, hQ, hω, hσω, hQc, hc₀⟩ := exists_twist_data hq hcard hσ
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hK₂ : Nat.card K₂ % 3 = 1 := by rw [hcard]; exact sq_mod_three hq
  have hK₂4 : 4 ≤ Nat.card K₂ := by rw [hcard]; nlinarith
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three_pow (K := K₂)
  set e := (Nat.card K₂ - 1).factorization 3 with he
  set μ := Subgroup.zpowers ζ with hμ
  have hμsq : ∀ u ∈ μ, ∃ b : K₂ˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hζq : ζ ^ (Nat.card K + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hζ]
    have hdvd : 3 ^ e ∣ (Nat.card K - 1) * (Nat.card K + 1) := by
      have h1 : 3 ^ e ∣ Nat.card K₂ - 1 := Nat.ordProj_dvd _ _
      have h2 : Nat.card K₂ - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
        rw [hcard]
        obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by
          have := Nat.card_pos (α := K); omega⟩
        rw [hm, Nat.add_sub_cancel]
        have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
        omega
      rwa [h2] at h1
    have hcop : Nat.Coprime (3 ^ e) (Nat.card K - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hμq : ∀ u ∈ μ, u ^ (Nat.card K + 1) = 1 := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζq, one_zpow]
  have hμσ : ∀ u ∈ μ, Units.map σ.toMonoidHom u = u⁻¹ := by
    intro u hu
    rw [units_frob hσ]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hμq u hu)
  have hζe : ζ ^ 3 ^ e = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hμ3 : ∀ u ∈ μ, u ^ 3 ^ e = 1 := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζe, one_zpow]
  have hT3ι : T3fix (ω := ω) (K := K₂) μ ≤ (ιTw K Q).range := by
    rintro t ⟨⟨a, ha, hta⟩, -⟩
    have hσt : bcAd σ t = t⁻¹ := by
      apply Subtype.ext
      rw [coe_bcAd_of_eq_rootDiagUnit σ hta, Subgroup.coe_inv, hta, rootDiagUnit_inv]
      congr 1
      funext j
      rw [Pi.inv_apply, hμσ _ (ha j)]
    have htinv : ((t⁻¹ : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 a⁻¹ := by
      rw [Subgroup.coe_inv, hta, rootDiagUnit_inv]
    refine mem_range_ιTw_of_fixed σ hσ hQc (k := e) ?_ ?_
    · rw [hσt, gTw_nSL_conj_diag c₀ htinv, inv_inv]
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hta, ← rootDiagUnit_pow_D4, Subgroup.coe_one, ← rootDiagUnit_one]
      congr 1
      funext j
      rw [Pi.pow_apply, Pi.one_apply, hμ3 _ (ha j)]
  obtain ⟨r, a₁, a₂, hr, hcr⟩ := exists_cocyc_eq_mul_bcAd hcard Nat.card_pos σ hσ hc₀
  have hπ3 : (r * yP hω3) ^ 3 = 1 := mul_yP_pow_three hω3 hr
  have hπnd : r * yP hω3 ∉ T3fix (ω := ω) (K := K₂) μ := by
    rintro ⟨⟨b, -, hb⟩, -⟩
    exact mul_yP_not_diag hω3 hω hr hb
  have hπ1 : r * yP hω3 ≠ 1 := by
    intro h1
    apply hπnd
    rw [h1]
    exact Subgroup.one_mem _
  have hπord : orderOf (r * yP hω3) = 3 := orderOf_eq_prime hπ3 hπ1
  have hπι : r * yP hω3 ∈ (ιTw K Q).range :=
    mem_range_ιTw_of_fixed σ hσ hQc (fixed_mul_yP hω3 hσω hr hcr) (k := 1)
      (by rw [pow_one]; exact hπ3)
  set P' := T3fix (ω := ω) (K := K₂) μ ⊔ Subgroup.zpowers (r * yP hω3) with hP'
  have hcardP' : Nat.card P' = Nat.card (T3fix (ω := ω) (K := K₂) μ) * 3 := by
    rw [hP', card_sup_of_le_normalizer
      ((Subgroup.zpowers_le).2 (mul_yP_mem_normalizer_T3fix hω3 μ hr))
      (inf_zpowers_eq_bot_of_pow_three hπ3 hπnd), Nat.card_zpowers, hπord]
  have hP'ge : 3 * Nat.card μ ^ 2 ≤ Nat.card P' := by
    rw [hcardP', mul_comm 3]
    exact Nat.mul_le_mul_right 3 (card_T3fix_ge (ω := ω) μ hμsq)
  have hP'p : IsPGroup 3 P' := by
    have hdvdT : Nat.card (T3fix (ω := ω) (K := K₂) μ) ∣ 3 ^ (4 * e) := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_left : T3fix (ω := ω) (K := K₂) μ ≤ torusSub μ)
      rwa [card_torusSub μ hμsq, hcardμ, ← pow_mul, mul_comm e 4] at h
    refine IsPGroup.of_card_dvd_pow (n := 4 * e + 1) ?_
    rw [hcardP', pow_succ]
    exact Nat.mul_dvd_mul_right hdvdT 3
  have hP'ι : P' ≤ (ιTw K Q).range := sup_le hT3ι ((Subgroup.zpowers_le).2 hπι)
  have hP'α : P' ≤ fixedSubgroup (gammaP K₂ (HSL ω)) :=
    sup_le inf_le_right ((Subgroup.zpowers_le).2 (gammaP_HSL_mul_yP hω3 hr))
  set P := P'.comap (ιTw K Q) with hP
  have hιinj : Function.Injective (ιTw K Q) := ιTw_injective Q
  have hcardP : Nat.card P = Nat.card P' := by
    rw [← Subgroup.card_map_of_injective hιinj, hP, Subgroup.map_comap_eq_self hP'ι]
  have hPp : IsPGroup 3 P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP'p
    exact IsPGroup.of_card (n := n) (by rw [hcardP, hn])
  have hPC : P ≤ fixedSubgroup (gammaP K (orderThreeSL K)) := by
    intro y hy
    show gammaP K (orderThreeSL K) y = y
    apply hιinj
    rw [ιTw_gammaP hQ y]
    exact hP'α hy
  have hmax : ∀ R : Subgroup ↥(adjointGroup Tag.D4 K), IsPGroup 3 R →
      R ≤ fixedSubgroup (gammaP K (orderThreeSL K)) → Nat.card R ≤ Nat.card P := by
    intro R hR hRC
    have h := card_le_of_isPGroup_fixed_gammaP hK₂ hK₂4 hω3 hω hζ (hR.map (ιTw K Q)) ?_
    · rw [Subgroup.card_map_of_injective hιinj] at h
      rw [hcardP]
      exact h.trans hP'ge
    · rintro y ⟨z, hz, rfl⟩
      rw [← ιTw_gammaP hQ z, show gammaP K (orderThreeSL K) z = z from hRC hz]
  obtain ⟨c, hcC, hcP⟩ := exists_conj_mem_of_forall_card_le hPC hPp hmax
    (show x ∈ fixedSubgroup (gammaP K (orderThreeSL K)) from hαx) hx3
  have hmem : ιTw K Q (c⁻¹ * x * c) ∈ P' := hcP
  obtain ⟨t, htT, y, hy, hty⟩ := CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.exists_mul_of_mem_sup
    ((Subgroup.zpowers_le).2 (mul_yP_mem_normalizer_T3fix hω3 μ hr)) hmem
  obtain ⟨⟨b, -, htb⟩, htα⟩ := htT
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hfixb : tupAct permM b = b := by
    have h1 : gammaP K₂ (HSL ω) t = t := htα
    have h2 := gammaP_HSL_diag ω htb
    rw [h1, htb] at h2
    exact (rootDiagUnit_injective_D4 h2).symm
  refine ⟨Q, ω, hω3, r, a₁, a₂, hQ, hω, hr, c, hcC, t, b, (k % 3).toNat, ?_, htb, hfixb, ?_⟩
  · have := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 3)
    omega
  · rw [hty, zpow_eq_pow_emod_three_inputs2311s hπ3]

end Sylow

section Planes

set_option linter.unusedSectionVars false

theorem pow_tuple_inputs2311s {L : Type} [Field L] (ω : Lˣ) (v : Fin Tag.D4.rank → ℤ) (n : ℕ) :
    (fun j => ω ^ v j) ^ n = fun j => ω ^ ((n : ℤ) * v j) := by
  funext j
  rw [Pi.pow_apply, ← zpow_natCast, ← zpow_mul, mul_comm]

theorem mul_tuple_inputs2311s {L : Type} [Field L] (ω : Lˣ) (v u : Fin Tag.D4.rank → ℤ) :
    (fun j => ω ^ v j) * (fun j => ω ^ u j) = fun j => ω ^ (v j + u j) := by
  funext j
  rw [Pi.mul_apply, ← zpow_add]

theorem tupXZ_pow_inputs2311s {L : Type} [Field L] (ω : Lˣ) (i l : ℕ) :
    tupXZ (ω ^ i) (ω ^ l) = fun j => ω ^ ((i : ℤ) * vX j + (l : ℤ) * vZ j) := by
  funext j
  rw [tupXZ_apply, ← zpow_natCast ω i, ← zpow_natCast ω l, ← zpow_mul, ← zpow_mul, ← zpow_add]

theorem mul_yP_pow_conj_diag_inputs2311s {L : Type} [Field L] {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    {r : ↥(adjointGroup Tag.D4 L)} {a : Fin Tag.D4.rank → Lˣ}
    (hr : (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 a) (k : ℕ) {g : ↥(adjointGroup Tag.D4 L)}
    {d : Fin Tag.D4.rank → Lˣ} (hg : (g : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 d) :
    (((r * yP hω3) ^ k * g * ((r * yP hω3) ^ k)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 (tupAct (weylG2M ^ (4 * k)) d) := by
  induction k generalizing g d with
  | zero =>
    simp only [pow_zero, one_mul, inv_one, mul_one, Nat.mul_zero, hg]
    rw [tupAct_one]
  | succ k ih =>
    have h1 := ih hg
    have h2 := yP_pow_conj_diag hω3 1 h1
    rw [pow_one] at h2
    have h3 := commute_of_diag hr h2
    have e : (r * yP hω3) ^ (k + 1) * g * ((r * yP hω3) ^ (k + 1))⁻¹ =
        r * (yP hω3 * ((r * yP hω3) ^ k * g * ((r * yP hω3) ^ k)⁻¹) * (yP hω3)⁻¹) * r⁻¹ := by
      rw [pow_succ', mul_inv_rev, mul_inv_rev]
      simp only [mul_assoc]
    rw [e, h3, mul_inv_cancel_right, h2, tupAct_tupAct, ← pow_add,
      show 4 * 1 + 4 * k = 4 * (k + 1) by ring]

theorem exponent_facts_inputs2311s :
    (∀ j, ((weylG2M ^ (4 * 1) * permM).mulVec (fun i => vD i - vH i) j) % 3 = (vD j - vH j) % 3) ∧
    (∀ j, ((weylG2M ^ (4 * 2) * permM).mulVec (fun i => vH i + vD i) j) % 3 = (vH j + vD j) % 3) ∧
    ∀ j, (3 : ℤ) ∣ (permM.mulVec vD j - vD j) - vX j ∧
      (3 : ℤ) ∣ 2 * vH j + 2 * (permM.mulVec vD j - vD j) - vZ j := by
  decide

theorem uniPlaneClosure_eq_top_nonsplit_of_ext_inputs2311s {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3) (hq : Nat.card K % 3 = 2)
    {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K K₂] (hcard : Nat.card K₂ = Nat.card K ^ 2)
    (σ : K₂ →+* K₂) (hσ : ∀ x, σ x = x ^ Nat.card K)
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} [hEa : CFSG.IsElementaryAbelian 3 ↥E]
    (hc : Nat.card E = 3 ^ 2) (hαE : gammaP K (orderThreeSL K) ∈ E)
    (hA2 : ∀ β ∈ E, β ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) → IsA2Type β)
    (hnf : ∀ c : ↥(adjointGroup Tag.D4 K), gammaP K (orderThreeSL K) c = c →
      MulAut.conj (frameDiag (orderThreeSL K)) ∉ E.map (MulAut.congr (MulAut.conj c)).toMonoidHom)
    {x : ↥(adjointGroup Tag.D4 K)} (hx1 : x ≠ 1) (hxE : MulAut.conj x ∈ E) :
    uniPlaneClosure (ringChar K) E = ⊤ := by
  classical
  obtain ⟨hrp, hrK, hK5⟩ := Inputs2311q.ringChar_facts_inputs2311q hK2 hK3
  have hK4 : 4 ≤ Nat.card K := by omega
  have hB3 : orderThreeSL K ^ 3 = 1 := orderThreeSL_pow_three K
  have hB1 : orderThreeSL K ≠ 1 := orderThreeSL_ne_one K
  have hinj : Function.Injective
      (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)) := conj_injective_adj
  have hx3 : x ^ 3 = 1 :=
    hinj (by rw [map_pow, map_one]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hxE)
  have hαx : gammaP K (orderThreeSL K) x = x := by
    apply hinj
    have hcomm : gammaP K (orderThreeSL K) * MulAut.conj x =
        MulAut.conj x * gammaP K (orderThreeSL K) := by
      have := hEa.toIsMulCommutative.is_comm.comm (⟨_, hαE⟩ : E) ⟨_, hxE⟩
      exact congrArg Subtype.val this
    rw [← Inputs2311r.conj_mulAut_conj_inputs2311r, hcomm, mul_inv_cancel_right]
  obtain ⟨Q, ω, hω3, r, a₁, a₂, hQ, hω, hr, c, hcα, t, b, k, hk3, htb, hfixb, hιx⟩ :=
    exists_conj_normalForm_inputs2311s hq hK4 hcard σ hσ hαx hx3
  have hcα' : gammaP K (orderThreeSL K) c⁻¹ = c⁻¹ := by rw [map_inv, hcα]
  suffices h : uniPlaneClosure (ringChar K) (E.map (MulAut.congr (MulAut.conj c⁻¹)).toMonoidHom) = ⊤ from
    (uniPlaneGen_map_congr (MulAut.conj c⁻¹) (ringChar K) E).1 h
  set E' := E.map (MulAut.congr (MulAut.conj c⁻¹)).toMonoidHom with hE'
  haveI hE'a : CFSG.IsElementaryAbelian 3 ↥E' := CFSG.IsElementaryAbelian.map _
  have hc' : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr (MulAut.conj c⁻¹)).injective, hc]
  have hαE' : gammaP K (orderThreeSL K) ∈ E' :=
    ⟨_, hαE, Inputs2311q.mulAut_congr_conj_of_fixed_inputs2311q hcα'⟩
  set x' := c⁻¹ * x * c with hx'def
  have hx'E' : MulAut.conj x' ∈ E' := by
    refine ⟨_, hxE, ?_⟩
    rw [mulAut_congr_conj, MulAut.conj_apply, inv_inv]
  have hx'1 : x' ≠ 1 := by
    intro h
    apply hx1
    have e : x = c * x' * c⁻¹ := by rw [hx'def]; group
    rw [e, h]
    group
  have hx'3 : x' ^ 3 = 1 :=
    hinj (by rw [map_pow, map_one]; exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hx'E')
  have hA2' : ∀ β ∈ E', β ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) → IsA2Type β := by
    rintro _ ⟨β₀, hβ₀, rfl⟩ hout
    rw [Inputs2311q.mulAut_congr_self_inputs2311q] at hout ⊢
    have hout' : β₀ ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) :=
      fun hmem => hout ((Inputs2311r.conj_mem_innerAut_iff_inputs2311r _ _).2 hmem)
    exact Inputs2311r.isA2Type_conj_inputs2311r _ (hA2 β₀ hβ₀ hout')
  have hnf' : MulAut.conj (frameDiag (orderThreeSL K)) ∉ E' := hnf c⁻¹ hcα'
  have hαout := gammaP_not_mem_innerAut_inputs2311s hK4 (orderThreeSL K)
  have hout : ∀ y : ↥(adjointGroup Tag.D4 K), MulAut.conj y * gammaP K (orderThreeSL K) ∉
      CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) := by
    intro y hy
    apply hαout
    have e : gammaP K (orderThreeSL K) =
        (MulAut.conj y)⁻¹ * (MulAut.conj y * gammaP K (orderThreeSL K)) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ⟨y, rfl⟩) hy
  set H := uniPlaneClosure (ringChar K) E' with hH
  have hNα : fixedSubgroup (gammaP K (orderThreeSL K)) ≤
      Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) :=
    fixedSubgroup_le_normalizer_of_isA2Type_inputs2311s hK2 hK3 hc' hαE' hαout
      ⟨1, orderThreeSL K, hB3, hB1, Or.inl (by rw [one_mul, inv_one, mul_one])⟩ hx'1 hx'E'
  suffices hd : frameD K (orderThreeSL K) ∈ Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) by
    have hN : Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) = ⊤ := by
      rw [eq_top_iff, ← closure_fixedSubgroup_frameD (A2NonsplitGen.d4GraphA2FrameGen_of
          A2NonsplitGen.frameTopRootsMem_holds A2NonsplitGen.frameClosing_holds) hK3 hK4,
        Subgroup.closure_le]
      rintro y (hy | hy)
      · exact hNα hy
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hd
    have hHn : H.Normal := Subgroup.normalizer_eq_top_iff.1 hN
    haveI hGs : IsSimpleGroup ↥(adjointGroup Tag.D4 K) := isSimpleGroup_adjointGroup_D4 K
    have hfix := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd.d4GraphA2FixIsoOdd_holds K hK2
      hK3 hK5 (orderThreeSL K) hB3 hB1
    obtain ⟨-, ⟨y₀, hαy₀, hy₀1, hy₀r⟩, -⟩ :=
      Inputs2311m.exists_rGen_escape_of_isPGLPiThree hK5 hfix hrp hK3 hrK hαx hx3
    have hα1 : gammaP K (orderThreeSL K) ≠ 1 := fun h => hαout ⟨1, by rw [map_one, h]⟩
    rcases hHn.eq_bot_or_eq_top with hb | ht
    · exfalso
      obtain ⟨n, hn⟩ := hy₀r
      have hy := mem_uniPlaneClosure hαE' hα1 hαy₀ hn
      rw [← hH, hb, Subgroup.mem_bot] at hy
      exact hy₀1 hy
    · exact ht
  have hιinj : Function.Injective (ιTw K Q) := ιTw_injective Q
  have hιψ : ((ιTw K Q (sl2At K ⟨2, by decide⟩ (orderThreeSL K)) : ↥(adjointGroup Tag.D4 K₂)) :
      ModGL Tag.D4 K₂) = rootDiagUnit Tag.D4 (fun j => ω ^ vH j) := by
    rw [ιTw_apply, bcAd_sl2At, mapSL_orderThreeSL, gTw_conj_sl2Two, hQ, sl2At_HSL, coe_torusElement]
    rfl
  have hιd : ((ιTw K Q (frameD K (orderThreeSL K)) : ↥(adjointGroup Tag.D4 K₂)) :
      ModGL Tag.D4 K₂) = rootDiagUnit Tag.D4 (fun j => ω ^ vD j) := by
    rw [ιTw_frameD hQ, coe_dTorus]
  have hψα : gammaP K (orderThreeSL K) (sl2At K ⟨2, by decide⟩ (orderThreeSL K)) =
      sl2At K ⟨2, by decide⟩ (orderThreeSL K) := by
    rw [gammaP, MulAut.mul_apply, MulAut.conj_apply, d4Graph_one_sl2Two, mul_inv_cancel_right]
  have hψN : sl2At K ⟨2, by decide⟩ (orderThreeSL K) ∈
      Subgroup.normalizer (H : Set ↥(adjointGroup Tag.D4 K)) := hNα hψα
  have hkey : ∀ (z : ↥(adjointGroup Tag.D4 K)) (v : Fin Tag.D4.rank → ℤ),
      ((ιTw K Q z : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 (fun j => ω ^ v j) →
      (∀ j, ((weylG2M ^ (4 * k) * permM).mulVec v j) % 3 = v j % 3) →
      (MulAut.conj x' * gammaP K (orderThreeSL K)) z = z := by
    intro z v hz hv
    apply hιinj
    apply Subtype.ext
    have hαz := gammaP_HSL_diag ω hz
    rw [← ιTw_gammaP hQ] at hαz
    have hconj := mul_yP_pow_conj_diag_inputs2311s hω3 hr k hαz
    have htc := commute_of_diag htb hconj
    have e : t * (r * yP hω3) ^ k * ιTw K Q (gammaP K (orderThreeSL K) z) * (t * (r * yP hω3) ^ k)⁻¹ =
        t * ((r * yP hω3) ^ k * ιTw K Q (gammaP K (orderThreeSL K) z) * ((r * yP hω3) ^ k)⁻¹) * t⁻¹ := by
      rw [mul_inv_rev]
      simp only [mul_assoc]
    rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hιx, e, htc, mul_inv_cancel_right,
      hconj, tupAct_tupAct, tupAct_zpow, hz]
    exact congrArg _ (zpow_tuple_eq_of_three hω3 hv)
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  ·
    exfalso
    rw [pow_zero, mul_one] at hιx
    have ht3 : t ^ 3 = 1 := by rw [← hιx, ← map_pow, hx'3, map_one]
    have hb3 : b ^ 3 = 1 := by
      apply rootDiagUnit_injective_D4
      rw [rootDiagUnit_pow_D4, ← htb, ← Subgroup.coe_pow, ht3, Subgroup.coe_one, rootDiagUnit_one]
    have hbXZ := eq_tupXZ_of_tupAct_permM hfixb
    have hprim : IsPrimitiveRoot (ω : K₂) 3 := by
      rw [IsPrimitiveRoot.coe_units_iff, ← hω]
      exact IsPrimitiveRoot.orderOf ω
    have hroot : ∀ u : K₂ˣ, u ^ 3 = 1 → ∃ i < 3, ω ^ i = u := by
      intro u hu
      obtain ⟨i, hi, hiu⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (u : K₂))
        (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one])
      exact ⟨i, hi, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hiu)⟩
    obtain ⟨i, hi3, hi⟩ := hroot (b ⟨0, by decide⟩) (by
      have := congrFun hb3 ⟨0, by decide⟩
      simpa using this)
    obtain ⟨l, hl3, hl⟩ := hroot (b ⟨2, by decide⟩) (by
      have := congrFun hb3 ⟨2, by decide⟩
      simpa using this)
    rw [← hi, ← hl] at hbXZ
    have hιΔ : ((ιTw K Q (frameDiag (orderThreeSL K)) : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 (fun j => ω ^ (permM.mulVec vD j - vD j)) := by
      have hΔ : frameDiag (orderThreeSL K) =
          gammaP K (orderThreeSL K) (frameD K (orderThreeSL K)) * (frameD K (orderThreeSL K))⁻¹ := by
        rw [Inputs2311r.gammaP_frameD_eq_inputs2311r hB3, mul_inv_cancel_right]
      rw [hΔ, map_mul, map_inv, ιTw_gammaP hQ, Subgroup.coe_mul, Subgroup.coe_inv, gammaP_HSL_diag ω hιd, hιd,
        rootDiagUnit_inv, ← rootDiagUnit_mul, tupAct_zpow]
      congr 1
      funext j
      rw [Pi.mul_apply, Pi.inv_apply, zpow_sub]
    have hιx' : ((ιTw K Q x' : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 (fun j => ω ^ ((i : ℤ) * vX j + (l : ℤ) * vZ j)) := by
      rw [hιx, htb, hbXZ, tupXZ_pow_inputs2311s]
    have hpow : ∀ n e m : ℕ, (∀ j, ((n : ℤ) * ((i : ℤ) * vX j + (l : ℤ) * vZ j) + (e : ℤ) * vH j) % 3 =
        ((m : ℤ) * (permM.mulVec vD j - vD j)) % 3) →
        x' ^ n * sl2At K ⟨2, by decide⟩ (orderThreeSL K) ^ e = frameDiag (orderThreeSL K) ^ m := by
      intro n e m hcong
      apply hιinj
      apply Subtype.ext
      rw [map_mul, map_pow, map_pow, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
        Subgroup.coe_pow, hιx', hιψ, hιΔ, ← rootDiagUnit_pow_D4, ← rootDiagUnit_pow_D4, ← rootDiagUnit_pow_D4,
        ← rootDiagUnit_mul, pow_tuple_inputs2311s, pow_tuple_inputs2311s, pow_tuple_inputs2311s,
        mul_tuple_inputs2311s]
      exact congrArg _ (zpow_tuple_eq_of_three hω3 hcong)
    have hdiv := exponent_facts_inputs2311s.2.2
    by_cases hl0 : l = 0
    ·
      subst hl0
      apply hnf'
      by_cases hi0 : i = 0
      · subst hi0
        exfalso
        apply hx'1
        have h1 := hpow 1 0 0 (fun j => by simp)
        rwa [pow_one, pow_zero, mul_one, pow_zero] at h1
      · have hi12 : 1 ≤ i := Nat.pos_of_ne_zero hi0
        have h1 := hpow i 0 1 (fun j => by
          obtain ⟨⟨p, hp⟩, -⟩ := hdiv j
          interval_cases i <;> push_cast <;> omega)
        rw [pow_zero, mul_one, pow_one] at h1
        rw [← h1, map_pow]
        exact E'.pow_mem hx'E' i
    ·
      have hl1 : 1 ≤ l := Nat.pos_of_ne_zero hl0
      have h1 := hpow l 1 (l * i + 2) (fun j => by
        obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hdiv j
        interval_cases i <;> interval_cases l <;> push_cast <;> omega)
      rw [pow_one] at h1
      set m := l * i + 2
      have hβE : MulAut.conj (x' ^ l) * gammaP K (orderThreeSL K) ∈ E' := by
        rw [map_pow]
        exact E'.mul_mem (E'.pow_mem hx'E' l) hαE'
      have hβA2 := hA2' _ hβE (hout (x' ^ l))
      have hβeq : MulAut.conj (x' ^ l) * gammaP K (orderThreeSL K) =
          MulAut.conj (frameDiag (orderThreeSL K) ^ m) * d4Graph K 1 := by
        rw [gammaP, ← mul_assoc, ← map_mul, h1]
      rw [hβeq] at hβA2
      have hγd : d4Graph K 1 (frameD K (orderThreeSL K)) =
          frameDiag (orderThreeSL K) * frameD K (orderThreeSL K) := by
        have h2 := Inputs2311r.gammaP_frameD_eq_inputs2311r (K := K) hB3
        rwa [gammaP_apply_of_commute (orderThreeSL K) (by
          rw [frameD, map_mul, map_inv, d4Graph_one_frameK₂, ← frameK₂_apply]
          exact (frameK_commute_sl2Two (orderThreeSL K) (orderThreeSL K)).1.mul_left
            (frameK_commute_sl2Two (orderThreeSL K) (orderThreeSL K)).2.2.inv_left)] at h2
      have hDF : Commute (frameDiag (orderThreeSL K) ^ m) (frameD K (orderThreeSL K) ^ m) :=
        ((Inputs2311m.commute_frameD_frameDiag (orderThreeSL K)).symm).pow_pow m m
      have hγF : d4Graph K 1 (frameD K (orderThreeSL K) ^ m) =
          frameDiag (orderThreeSL K) ^ m * frameD K (orderThreeSL K) ^ m := by
        rw [map_pow, hγd, ((Inputs2311m.commute_frameD_frameDiag (orderThreeSL K)).symm).mul_pow]
      have hγ2 : MulAut.conj (frameD K (orderThreeSL K) ^ m) *
          (MulAut.conj (frameDiag (orderThreeSL K) ^ m) * d4Graph K 1) *
          (MulAut.conj (frameD K (orderThreeSL K) ^ m))⁻¹ = d4Graph K 1 := by
        rw [Inputs2311m.conj_mul_conj_inv_eq_inputs2311m, MulAut.mul_apply, MulAut.conj_apply, hγF,
          ← mul_assoc, ← map_mul]
        have e : frameD K (orderThreeSL K) ^ m * (frameDiag (orderThreeSL K) ^ m *
            (frameDiag (orderThreeSL K) ^ m * frameD K (orderThreeSL K) ^ m) *
            (frameDiag (orderThreeSL K) ^ m)⁻¹)⁻¹ * frameDiag (orderThreeSL K) ^ m = 1 := by
          rw [hDF.eq]
          group
        rw [e, map_one, one_mul]
      have hγA2 := Inputs2311r.isA2Type_conj_inputs2311r (MulAut.conj (frameD K (orderThreeSL K) ^ m)) hβA2
      rw [hγ2] at hγA2
      exact not_isA2Type_d4Graph_one_inputs2311s hK2 hK3 hγA2
  ·
    have hz : ((ιTw K Q ((sl2At K ⟨2, by decide⟩ (orderThreeSL K))⁻¹ * frameD K (orderThreeSL K)) :
        ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 (fun j => ω ^ (vD j - vH j)) := by
      rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hιψ, hιd, rootDiagUnit_inv,
        ← rootDiagUnit_mul]
      congr 1
      funext j
      rw [Pi.mul_apply, Pi.inv_apply, zpow_sub, mul_comm]
    have hfixz := hkey _ _ hz exponent_facts_inputs2311s.1
    have hβE : MulAut.conj x' * gammaP K (orderThreeSL K) ∈ E' := E'.mul_mem hx'E' hαE'
    have hβN := fixedSubgroup_le_normalizer_of_isA2Type_inputs2311s hK2 hK3 hc' hβE (hout x')
      (hA2' _ hβE (hout x')) hx'1 hx'E'
    have hzN := hβN hfixz
    rw [← mul_inv_cancel_left (sl2At K ⟨2, by decide⟩ (orderThreeSL K)) (frameD K (orderThreeSL K))]
    exact Subgroup.mul_mem _ hψN hzN
  ·
    have hz : ((ιTw K Q (sl2At K ⟨2, by decide⟩ (orderThreeSL K) * frameD K (orderThreeSL K)) :
        ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 (fun j => ω ^ (vH j + vD j)) := by
      rw [map_mul, Subgroup.coe_mul, hιψ, hιd, ← rootDiagUnit_mul, mul_tuple_inputs2311s]
    have hfixz := hkey _ _ hz exponent_facts_inputs2311s.2.1
    have hβE : MulAut.conj x' * gammaP K (orderThreeSL K) ∈ E' := E'.mul_mem hx'E' hαE'
    have hβN := fixedSubgroup_le_normalizer_of_isA2Type_inputs2311s hK2 hK3 hc' hβE (hout x')
      (hA2' _ hβE (hout x')) hx'1 hx'E'
    have hzN := hβN hfixz
    rw [← inv_mul_cancel_left (sl2At K ⟨2, by decide⟩ (orderThreeSL K)) (frameD K (orderThreeSL K))]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hψN) hzN

theorem d4NonsplitGraphPlanes_holds : Inputs2311r.D4NonsplitGraphPlanes := by
  intro K _ _ hK2 hK3 hq E hEa hc hαE hA2 hnf x hx1 hxE _
  have := Fintype.ofFinite K
  obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  haveI := hEa
  exact uniPlaneClosure_eq_top_nonsplit_of_ext_inputs2311s hK2 hK3 hq
    (FiniteField.natCard_extension K (ringChar K) 2)
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv.toRingHom
    (fun y => FiniteField.Extension.frob_apply K (ringChar K) 2) hc hαE hA2 hnf hx1 hxE

end Planes

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311s
