module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterD4Three
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneUntw
public import CFSG.Adapters.CatalogueFieldBridges.Exceptional
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YHCat
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Adapters.CatalogueFieldBridges
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.RankThree.Chevalley


theorem idxCoreAt_entrywiseAdjointAut_D4 {K : Type} [Field K] [Finite K]
    {q : TauCeti.PrimePower} (hKq : Nat.card K = q.card) (σ : K ≃+* K)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    IdxCoreAt 3 (.D 4 q) (entrywiseAdjointAut Tag.D4 σ) := by
  classical
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  let k := fixSubfield σ
  haveI : Finite k := Subtype.finite
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨q₀, -, hq₀card, hqcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.exists_primePower_fixSubfield
      hKq σ Nat.prime_three hord
  have hv : (TauCeti.LieTypeIndex.D 4 q₀).Valid := CFSG.LocalAnalysis.GLTheoremA.D4Y.valid_D4 q₀
  obtain ⟨ι, hι, hJC, hnorm, -⟩ := ExcCopy.exists_fixed_structure (K := K) Tag.D4 σ
  have hperf : Group.IsPerfect (adjointGroup Tag.D4 k) :=
    ExcCopy.isPerfect_adjointGroup .D4 k (fun h => absurd h (by decide))
  obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect .D4 k hperf
  haveI : IsSimpleGroup ↥(adjointGroup Tag.D4 k) := hs
  have hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.D4 k) :=
    LieSemisimple.isQuasisimple_of_isSimpleGroup hs hnc
  let e : ↥(adjointGroup Tag.D4 k) ≃* ι.range := MonoidHom.ofInjective hι
  have hTq : CFSG.IsQuasisimple ι.range := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
  haveI : IsSimpleGroup ι.range := e.symm.isSimpleGroup
  have hncT : ∃ a b : ι.range, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa using h))⟩
  have hZT : Subgroup.center ι.range = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncT).2
  have hTp : 3 ∣ Nat.card ι.range := by
    rw [← Nat.card_congr e.toEquiv]
    exact (by norm_num : (3 : ℕ) ∣ 27).trans (twentySeven_dvd_card_adjointGroup_D4 k)
  have hZk : Subgroup.center ↥(adjointGroup Tag.D4 k) = ⊥ := center_adjointGroup_eq_bot
  let eA : AdjointQuotient Tag.D4 k ≃* ↥(adjointGroup Tag.D4 k) :=
    (QuotientGroup.quotientMulEquivOfEq hZk).trans QuotientGroup.quotientBot
  obtain ⟨eB⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_adjointQuotient_D4_equiv
      (F := k) q₀ hv hq₀card.symm
  let eM : ↥(adjointGroup Tag.D4 k) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.D 4 q₀, hv⟩).Group :=
    eA.symm.trans eB
  refine ⟨ι.range, hJC, ?_, hTq, hTp, ⟨.lie ⟨.D 4 q₀, hv⟩, ?_, ?_⟩⟩
  · intro f hf t ht
    have h := hnorm.conj_mem (⟨t, hJC ht⟩ : ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)))
      (Subgroup.mem_subgroupOf.2 ht) (⟨f, hf⟩ : ↥(fixSubgroup (entrywiseAdjointAut Tag.D4 σ)))
    simpa [Subgroup.mem_subgroupOf] using h
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hZT).trans
      (QuotientGroup.quotientBot.trans (e.symm.trans eM))⟩
  · exact Or.inl ⟨rfl, by rw [fieldSize, fieldSize]; exact hqcard.symm⟩


theorem twistedFixedGroup_eq_graphFixedRootGroup_of_frobenius {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ e) ^ 3) :
    ∀ (σ : K ≃+* K) (r : ℕ), r = 1 ∨ r = 2 → (∀ c, σ c = c ^ ((ℓ ^ e) ^ r)) →
      twistedFixedGroup TwistTag.D4 K σ.toRingHom = graphFixedRootGroup TwistTag.D4 K σ.toRingHom ∧
      IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      ∃ x y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), x * y ≠ y * x := by
  intro σ r hr hσ
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (k := e * 3)
      (by omega) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨-, -, hfixeq, hs, hnc⟩ :=
    triality_both_field_orientations_simple_full_ambient_fixed_group ℓ e hℓ he K hK
      (AlgebraicClosure K) r hr σ.toRingHom hσ
      (iterateFrobenius (AlgebraicClosure K) ℓ e) (fun c => by simp [iterateFrobenius_def])
  exact ⟨hfixeq, hs, hnc⟩


theorem fixedSubgroup_twistedEntrywiseAut_D4_eq_mod {K : Type} [Field K] (T : K ≃+* K) (j : ℤ) :
    fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T) =
      fixedSubgroup (twistedEntrywiseAut TwistTag.D4 (j % 3) T) := by
  have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (j % 3) (j / 3) T
  rw [show j % 3 + j / 3 * ((TwistTag.D4.order : ℕ) : ℤ) = j by
    change j % 3 + j / 3 * 3 = j
    omega] at h
  rw [h]

theorem exists_fixedSubgroup_twistedEntrywiseAut_D4_equiv_graphFixed {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (he : 1 ≤ e) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ e) ^ 3)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2) :
    Nonempty (↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hT3 : T ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    change T (T (T c)) = c
    rw [hT, hT, hT, ← pow_mul, ← pow_mul,
      show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
  have hfixper := fixedSubgroup_twistedEntrywiseAut_D4_eq_mod T j
  rw [hfixper]
  rcases hj with hj | hj
  · rw [hj]
    obtain ⟨hfixeq, -, -⟩ := twistedFixedGroup_eq_graphFixedRootGroup_of_frobenius hℓ he hK T 1
      (Or.inl rfl) (fun c => by rw [hT, pow_one])
    exact ⟨(fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4 T).trans
      (MulEquiv.subgroupCongr hfixeq)⟩
  · rw [hj, fixedSubgroup_twistedEntrywiseAut_D4_two]
    have hinv : ∀ c, T⁻¹ c = c ^ ((ℓ ^ e) ^ 2) := by
      have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
      intro c
      rw [h1, pow_two]
      change T (T c) = _
      rw [hT, hT, ← pow_mul, sq]
    obtain ⟨hfixeq, -, -⟩ := twistedFixedGroup_eq_graphFixedRootGroup_of_frobenius hℓ he hK T⁻¹ 2
      (Or.inr rfl) hinv
    have hswap : Nonempty (↥(graphFixedRootGroup TwistTag.D4 K T.symm.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom)) := by
      have hmap := map_trialityTranspositionAut_graphFixedRootGroup (K := K) T
      exact ⟨((Subgroup.equivMapOfInjective _ _ (trialityTranspositionAut K).injective).trans
        (MulEquiv.subgroupCongr hmap)).symm⟩
    obtain ⟨eswap⟩ := hswap
    exact ⟨((fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4 T⁻¹).trans
      (MulEquiv.subgroupCongr hfixeq)).trans eswap⟩

theorem idxCoreAt_twistedEntrywiseAut_D4 {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (h3 : ¬ 3 ∣ ℓ ^ e) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ e) ^ 3) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e))
    (j : ℤ) (hj : j % 3 = 1 ∨ j % 3 = 2)
    {q : TauCeti.PrimePower} (hKq : Nat.card K = q.card) :
    IdxCoreAt 3 (.D 4 q) (twistedEntrywiseAut TwistTag.D4 j T) := by
  classical
  let q₀ : TauCeti.PrimePower := ⟨ℓ, e, hℓ, he⟩
  have hq₀card : q₀.card = ℓ ^ e := TauCeti.PrimePower.card_def q₀
  have hKq₀ : Nat.card K = q₀.card ^ 3 := by rw [hq₀card]; exact hK
  have hTq₀ : ∀ c, T c = c ^ q₀.card := fun c => by rw [hq₀card]; exact hT c
  have hv : (TauCeti.LieTypeIndex.trialityD4 q₀).Valid :=
    TauCeti.LieTypeIndex.valid_trialityD4 q₀
  obtain ⟨eT⟩ := exists_fixedSubgroup_twistedEntrywiseAut_D4_equiv_graphFixed hℓ he hK T hT j hj
  obtain ⟨eC⟩ := nonempty_catEquiv_graphFixedRootGroup_trialityD4 hv hKq₀ T hTq₀
  have hGsimple : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom) := by
    obtain ⟨-, hs, -⟩ := twistedFixedGroup_eq_graphFixedRootGroup_of_frobenius hℓ he hK T 1
      (Or.inl rfl) (fun c => by rw [hT, pow_one])
    exact hs
  have hGnc : ∃ x y : ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom), x * y ≠ y * x := by
    obtain ⟨-, -, hnc⟩ := twistedFixedGroup_eq_graphFixedRootGroup_of_frobenius hℓ he hK T 1
      (Or.inl rfl) (fun c => by rw [hT, pow_one])
    exact hnc
  haveI : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.D4 K T.toRingHom) := hGsimple
  haveI : IsSimpleGroup ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) :=
    eT.isSimpleGroup
  have hTnc : ∃ a b : ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hGnc
    refine ⟨eT.symm x, eT.symm y, fun h => hxy ?_⟩
    have h' := congrArg eT h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    exact h'
  have hTq : CFSG.IsQuasisimple ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hTnc).1
  have hZT : Subgroup.center ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hTnc).2
  have h27 : 27 ∣ Nat.card ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) := by
    rw [fixedSubgroup_twistedEntrywiseAut_D4_eq_mod T j]
    exact twentySeven_dvd_card_fixedSubgroup_twistedEntrywiseAut_D4 hℓ he h3 K hK T hT
      (j % 3) hj
  have hTp : 3 ∣ Nat.card ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) :=
    (by norm_num : (3 : ℕ) ∣ 27).trans h27
  let eCat : ↥(fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T)) ≃*
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.trialityD4 q₀, hv⟩).Group :=
    eT.trans eC.symm
  refine ⟨fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T), le_rfl, ?_, hTq, hTp,
    ⟨.lie ⟨.trialityD4 q₀, hv⟩, ?_, ?_⟩⟩
  · intro f hf t ht
    change twistedEntrywiseAut TwistTag.D4 j T (f * t * f⁻¹) = f * t * f⁻¹
    have hf' : twistedEntrywiseAut TwistTag.D4 j T f = f := hf
    have ht' : twistedEntrywiseAut TwistTag.D4 j T t = t := ht
    rw [map_mul, map_mul, map_inv, hf', ht']
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hZT).trans
      (QuotientGroup.quotientBot.trans eCat)⟩
  · refine Or.inr (Or.inl ⟨⟨q, rfl⟩, ⟨q₀, rfl⟩, ?_⟩)
    show q₀.card ^ 3 = q.card
    rw [hq₀card, ← hKq, hK]


theorem idxCoreAt_graphField_D4 {K : Type} [Field K] [Finite K] {q : TauCeti.PrimePower}
    (hKq : Nat.card K = q.card) (h3K : ringChar K ≠ 3) {α : MulAut (adjointGroup Tag.D4 K)}
    (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (σ : K ≃+* K) (hσ1 : σ ≠ 1) (hσ3 : σ ^ 3 = 1) {ε : ℕ} (hε : ε = 1 ∨ ε = 2)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    IdxCoreAt 3 (.D 4 q) α := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓp, hKf⟩ := FiniteField.card K (ringChar K)
  have hKf' : Nat.card K = ringChar K ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hKf
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three hℓp f.pos K hKf' σ hord
  have hK' : Nat.card K = (ringChar K ^ e) ^ 3 := by rw [hKf', ← hef, pow_mul]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK', ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ringChar K ^ 2 := Nat.pow_le_pow_left hℓp.two_le 2
      _ ≤ ringChar K ^ (e * 3) := Nat.pow_le_pow_right hℓp.pos (by omega)
  have h3e : ¬ 3 ∣ ringChar K ^ e := by
    intro h
    have h37 : 3 ∣ ringChar K := Nat.prime_three.dvd_of_dvd_pow h
    have h3r : ringChar K = 3 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓp).1 h37).symm
    exact h3K h3r
  haveI : Fact (ringChar K).Prime := ⟨hℓp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  rcases hσT with hσT | hσT
  · have hαT : α = MulAut.conj g * (exactNormalAut Tag.D4 K a T 0 * d4Graph K ε) := by
      rw [hαeq, hσT]
    obtain ⟨ψ, hψ⟩ :=
      exists_conj_eq_twistedEntrywiseAut_of_normalForm K hKf' hK4 he hef T hT α hα3 g a ε hαT
    refine idxCoreAt_of_conj (idxCoreAt_twistedEntrywiseAut_D4 hℓp he h3e hK' T hT (ε : ℤ)
      (by rcases hε with rfl | rfl <;> norm_num) hKq) ψ hψ
  · have hαT : α = MulAut.conj g * (exactNormalAut Tag.D4 K a T⁻¹ 0 * d4Graph K ε) := by
      rw [hαeq, hσT]
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hKf' hK4 he hef
      T T⁻¹ hT (mul_inv_cancel T) α hα3 g a ε hαT
    have hcore : IdxCoreAt 3 (.D 4 q) α⁻¹ :=
      idxCoreAt_of_conj (idxCoreAt_twistedEntrywiseAut_D4 hℓp he h3e hK' T hT (-(ε : ℤ))
        (by rcases hε with rfl | rfl <;> norm_num) hKq) ψ hψ
    exact idxCoreAt_of_fixSubgroup_eq (by rw [fixSubgroup_inv_eq]) hcore

theorem outerIdxAt_pomegaPlus_four_three {ℓ f : ℕ} (h3ℓ : 3 ≠ ℓ) {q : TauCeti.PrimePower}
    (hq : q.card = ℓ ^ f) {G : Type} [Group G] [Finite G]
    (h : CFSG.Open.StatedClassicalModel G .POmegaPlus 4 ℓ f) (h3 : 3 ∣ Nat.card G) :
    OuterIdxAt 3 (.D 4 q) G := by
  obtain ⟨⟨hℓ, hf, -⟩, K, hfield, hfinite, hK, ⟨eG⟩⟩ := h
  letI := hfield
  letI := hfinite
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have hKq : Nat.card K = q.card := hK.trans hq.symm
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K ℓ]
    exact fun h' => h3ℓ h'.symm
  obtain ⟨eC⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  have hcore : ∀ x : MulAut (adjointGroup Tag.D4 K), x ^ 3 = 1 →
      x ∉ innAutDerived (adjointGroup Tag.D4 K) → IdxCoreAt 3 (.D 4 q) x := by
    intro α hα3 hαout
    obtain ⟨g, a, σ, ε, hε3, hσ3, hαeq⟩ := exists_cube_normal_form_sigma α hα3
    interval_cases ε
    · have hα0 : α = MulAut.conj g * exactNormalAut Tag.D4 K a σ 0 := by
        rw [hαeq, d4Graph_zero, mul_one]
      by_cases hσ1 : σ = 1
      · subst hσ1
        rw [hα0] at hα3 hαout
        obtain ⟨h, hh⟩ := d4_inner_of_diag hK3 g a hα3
        exact absurd (hh ▸ (inner_le_innAutDerived _ ⟨h, rfl⟩)) hαout
      · rw [hα0] at hα3
        obtain ⟨ψ, hψ⟩ :=
          ExcCopy.exists_conj_eq_entrywiseAdjointAut .D4 Nat.prime_three g a σ hσ1 hσ3 hα3
        exact idxCoreAt_of_conj (idxCoreAt_entrywiseAdjointAut_D4 hKq σ hσ3 hσ1) ψ (hα0.symm ▸ hψ)
    · by_cases hσ1 : σ = 1
      · subst hσ1
        rw [hαeq] at hα3 hαout
        exact absurd (mem_innAutDerived_of_graphType g a (Or.inl rfl) hα3) hαout
      · exact idxCoreAt_graphField_D4 hKq hK3 hα3 g a σ hσ1 hσ3 (Or.inl rfl) hαeq
    · by_cases hσ1 : σ = 1
      · subst hσ1
        rw [hαeq] at hα3 hαout
        exact absurd (mem_innAutDerived_of_graphType g a (Or.inr rfl) hα3) hαout
      · exact idxCoreAt_graphField_D4 hKq hK3 hα3 g a σ hσ1 hσ3 (Or.inr rfl) hαeq
  exact outerIdxAt_of_mulEquiv Nat.prime_three (eG.trans eC).symm
    (outerIdxAt_of_idxCoreAt Nat.prime_three hcore)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
