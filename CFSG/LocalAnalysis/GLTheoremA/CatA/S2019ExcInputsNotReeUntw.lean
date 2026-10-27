module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsNotReeComp
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldCopy
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

set_option linter.unusedSectionVars false


theorem fixCompsEquiv_entrywiseAdjointAut_untw {τ : Tag}
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hk3 : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ)) (q' : TauCeti.PrimePower)
    (hv' : (c q').Valid) (hq' : Nat.card (fixSubfield σ) = q'.card) :
    FixCompsEquiv (entrywiseAdjointAut τ σ) (TauCeti.CFSGIndex.lie ⟨c q', hv'⟩).Group ∧
      Subgroup.center (TauCeti.CFSGIndex.lie ⟨c q', hv'⟩).Group = ⊥ := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨ι, hι, hJC, hJn, hsol⟩ := ExcCopy.exists_fixed_structure τ σ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL τ (fixSubfield σ)) := finite_modGL
  have hperf := ExcCopy.isPerfect_adjointGroup τ (fixSubfield σ) hk3
  obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect τ (fixSubfield σ) hperf
  let e : adjointGroup τ (fixSubfield σ) ≃* ι.range := MonoidHom.ofInjective hι
  haveI := hs
  have hJs : IsSimpleGroup ι.range := e.symm.isSimpleGroup
  have hJnc : ∃ x y : ι.range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa using h))⟩
  obtain ⟨eq⟩ := hB q' hv' (fixSubfield σ) hq'
  have hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  let eX : ↥(adjointGroup τ (fixSubfield σ)) ≃* (TauCeti.CFSGIndex.lie ⟨c q', hv'⟩).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eq
  haveI := hJn
  refine ⟨fixCompsEquiv_of_normal_simple hJC hJs hJnc hsol (e.symm.trans eX), ?_⟩
  rw [← Subgroup.map_center_eq eX, hZ, Subgroup.map_bot]

theorem s2019OuterComp_untw_of_descent {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    {p : ℕ} (hp : p.Prime) (q : TauCeti.PrimePower) (hq2 : q.p ≠ 2) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card) {S : Type} [Group S] (e : S ≃* ↥(adjointGroup τ K))
    (β : MulAut S) (σ : K ≃+* K) (hσ : orderOf σ = p) (r j : ℕ) (ψ : MulAut ↥(adjointGroup τ K))
    (hrj : (MulAut.congr e β ^ r) ^ j = MulAut.congr e β)
    (hψ : ψ * MulAut.congr e β ^ r * ψ⁻¹ = entrywiseAdjointAut τ σ)
    (J : Subgroup S) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (c q').Valid), q'.card ^ p = q.card ∧
        Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨c q', hv'⟩).Group) := by
  classical
  have hKq : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield q.prime_p q.exponent_pos hKq σ
  rw [hσ] at hdvd hcard
  obtain ⟨d, hd⟩ := hdvd
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · have := q.exponent_pos
      rw [h, mul_zero] at hd
      omega
    · exact h
  let q' : TauCeti.PrimePower := ⟨q.p, d, q.prime_p, hd1⟩
  have hq'card : q'.card = q.p ^ d := TauCeti.PrimePower.card_def q'
  have hk : Nat.card (fixSubfield σ) = q'.card := by
    rw [hcard, hq'card, hd, Nat.mul_div_cancel_left d hp.pos]
  have h3 : 3 ≤ q'.card := by
    rw [hq'card]
    have hp3 : 3 ≤ q.p := by have := q.prime_p.two_le; omega
    calc 3 ≤ q.p := hp3
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ d := Nat.pow_le_pow_right q.prime_p.pos hd1
  have hv' : (c q').Valid := hvalid q' fun _ => h3
  obtain ⟨hF, hT⟩ :=
    fixCompsEquiv_entrywiseAdjointAut_untw hB σ (fun _ => hk ▸ h3) q' hv' hk
  have hFβ : FixCompsEquiv β (TauCeti.CFSGIndex.lie ⟨c q', hv'⟩).Group := by
    refine FixCompsEquiv.of_congr e (FixCompsEquiv.of_pow_pow hrj (FixCompsEquiv.of_conj ψ ?_))
    rw [hψ]
    exact hF
  refine ⟨hFβ.center_eq_bot hT hJ, q', hv', ?_, hFβ J hJ⟩
  rw [hq'card, ← pow_mul, mul_comm d p, ← hd, TauCeti.PrimePower.card_def]

private theorem congr_not_mem_inner {S G : Type} [Group S] [Group G] (e : S ≃* G)
    {β : MulAut S} (hout : ∀ a : S, MulAut.conj a ≠ β) : MulAut.congr e β ∉ inner G := by
  rintro ⟨g, hg⟩
  refine hout (e.symm g) ?_
  apply (MulAut.congr e).injective
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply]
  exact hg

private theorem orderOf_congr_eq {S G : Type} [Group S] [Group G] (e : S ≃* G) {p : ℕ}
    (hp : p.Prime) {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    orderOf (MulAut.congr e β) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hβ1 : β ≠ 1 := fun h => hout 1 (by rw [map_one, h])
  refine orderOf_eq_prime (by rw [← map_pow, hβ, map_one]) fun h => hβ1 ?_
  exact (MulAut.congr e).injective (h.trans (map_one _).symm)

private theorem s2019OuterComp_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (hvalid : ∀ q, (c q).Valid)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : TauCeti.PrimePower) (hv : (c q).Valid)
    (hq2 : q.p ≠ 2) {S : Type} [Group S] [Finite S]
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) (β : MulAut S) (hβ : β ^ p = 1)
    (hout : ∀ a : S, MulAut.conj a ≠ β) (J : Subgroup S) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (c q').Valid), q'.card ^ p = q.card ∧
        Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨c q', hv'⟩).Group) := by
  classical
  obtain ⟨K, _, hKfin, hK, -, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e : S ≃* ↥(adjointGroup τ K) := eS.trans eK
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hKq : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
  have hφp : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hdet : ¬ p ∣ τ.cartan.det.natAbs := by
    intro h
    have h3 : 0 < τ.cartan.det.natAbs ∧ τ.cartan.det.natAbs ≤ 3 := by
      rcases hτ with rfl | rfl | rfl
      · rw [det_cartan_E6]; norm_num
      · rw [det_cartan_E7]; norm_num
      · rw [det_cartan_E8]; norm_num
    have := Nat.le_of_dvd h3.1 h
    omega
  obtain ⟨-, T, r, j, ψ, -, hTo, -, hrj, hψ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_outer_E τ hτ q.exponent_pos K hKq
      hp (by omega) hdet _ hφp (congr_not_mem_inner e hout)
  exact s2019OuterComp_untw_of_descent hB (fun q _ => hvalid q) hp q hq2 hK e β T hTo r j ψ hrj
    hψ J hJ

theorem s2019OuterComp_G2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hq2 : q.p ≠ 2) {K : Type} [Group K] [Finite K]
    (eK : K ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) (β : MulAut K) (hβ : β ^ p = 1)
    (hout : ∀ a : K, MulAut.conj a ≠ β) (J : Subgroup K) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (TauCeti.LieTypeIndex.G2 q').Valid),
        q'.card ^ p = q.card ∧
          Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q', hv'⟩).Group) := by
  classical
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
  obtain ⟨F, _, hFfin, hF, hFchar, ⟨eF⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e : K ≃* ↥(adjointGroup .G2 F) := eK.trans eF
  have hFq : Nat.card F = q.p ^ q.exponent := by rw [hF, TauCeti.PrimePower.card_def]
  have hφo : orderOf (MulAut.congr e β) = p := orderOf_congr_eq e hp hβ hout
  have hφinn : MulAut.congr e β ∉ inner ↥(adjointGroup .G2 F) := congr_not_mem_inner e hout
  have hform : ∃ (x : ↥(adjointGroup .G2 F)) (σ : F ≃+* F),
      orderOf σ = p ∧ MulAut.congr e β = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
    by_cases hℓ3 : q.p = 3
    · have hF3 : Nat.card F = 3 ^ q.exponent := by rw [hFq, hℓ3]
      haveI : CharP F 3 := hℓ3 ▸ hFchar
      exact CFSG.HardMathSupport.Lang.E6Descent.G2_form_three q.exponent_pos F hF3 hp (by omega) _
        hφo hφinn
    · exact CFSG.HardMathSupport.Lang.E6Descent.G2_form_odd q.prime_p hq2 hℓ3 q.exponent_pos F hFq
        hp _ hφo hφinn
  obtain ⟨x, σ, hσp, hφσ⟩ := hform
  obtain ⟨δ, hδ⟩ := CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_entrywiseAdjointAut_of_form
    .G2 q.prime_p q.exponent_pos F hFq hp _ hφo x σ hσp hφσ
  have hvalid : ∀ q : TauCeti.PrimePower, (Tag.G2 = .G2 → 3 ≤ q.card) →
      (TauCeti.LieTypeIndex.G2 q).Valid := fun q hq => by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hq rfl, by simp⟩
  exact s2019OuterComp_untw_of_descent hB hvalid hp q hq2 hF e β σ hσp 1 1 δ
    (by rw [pow_one, pow_one]) (by rw [pow_one]; exact hδ) J hJ

theorem s2019OuterComp_F4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hq2 : q.p ≠ 2) {K : Type} [Group K] [Finite K]
    (eK : K ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) (β : MulAut K) (hβ : β ^ p = 1)
    (hout : ∀ a : K, MulAut.conj a ≠ β) (J : Subgroup K) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (TauCeti.LieTypeIndex.F4 q').Valid),
        q'.card ^ p = q.card ∧
          Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q', hv'⟩).Group) := by
  classical
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
  obtain ⟨F, _, hFfin, hF, -, ⟨eF⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e : K ≃* ↥(adjointGroup .F4 F) := eK.trans eF
  have hFq : Nat.card F = q.p ^ q.exponent := by rw [hF, TauCeti.PrimePower.card_def]
  have hφo : orderOf (MulAut.congr e β) = p := orderOf_congr_eq e hp hβ hout
  obtain ⟨-, σ, δ, hσp, -, hδ, -, -⟩ :=
    odd_F4_prime_field_coset_descent q.prime_p hq2 q.exponent_pos F hFq hp _ hφo
      (congr_not_mem_inner e hout)
  exact s2019OuterComp_untw_of_descent hB (fun q _ => by simp) hp q hq2 hF e β σ hσp 1 1 δ
    (by rw [pow_one, pow_one]) (by rw [pow_one]; exact hδ) J hJ

theorem s2019OuterComp_E6 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hq2 : q.p ≠ 2) {K : Type} [Group K] [Finite K]
    (eK : K ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) (β : MulAut K) (hβ : β ^ p = 1)
    (hout : ∀ a : K, MulAut.conj a ≠ β) (J : Subgroup K) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (TauCeti.LieTypeIndex.E6 q').Valid),
        q'.card ^ p = q.card ∧
          Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q', hv'⟩).Group) :=
  s2019OuterComp_E (Or.inl rfl) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
    (fun q => by simp) hp hp5 q hv hq2 eK β hβ hout J hJ

theorem s2019OuterComp_E7 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E7 q).Valid) (hq2 : q.p ≠ 2) {K : Type} [Group K] [Finite K]
    (eK : K ≃* (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group) (β : MulAut K) (hβ : β ^ p = 1)
    (hout : ∀ a : K, MulAut.conj a ≠ β) (J : Subgroup K) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (TauCeti.LieTypeIndex.E7 q').Valid),
        q'.card ^ p = q.card ∧
          Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨.E7 q', hv'⟩).Group) :=
  s2019OuterComp_E (Or.inr (Or.inl rfl)) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
    (fun q => by simp) hp hp5 q hv hq2 eK β hβ hout J hJ

theorem s2019OuterComp_E8 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E8 q).Valid) (hq2 : q.p ≠ 2) {K : Type} [Group K] [Finite K]
    (eK : K ≃* (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) (β : MulAut K) (hβ : β ^ p = 1)
    (hout : ∀ a : K, MulAut.conj a ≠ β) (J : Subgroup K) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (TauCeti.LieTypeIndex.E8 q').Valid),
        q'.card ^ p = q.card ∧
          Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨.E8 q', hv'⟩).Group) :=
  s2019OuterComp_E (Or.inr (Or.inr rfl)) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
    (fun q => by simp) hp hp5 q hv hq2 eK β hβ hout J hJ

end CFSG.LocalAnalysis.GLTheoremA.S2019
