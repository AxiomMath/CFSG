module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldCopy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FormCopy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.G2TwoChev
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyE

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang

set_option linter.unusedSectionVars false


theorem lieCompExport_entrywiseAdjointAut_of_simple {q : ℕ} (τ : Tag) {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) (hs : IsSimpleGroup (adjointGroup τ (fixSubfield σ)))
    (hnc : ∃ x y : adjointGroup τ (fixSubfield σ), x * y ≠ y * x)
    (hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q ↥(adjointGroup τ (fixSubfield σ)))
    (hA6 : IsEmpty (↥(adjointGroup τ (fixSubfield σ)) ≃* alternatingGroup (Fin 6))) :
    LieCompExport q (entrywiseAdjointAut τ σ) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨ι, hι, hJC, hJn, hsol⟩ := ExcCopy.exists_fixed_structure τ σ
  let e : adjointGroup τ (fixSubfield σ) ≃* ι.range := MonoidHom.ofInjective hι
  have hJs : IsSimpleGroup ι.range := e.symm.isSimpleGroup
  have hJnc : ∃ x y : ι.range, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa using h))⟩
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL τ (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(adjointGroup τ (fixSubfield σ)) := Subtype.finite
  haveI := hs
  haveI := hJn
  refine lieCompExport_of_normal_quasisimple hJC (isQuasisimple_of_isSimpleGroup hJs hJnc) hsol
    ⟨↥(adjointGroup τ (fixSubfield σ)), inferInstance, inferInstance,
      lieFactorData_of_simple hnc hchev, ι.rangeRestrict, ι.rangeRestrict_surjective, ?_⟩ ?_
  · intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, ← map_one ι] at hx
    rw [hι hx]
    exact one_mem _
  · exact isEmpty_quotient_center_alt6 (b3Lie_center_eq_bot hJnc) ⟨fun f => hA6.false (e.trans f)⟩

theorem lieCompExport_entrywiseAdjointAut_G2_two {q : ℕ} {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2)
    (hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q
      ↥(commutator ↥(adjointGroup .G2 (fixSubfield σ)))) :
    LieCompExport q (entrywiseAdjointAut .G2 σ) := by
  classical
  have : Finite (ModGL .G2 K) := finite_modGL
  obtain ⟨ι, hι, hJC, hJn, hsol⟩ := ExcCopy.exists_fixed_structure .G2 σ
  obtain ⟨hDs, hDcard⟩ := ExcCopy.g2Two_derived_exc hk
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL .G2 (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(adjointGroup .G2 (fixSubfield σ)) := Subtype.finite
  haveI : Finite ↥(commutator ↥(adjointGroup .G2 (fixSubfield σ))) := Subtype.finite
  haveI := hDs
  have hDnc : ∃ a b : ↥(commutator ↥(adjointGroup .G2 (fixSubfield σ))), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup ↥(commutator ↥(adjointGroup .G2 (fixSubfield σ))) :=
      { (inferInstance : Group ↥(commutator ↥(adjointGroup .G2 (fixSubfield σ)))) with
        mul_comm := hcon }
    have hp := IsSimpleGroup.prime_card
      (α := ↥(commutator ↥(adjointGroup .G2 (fixSubfield σ))))
    rw [hDcard] at hp
    exact absurd hp (by norm_num)
  let e : ↥(commutator ↥(adjointGroup .G2 (fixSubfield σ))) ≃* ↥⁅ι.range, ι.range⁆ :=
    ((commutator ↥(adjointGroup .G2 (fixSubfield σ))).equivMapOfInjective ι hι).trans
      (MulEquiv.subgroupCongr (map_commutator_eq _ ι))
  have hDs' : IsSimpleGroup ↥⁅ι.range, ι.range⁆ := e.symm.isSimpleGroup
  have hDnc' : ∃ x y : ↥⁅ι.range, ι.range⁆, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hDnc
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa using h))⟩
  have hDq : CFSG.IsQuasisimple ↥⁅ι.range, ι.range⁆ := isQuasisimple_of_isSimpleGroup hDs' hDnc'
  haveI := hJn
  have hDJ : ⁅ι.range, ι.range⁆ ≤ ι.range := Subgroup.commutator_le_self _
  haveI : (⁅ι.range, ι.range⁆.subgroupOf ι.range).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left _ _)
  have hcomp : IsComponentOf ⁅ι.range, ι.range⁆ (fixSubgroup (entrywiseAdjointAut .G2 σ)) :=
    isComponentOf_of_normal_normal hDJ hJC inferInstance inferInstance hDq
  have hperf : ∀ P : Subgroup ↥(adjointGroup .G2 K),
      P ≤ fixSubgroup (entrywiseAdjointAut .G2 σ) → ⁅P, P⁆ = P → P ≤ ⁅ι.range, ι.range⁆ := by
    intro P hPC hP
    have hPJ := perfect_le_of_solvable_quotient hJC hsol hPC hP
    calc P = ⁅P, P⁆ := hP.symm
      _ ≤ ⁅ι.range, ι.range⁆ := Subgroup.commutator_mono hPJ hPJ
  have hlayer : PerfectInLayer (entrywiseAdjointAut .G2 σ) := fun P hPC hP =>
    (hperf P hPC hP).trans (le_sSup hcomp)
  have hZ : Subgroup.center ↥⁅ι.range, ι.range⁆ = ⊥ := b3Lie_center_eq_bot hDnc'
  have hcardD : Nat.card ↥⁅ι.range, ι.range⁆ = 6048 := by
    rw [← Nat.card_congr e.toEquiv, hDcard]
  refine lieCompExport_of_unique_component hlayer hcomp hperf
    ⟨↥(commutator ↥(adjointGroup .G2 (fixSubfield σ))), inferInstance, inferInstance,
      lieFactorData_of_simple hDnc hchev, e.toMonoidHom, e.surjective, ?_⟩ ?_
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := e.injective (by simpa using hx)
    rw [this]
    exact one_mem _
  · exact isEmpty_quotient_center_alt6 hZ
      (isEmpty_mulEquiv_alt6_of_card_ne (by rw [hcardD]; norm_num))

theorem exists_primePower_card_subfield {K : Type} [Field K] [Finite K] {ℓ : ℕ} (hℓ : ringChar K = ℓ)
    (k : Subfield K) : ∃ q : TauCeti.PrimePower, q.p = ℓ ∧ Nat.card k = q.card := by
  classical
  haveI : Fintype k := Fintype.ofFinite _
  haveI : CharP K ℓ := hℓ ▸ ringChar.charP K
  haveI : CharP k ℓ := (k.subtype.charP_iff k.subtype_injective ℓ).2 inferInstance
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k ℓ
  exact ⟨⟨ℓ, n, hp, n.pos⟩, rfl, by
    rw [Nat.card_eq_fintype_card, hcard, TauCeti.PrimePower.card_def]⟩

theorem lieCompExport_entrywiseAdjointAut_untw {τ : Tag} {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c)
    (hchar : ∀ q : TauCeti.PrimePower, (c q).characteristic = q.p)
    (hvalid : ∀ q : TauCeti.PrimePower, (τ = .G2 → 3 ≤ q.card) → (c q).Valid)
    (hA6 : ∀ (q : TauCeti.PrimePower) (hv : (c q).Valid),
      IsEmpty ((TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group ≃* alternatingGroup (Fin 6)))
    {K : Type} [Field K] [Finite K] {ℓ : ℕ} (hℓ : ringChar K = ℓ) (σ : K ≃+* K) :
    LieCompExport ℓ (entrywiseAdjointAut τ σ) := by
  classical
  obtain ⟨q, hqp, hqcard⟩ := exists_primePower_card_subfield hℓ (fixSubfield σ)
  haveI : Finite (fixSubfield σ) := Subtype.finite
  by_cases hG2 : τ = .G2 ∧ Nat.card (fixSubfield σ) = 2
  · obtain ⟨rfl, hk⟩ := hG2
    have hℓ2 : ℓ = 2 := by
      have h1 : ℓ ^ q.exponent = 2 := by rw [← hqp, ← TauCeti.PrimePower.card_def, ← hqcard]; exact hk
      exact (Nat.prime_dvd_prime_iff_eq (hqp ▸ q.prime_p) Nat.prime_two).1
        (by rw [← h1]; exact dvd_pow_self _ q.exponent_pos.ne')
    subst hℓ2
    exact lieCompExport_entrywiseAdjointAut_G2_two σ hk (isChevSimple_two_derived_G2 hk)
  · have hk3 : τ = .G2 → 3 ≤ Nat.card (fixSubfield σ) := by
      intro h
      have h2 : 1 < Nat.card (fixSubfield σ) := Finite.one_lt_card
      have : Nat.card (fixSubfield σ) ≠ 2 := fun h' => hG2 ⟨h, h'⟩
      omega
    have hperf := ExcCopy.isPerfect_adjointGroup τ (fixSubfield σ) hk3
    obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect τ (fixSubfield σ) hperf
    have hv : (c q).Valid := hvalid q (fun h => by rw [← hqcard]; exact hk3 h)
    obtain ⟨eq⟩ := hB q hv (fixSubfield σ) hqcard
    have hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
    let eX : ↥(adjointGroup τ (fixSubfield σ)) ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eq
    have hchev := isChevSimple_of_lie ⟨c q, hv⟩ ((hchar q).trans hqp) eX
    exact lieCompExport_entrywiseAdjointAut_of_simple τ σ hs hnc hchev
      ⟨fun f => (hA6 q hv).false (eX.symm.trans f)⟩


theorem exists_field_or_inndiag_FG {τ : Tag} (hτ : τ = .F4 ∨ τ = .G2) {K : Type} [Field K]
    [Finite K] (hG2 : τ = .G2 → 3 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (β : MulAut ↥(adjointGroup τ K)) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1) := by
  classical
  obtain ⟨g, σ, hβe, hσp⟩ := ExcCopy.exists_form_FG hτ hG2 hp hp2 β hβ
  by_cases hσ : σ = 1
  · subst hσ
    right
    rw [exactNormalAut_one_one_zero, mul_one] at hβe
    subst hβe
    have hgp : g ^ p = 1 := by
      have : MulAut.conj (g ^ p) = MulAut.conj 1 := by rw [map_pow, hβ, map_one]
      exact mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot this
    have hg1 : (g : ModGL τ K) ≠ 1 := fun h1 => hβ1 (by
      have : g = 1 := Subtype.ext h1
      rw [this, map_one])
    refine ⟨(g : ModGL τ K), adjointGroup_le_inndiagGroup g.2, fun c => ?_, ?_, hg1⟩
    · simp [MulAut.conj_apply]
    · rw [← Subgroup.coe_pow, hgp]
      rfl
  · left
    have hα : (MulAut.conj g * exactNormalAut τ K 1 σ 0) ^ p = 1 := by rw [← hβe]; exact hβ
    obtain ⟨ψ, hψ⟩ := ExcCopy.exists_conj_eq_entrywiseAdjointAut τ hp g 1 σ hσ hσp hα
    exact ⟨σ, ψ, hσ, by rw [hβe]; exact hψ⟩

theorem exists_field_or_inndiag_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (β : MulAut ↥(adjointGroup τ K)) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧
      h ^ p = 1 ∧ h ≠ 1) := by
  classical
  obtain ⟨g, a, σ, hβe, hσp⟩ := ExcCopy.exists_form_E hτ hp hp2 β hβ
  by_cases hσ : σ = 1
  · subst hσ
    right
    have hβw : ∀ c : adjointGroup τ K, (β c : ModGL τ K) =
        ((g : ModGL τ K) * rootDiagUnit τ a) * c * ((g : ModGL τ K) * rootDiagUnit τ a)⁻¹ := by
      intro c
      have e : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (c : ModGL τ K) = c :=
        Units.ext (entrywise_id _)
      rw [hβe, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, inv_one, mul_inv_rev, e]
      simp only [mul_assoc, mul_one]
    have hw : (g : ModGL τ K) * rootDiagUnit τ a ∈ inndiagGroup τ K :=
      mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
    obtain ⟨h', hh', hβh', hh'p⟩ := exists_inndiag_pow_eq_one hτ hp β hβ hw hβw
    refine ⟨h', hh', hβh', hh'p, ?_⟩
    rintro rfl
    apply hβ1
    refine MulEquiv.ext fun c => Subtype.ext ?_
    rw [hβh' c]
    simp
  · left
    have hα : (MulAut.conj g * exactNormalAut τ K a σ 0) ^ p = 1 := by rw [← hβe]; exact hβ
    obtain ⟨ψ, hψ⟩ := ExcCopy.exists_conj_eq_entrywiseAdjointAut τ hp g a σ hσ hσp hα
    exact ⟨σ, ψ, hσ, by rw [hβe]; exact hψ⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
