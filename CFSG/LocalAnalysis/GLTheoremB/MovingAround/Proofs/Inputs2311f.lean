module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311d2
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFieldCube
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E78

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP

section Abstract

variable {P : Type*} [Group P]

theorem eq_top_of_overgroup_escape {N : Subgroup (MulAut P)} [N.Normal] {α ι ψa ψb : MulAut P}
    (hι1 : ι ≠ 1) (hιN : ι ∈ N) {Ja Jb : Subgroup P}
    (hmax : ∀ M : Subgroup P, Ja ≤ M → M ≤ fixedSubgroup (ψa * α * ψa⁻¹) ∨ M = ⊤)
    (hJb : Jb ≤ fixedSubgroup (ψb * (α * ι) * ψb⁻¹))
    (hker : ∀ ι' ∈ N, (∀ x ∈ Jb, ι' x = x) → ι' = 1)
    {X : Subgroup P} (hXa : Ja.comap ψa.toMonoidHom ≤ X) (hXb : Jb.comap ψb.toMonoidHom ≤ X) :
    X = ⊤ := by
  have hle : Ja ≤ X.map ψa.toMonoidHom := fun y hy =>
    ⟨ψa⁻¹ y, hXa (by simpa using hy), by simp⟩
  rcases hmax _ hle with h | h
  · exfalso
    have hXα : ∀ x ∈ X, α x = x := by
      intro x hx
      have h1 : (ψa * α * ψa⁻¹) (ψa x) = ψa x := mem_fixedSubgroup.1 (h ⟨x, hx, rfl⟩)
      simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h1
      exact ψa.injective h1
    have hfix : ∀ y ∈ Jb, (ψb * ι * ψb⁻¹) y = y := by
      intro y hy
      have hy' : ψb⁻¹ y ∈ X := hXb (by simpa using hy)
      have h1 : α (ψb⁻¹ y) = ψb⁻¹ y := hXα _ hy'
      have h2 : (ψb * (α * ι) * ψb⁻¹) y = y := mem_fixedSubgroup.1 (hJb hy)
      simp only [MulAut.mul_apply] at h2 ⊢
      have h3 : α (ι (ψb⁻¹ y)) = α (ψb⁻¹ y) := by
        rw [h1]
        have := congrArg (fun z => ψb⁻¹ z) h2
        simpa using this
      rw [α.injective h3, MulAut.apply_inv_self]
    have h1 := hker _ (‹N.Normal›.conj_mem ι hιN ψb) hfix
    apply hι1
    have h2 : ψb⁻¹ * (ψb * ι * ψb⁻¹) * ψb = ι := by group
    rw [← h2, h1]
    group
  · rw [eq_top_iff]
    intro x _
    have hx : ψa x ∈ X.map ψa.toMonoidHom := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [ψa.injective hyx] at hy

theorem comap_le_uniPlaneClosure {r : ℕ} {E : Subgroup (MulAut P)} {α ψ : MulAut P} (hαE : α ∈ E)
    (hα1 : α ≠ 1) {J : Subgroup P} (hJfix : J ≤ fixedSubgroup (ψ * α * ψ⁻¹))
    (hJgen : J ≤ Subgroup.closure {s | s ∈ J ∧ ∃ n : ℕ, s ^ (r ^ n) = 1}) :
    J.comap ψ.toMonoidHom ≤ uniPlaneClosure r E := by
  intro x hx
  have hx' : ψ x ∈ J := hx
  have h1 := Subgroup.mem_map_of_mem (ψ⁻¹ : MulAut P).toMonoidHom (hJgen hx')
  rw [MonoidHom.map_closure] at h1
  have h2 : (ψ⁻¹ : MulAut P).toMonoidHom (ψ x) = x := by simp
  rw [h2] at h1
  refine (Subgroup.closure_le _).2 ?_ h1
  rintro _ ⟨s, ⟨hsJ, n, hn⟩, rfl⟩
  refine mem_uniPlaneClosure hαE hα1 ?_ (n := n) ?_
  · have h3 : (ψ * α * ψ⁻¹) s = s := mem_fixedSubgroup.1 (hJfix hsJ)
    simp only [MulAut.mul_apply] at h3
    have h4 := congrArg (fun z => ψ⁻¹ z) h3
    simpa using h4
  · rw [MulEquiv.coe_toMonoidHom, ← map_pow, hn, map_one]

end Abstract

section E6

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

set_option linter.unusedSectionVars false


theorem fixedFieldImage_subgroupOf_le_closure (τ : Tag) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≤
      Subgroup.closure {s | s ∈ (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ∧
        ∃ n : ℕ, s ^ (ringChar K ^ n) = 1} := by
  have hchar : ringChar (fixSubfield σ) = ringChar K := by
    have : CharP (fixSubfield σ) (ringChar K) := inferInstance
    exact ringChar.eq _ _
  have hJC : fixedFieldImage τ σ ≤ adjointGroup τ K := fixedFieldImage_le.trans inf_le_left
  set φ : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K :=
    (Subgroup.inclusion hJC).comp (fixedFieldImageEquiv (τ := τ) σ).toMonoidHom with hφ
  intro y hy
  obtain ⟨z, hz⟩ := (fixedFieldImageEquiv (τ := τ) σ).surjective ⟨(y : ModGL τ K), hy⟩
  have hφz : φ z = y := by
    apply Subtype.ext
    simp only [hφ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hz]
    rfl
  have hzc : z ∈ Subgroup.closure {g : adjointGroup τ (fixSubfield σ) | g ^ ringChar (fixSubfield σ) = 1} := by
    rw [closure_pow_ringChar_adjointGroup]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem φ hzc
  rw [MonoidHom.map_closure, hφz] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨?_, 1, ?_⟩
  · show ((φ g : adjointGroup τ K) : ModGL τ K) ∈ fixedFieldImage τ σ
    simp only [hφ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ((fixedFieldImageEquiv (τ := τ) σ) g).2
  · rw [pow_one, ← map_pow, ← hchar, hg, map_one]

theorem uniPlaneGen_E6_field_of_ne_eight {K : Type} [Field K] [Finite K] (h8 : Nat.card K ≠ 8)
    (E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K)))
    [hE : CFSG.IsElementaryAbelian 3 ↥E] (hEc : Nat.card ↥E = 3 ^ 2) (hout : ¬ E ≤ e6Inndiag K) :
    UniPlaneGen (ringChar K) E := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  have hDn : (e6Inndiag K).Normal := e6Inndiag_normal K
  obtain ⟨Θ, -, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨ι, hιE, hι1, hιker⟩ :=
    exists_ne_one_mem_ker_of_plane Tag.E6 (Or.inl rfl) Nat.prime_three (by norm_num) Θ E hEc
  have hιdiag : ι ∈ e6Inndiag K := (mem_ker_iff_mem_e6Inndiag Θ hker ι).1 hιker
  obtain ⟨α, hαE, hα⟩ : ∃ α ∈ E, α ∉ e6Inndiag K := by
    by_contra h
    push Not at h
    exact hout fun x hx => h x hx
  have hα1 : α ≠ 1 := fun h => hα (h ▸ one_mem _)
  have hβ : α * ι ∉ e6Inndiag K := fun h => hα (by simpa using mul_mem h (inv_mem hιdiag))
  have hβ1 : α * ι ≠ 1 := fun h => hβ (h ▸ one_mem _)
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  have hβ3 : (α * ι) ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (α * ι) (E.mul_mem hαE hιE)
  obtain ⟨σa, hσa, -, ψa, hψa⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
    Nat.prime_three (by norm_num) hα3 hα
  obtain ⟨σb, hσb, -, ψb, hψb⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
    Nat.prime_three (by norm_num) hβ3 hβ
  have hbig : ∀ σ : K ≃+* K, orderOf σ = 3 → 2 < Nat.card (fixSubfield σ) := by
    intro σ hσ3
    have hcard := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ
    rw [hσ3] at hcard
    have h2 : 1 < Nat.card (fixSubfield σ) := Finite.one_lt_card
    by_contra hle
    have hN : Nat.card (fixSubfield σ) = 2 := by omega
    rw [hN] at hcard
    norm_num at hcard
    exact h8 (by simpa [Nat.card_eq_fintype_card] using hcard)
  have hgen := fun σ => fixedFieldImage_subgroupOf_le_closure Tag.E6 (K := K) σ
  refine eq_top_of_overgroup_escape (N := e6Inndiag K) (α := α) (ψa := ψa) (ψb := ψb) hι1 hιdiag
    (Ja := (fixedFieldImage Tag.E6 σa).subgroupOf (adjointGroup Tag.E6 K))
    (Jb := (fixedFieldImage Tag.E6 σb).subgroupOf (adjointGroup Tag.E6 K)) ?_ ?_ ?_
    (comap_le_uniPlaneClosure (ψ := ψa) hαE hα1 ?_ (hgen σa))
    (comap_le_uniPlaneClosure (ψ := ψb) (E.mul_mem hαE hιE) hβ1 ?_ (hgen σb))
  · intro M hM
    rw [hψa]
    exact le_subfieldGroup_or_eq_top_of_fixedFieldImage_le (Or.inl rfl) σa Nat.prime_three
      (by norm_num) hσa (hbig σa hσa).ne' M hM
  · rw [hψb]
    exact fixedFieldImage_subgroupOf_le_subfieldGroup Tag.E6 σb
  · intro ι' hι' hfix
    exact eq_one_of_mem_e6Inndiag_of_fix_subfield (fixSubfield σb) (hbig σb hσb) hι'
      fun x hx => hfix x (Subgroup.mem_subgroupOf.2 hx)
  · rw [hψa]
    exact fixedFieldImage_subgroupOf_le_subfieldGroup Tag.E6 σa
  · rw [hψb]
    exact fixedFieldImage_subgroupOf_le_subfieldGroup Tag.E6 σb

theorem uniPlaneGen_E6_field {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK2 : ringChar K ≠ 2) (E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K)))
    [hE : CFSG.IsElementaryAbelian 3 ↥E] (hEc : Nat.card ↥E = 3 ^ 2) (hout : ¬ E ≤ e6Inndiag K) :
    UniPlaneGen (ringChar K) E := by
  refine uniPlaneGen_E6_field_of_ne_eight (K := K) ?_ E hEc hout
  intro h
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have hdvd8 : ringChar K ∣ 8 := by
    rw [← h]
    exact hdvd
  have hdvd2 : ringChar K ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact hdvd8
  exact hK2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hdvd2))

theorem uniSeitzPlanes_E6_field :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧
      (∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ q.p ≠ 2) ∧ ¬ IsE6DiagPlane d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨-, rfl, ⟨q, rfl, hq2⟩, hdiag⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hchar : ringChar K = q.p := ringChar.eq K q.p
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hout : ¬ E.map (MulAut.congr e).toMonoidHom ≤ e6Inndiag K := fun h =>
    hdiag ⟨q, rfl, K, inferInstance, inferInstance, hKchar, e, h⟩
  have h := (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_E6_field (K := K)
    (by rw [hchar]; exact fun h => hpd (by simpa using h.symm)) (by rw [hchar]; exact hq2) _ hc' hout)
  rw [hchar] at h
  simpa using h

end E6

section TwE6

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


theorem twFJ_le_closure {K : Type} [Field K] [Finite K] {ℓ : ℕ} [CharP K ℓ] (σ η : K ≃+* K) :
    twFJ σ η ≤ Subgroup.closure {s | s ∈ twFJ σ η ∧ ∃ n : ℕ, s ^ (ℓ ^ n) = 1} := by
  have : Finite (fixSubfield η) := Subtype.finite
  have hle := subfieldRootGroupImage_le_twistedE6 σ η
  intro y hy
  obtain ⟨z, hz, hzy⟩ := mem_twFJ.1 hy
  have h1 := twOut_graphFixedRootGroup_le_closure TwistTag.E6 ℓ
    (fixSubfieldRestrict σ η).toRingHom hz
  set f : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom) →*
      ↥(twistedE6RootGroup K σ) :=
    { toFun := fun w => ⟨baseChangeGL (fixSubfield η).subtype (w : ModGL TwistTag.E6.tag (fixSubfield η)),
        hle ⟨(w : ModGL TwistTag.E6.tag (fixSubfield η)), w.2, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul] } with hf
  have h2 : (⟨z, hz⟩ : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield η)
      (fixSubfieldRestrict σ η).toRingHom)) ∈ Subgroup.closure {w | ∃ n : ℕ, w ^ (ℓ ^ n) = 1} := by
    have h3 : Subgroup.closure {s | s ∈ graphFixedRootGroup TwistTag.E6 (fixSubfield η)
        (fixSubfieldRestrict σ η).toRingHom ∧ ∃ n : ℕ, s ^ (ℓ ^ n) = 1} ≤
        (Subgroup.closure {w : ↥(graphFixedRootGroup TwistTag.E6 (fixSubfield η)
          (fixSubfieldRestrict σ η).toRingHom) | ∃ n : ℕ, w ^ (ℓ ^ n) = 1}).map
            (graphFixedRootGroup TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom).subtype := by
      rw [Subgroup.closure_le]
      rintro s ⟨hs, n, hn⟩
      exact ⟨⟨s, hs⟩, Subgroup.subset_closure ⟨n, Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hn)⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := h3 h1
    rwa [show w = ⟨z, hz⟩ from Subtype.ext hwz] at hw
  have h4 := Subgroup.mem_map_of_mem f h2
  rw [MonoidHom.map_closure] at h4
  have hfz : f ⟨z, hz⟩ = y := Subtype.ext hzy
  rw [hfz] at h4
  refine Subgroup.closure_mono ?_ h4
  rintro _ ⟨w, ⟨n, hn⟩, rfl⟩
  refine ⟨mem_twFJ.2 ⟨(w : ModGL TwistTag.E6.tag (fixSubfield η)), w.2, rfl⟩, n, ?_⟩
  rw [← map_pow, hn, map_one]

theorem exists_ne_one_mem_inf_of_plane_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (E : Subgroup (MulAut ↥(twistedE6RootGroup K σ))) [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2) {x₀ : MulAut ↥(twistedE6RootGroup K σ)} (hx₀E : x₀ ∈ E)
    (hx₀D : x₀ ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    ∃ ι ∈ E, ι ≠ 1 ∧ ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
  classical
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  obtain ⟨fr, -, -, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK2f
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩
  have hx₀3 : x₀ ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian x₀ hx₀E
  have hΘx₀ : orderOf (Θ x₀) = 3 := by
    refine orderOf_eq_prime (by rw [← map_pow, hx₀3, map_one]) fun h => hx₀D ?_
    rw [← hker]
    exact MonoidHom.mem_ker.2 h
  have hfinE : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  obtain ⟨y, hyE, hy⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers x₀ := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers x₀ := fun z hz => hcon z hz
    have hx₀1 : x₀ ≠ 1 := fun h => hx₀D (h ▸ one_mem _)
    have hord : orderOf x₀ = 3 := orderOf_eq_prime hx₀3 hx₀1
    have hZ : Nat.card (Subgroup.zpowers x₀) = 3 := by rw [Nat.card_zpowers, hord]
    have hfZ : Finite (Subgroup.zpowers x₀) :=
      finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hx₀3⟩)
    have := Subgroup.card_le_of_le hle
    rw [hEc, hZ] at this
    norm_num at this
  have hy3 : Θ y ^ 3 = 1 := by
    rw [← map_pow, CFSG.elemPow_eq_one_of_isElementaryAbelian y hyE, map_one]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hΘx₀ hy3)
  refine ⟨y * (x₀ ^ j)⁻¹, E.mul_mem hyE (E.inv_mem (E.zpow_mem hx₀E j)), ?_, ?_⟩
  · intro h
    apply hy
    rw [mul_inv_eq_one] at h
    rw [h]
    exact Subgroup.zpow_mem_zpowers x₀ j
  · rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hj, mul_inv_cancel]

theorem uniPlaneGen_twE6_field_of_ne_eight {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h8 : ℓ ^ f ≠ 8)
    (hℓ3 : ℓ ≠ 3) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)))
    [hE : CFSG.IsElementaryAbelian 3 ↥E] (hEc : Nat.card ↥E = 3 ^ 2)
    (hout : ¬ E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : UniPlaneGen ℓ E := by
  classical
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
    (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul])
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have hDn : (twistedE6Inn K σ ⊔ twistedE6Diag K σ).Normal := by
    rw [← hker]
    infer_instance
  obtain ⟨α, hαE, hα⟩ : ∃ α ∈ E, α ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    by_contra h
    push Not at h
    exact hout fun x hx => h x hx
  obtain ⟨ι, hιE, hι1, hιD⟩ := exists_ne_one_mem_inf_of_plane_twE6 hℓ hf hK σ hσ E hEc hαE hα
  have hα1 : α ≠ 1 := fun h => hα (h ▸ one_mem _)
  have hβ : α * ι ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := fun h =>
    hα (by simpa using mul_mem h (inv_mem hιD))
  have hβ1 : α * ι ≠ 1 := fun h => hβ (h ▸ one_mem _)
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  have hβ3 : (α * ι) ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (α * ι) (E.mul_mem hαE hιE)
  obtain ⟨hηa, -, ψa, hψa⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf K hK2f σ hσ
    Θ hΘ Nat.prime_three (by norm_num) hα3 hα
  obtain ⟨hηb, -, ψb, hψb⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf K hK2f σ hσ
    Θ hΘ Nat.prime_three (by norm_num) hβ3 hβ
  refine eq_top_of_overgroup_escape (N := twistedE6Inn K σ ⊔ twistedE6Diag K σ) (α := α) (ψa := ψa)
    (ψb := ψb) hι1 hιD (Ja := twFJ σ (Θ α)) (Jb := twFJ σ (Θ (α * ι))) ?_ ?_ ?_
    (comap_le_uniPlaneClosure (ψ := ψa) hαE hα1 ?_ (twFJ_le_closure σ _))
    (comap_le_uniPlaneClosure (ψ := ψb) (E.mul_mem hαE hιE) hβ1 ?_ (twFJ_le_closure σ _))
  · intro M hM
    rw [hψa]
    exact le_fixedSubgroup_or_eq_top_of_twFJ_le hℓ hf hK σ hσ hℓ3 h8 hηa hM
  · rw [hψb]
    exact twFJ_le_twR σ _
  · intro ι' hι' hfix
    obtain ⟨η', rfl⟩ := exists_fieldActor_eq_of_fix_twFJ hℓ hf hK σ hσ _ hfix
    have h1 : Θ (fieldActor σ η') = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hι'
    have h2 : Θ (fieldActor σ η') = η' := hΘ _ 1 1 η' (by rw [map_one, map_one, one_mul, one_mul])
    rw [h2] at h1
    rw [h1, CFSG.LieType.Chevalley.fieldActor_one]
  · rw [hψa]
    exact twFJ_le_twR σ _
  · rw [hψb]
    exact twFJ_le_twR σ _

theorem uniPlaneGen_twE6_field {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)))
    [hE : CFSG.IsElementaryAbelian 3 ↥E] (hEc : Nat.card ↥E = 3 ^ 2)
    (hout : ¬ E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : UniPlaneGen ℓ E := by
  refine uniPlaneGen_twE6_field_of_ne_eight hℓ hf ?_ hℓ3 hK σ hσ E hEc hout
  intro h
  have h2 : 2 ∣ ℓ ^ f := by rw [h]; norm_num
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 (Nat.prime_two.dvd_of_dvd_pow h2)).symm

theorem uniSeitzPlanes_twE6_field :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧
      (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ q.p ≠ 2) ∧
      ¬ ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (σ : K ≃+* K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
        ∃ e : CFSG.LieType.SeitzGeneration.Cat d ≃* twistedE6RootGroup K σ,
          E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨-, rfl, ⟨q, rfl, hq2⟩, hdiag⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hpq : 3 ≠ q.p := by simpa using hpd
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hout : ¬ E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := fun h =>
    hdiag ⟨q, rfl, K, inferInstance, inferInstance, σ, hK, hσ, e, h⟩
  have h := (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_twE6_field q.prime_p q.exponent_pos hq2
    (fun h => hpq h.symm) hK σ hσ _ hc' hout)
  simpa using h

end TwE6

section E78

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality TauCeti

set_option linter.unusedSectionVars false


theorem normalizesRSubgroup_of_native {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (hchar : ∀ q, (c q).characteristic = q.p)
    (h : ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
      ∀ A : Subgroup (adjointGroup τ K), (∀ x ∈ A, x ^ 3 = 1) → Nat.card A = 3 ^ 2 →
        NormalizesRNative τ K A)
    (q : PrimePower) (hv : (c q).Valid) (hq3 : 3 ≠ q.p) (E : Subgroup (MulAut (Cat ⟨c q, hv⟩)))
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2) (hin : InnerPlane ⟨c q, hv⟩ 3 E) :
    NormalizesRSubgroup ⟨c q, hv⟩ E := by
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hnd : ¬ 3 ∣ Nat.card K := by
    rw [hKq, PrimePower.card_def]
    intro hd
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow hd))
  have hinj : Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)) :=
    conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot)
  set E₀C : Subgroup (Cat ⟨c q, hv⟩) := E.comap (MulAut.conj : _ →* MulAut (Cat ⟨c q, hv⟩))
    with hE₀C
  have hmap : E₀C.map (MulAut.conj : _ →* MulAut (Cat ⟨c q, hv⟩)) = E :=
    Subgroup.map_comap_eq_self hin
  have hE₀p : ∀ x ∈ E₀C.map e.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (MulAut.conj : _ →* MulAut (Cat ⟨c q, hv⟩)) (x ^ 3) = 1 := by
      rw [map_pow]
      exact hE.2 _ hx
    have h2 : x ^ 3 = 1 := hinj (h1.trans (map_one _).symm)
    rw [← map_pow, h2, map_one]
  have hE₀c : Nat.card (E₀C.map e.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective e.injective, ← hc, ← hmap,
      Subgroup.card_map_of_injective hinj]
  obtain ⟨R, hR1, hRp, hRn⟩ := h K hnd _ hE₀p hE₀c
  obtain ⟨R', hR'1, hR'p, hR'n⟩ := exists_normalized_of_native e
    ⟨R, hR1, by simpa [hring] using hRp, fun g hg => (map_conj_eq_iff_mem_normalizer R g).2 (hRn hg)⟩
  rw [hmap] at hR'n
  refine ⟨R', hR'1, ?_, hR'n⟩
  show IsPGroup (c q).characteristic R'
  rw [hchar q]
  exact hR'p

theorem uniSeitzPlanes_E78_inner_three :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ p = 3 ∧ (IsE7Index d.1 ∨ IsE8Index d.1) ∧
      ¬ NormalizesRSubgroup d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, rfl, hd, hn⟩
  exfalso
  apply hn
  rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩
  · obtain rfl : d = .E7 q := hq
    have hq3 : 3 ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E7 q).symm)
    exact normalizesRSubgroup_of_native CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
      LieTypeIndex.characteristic_E7
      (fun K _ _ hK3 A hA hcard => allParabolic_of_lang
        (langToralOrParabolic_of_langToralPlane langToralPlane_E7_three) langPlaneKillsRoot_E7
        langPlaneKilled_E7 K hK3 A hA hcard) q hv hq3 E hE hc hin
  · obtain rfl : d = .E8 q := hq
    have hq3 : 3 ≠ q.p := fun h => hpd (h.trans (LieTypeIndex.characteristic_E8 q).symm)
    exact normalizesRSubgroup_of_native CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      LieTypeIndex.characteristic_E8
      (fun K _ _ hK3 A hA hcard => allParabolic_of_lang
        (langToralOrParabolic_of_langToralPlane langToralPlane_E8_three) langPlaneKillsRoot_E8
        langPlaneKilled_E8 K hK3 A hA hcard) q hv hq3 E hE hc hin

end E78

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311f
