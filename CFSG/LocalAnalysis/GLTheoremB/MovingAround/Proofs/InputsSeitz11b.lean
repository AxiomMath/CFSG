module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz11
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310t
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Field
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz11

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

set_option linter.unusedSectionVars false

section FixedLayer

theorem twE6Eight_fixed_layer {L : Type} [Field L] [Finite L] (hL : Nat.card L = (2 ^ 3) ^ 2)
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ (2 ^ 3)) {η : L ≃+* L} (hη : orderOf η = 3) :
    ∃ (k : Subfield L) (σ₀ : k ≃+* k) (J : Subgroup ↥(twistedE6RootGroup L σ)),
      Nat.card k = 2 ^ 2 ∧ (∀ c, σ₀ c = c ^ 2) ∧ Nonempty (↥J ≃* ↥(twistedE6RootGroup k σ₀)) ∧
      J ≤ fixSubgroup (fieldActor σ η) ∧ (J.subgroupOf (fixSubgroup (fieldActor σ η))).Normal ∧
      ∀ g ∈ fixSubgroup (fieldActor σ η), (∀ j ∈ J, g * j = j * g) → g = 1 := by
  classical
  have hℓ : Nat.Prime 2 := Nat.prime_two
  haveI : Fact (Nat.Prime 2) := ⟨hℓ⟩
  have hK : Nat.card L = 2 ^ (2 * 1 * 3) := by rw [hL]; norm_num
  have hσ' : ∀ c, σ c = c ^ 2 ^ (1 * 3) := fun c => by rw [hσ]
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by norm_num : 1 ≤ 2 * 1 * 3) hK
  haveI : Finite (L ≃+* L) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  haveI : IsCyclic (L ≃+* L) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩
  have hT : ∀ c, fr c = c ^ 2 ^ 1 := fun c => by rw [hfr, pow_one]
  have hT6 : fr ^ (2 * 3) = 1 := by
    rw [show 2 * 3 = orderOf fr by rw [hord]]
    exact pow_orderOf_eq_one fr
  obtain ⟨ε, hεdef⟩ : ∃ ε, fr ^ (3 + 1) = ε := ⟨_, rfl⟩
  have hε : ∀ c, ε c = c ^ 2 ^ (1 * (3 + 1)) := fun c => by
    rw [← hεdef, CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hfr, one_mul]
  have hε3 : ε ^ 3 = 1 := by
    rw [← hεdef, ← pow_mul, show (3 + 1) * 3 = 2 * 3 * 2 by norm_num, pow_mul, hT6, one_pow]
  obtain ⟨κ, hκdef⟩ : ∃ κ, fr ^ 2 = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ 2 ^ (2 * 1) := fun c => by
    rw [← hκdef, CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hfr, mul_one]
  have hσ₀ : ∀ c, (fixSubfieldRestrict fr κ c : L) = (c : L) ^ 2 ^ 1 := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hkcard, hJC, hδord, hderived, -, -, -, -, -, hcent, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ le_rfl le_rfl
      (by decide) L hK κ hκ σ hσ' (fixSubfieldRestrict fr κ) hσ₀ ε hε
  have hεne : ε ≠ 1 := fun h => by
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact absurd hδord (by norm_num)
  have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hεne
  have hz : Subgroup.zpowers ε = Subgroup.zpowers η := by
    refine le_antisymm (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num)
        hη hε3
    · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num)
        hεo (by rw [← hη]; exact pow_orderOf_eq_one _)
  have hzA : Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ ε) =
      Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ η) := by
    have h1 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) ε
    have h2 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) η
    rw [hz] at h1
    exact h1.symm.trans h2
  have hfix := CFSG.HardMathSupport.Dickson.Sec6.I923.fixSubgroup_eq_of_zpowers_eq hzA.symm
  set k := fixSubfield κ with hkdef
  set σ₀ := fixSubfieldRestrict fr κ with hσ₀def
  set C := graphFixedRootGroup TwistTag.E6 L σ.toRingHom with hC
  set J₀ := subfieldRootGroupImage TwistTag.E6 k σ₀ with hJ₀
  set Γ := fixSubgroup (fieldActor (t := TwistTag.E6) σ η) with hΓdef
  have hΓε : Γ = MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom (MonoidHom.id C) := hfix
  have hSD : J₀.subgroupOf C = ⁅Γ, Γ⁆ := by
    rw [hΓε]
    exact hderived.symm
  haveI : Finite k := Subtype.finite
  refine ⟨k, σ₀, J₀.subgroupOf C, ?_, ?_, ⟨(Subgroup.subgroupOfEquivOfLe hJC).trans
    (Subgroup.equivMapOfInjective (twistedE6RootGroup k σ₀) _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) k.subtype)).symm⟩, ?_, ?_, ?_⟩
  · rw [hkcard]
  · intro c
    apply Subtype.ext
    rw [hσ₀ c, SubmonoidClass.coe_pow, pow_one]
  · rw [hSD]
    exact Subgroup.commutator_le_self Γ
  · have h := Subgroup.normal_subgroupOf_commutator_sup Γ Γ
    rw [sup_idem] at h
    rw [hSD]
    exact h
  · intro g hg hgJ
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -, -, hZC, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ (by norm_num : 1 ≤ 3) L hL σ hσ
    have hgε : (fieldActor σ ε) g = g := by
      have h : g ∈ MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom (MonoidHom.id C) := hΓε ▸ hg
      exact h
    have h1 : MulAut.conj g ∈ Subgroup.centralizer {fieldActor σ ε} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine MulEquiv.ext fun y => ?_
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hgε]
    have h2 : MulAut.conj g ∈ Subgroup.centralizer
        (subfieldRootGroupInner TwistTag.E6 σ k σ₀ : Set (MulAut C)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      rw [← map_mul, ← map_mul, hgJ j hj]
    have h3 : MulAut.conj g ∈ Subgroup.zpowers (fieldActor σ ε) := hcent ▸ ⟨h1, h2⟩
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h3
    have hΘc : Θ (MulAut.conj g) = 1 :=
      hΘ _ g 1 1 (by rw [map_one, fieldActor_one, mul_one, mul_one])
    have hΘε : Θ (fieldActor σ ε) = ε := hΘ _ 1 1 ε (by rw [map_one, map_one, one_mul, one_mul])
    have hεi : ε ^ i = 1 := by rw [← hΘε, ← map_zpow, hi, hΘc]
    have h3i : ((3 : ℕ) : ℤ) ∣ i := by
      rw [← hεo]
      exact orderOf_dvd_iff_zpow_eq_one.2 hεi
    have hf3 : fieldActor (t := TwistTag.E6) σ ε ^ 3 = 1 := by
      rw [← hδord]
      exact pow_orderOf_eq_one _
    have hconj1 : MulAut.conj g = 1 := by
      obtain ⟨j, rfl⟩ := h3i
      rw [← hi, zpow_mul, zpow_natCast, hf3, one_zpow]
    have hgZ : g ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h4 := congrArg (fun φ : MulAut C => φ y) hconj1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h4
      calc y * g = g * y * g⁻¹ * g := by rw [h4]
        _ = g * y := by group
    rw [hZC] at hgZ
    exact Subgroup.mem_bot.1 hgZ

end FixedLayer

section Tools

variable {X : Type} [Group X] [Finite X]

theorem add_le_pRank_of_fixed_twE6Out {K : Subgroup X} {a : X} (ha3 : a ^ 3 = 1) (haK : a ∉ K)
    {E : Subgroup ↥K} (hE : IsElemAbelian 3 E) {r : ℕ} (hEc : Nat.card E = 3 ^ r)
    (hfix : ∀ y ∈ E, a * (y : X) * a⁻¹ = y) : 1 + r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have ha1 : a ≠ 1 := fun h => haK (h ▸ K.one_mem)
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hZel : IsElemAbelian 3 (Subgroup.zpowers a) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.F4InnerExAux.isElemAbelian_zpowers ha3
  have hZc : Nat.card (Subgroup.zpowers a) = 3 ^ 1 := by rw [Nat.card_zpowers, hao, pow_one]
  have hEXel : IsElemAbelian 3 (E.map K.subtype) := CFSG.SectionRank.isElemAbelian_map hE _
  have hEXc : Nat.card (E.map K.subtype) = 3 ^ r := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hEc]
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ E.map K.subtype, x * y = y * x := by
    rintro x hx _ ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hya : Commute a (y : X) := by
      show a * y = y * a
      calc a * (y : X) = (a * y * a⁻¹) * a := by group
        _ = y * a := by rw [hfix y hy]
    exact (hya.zpow_left i).eq
  have hdisj : Subgroup.zpowers a ⊓ E.map K.subtype = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ E.map K.subtype) ∣ 3 := by
      rw [← pow_one 3, ← hZc]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ E.map K.subtype = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZc, h3, pow_one])
      have haE : a ∈ Subgroup.zpowers a ⊓ E.map K.subtype := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      obtain ⟨y, -, hy⟩ := haE.2
      exact haK (hy ▸ y.2)
  exact InputsSeitz.add_le_pRank_of_commute hp hZel hEXel hcomm hdisj hZc hEXc

theorem exists_elemAbelian_five_twE6Two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2 ^ 2)
    (σ₀ : k ≃+* k) (hσ₀ : ∀ c, σ₀ c = c ^ 2) :
    ∃ E : Subgroup ↥(twistedE6RootGroup k σ₀), IsElemAbelian 3 E ∧ ∃ r, 5 ≤ r ∧ Nat.card E = 3 ^ r := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have he : orderOf (((2 ^ 1 : ℕ)) : ZMod 3) = 2 := by
    rcases CFSG.LieType.SeitzGeneration.orderOf_natCast_three (by norm_num : ¬ 3 ∣ 2 ^ 1) with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      revert h
      decide
    · exact h
  obtain ⟨E, hE, h6⟩ := CFSG.LieType.SeitzGeneration.exists_elemAbelian_twistedE6_three_two Nat.prime_two
    le_rfl k (by rw [hk]; norm_num) σ₀ (fun c => by rw [hσ₀]; norm_num) he
  obtain ⟨r, hr⟩ := GL83.CompFam.exists_card_eq_pow hE
  refine ⟨E, hE, r, ?_, hr⟩
  rw [hr, ← pow_succ'] at h6
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h6
  omega

end Tools

section FieldData

theorem twE6Eight_field_data {K : Type} [Group K] {L : Type} [Field L] [Finite L]
    (hL : Nat.card L = (2 ^ 3) ^ 2) (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ (2 ^ 3))
    (θ : K ≃* ↥(twistedE6RootGroup L σ)) {xa : MulAut K} (hxa3 : xa ^ 3 = 1)
    (hxaD : MulAut.congr θ xa ∉ twistedE6Inn L σ ⊔ twistedE6Diag L σ) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (σ₀ : k ≃+* k), Nat.card k = 2 ^ 2 ∧ (∀ c, σ₀ c = c ^ 2) ∧
      ∃ ι : ↥(twistedE6RootGroup k σ₀) →* K, Function.Injective ι ∧ (∀ v, xa (ι v) = ι v) ∧
        ∃ ρ : ↥(fixSubgroup xa) →* MulAut ↥(twistedE6RootGroup k σ₀), Function.Injective ρ ∧
          ∀ (z : ↥(fixSubgroup xa)) v, ι (ρ z v) = (z : K) * ι v * (z : K)⁻¹ := by
  classical
  set α := MulAut.congr θ xa with hαdef
  have hα3 : α ^ 3 = 1 := by rw [← map_pow, hxa3, map_one]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two (by norm_num : 1 ≤ 3) L
      hL σ hσ
  obtain ⟨hηo, -, ψ, hψ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_conj_fieldActor_of_not_mem_twistedE6Inndiag
      Nat.prime_two (by norm_num : 1 ≤ 3) L (by rw [hL]; norm_num) σ hσ Θ hΘ Nat.prime_three
      (by norm_num) hα3 hxaD
  obtain ⟨k, σ₀, J, hk4, hσ₀, ⟨eJ⟩, hJΓ, hJn, hfaith⟩ := twE6Eight_fixed_layer hL σ hσ hηo
  haveI : Finite k := Subtype.finite
  set Γ := fixSubgroup (fieldActor (t := TwistTag.E6) σ (Θ α)) with hΓdef
  let χ : K ≃* ↥(twistedE6RootGroup L σ) := θ.trans ψ
  have hχ : ∀ z : K, χ (xa z) = fieldActor σ (Θ α) (χ z) := by
    intro z
    have h1 : (ψ * α * ψ⁻¹) (χ z) = fieldActor σ (Θ α) (χ z) := by rw [hψ]
    rw [← h1]
    simp [χ, α, MulAut.congr_apply, MulAut.mul_apply]
  have hfixK : ∀ z ∈ fixSubgroup xa, χ z ∈ Γ := fun z hz => by
    show fieldActor σ (Θ α) (χ z) = χ z
    rw [← hχ, mem_fixSubgroup.1 hz]
  have hfixK' : ∀ z : K, χ z ∈ Γ → xa z = z := fun z hz =>
    χ.injective (by rw [hχ]; exact hz)
  let ι : ↥(twistedE6RootGroup k σ₀) →* K := χ.symm.toMonoidHom.comp (J.subtype.comp eJ.symm.toMonoidHom)
  have hι : Function.Injective ι := by
    intro v w hvw
    apply eJ.symm.injective
    apply Subtype.ext
    exact χ.symm.injective hvw
  have hιΓ : ∀ v, χ (ι v) ∈ Γ := fun v => by
    have : χ (ι v) = (eJ.symm v : ↥(twistedE6RootGroup L σ)) := by simp [ι]
    rw [this]
    exact hJΓ (eJ.symm v).2
  let ιD : ↥(fixSubgroup xa) →* ↥Γ :=
    (χ.toMonoidHom.comp (fixSubgroup xa).subtype).codRestrict Γ fun z => hfixK z z.2
  haveI := hJn
  let eJ' : ↥(J.subgroupOf Γ) ≃* ↥(twistedE6RootGroup k σ₀) := (Subgroup.subgroupOfEquivOfLe hJΓ).trans eJ
  let ρ : ↥(fixSubgroup xa) →* MulAut ↥(twistedE6RootGroup k σ₀) :=
    (MulAut.congr eJ').toMonoidHom.comp ((MulAut.conjNormal (H := J.subgroupOf Γ)).comp ιD)
  have hρι : ∀ (z : ↥(fixSubgroup xa)) v, ι (ρ z v) = (z : K) * ι v * (z : K)⁻¹ := by
    intro z v
    apply χ.injective
    simp [ι, ρ, ιD, eJ', MulAut.congr_apply, MulAut.conjNormal_apply, Subgroup.subgroupOfEquivOfLe]
    rfl
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hz1 : χ (z : K) = 1 := by
      refine hfaith _ (hfixK z z.2) fun j hj => ?_
      have h1 := hρι z (eJ ⟨j, hj⟩)
      rw [hz, MulAut.one_apply] at h1
      have h2 := congrArg χ h1
      simp only [ι, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
        MulEquiv.symm_apply_apply, Subgroup.coe_subtype, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
      calc χ z * j = (χ z * j * (χ z)⁻¹) * χ z := by group
        _ = j * χ z := by rw [← h2]
    exact Subgroup.mem_bot.2 (Subtype.ext (by simpa using χ.injective (hz1.trans (map_one χ).symm)))
  exact ⟨↥k, inferInstance, inferInstance, σ₀, hk4, hσ₀, ι, hι, fun v => hfixK' _ (hιΓ v), ρ, hρinj, hρι⟩

end FieldData

section Layer

theorem exists_twoGroup_of_layer_twE6Out {K T : Type} [Group K] [Finite K] [Group T] [Finite (MulAut T)]
    (hT : ∀ D : Subgroup (MulAut T), IsElemAbelian 3 D → Nat.card D = 3 ^ 4 →
      ∃ E : Subgroup (MulAut T), E ≤ D ∧ 9 ≤ Nat.card E ∧
        ∃ V : Subgroup T, V ≠ ⊥ ∧ IsPGroup 2 ↥V ∧ ∀ φ ∈ E, ∀ v ∈ V, φ v ∈ V)
    {xa : MulAut K} {ι : T →* K} (hι : Function.Injective ι) (hιfix : ∀ v, xa (ι v) = ι v)
    {ρ : ↥(fixSubgroup xa) →* MulAut T} (hρ : Function.Injective ρ)
    (hρι : ∀ (z : ↥(fixSubgroup xa)) v, ι (ρ z v) = (z : K) * ι v * (z : K)⁻¹)
    {D : Subgroup K} (hD : IsElemAbelian 3 D) (hDfix : D ≤ fixSubgroup xa) (hD4 : 3 ^ 4 ≤ Nat.card D) :
    ∃ E : Subgroup K, E ≤ D ∧ 9 ≤ Nat.card E ∧
      ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ (∀ u ∈ U, xa u = u) ∧ ∀ z ∈ E, ∀ u ∈ U, z * u * z⁻¹ ∈ U := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρD : ↥D →* MulAut T := ρ.comp (Subgroup.inclusion hDfix) with hρD
  have hρDinj : Function.Injective ρD := hρ.comp (Subgroup.inclusion_injective hDfix)
  have hρDι : ∀ (z : ↥D) v, ι (ρD z v) = (z : K) * ι v * (z : K)⁻¹ := fun z v =>
    hρι (Subgroup.inclusion hDfix z) v
  set Dbar := ρD.range with hDbar
  have hDbarel : IsElemAbelian 3 Dbar := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨_, a, rfl⟩ := x
      obtain ⟨_, b, rfl⟩ := y
      apply Subtype.ext
      show ρD a * ρD b = ρD b * ρD a
      rw [← map_mul, ← map_mul, hD.1.is_comm.comm a b]
    · obtain ⟨z, rfl⟩ := hg
      rw [← map_pow]
      have : z ^ 3 = 1 := Subtype.ext (hD.2 z z.2)
      rw [this, map_one]
  have hDbarc : Nat.card Dbar = Nat.card D := by
    rw [hDbar, ← Nat.card_congr (MonoidHom.ofInjective hρDinj).toEquiv]
  obtain ⟨s, hs⟩ := GL83.CompFam.exists_card_eq_pow hDbarel
  have hs4 : 4 ≤ s := by
    have h1 : 3 ^ 4 ≤ 3 ^ s := by rw [← hs, hDbarc]; exact hD4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
  obtain ⟨D4, hD4c, -, hD4le⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three (n := 4)
    (H := ⊥) (L := Dbar) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hs]; exact Nat.pow_dvd_pow 3 hs4) bot_le
  obtain ⟨E, hED4, hE9, V, hV0, hV2, hEV⟩ := hT D4 (GL83.CompFam.elem_mono hDbarel hD4le) hD4c
  refine ⟨(E.comap ρD).map D.subtype, Subgroup.map_subtype_le _, ?_, V.map ι,
    fun h => hV0 ((Subgroup.map_eq_bot_iff_of_injective V hι).1 h), hV2.map ι, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective D.subtype_injective, ← Subgroup.card_map_of_injective hρDinj,
      Subgroup.map_comap_eq_self (hED4.trans hD4le)]
    exact hE9
  · rintro _ ⟨v, -, rfl⟩
    exact hιfix v
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨v, hv, rfl⟩
    rw [Subgroup.coe_subtype, ← hρDι]
    exact ⟨_, hEV _ hw v hv, rfl⟩

end Layer

section Cube

variable {X : Type} [Group X] [Finite X]

theorem le_glbCore_of_outer_twoGroup_twE6Out {B K : Subgroup X} (hB : IsElemAbelian 3 B)
    {d : TauCeti.ValidLieTypeIndex} (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hconj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K)) {xa : MulAut ↥K}
    (hxaA : xa ∈ InputsSeitz3.autIm B K) (hxaI : xa ∉ (MulAut.conj : ↥K →* MulAut ↥K).range)
    {E : Subgroup ↥K} (hEA : E.map MulAut.conj ≤ InputsSeitz3.autIm B K) (hE9 : 9 ≤ Nat.card E)
    {U : Subgroup ↥K} (hU0 : U ≠ ⊥) (hU2 : IsPGroup 2 ↥U) (hUfix : ∀ u ∈ U, xa u = u)
    (hEU : ∀ z ∈ E, ∀ u ∈ U, z * u * z⁻¹ ∈ U) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set A := InputsSeitz3.autIm B K with hAdef
  have hAel : IsElemAbelian 3 A := InputsSeitz3.isElemAbelian_autIm hB K
  set M : Subgroup (MulAut ↥K) := E.map MulAut.conj with hM
  have hMI : M ≤ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  have hMc : Nat.card M = Nat.card E := Subgroup.card_map_of_injective hconj
  set F₀ := Subgroup.zpowers xa ⊔ M with hF₀
  have hF₀A : F₀ ≤ A := sup_le ((Subgroup.zpowers_le).2 hxaA) hEA
  have hF₀el : IsElemAbelian 3 F₀ := GL83.CompFam.elem_mono hAel hF₀A
  have hxa3 : xa ^ 3 = 1 := hAel.2 xa hxaA
  have hxa1 : xa ≠ 1 := fun h => hxaI ⟨1, by rw [h, map_one]⟩
  have hxao : orderOf xa = 3 := orderOf_eq_prime hxa3 hxa1
  have hZc : Nat.card (Subgroup.zpowers xa) = 3 ^ 1 := by rw [Nat.card_zpowers, hxao, pow_one]
  have hcommF : ∀ a ∈ Subgroup.zpowers xa, ∀ b ∈ M, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, (Subgroup.zpowers_le).2 hxaA ha⟩ ⟨b, hEA hb⟩)
  have hdisjF : Subgroup.zpowers xa ⊓ M = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers xa ⊓ M) ∣ 3 := by
      rw [← pow_one 3, ← hZc]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers xa ⊓ M = Subgroup.zpowers xa :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZc, h3, pow_one])
      have hxM : xa ∈ Subgroup.zpowers xa ⊓ M := by
        rw [heq]
        exact Subgroup.mem_zpowers xa
      exact hxaI (hMI hxM.2)
  have hF₀27 : 27 ≤ Nat.card F₀ := by
    rw [hF₀, ClassicalEA.card_sup_of_inf_eq_bot hcommF hdisjF, hZc, hMc]
    omega
  obtain ⟨F, hFF₀, hFc⟩ := InputsSeitz10.exists_card_twentySeven_orthEight hF₀el hF₀27
  let St : Subgroup (MulAut ↥K) :=
    { carrier := {φ | ∀ u ∈ U, φ u ∈ U ∧ φ⁻¹ u ∈ U}
      mul_mem' := fun {φ φ'} hφ hφ' u hu => by
        refine ⟨(hφ _ (hφ' u hu).1).1, ?_⟩
        rw [mul_inv_rev, MulAut.mul_apply]
        exact (hφ' _ (hφ u hu).2).2
      one_mem' := fun u hu => ⟨hu, by rw [inv_one]; exact hu⟩
      inv_mem' := fun {φ} hφ u hu => ⟨(hφ u hu).2, by rw [inv_inv]; exact (hφ u hu).1⟩ }
  have hxaSt : xa ∈ St := by
    intro u hu
    refine ⟨by rw [hUfix u hu]; exact hu, ?_⟩
    have h1 : xa⁻¹ u = u := by
      calc xa⁻¹ u = xa⁻¹ (xa u) := by rw [hUfix u hu]
        _ = u := by simp
    rw [h1]
    exact hu
  have hMSt : M ≤ St := by
    rintro _ ⟨z, hz, rfl⟩ u hu
    refine ⟨by rw [MulAut.conj_apply]; exact hEU z hz u hu, ?_⟩
    rw [← map_inv, MulAut.conj_apply]
    exact hEU z⁻¹ (inv_mem hz) u hu
  have hF₀St : F₀ ≤ St := sup_le ((Subgroup.zpowers_le).2 hxaSt) hMSt
  exact InputsSeitz10.le_glbCore_of_e27_twoGroup hB hs eK le_rfl hC (hFF₀.trans hF₀A) hFc hU0 hU2
    fun φ hφ u hu => (hF₀St (hFF₀ hφ) u hu).1

end Cube

section TwE6EightField

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

variable {X : Type} [Group X] [Finite X]

theorem le_glbCore_of_twE6Eight_field (hR7 : Claims1310t.Rank3CuResExcSeven)
    (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (d : TauCeti.ValidLieTypeIndex)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : OuterFourInAux.IsTwE6EightIndex d.1)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hfield : ∀ (L : Type) [Field L] [Finite L] (σ : L ≃+* L), Nat.card L = (2 ^ 3) ^ 2 →
      (∀ c, σ c = c ^ (2 ^ 3)) → ∀ θ : ↥K ≃* twistedE6RootGroup L σ,
        ¬ (InputsSeitz3.autIm B K).map (MulAut.congr θ).toMonoidHom ≤
          twistedE6Inn L σ ⊔ twistedE6Diag L σ) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    exact InputsSeitz7.cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN hC
  have hKs : IsSimpleGroup ↥K := InputsSeitz3.isSimpleGroup_of_center_eq_bot hK.2.2 hZ
  have hna : ∃ a b : ↥K, a * b ≠ b * a := InputsSeitz3.exists_noncomm_of_quasisimple hK.2.2
  have hconj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [← hZ, Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun ψ : MulAut ↥K => ψ h) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨d0, hv⟩ := d
  obtain ⟨q, rfl, hq⟩ : ∃ q : TauCeti.PrimePower, d0 = .twistedE6 q ∧ IsTwoPow q 3 := by
    cases d0 with
    | twistedE6 q => exact ⟨q, rfl, hd⟩
    | _ => exact hd.elim
  obtain ⟨L, _, σ, hL, hσ, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  have hq8 : q.p ^ q.exponent = 2 ^ 3 := by rw [hq.1, hq.2]
  have hL64 : Nat.card L = (2 ^ 3) ^ 2 := by rw [hL, hq8]
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL64]; norm_num)
  have hσ8 : ∀ c, σ c = c ^ (2 ^ 3) := fun c => by rw [hσ, hq8]
  let θ : ↥K ≃* twistedE6RootGroup L σ := eK.trans eC
  set A := InputsSeitz3.autIm B K with hAdef
  have hAel : IsElemAbelian 3 A := InputsSeitz3.isElemAbelian_autIm hB K
  have hAc : Nat.card A = 3 ^ CFSG.Open.pRank 3 B :=
    (InputsSeitz3.card_autIm hBN hC).trans (GL83.PiGen.card_eq_pow_pRank hB)
  obtain ⟨y, hyA, hyD⟩ := SetLike.not_le_iff_exists.1 (hfield L σ hL64 hσ8 θ)
  obtain ⟨x, hxA, rfl⟩ := hyA
  have hxA' := hxA
  obtain ⟨n, hn, rfl⟩ := hxA
  have hnB : (n : X) ∈ B := Subgroup.mem_subgroupOf.1 hn
  set xa := K.normalizerMonoidHom n with hxadef
  have hxa3 : xa ^ 3 = 1 := hAel.2 _ hxA'
  have hxaI : xa ∉ (MulAut.conj : ↥K →* MulAut ↥K).range := by
    rintro ⟨g, hg⟩
    apply hyD
    refine Subgroup.mem_sup_left ⟨θ g, ?_⟩
    show MulAut.conj (θ g) = (MulAut.congr θ).toMonoidHom xa
    rw [← hg]
    exact (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj θ g).symm
  obtain ⟨-, haK⟩ := isOuterOfOrder_of_not_mem_inner_orthOut hB hnB n.2 hxaI
  obtain ⟨k, _, _, σ₀, hk4, hσ₀, ι, hι, hιfix, ρ, hρ, hρι⟩ := twE6Eight_field_data hL64 σ hσ8 θ hxa3 hyD
  obtain ⟨E₀, hE₀el, r, hr5, hE₀c⟩ := exists_elemAbelian_five_twE6Two hk4 σ₀ hσ₀
  have h6 : 6 ≤ CFSG.Open.pRank 3 B := by
    have h := add_le_pRank_of_fixed_twE6Out (hB.2 _ hnB) haK (CFSG.SectionRank.isElemAbelian_map hE₀el ι)
      (by rw [Subgroup.card_map_of_injective hι, hE₀c]) (by
        rintro _ ⟨v, -, rfl⟩
        have h1 := congrArg Subtype.val (hιfix v)
        rwa [hxadef, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1)
    rw [hrk]
    omega
  set A₁ := A ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range with hA₁def
  have hA₁el : IsElemAbelian 3 A₁ := GL83.CompFam.elem_mono hAel inf_le_left
  set D : Subgroup ↥K := A₁.comap (MulAut.conj : ↥K →* MulAut ↥K) with hDdef
  have hDmap : D.map MulAut.conj = A₁ := Subgroup.map_comap_eq_self inf_le_right
  have hDc : Nat.card D = Nat.card A₁ := by
    rw [← hDmap, Subgroup.card_map_of_injective hconj]
  have hDel : IsElemAbelian 3 D := InputsSeitz7.isElemAbelian_comap_of_injective hconj hA₁el
  have hidx := KSFourU.kd26_twE6Eight ↥K hKs hna ⟨.twistedE6 q, hv⟩ hq eK A hAel
  have hD4 : 3 ^ 4 ≤ Nat.card D := by
    rw [hDc]
    have h1 : 3 ^ CFSG.Open.pRank 3 B ≤ 3 * Nat.card A₁ := hAc ▸ hidx
    set m := CFSG.Open.pRank 3 B
    have h2 : 3 ^ m = 3 * 3 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2] at h1
    have h3 := Nat.le_of_mul_le_mul_left h1 (by norm_num)
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h3
  have hDfix : D ≤ fixSubgroup xa := by
    intro z hz
    have hzA : MulAut.conj z ∈ A := (hz : MulAut.conj z ∈ A₁).1
    have hcomm : xa * MulAut.conj z = MulAut.conj z * xa :=
      congrArg Subtype.val (hAel.1.is_comm.comm ⟨_, hxA'⟩ ⟨_, hzA⟩)
    have h1 : MulAut.conj (xa z) = MulAut.conj z := by
      have e1 : MulAut.conj (xa z) = xa * MulAut.conj z * xa⁻¹ := by
        ext w
        simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [e1, hcomm, mul_inv_cancel_right]
    exact hconj h1
  haveI : Finite (MulAut ↥(twistedE6RootGroup k σ₀)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.CartanConjAux.finite_mulAut _
  obtain ⟨E, hED, hE9, U, hU0, hU2, hUfix, hEU⟩ :=
    exists_twoGroup_of_layer_twE6Out (hR7 k σ₀ hk4 hσ₀) hι hιfix hρ hρι hDel hDfix hD4
  refine le_glbCore_of_outer_twoGroup_twE6Out (d := ⟨.twistedE6 q, hv⟩) hB hq.1 eK hC hconj hxA' hxaI
    ((Subgroup.map_mono hED).trans (hDmap.le.trans inf_le_left)) hE9 hU0 hU2 hUfix hEU

end TwE6EightField

section Residual

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

section ResidualDef

@[expose] def Input23_19CoverCaseStmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → 4 ≤ CFSG.Open.pRank 3 B →
      CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) →
      3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      B ≤ Subgroup.normalizer (K : Set X) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ExcIndex 3 d.1 → d.1 ≠ .tits → ¬ IsL2EightIndex d.1 → ¬ Gen2318Index d.1 →
        ¬ InputsSeitz7.IsSpTwoIndex d → ¬ InputsSeitz7.IsUnitaryTwoIndex d →
        ¬ InputsSeitz7.IsSpEightIndex d → ¬ InputsSeitz7.IsUnitaryEightIndex d →
        ¬ InputsSeitz7.IsUThreeEightIndex d →
        ¬ InputsSeitz8.IsOrthTwoIndex d → ¬ InputsSeitz8.IsTriD4TwoIndex d →
        ¬ InputsSeitz8.IsG2EightIndex d → ¬ InputsSeitz7.IsUSixIndex d →
        ¬ InputsSeitz8.IsOmegaEightTwoIndex d → ¬ IsD4FourIndex d.1 →
        ¬ Bal209F4Aux.IsF4TwoIndex d.1 → ¬ IsTwistedE6FourIndex d.1 → ¬ IsF4EightIndex d.1 →
        ¬ OuterFourAux.IsD4EightIndex d.1 →
        (InputsSeitz10.IsOrthEightIndex d → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        (OuterFourInAux.IsTwE6EightIndex d.1 → B ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
          ∀ (L : Type) [Field L] [Finite L] (σ : L ≃+* L), Nat.card L = (2 ^ 3) ^ 2 →
            (∀ c, σ c = c ^ (2 ^ 3)) → ∀ θ : ↥K ≃* twistedE6RootGroup L σ,
              ¬ (InputsSeitz3.autIm B K).map (MulAut.congr θ).toMonoidHom ≤
                twistedE6Inn L σ ⊔ twistedE6Diag L σ) →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        Subgroup.center ↥K ≠ ⊥ → CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 →
        B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ →
        K ≤ GLBCore 3 2 B

@[expose] def Input23_19ExcThreeRest5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → 4 ≤ CFSG.Open.pRank 3 B →
      CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) →
      3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      B ≤ Subgroup.normalizer (K : Set X) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ExcIndex 3 d.1 → d.1 ≠ .tits → ¬ IsL2EightIndex d.1 → ¬ Gen2318Index d.1 →
        ¬ InputsSeitz7.IsSpTwoIndex d → ¬ InputsSeitz7.IsUnitaryTwoIndex d →
        ¬ InputsSeitz7.IsSpEightIndex d → ¬ InputsSeitz7.IsUnitaryEightIndex d →
        ¬ InputsSeitz7.IsUThreeEightIndex d →
        ¬ InputsSeitz8.IsOrthTwoIndex d → ¬ InputsSeitz8.IsTriD4TwoIndex d →
        ¬ InputsSeitz8.IsG2EightIndex d → ¬ InputsSeitz7.IsUSixIndex d →
        ¬ InputsSeitz8.IsOmegaEightTwoIndex d → ¬ IsD4FourIndex d.1 →
        ¬ Bal209F4Aux.IsF4TwoIndex d.1 → ¬ IsTwistedE6FourIndex d.1 → ¬ IsF4EightIndex d.1 →
        ¬ OuterFourAux.IsD4EightIndex d.1 →
        (InputsSeitz10.IsOrthEightIndex d → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        (OuterFourInAux.IsTwE6EightIndex d.1 → B ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
          ∀ (L : Type) [Field L] [Finite L] (σ : L ≃+* L), Nat.card L = (2 ^ 3) ^ 2 →
            (∀ c, σ c = c ^ (2 ^ 3)) → ∀ θ : ↥K ≃* twistedE6RootGroup L σ,
              ¬ (InputsSeitz3.autIm B K).map (MulAut.congr θ).toMonoidHom ≤
                twistedE6Inn L σ ⊔ twistedE6Diag L σ) →
        (IsSixIndex d.1 → ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        ¬ InputsSeitz10.IsOrthEightIndex d → ¬ OuterFourInAux.IsTwE6EightIndex d.1 →
        B ⊓ Subgroup.centralizer (K : Set X) = ⊥ →
        K ≤ GLBCore 3 2 B

end ResidualDef

theorem input23_19ExcThreeRest4_of_rest5 (hR7 : Claims1310t.Rank3CuResExcSeven)
    (hCov : Input23_19CoverCaseStmt) (h : Input23_19ExcThreeRest5) : InputsSeitz10.Input23_19ExcThreeRest4 := by
  intro X _ _ hKX hcore B hB hB4 hrk K hK haut hsmall hBN d hd hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
    hO2 hT2 hG8 hU6 hO8 hD44 hF2 hE4 hF8 hD8 hOut hT8 hsix hrest
  rcases hrest with ⟨hZ, hcov, hCne⟩ | hC
  · exact hCov X hKX hcore B hB hB4 hrk K hK haut hsmall hBN d hd hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
      hO2 hT2 hG8 hU6 hO8 hD44 hF2 hE4 hF8 hD8 hOut hT8 hsix hZ hcov hCne
  obtain ⟨e⟩ := hd
  by_cases hO : InputsSeitz10.IsOrthEightIndex d
  · exact le_glbCore_of_orthEight_outer hcore hB hrk hK d e hO hBN hC (hOut hO)
  by_cases hT : OuterFourInAux.IsTwE6EightIndex d.1
  · exact le_glbCore_of_twE6Eight_field hR7 hcore hB hrk hK d e hT hBN hC (hT8 hT hC)
  exact h X hKX hcore B hB hB4 hrk K hK haut hsmall hBN d ⟨e⟩ hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
    hO2 hT2 hG8 hU6 hO8 hD44 hF2 hE4 hF8 hD8 hOut hT8 hsix hO hT hC

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz11

end
