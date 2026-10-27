module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseANatural

public section

open scoped MatrixGroups commutatorElement

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.OddStandard.Seitz77 (Datum)
open Matrix CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.ComponentClassification.CatalogueBLinearTwoFixed (fixedField mem_fixedField_iff
  subfieldCoordinateEquivImage)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (fieldExtension_mul fieldExtension_inv
  fieldExtension_one fieldExtension_mem_G_iff fieldExtension_conj_mem_G exists_coordinateE_factor
  coordinateD_eq_G even_linear_two_involution_normal_forms)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

namespace CaseAAux

section Coordinates

variable {F : Type} [Field F]

@[expose] def transSub (k : Subfield F) : Subgroup (Equiv.Perm (Omega F)) where
  carrier := {g | ∃ b ∈ k, translation F b = g}
  mul_mem' := by
    rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨b + c, k.add_mem hb hc, (translation_mul_translation b c).symm⟩
  one_mem' := ⟨0, k.zero_mem, translation_zero⟩
  inv_mem' := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨-b, k.neg_mem hb, ?_⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [translation_mul_translation, neg_add_cancel, translation_zero]

theorem card_transSub (k : Subfield F) : Nat.card (transSub k) = Nat.card k := by
  refine (Nat.card_congr (Equiv.ofBijective (fun b : k => (⟨translation F b, b, b.2, rfl⟩ :
    transSub k)) ⟨fun b c h => ?_, fun g => ?_⟩)).symm
  · exact Subtype.ext (translation_injective (congrArg Subtype.val h))
  · obtain ⟨b, hb, hbg⟩ := g.2
    exact ⟨⟨b, hb⟩, Subtype.ext hbg⟩

variable [Finite F] [CharP F 2]

theorem transSub_le {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    transSub (fixedField F σ) ≤ subfieldGImage (fixedField F σ) := by
  rw [subfieldGImage_eq_centralizer hσ]
  rintro _ ⟨b, hb, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨CFSG.LinearGroups.translation_mem_coordinateG b,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h1 := fieldExtension_conj_translation σ b
  rw [(mem_fixedField_iff F σ b).mp hb] at h1
  calc translation F b * fieldExtension F σ =
      fieldExtension F σ * translation F b * (fieldExtension F σ)⁻¹ * fieldExtension F σ := by
        rw [h1]
    _ = fieldExtension F σ * translation F b := by group

omit [Finite F] [CharP F 2] in
theorem fieldExtension_conj_mem_transSub {σ τ : F ≃+* F} (hστ : σ * τ = τ * σ)
    {g : Equiv.Perm (Omega F)} (hg : g ∈ transSub (fixedField F σ)) :
    fieldExtension F τ * g * (fieldExtension F τ)⁻¹ ∈ transSub (fixedField F σ) := by
  obtain ⟨b, hb, rfl⟩ := hg
  refine ⟨τ b, ?_, (fieldExtension_conj_translation τ b).symm⟩
  rw [mem_fixedField_iff] at hb ⊢
  have h : σ (τ b) = τ (σ b) := congrArg (fun φ : F ≃+* F => φ b) hστ
  rw [h, hb]

theorem card_subfieldGImage (k : Subfield F) :
    Nat.card (subfieldGImage k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  rw [subfieldGImage_eq, ← Nat.card_congr (subfieldCoordinateEquivImage F _).toEquiv,
    coordinateD_eq_G, ← Nat.card_congr (slCoord k).toEquiv,
    CFSG.GorensteinWalter.sl2_card_formula]

omit [Finite F] [CharP F 2] in
theorem exists_pow_eq_mul_fieldExtension {g : Equiv.Perm (Omega F)} (hg : g ∈ coordinateG F)
    (φ : F ≃+* F) (n : ℕ) : ∃ g' ∈ coordinateG F,
      (g * fieldExtension F φ) ^ n = g' * fieldExtension F (φ ^ n) := by
  induction n with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, fieldExtension_one, mul_one]⟩
  | succ n ih =>
    obtain ⟨g', hg', he⟩ := ih
    refine ⟨g' * (fieldExtension F (φ ^ n) * g * (fieldExtension F (φ ^ n))⁻¹),
      mul_mem hg' (fieldExtension_conj_mem_G _ hg), ?_⟩
    rw [pow_succ, he, pow_succ, ← fieldExtension_mul]
    group

omit [Finite F] [CharP F 2] in
theorem pow_eq_one_of_mul_fieldExtension {g : Equiv.Perm (Omega F)} (hg : g ∈ coordinateG F)
    {φ : F ≃+* F} {n : ℕ} (hn : (g * fieldExtension F φ) ^ n = 1) : φ ^ n = 1 := by
  obtain ⟨g', hg', he⟩ := exists_pow_eq_mul_fieldExtension hg φ n
  rw [hn] at he
  have : fieldExtension F (φ ^ n) = g'⁻¹ := eq_inv_of_mul_eq_one_right he.symm
  exact (fieldExtension_mem_G_iff _).mp (this ▸ inv_mem hg')

end Coordinates

section FieldImage

variable {F : Type} [Field F] [Finite F] {X : Type*} [Group X]

@[expose] def fieldImage (a : X →* Equiv.Perm (Omega F)) : Subgroup (F ≃+* F) where
  carrier := {φ | fieldExtension F φ ∈ a.range}
  mul_mem' := by
    intro φ ψ hφ hψ
    change fieldExtension F (φ * ψ) ∈ a.range
    rw [← fieldExtension_mul]
    exact mul_mem hφ hψ
  one_mem' := by
    change fieldExtension F 1 ∈ a.range
    rw [fieldExtension_one]
    exact one_mem _
  inv_mem' := by
    intro φ hφ
    change fieldExtension F φ⁻¹ ∈ a.range
    rw [← fieldExtension_inv]
    exact inv_mem hφ

theorem exists_two_part {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (Γ : Subgroup (F ≃+* F)) :
    ∃ τ ∈ Γ, (∃ b : ℕ, orderOf τ = 2 ^ b) ∧
      ∀ φ ∈ Γ, ∀ c : ℕ, φ ^ 2 ^ c = 1 → φ ∈ zpowers τ := by
  obtain ⟨σ₀, -, -, hzp, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hF
  have : IsCyclic (F ≃+* F) := ⟨⟨σ₀, fun x => by
    have : x ∈ zpowers σ₀ := by rw [hzp]; exact Subgroup.mem_top x
    exact Subgroup.mem_zpowers_iff.mp this⟩⟩
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) fun _ _ h => RingEquiv.ext (congrFun h)
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Γ)
  have hm : orderOf γ ≠ 0 := (orderOf_pos γ).ne'
  obtain ⟨b, m', hm', hmeq⟩ := Nat.exists_eq_two_pow_mul_odd hm
  have hm'0 : m' ≠ 0 := fun h => by rw [h] at hm'; exact absurd hm' (by decide)
  refine ⟨((γ ^ m' : Γ) : F ≃+* F), (γ ^ m').2, ⟨b, ?_⟩, fun φ hφ c hc => ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_pow' γ hm'0, hmeq, Nat.gcd_mul_left_left,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm'0)]
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hγ ⟨φ, hφ⟩)
    have h1 : (γ ^ j) ^ ((2 ^ c : ℕ) : ℤ) = 1 := by
      rw [hj, zpow_natCast]
      exact Subtype.ext hc
    rw [← _root_.zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, hmeq] at h1
    have h2 : (m' : ℤ) ∣ j := by
      have h3 : (m' : ℤ) ∣ j * 2 ^ c := by
        refine dvd_trans ?_ h1
        exact ⟨2 ^ b, by push_cast; ring⟩
      refine IsCoprime.dvd_of_dvd_mul_right ?_ h3
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime m' (2 ^ c) :=
        Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm')
      exact_mod_cast this
    obtain ⟨j', rfl⟩ := h2
    refine Subgroup.mem_zpowers_iff.mpr ⟨j', ?_⟩
    have : ((γ ^ m' : Γ) : F ≃+* F) ^ j' = ((γ ^ ((m' : ℤ) * j') : Γ) : F ≃+* F) := by
      rw [_root_.zpow_mul, zpow_natCast, Subgroup.coe_zpow]
    rw [this, hj]

end FieldImage

section FieldPerm

variable {F : Type} [Field F]

theorem fieldPerm_injective : Function.Injective (CFSG.Wreathed.CentralSL2.fieldPerm F) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  rw [CFSG.Wreathed.CentralSL2.fieldPerm_apply] at hφ
  exact (fieldExtension_mem_G_iff φ).mp (hφ ▸ one_mem _)

theorem orderOf_fieldExtension [Finite F] (φ : F ≃+* F) :
    orderOf (fieldExtension F φ) = orderOf φ := by
  rw [← CFSG.Wreathed.CentralSL2.fieldPerm_apply, orderOf_injective _ fieldPerm_injective]

theorem fieldExtension_zpow (φ : F ≃+* F) (j : ℤ) :
    fieldExtension F (φ ^ j) = fieldExtension F φ ^ j := by
  rw [← CFSG.Wreathed.CentralSL2.fieldPerm_apply, ← CFSG.Wreathed.CentralSL2.fieldPerm_apply,
    map_zpow]

end FieldPerm

end CaseAAux

open CaseAAux

namespace WData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}

abbrev Vbar (w : WData d Vi q) : Subgroup w.Nbar := (d.V.subgroupOf w.N).map w.projBar

abbrev Vtil (w : WData d Vi q) : Subgroup w.Ntil := w.Vbar.map w.projTil

variable [Finite G]

theorem V_le_normalizer {V₁ V₂ : Subgroup G} {q' : ℕ} (hR : Radicals d.V V₁ V₂ q')
    (hW : Vi = V₁ ∨ Vi = V₂) : d.V ≤ normalizer (Vi : Set G) := by
  intro v hv
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hVV, -, -⟩ := hR.property hW
  have := (hR.normal hW).conj_mem ⟨x, hVV hx⟩ (mem_subgroupOf.mpr hx) ⟨v, hv⟩
  exact mem_subgroupOf.mp this

theorem V_le_N {V₁ V₂ : Subgroup G} {q' : ℕ} (hR : Radicals d.V V₁ V₂ q')
    (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi q) : d.V ≤ w.N := fun _ hv =>
  w.levi_norm ⟨hv.2, V_le_normalizer hR hW hv⟩

theorem isPGroup_Vbar (w : WData d Vi q) : IsPGroup 2 w.Vbar := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (d.V_isSylow.isPGroup.comap_subtype (K := w.N)).map _

theorem card_Vbar {f : ℕ} {V₁ V₂ : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) : Nat.card w.Vbar = 2 ^ f := by
  obtain ⟨hVV, -, hVc⟩ := hR.property hW
  have hVN := V_le_N hR hW w
  have h1 : Nat.card w.Vbar = w.WN.relIndex (d.V.subgroupOf w.N) := by
    have := relIndex_ker (d.V.subgroupOf w.N) w.projBar
    rw [← this]
    congr 1
    exact QuotientGroup.ker_mk' w.WN
  have h2 := relIndex_mul_card w.WN (d.V.subgroupOf w.N)
  have h3 : Nat.card (d.V.subgroupOf w.N) = (2 ^ f) ^ 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVN).toEquiv, hR.card]
  have h4 : Nat.card (w.WN ⊓ d.V.subgroupOf w.N : Subgroup w.N) = (2 ^ f) ^ 2 := by
    have hinf : w.W ⊓ d.V = Vi := by
      refine le_antisymm (fun x hx => ?_) (le_inf w.le_W hVV)
      rw [← SetLike.ext_iff.mp w.fix x]
      exact ⟨hx.1, mem_centralizer_singleton_iff.mpr (d.V_comm_t hx.2)⟩
    have h5 : w.WN ⊓ d.V.subgroupOf w.N = (w.W ⊓ d.V).subgroupOf w.N :=
      (Subgroup.comap_inf _ _ _).symm
    rw [h5, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans w.W_le_N)).toEquiv, hinf, hVc]
  rw [h3, h4] at h2
  rw [h1]
  have : (2 ^ f) ^ 3 = 2 ^ f * (2 ^ f) ^ 2 := by ring
  rw [this] at h2
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h2

end WData

theorem CaseAAux.eq_one_of_two_pow_of_mem_odd {X : Type*} [Group X] {R : Subgroup X}
    (hR : Odd (Nat.card R)) {x : X} (hx : x ∈ R) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (Nat.card R) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hR)
  exact orderOf_eq_one_iff.mp
    ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd (Subgroup.orderOf_dvd_natCard R hx))

namespace CaseACoord

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
  {K : Type} [Field K] {D : LeviData A Vi K}

theorem Vtil_le_Ltil {f : ℕ} {V₁ V₂ : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) {w : WData d Vi (2 ^ f)} [Finite K] (hKc : Nat.card K = 2 ^ f)
    (C : CaseACoord f w D.lev.range) : w.Vtil ≤ w.Ltil D.lev.range := by
  rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have hvV : (v : G) ∈ d.V := mem_subgroupOf.mp hv
  obtain ⟨u, l, B, huB⟩ := (D.mem_normalizer_iff (v : G) hvV.2).mp
    (WData.V_le_normalizer hR hW hvV)
  have huV : D.ι u ∈ Vi := (SetLike.ext_iff.mp D.range_ι _).mp ⟨u, rfl⟩
  have hιN : D.ι u ∈ w.N := w.W_le_N (w.le_W huV)
  have hdec : v = ⟨D.ι u, hιN⟩ * ⟨D.tor l, w.tor_mem_N D l⟩ * w.levE D B := Subtype.ext huB
  have h1 : w.projBar ⟨D.ι u, hιN⟩ = 1 := (w.projBar_eq_one_iff _).mpr (w.le_W huV)
  refine ⟨w.levQ D B, w.levBar_mem_Lbar D B, ?_⟩
  rw [hdec]
  simp only [map_mul, h1, one_mul, C.projTil_tor hKc l]

theorem card_Vtil {f : ℕ} {V₁ V₂ : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) (w : WData d Vi (2 ^ f)) : Nat.card w.Vtil = 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [WData.Vtil, card_map_of_injOn _ (fun x hx h1 => ?_), w.card_Vbar hR hW]
  obtain ⟨k, hk⟩ := w.isPGroup_Vbar ⟨x, hx⟩
  exact eq_one_of_two_pow_of_mem_odd
    (CFSG.LocalAnalysis.EvenBN.GMSK.odd_card_standardComponentOddCore _)
    ((QuotientGroup.eq_one_iff _).mp h1) (congrArg Subtype.val hk)

open CFSG.Wreathed.CentralSL2 (fieldPerm fieldPerm_apply) in
theorem exists_wtil {f : ℕ} {V₁ V₂ : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) {w : WData d Vi (2 ^ f)} [Finite K] (hKc : Nat.card K = 2 ^ f)
    (C : CaseACoord f w D.lev.range) :
    ∃ wt : w.Ntil, (∃ b : ℕ, orderOf wt = 2 ^ b) ∧ w.ttil ∈ zpowers wt ∧
      (∀ j : ℤ, wt ^ j ∈ normalClosure (w.Ltil D.lev.range : Set w.Ntil) → wt ^ j = 1) ∧
      (∀ v ∈ w.Vtil, wt * v * wt⁻¹ ∈ w.Vtil) ∧
      ∀ s : w.Ntil, (∃ c : ℕ, s ^ 2 ^ c = 1) →
        ∃ j : ℤ, s * wt ^ (-j) ∈ normalClosure (w.Ltil D.lev.range : Set w.Ntil) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hpos
    · exfalso
      have h0 := Finite.one_lt_card (α := K)
      rw [hKc, pow_zero] at h0
      exact lt_irrefl _ h0
    · exact hpos
  set k := fixedField C.F C.σ with hk
  set J := subfieldGImage k with hJ
  set E := normalClosure (w.Ltil D.lev.range : Set w.Ntil) with hE
  have hpos : (2 ^ f) ^ 2 - 1 ≠ 0 := by
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have h2 : 1 < (2 ^ f) ^ 2 := Nat.one_lt_pow (by norm_num) h1
    omega
  have hJfac : (Nat.card J).factorization 2 = f := by
    rw [hJ, card_subfieldGImage, C.card_fixed, Nat.factorization_mul (by positivity) hpos,
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two]
    have hodd : ¬ 2 ∣ (2 ^ f) ^ 2 - 1 := by
      have h2 : 2 ∣ (2 ^ f) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
      have h3 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    rw [Nat.factorization_eq_zero_of_not_dvd hodd]
    simp
  have hVJ : w.Vtil.map C.a ≤ J := by
    rw [hJ, ← C.a_Ltil]
    exact Subgroup.map_mono (C.Vtil_le_Ltil hR hW hKc)
  have hsylV : IsSylowOf 2 (w.Vtil.map C.a) J := isSylowOf_of_card hVJ (by
    rw [Subgroup.card_map_of_injective C.a_injective, card_Vtil hR hW w, hJfac])
  have hsylT : IsSylowOf 2 (transSub k) J := isSylowOf_of_card (transSub_le C.orderOf_σ) (by
    rw [card_transSub, C.card_fixed, hJfac])
  obtain ⟨c, hcJ, hc⟩ := hsylV.exists_mem_conj hsylT
  have hcG : c ∈ coordinateG C.F := subfieldGImage_le_G k hcJ
  have hcσ : c * fieldExtension C.F C.σ = fieldExtension C.F C.σ * c := by
    have := (subfieldGImage_eq_centralizer C.orderOf_σ ▸ hcJ : c ∈ coordinateG C.F ⊓
      Subgroup.centralizer {fieldExtension C.F C.σ})
    exact Subgroup.mem_centralizer_singleton_iff.mp this.2
  set a' : w.Ntil →* Equiv.Perm (Omega C.F) := (MulAut.conj c).toMonoidHom.comp C.a with ha'
  have ha'app : ∀ x, a' x = c * C.a x * c⁻¹ := fun x => rfl
  have ha'inj : Function.Injective a' := (MulAut.conj c).injective.comp C.a_injective
  have hcE : c ∈ coordinateE C.F := coordinateD_le_E C.F (coordinateG_le_D C.F hcG)
  have ha'E : ∀ x, a' x ∈ coordinateE C.F := fun x => by
    rw [ha'app]; exact mul_mem (mul_mem hcE (C.a_mem x)) (inv_mem hcE)
  have ha'G : ∀ x ∈ E, a' x ∈ coordinateG C.F := fun x hx => by
    rw [ha'app]; exact mul_mem (mul_mem hcG (C.a_layer x hx)) (inv_mem hcG)
  have ha'S : ∀ g ∈ coordinateG C.F, ∃ x ∈ E, a' x = g := by
    intro g hg
    obtain ⟨x, hx, hxg⟩ := C.a_layer_onto (c⁻¹ * g * c) (mul_mem (mul_mem (inv_mem hcG) hg) hcG)
    exact ⟨x, hx, by rw [ha'app, hxg]; group⟩
  have ha't : a' w.ttil = fieldExtension C.F C.σ := by
    rw [ha'app, C.a_t, hcσ, mul_inv_cancel_right]
  have ha'V : ∀ v ∈ w.Vtil, a' v ∈ transSub k := fun v hv =>
    (hc _).mpr ⟨v, hv, by rw [ha'app]; group⟩
  have ha'V' : ∀ g ∈ transSub k, ∃ v ∈ w.Vtil, a' v = g := by
    intro g hg
    obtain ⟨v, hv, hvg⟩ := (hc g).mp hg
    exact ⟨v, hv, by rw [ha'app, hvg]; group⟩
  have hE' : ∀ x, a' x ∈ coordinateG C.F → x ∈ E := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := ha'S _ hx
    rw [ha'inj hyx] at hy
    exact hy
  obtain ⟨τ, hτΓ, ⟨b, hτb⟩, hτ2⟩ := exists_two_part (by omega : 1 ≤ 2 * f) C.card
    (fieldImage a')
  have hσΓ : C.σ ∈ fieldImage a' := ⟨w.ttil, ha't⟩
  obtain ⟨jσ, hjσ⟩ := Subgroup.mem_zpowers_iff.mp
    (hτ2 C.σ hσΓ 1 (by rw [pow_one, sq]; exact pow_orderOf_eq_one C.σ ▸ (by rw [C.orderOf_σ, sq])))
  obtain ⟨wt, hwt⟩ := hτΓ
  have hτσ : C.σ * τ = τ * C.σ := by rw [← hjσ]; exact (Commute.zpow_self τ jσ).eq
  refine ⟨wt, ⟨b, ?_⟩, ?_, fun j hj => ?_, fun v hv => ?_, fun s ⟨cs, hcs⟩ => ?_⟩
  · rw [← orderOf_injective a' ha'inj, hwt, orderOf_fieldExtension, hτb]
  · refine Subgroup.mem_zpowers_iff.mpr ⟨jσ, ha'inj ?_⟩
    rw [map_zpow, hwt, ← fieldExtension_zpow, hjσ, ha't]
  · have h1 : a' (wt ^ j) ∈ coordinateG C.F := ha'G _ hj
    rw [map_zpow, hwt, ← fieldExtension_zpow, fieldExtension_mem_G_iff] at h1
    apply ha'inj
    rw [map_zpow, hwt, ← fieldExtension_zpow, h1, fieldExtension_one, map_one]
  · obtain ⟨v', hv', hv'e⟩ := ha'V' (a' (wt * v * wt⁻¹)) (by
      rw [map_mul, map_mul, map_inv, hwt]
      exact fieldExtension_conj_mem_transSub hτσ (ha'V v hv))
    rw [← ha'inj hv'e]
    exact hv'
  · obtain ⟨g, hg, φ, hgφ⟩ := exists_coordinateE_factor (ha'E s)
    have hφΓ : φ ∈ fieldImage a' := by
      obtain ⟨x, hx, hxg⟩ := ha'S g hg
      refine ⟨x⁻¹ * s, ?_⟩
      rw [map_mul, map_inv, hxg, hgφ]
      group
    have hφ2 : φ ^ 2 ^ cs = 1 := by
      refine pow_eq_one_of_mul_fieldExtension hg ?_
      rw [← hgφ, ← map_pow, hcs, map_one]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hτ2 φ hφΓ cs hφ2)
    refine ⟨j, hE' _ ?_⟩
    rw [map_mul, map_zpow, hwt, hgφ, ← fieldExtension_zpow, _root_.zpow_neg, hj,
      ← fieldExtension_inv, mul_inv_cancel_right]
    exact hg

end CaseACoord

namespace CaseACoord

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}

theorem exists_conj_tbar {f : ℕ} {w : WData d Vi (2 ^ f)} {L : Subgroup G}
    (C : CaseACoord f w L) {x : w.Nbar} (hx : x ∈ w.Ebar L)
    (hx2 : x * w.tbar * (x * w.tbar) = 1) :
    ∃ e ∈ w.Ebar L, e * w.tbar * e⁻¹ = x * w.tbar := by
  have hf : 1 ≤ 2 * f := by
    rcases Nat.eq_zero_or_pos f with rfl | hpos
    · exfalso
      have h0 := Finite.one_lt_card (α := C.F)
      rw [C.card, mul_zero, pow_zero] at h0
      exact lt_irrefl _ h0
    · omega
  have hnf := (even_linear_two_involution_normal_forms (K := C.F) hf C.card).2.2.2.2.2.2.2.2.2
  set y := x * w.tbar with hy
  have hxG : C.a (w.projTil x) ∈ coordinateG C.F :=
    C.a_layer _ (by rw [← WData.map_Ebar_projTil]; exact ⟨x, hx, rfl⟩)
  have hσ2 : C.σ * C.σ = 1 := by
    rw [← sq, ← C.orderOf_σ]; exact pow_orderOf_eq_one _
  have hσ1 : C.σ ≠ 1 := fun h1 => by
    have := C.orderOf_σ; rw [h1, orderOf_one] at this; omega
  have hay : C.a (w.projTil y) = C.a (w.projTil x) * fieldExtension C.F C.σ := by
    rw [hy, map_mul, map_mul, C.a_t]
  have hyord : orderOf (C.a (w.projTil y)) = 2 := by
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [sq, ← map_mul, ← map_mul, hx2, map_one, map_one]
    · rw [hay] at h1
      have : fieldExtension C.F C.σ ∈ coordinateG C.F := by
        have h2 : fieldExtension C.F C.σ = (C.a (w.projTil x))⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [h2]; exact inv_mem hxG
      exact hσ1 ((fieldExtension_mem_G_iff _).mp this)
  have hyE : C.a (w.projTil y) ∈ coordinateE C.F := C.a_mem _
  rcases hnf _ hyE hyord with ⟨h1, -⟩ | ⟨-, -, σ', -, -, -, hσu, -, ⟨h, hh, hhe⟩, -⟩
  · exfalso
    rw [hay] at h1
    have : fieldExtension C.F C.σ ∈ coordinateG C.F := by
      have h2 := mul_mem (inv_mem hxG) h1
      rwa [inv_mul_cancel_left] at h2
    exact hσ1 ((fieldExtension_mem_G_iff _).mp this)
  · have hσσ' : C.σ = σ' := hσu C.σ hσ1 hσ2
    rw [← hσσ'] at hhe
    obtain ⟨e', he', hee'⟩ := C.a_layer_onto h hh
    rw [← WData.map_Ebar_projTil] at he'
    obtain ⟨e, he, hee⟩ := he'
    refine ⟨e, he, ?_⟩
    have h3 : w.projTil (e * w.tbar * e⁻¹) = w.projTil y := by
      apply C.a_injective
      rw [hhe, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hee, hee', C.a_t]
    have hmem : y * (e * w.tbar * e⁻¹)⁻¹ ∈ w.Ebar L := by
      have h4 : y * (e * w.tbar * e⁻¹)⁻¹ = x * (w.tbar * e * w.tbar⁻¹) * e⁻¹ := by
        rw [hy]; group
      rw [h4]
      exact mul_mem (mul_mem hx (conj_t_mem ⟨e, he⟩)) (inv_mem he)
    have h5 := C.eq_one_of_projTil ⟨_, hmem⟩ (by
      change w.projTil (y * (e * w.tbar * e⁻¹)⁻¹) = 1
      rw [map_mul, map_inv, h3, mul_inv_cancel])
    have h6 : y * (e * w.tbar * e⁻¹)⁻¹ = 1 := congrArg Subtype.val h5
    exact (mul_inv_eq_one.mp h6).symm

end CaseACoord

namespace CaseACoord

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G}
  {K : Type} [Field K] {D : LeviData A Vi K}

theorem mem_Ebar_of_two_pow {f : ℕ} {w : WData d Vi (2 ^ f)} {L : Subgroup G}
    (C : CaseACoord f w L) (hO : ⁅standardComponentOddCore w.Nbar, w.Ebar L⁆ = ⊥) {x : w.Nbar}
    (hx : w.projTil x ∈ normalClosure (w.Ltil L : Set w.Ntil)) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ w.Ebar L := by
  rw [← WData.map_Ebar_projTil] at hx
  obtain ⟨e, he, hex⟩ := hx
  set o := e⁻¹ * x with ho_def
  have ho : o ∈ standardComponentOddCore w.Nbar := (QuotientGroup.eq_one_iff _).mp (by
    change w.projTil (e⁻¹ * x) = 1
    rw [map_mul, map_inv, hex, inv_mul_cancel])
  have hcomm : Commute e o := by
    have h1 : ⁅o, e⁆ ∈ ⁅standardComponentOddCore w.Nbar, w.Ebar L⁆ :=
      Subgroup.commutator_mem_commutator ho he
    rw [hO, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hxeo : x = e * o := by rw [ho_def]; group
  have hk' : o ^ 2 ^ k = (e ^ 2 ^ k)⁻¹ := by
    rw [hxeo, hcomm.mul_pow] at hk
    exact eq_inv_of_mul_eq_one_right hk
  have hoE : o ^ 2 ^ k ∈ w.Ebar L := by rw [hk']; exact inv_mem (pow_mem he _)
  have hoO : o ^ 2 ^ k ∈ standardComponentOddCore w.Nbar := pow_mem ho _
  have h1 : o ^ 2 ^ k = 1 := by
    have := C.eq_one_of_projTil ⟨_, hoE⟩ ((QuotientGroup.eq_one_iff _).mpr hoO)
    exact congrArg Subtype.val this
  have h2 : o = 1 := eq_one_of_two_pow_of_mem_odd
    (CFSG.LocalAnalysis.EvenBN.GMSK.odd_card_standardComponentOddCore _) ho h1
  rw [hxeo, h2, mul_one]
  exact he

theorem exists_wbar {f : ℕ} {V₁ V₂ : Subgroup G} (hR : Radicals d.V V₁ V₂ (2 ^ f))
    (hW : Vi = V₁ ∨ Vi = V₂) {w : WData d Vi (2 ^ f)} [Finite K] (hKc : Nat.card K = 2 ^ f)
    (C : CaseACoord f w D.lev.range)
    (hO : ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥) :
    ∃ wb : w.Nbar, (∃ b : ℕ, orderOf wb = 2 ^ b) ∧ w.tbar ∈ zpowers wb ∧
      (∀ j : ℤ, wb ^ j ∈ w.Ebar D.lev.range → wb ^ j = 1) ∧
      (∀ v ∈ w.Vbar, wb * v * wb⁻¹ ∈ w.Vbar) ∧ w.Vbar ≤ w.Ebar D.lev.range ∧
      ∀ S : Subgroup w.Nbar, IsPGroup 2 S → wb ∈ S →
        ∀ s ∈ S, ∃ j : ℤ, s * wb ^ (-j) ∈ w.Ebar D.lev.range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨wt, ⟨b, hb⟩, htw, hwE, hwV, hk⟩ := C.exists_wtil hR hW hKc
  set O := standardComponentOddCore w.Nbar with hOdef
  have hOodd : Odd (Nat.card O) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.odd_card_standardComponentOddCore _
  have hVb2 := w.isPGroup_Vbar
  have hwt2 : IsPGroup 2 (zpowers wt) := IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  have hVt2 : IsPGroup 2 w.Vtil := hVb2.map _
  set Pt := w.Vtil ⊔ zpowers wt with hPt
  have hPt2 : IsPGroup 2 Pt := IsPGroup.to_sup_of_normal_left' hVt2 hwt2
    ((zpowers_le).mpr (Subgroup.mem_normalizer_fintype fun v hv => hwV v hv))
  set M := Pt.comap w.projTil with hM
  have htb2 : IsPGroup 2 (zpowers w.tbar) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, w.orderOf_tbar, pow_one])
  have htV : w.tbar ∈ normalizer (w.Vbar : Set w.Nbar) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := hx
    have hvt : (v : G) * d.t = d.t * v := d.V_comm_t (mem_subgroupOf.mp hv)
    have : w.tbar * w.projBar v * w.tbar⁻¹ = w.projBar v := by
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      change d.t * (v : G) * d.t⁻¹ = v
      rw [← hvt, mul_inv_cancel_right]
    rw [this]
    exact ⟨v, hv, rfl⟩
  set Q₀ := w.Vbar ⊔ zpowers w.tbar with hQ₀
  have hQ₀2 : IsPGroup 2 Q₀ := IsPGroup.to_sup_of_normal_left' hVb2 htb2 ((zpowers_le).mpr htV)
  have hQ₀M : Q₀ ≤ M := by
    refine sup_le (fun x hx => ?_) ((zpowers_le).mpr ?_)
    · rw [hM, mem_comap]
      exact mem_sup_left ⟨x, hx, rfl⟩
    · rw [hM, mem_comap]
      exact mem_sup_right htw
  obtain ⟨Q, hQ⟩ := (hQ₀2.comap_subtype (K := M)).exists_le_sylow
  set T := (Q : Subgroup M).map M.subtype with hT
  have hTM : T ≤ M := map_subtype_le _
  have hT2 : IsPGroup 2 T := Q.isPGroup'.map _
  have hQ₀T : Q₀ ≤ T := fun x hx => ⟨⟨x, hQ₀M hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩
  have hinjT : ∀ x ∈ T, w.projTil x = 1 → x = 1 := by
    intro x hx h1
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx⟩
    exact eq_one_of_two_pow_of_mem_odd hOodd ((QuotientGroup.eq_one_iff _).mp h1)
      (congrArg Subtype.val hk)
  have hinjT' : ∀ x ∈ T, ∀ y ∈ T, w.projTil x = w.projTil y → x = y := by
    intro x hx y hy hxy
    have := hinjT (x⁻¹ * y) (mul_mem (inv_mem hx) hy) (by rw [map_mul, map_inv, hxy,
      inv_mul_cancel])
    exact inv_mul_eq_one.mp this
  have hmapT : T.map w.projTil = Pt := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := hx
      exact hTM hy
    · obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hPt2
      have hker : w.projTil.ker = O := QuotientGroup.ker_mk' _
      have hcardM : Nat.card M = Nat.card Pt * Nat.card O := by
        have h1 := relIndex_mul_card w.projTil.ker M
        have h2 : w.projTil.ker ⊓ M = w.projTil.ker := inf_eq_left.mpr fun x hx => by
          rw [hM, mem_comap, (MonoidHom.mem_ker).mp hx]; exact one_mem _
        rw [h2, relIndex_ker, hM, map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective _), hker] at h1
        exact h1.symm
      have hTcard : Nat.card T = Nat.card Pt := by
        have h1 : Nat.card T = 2 ^ (Nat.card M).factorization 2 := by
          rw [hT, Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity]
        rw [h1, hcardM, he, Nat.factorization_mul (by positivity) (Nat.card_pos (α := O)).ne',
          Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
          Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hOodd)
            (even_iff_two_dvd.mpr h2))]
        simp
      rw [card_map_of_injOn _ hinjT, hTcard]
  have hwtP : wt ∈ Pt := mem_sup_right (mem_zpowers wt)
  rw [← hmapT] at hwtP
  obtain ⟨wb, hwbT, hwbe⟩ := hwtP
  have hwbpow : ∀ j : ℤ, w.projTil (wb ^ j) = wt ^ j := fun j => by rw [map_zpow, hwbe]
  refine ⟨wb, ⟨b, ?_⟩, ?_, fun j hj => ?_, fun v hv => ?_, fun v hv => ?_, fun S hS hwbS s hs => ?_⟩
  · have h1 : orderOf (⟨wb, hwbT⟩ : T) = orderOf wt := by
      rw [← hwbe]
      exact (orderOf_injective (w.projTil.comp T.subtype) (by
        rw [injective_iff_map_eq_one]
        intro x hx
        exact Subtype.ext (hinjT x x.2 hx)) ⟨wb, hwbT⟩).symm
    rw [← Subgroup.orderOf_mk wb hwbT, h1, hb]
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp htw
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, hinjT' _ (zpow_mem hwbT j) _
      (hQ₀T (mem_sup_right (mem_zpowers _))) ?_⟩
    rw [hwbpow, hj]
  · have h1 : wt ^ j = 1 := hwE j (by
      rw [← hwbpow, ← WData.map_Ebar_projTil]; exact ⟨_, hj, rfl⟩)
    exact hinjT _ (zpow_mem hwbT j) (by rw [hwbpow, h1])
  · have hvT : v ∈ T := hQ₀T (mem_sup_left hv)
    have h1 : w.projTil (wb * v * wb⁻¹) ∈ w.Vtil := by
      rw [map_mul, map_mul, map_inv, hwbe]
      exact hwV _ ⟨v, hv, rfl⟩
    obtain ⟨v', hv', hv'e⟩ := h1
    rw [hinjT' _ (mul_mem (mul_mem hwbT hvT) (inv_mem hwbT)) _ (hQ₀T (mem_sup_left hv'))
      hv'e.symm]
    exact hv'
  · obtain ⟨k, hk'⟩ := hVb2 ⟨v, hv⟩
    exact C.mem_Ebar_of_two_pow hO (Subgroup.le_normalClosure
      (C.Vtil_le_Ltil hR hW hKc ⟨v, hv, rfl⟩)) (congrArg Subtype.val hk')
  · obtain ⟨c, hc⟩ := hS ⟨s, hs⟩
    obtain ⟨j, hj⟩ := hk (w.projTil s) ⟨c, by
      rw [← map_pow]
      have : s ^ 2 ^ c = 1 := congrArg Subtype.val hc
      rw [this, map_one]⟩
    refine ⟨j, ?_⟩
    obtain ⟨c', hc'⟩ := hS ⟨s * wb ^ (-j), mul_mem hs (zpow_mem hwbS _)⟩
    exact C.mem_Ebar_of_two_pow hO (by rw [map_mul, hwbpow]; exact hj)
      (congrArg Subtype.val hc')

end CaseACoord

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem seitz32
    (hf : 3 ≤ f) (d : Datum A) {V₁ V₂ Vi : Subgroup G}
    (hR : Radicals d.V V₁ V₂ (2 ^ f)) (hW : Vi = V₁ ∨ Vi = V₂)
    (hN : normalizer ((Vi ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (Vi : Set G))
    (w : WData d Vi (2 ^ f))
    {K : Type} [Field K] [Finite K] (D : LeviData A Vi K) (hKc : Nat.card K = 2 ^ f)
    (hA : w.CaseA f D.lev.range)
    (hO : ⁅standardComponentOddCore w.Nbar, w.Ebar D.lev.range⁆ = ⊥) :
    ∃ C : CaseACoord f w D.lev.range,
      (∀ x : w.Ebar D.lev.range, C.ψ ⟨_, CaseACoord.conj_t_mem x⟩ =
        SpecialLinearGroup.map C.σ.toRingHom (C.ψ x)) ∧
      (∀ x ∈ w.Ebar D.lev.range, x * w.tbar * (x * w.tbar) = 1 →
        ∃ e ∈ w.Ebar D.lev.range, e * w.tbar * e⁻¹ = x * w.tbar) ∧
      ∃ (w₁ : G) (hw₁ : w₁ ∈ w.N) (S₁ S₀ : Subgroup G),
        w.Ebar D.lev.range ⊔ zpowers (w.projBar ⟨w₁, hw₁⟩) ⊔ zpowers w.tbar =
          w.Ebar D.lev.range ⊔ zpowers (w.projBar ⟨w₁, hw₁⟩) ∧
        w.Ebar D.lev.range ⊓ zpowers (w.projBar ⟨w₁, hw₁⟩) = ⊥ ∧
        IsSylowOf 2 S₁ w.N ∧ IsSylowOf 2 S₀ (w.Ehat D.lev.range) ∧
        S₀ = S₁ ⊓ w.Ehat D.lev.range ∧ S₁ = S₀ ⊔ zpowers w₁ ∧ S₀ ⊓ zpowers w₁ = ⊥ ∧
        d.t ∈ zpowers w₁ ∧ d.V ≤ S₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C⟩ := WData.CaseA.nonempty_coord hf hR hW hN hKc hA hO
  obtain ⟨wb, ⟨b, hb⟩, htwb, hwbE, hwbV, hVE, hdecS⟩ := C.exists_wbar hR hW hKc hO
  obtain ⟨Y, hYN, hWY, htY, hdec⟩ := C.exists_complement hf hKc
  set E := w.Ehat D.lev.range with hEdef
  have hone : ∀ (y : G) (hy : y ∈ Y), w.projBar ⟨y, hYN hy⟩ = 1 → y = 1 := by
    intro y hy h1
    have h2 : y ∈ w.W ⊓ Y := ⟨(w.projBar_eq_one_iff _).mp h1, hy⟩
    rwa [hWY, mem_bot] at h2
  have hinjY : ∀ (y : G) (hy : y ∈ Y) (y' : G) (hy' : y' ∈ Y),
      w.projBar ⟨y, hYN hy⟩ = w.projBar ⟨y', hYN hy'⟩ → y = y' := by
    intro y hy y' hy' hyy
    have h1 : y⁻¹ * y' ∈ w.W := (w.projBar_eq_iff _ _).mp hyy
    have h2 : y⁻¹ * y' ∈ w.W ⊓ Y := ⟨h1, Y.mul_mem (Y.inv_mem hy) hy'⟩
    rw [hWY, mem_bot] at h2
    calc y = y * (y⁻¹ * y') := by rw [h2, mul_one]
      _ = y' := by group
  have hlift : ∀ x : w.Nbar, ∃ (y : G) (hy : y ∈ Y), w.projBar ⟨y, hYN hy⟩ = x := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective w.WN x
    obtain ⟨a, ha, y, hy, hny⟩ := hdec n n.2
    refine ⟨y, hy, ?_⟩
    change w.projBar ⟨y, hYN hy⟩ = w.projBar n
    rw [w.projBar_eq_iff]
    change y⁻¹ * (n : G) ∈ w.W
    rw [hny, show y⁻¹ * (a * y) = y⁻¹ * a * y⁻¹⁻¹ by group]
    exact (mem_normalizer_iff.mp (inv_mem (hYN hy)) a).mp ha
  obtain ⟨w₁, hw₁Y, hw₁e⟩ := hlift wb
  have hw₁N := hYN hw₁Y
  have hw₁pow : ∀ j : ℤ, w.projBar ⟨w₁ ^ j, zpow_mem hw₁N j⟩ = wb ^ j := fun j => by
    rw [← hw₁e, ← map_zpow]
    rfl
  set Tb := w.Vbar ⊔ zpowers wb with hTb
  have hwb2 : IsPGroup 2 (zpowers wb) :=
    IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  have hTb2 : IsPGroup 2 Tb := IsPGroup.to_sup_of_normal_left' w.isPGroup_Vbar hwb2
    ((zpowers_le).mpr (Subgroup.mem_normalizer_fintype fun v hv => hwbV v hv))
  set T : Subgroup G := Y ⊓ (Tb.comap w.projBar).map w.N.subtype with hT
  have hmemT : ∀ y : G, y ∈ T ↔ ∃ hy : y ∈ Y, w.projBar ⟨y, hYN hy⟩ ∈ Tb := by
    intro y
    constructor
    · rintro ⟨hyY, ⟨z, hz, rfl⟩⟩
      exact ⟨hyY, hz⟩
    · rintro ⟨hyY, hyT⟩
      exact ⟨hyY, ⟨⟨y, hYN hyY⟩, hyT, rfl⟩⟩
  have hT2 : IsPGroup 2 T := by
    rintro ⟨y, hyT⟩
    obtain ⟨hyY, hyTb⟩ := (hmemT y).mp hyT
    obtain ⟨k, hk⟩ := hTb2 ⟨_, hyTb⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : w.projBar ⟨y ^ 2 ^ k, hYN (pow_mem hyY _)⟩ = 1 := by
      have : (⟨y ^ 2 ^ k, hYN (pow_mem hyY _)⟩ : w.N) = ⟨y, hYN hyY⟩ ^ 2 ^ k :=
        Subtype.ext (by simp)
      rw [this, map_pow]
      exact congrArg Subtype.val hk
    exact hone _ (pow_mem hyY _) h1
  have hW2 : IsPGroup 2 w.W := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]; exact w.elem.2 x x.2)⟩
  have hTN : T ≤ w.N := fun y hy => hYN hy.1
  have hS'2 : IsPGroup 2 (w.W ⊔ T : Subgroup G) := IsPGroup.to_sup_of_normal_left' hW2 hT2 hTN
  have hS'N : w.W ⊔ T ≤ w.N := sup_le w.W_le_N hTN
  obtain ⟨Q, hQ⟩ := (hS'2.comap_subtype (K := w.N)).exists_le_sylow
  set S₁ := (Q : Subgroup w.N).map w.N.subtype with hS₁def
  have hS₁ : IsSylowOf 2 S₁ w.N := ⟨Q, rfl⟩
  have hS'S₁ : w.W ⊔ T ≤ S₁ := fun x hx => ⟨⟨x, hS'N hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩
  have hw₁T : w₁ ∈ T := (hmemT w₁).mpr ⟨hw₁Y, by rw [hw₁e]; exact mem_sup_right (mem_zpowers wb)⟩
  have hw₁S₁ : w₁ ∈ S₁ := hS'S₁ (mem_sup_right hw₁T)
  have hEN : w.N ≤ normalizer (E : Set G) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    obtain ⟨heN, heE⟩ := (w.mem_Ehat _).mp he
    refine (w.mem_Ehat _).mpr ⟨mul_mem (mul_mem hn heN) (inv_mem hn), ?_⟩
    have : w.projBar ⟨n * e * n⁻¹, mul_mem (mul_mem hn heN) (inv_mem hn)⟩ =
        w.projBar ⟨n, hn⟩ * w.projBar ⟨e, heN⟩ * (w.projBar ⟨n, hn⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact (inferInstance : (w.Ebar D.lev.range).Normal).conj_mem _ heE _
  have hS₀ : IsSylowOf 2 (S₁ ⊓ E) E := hS₁.inf_of_le_normalizer (w.Ehat_le_N _) hEN
  refine ⟨C, C.ψ_conj_t, fun x hx hx2 => C.exists_conj_tbar hx hx2, w₁, hw₁N, S₁, S₁ ⊓ E, ?_, ?_,
    hS₁, hS₀, rfl, ?_, ?_, ?_, ?_⟩
  ·
    rw [hw₁e]
    exact sup_eq_left.mpr ((zpowers_le).mpr (mem_sup_right htwb))
  · rw [hw₁e, eq_bot_iff]
    rintro x ⟨hxE, hxw⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxw
    exact hwbE j hxE
  ·
    apply le_antisymm
    · intro s hs
      have hsN : s ∈ w.N := hS₁.le hs
      set Sb : Subgroup w.Nbar := (S₁.subgroupOf w.N).map w.projBar with hSb
      have hSb2 : IsPGroup 2 Sb := (hS₁.isPGroup.comap_subtype (K := w.N)).map _
      have hwbSb : wb ∈ Sb := ⟨⟨w₁, hw₁N⟩, mem_subgroupOf.mpr hw₁S₁, hw₁e⟩
      obtain ⟨j, hj⟩ := hdecS Sb hSb2 hwbSb _ ⟨⟨s, hsN⟩, mem_subgroupOf.mpr hs, rfl⟩
      have hsw : s * w₁ ^ (-j) ∈ S₁ ⊓ E := by
        refine ⟨mul_mem hs (zpow_mem hw₁S₁ _), (w.mem_Ehat _).mpr ⟨mul_mem hsN (zpow_mem hw₁N _),
          ?_⟩⟩
        have : w.projBar ⟨s * w₁ ^ (-j), mul_mem hsN (zpow_mem hw₁N _)⟩ =
            w.projBar ⟨s, hsN⟩ * wb ^ (-j) := by
          rw [← hw₁pow, ← map_mul]
          rfl
        rw [this]
        exact hj
      have : s = (s * w₁ ^ (-j)) * w₁ ^ j := by group
      rw [this]
      exact mul_mem (mem_sup_left hsw) (mem_sup_right (zpow_mem (mem_zpowers _) _))
    · exact sup_le inf_le_left ((zpowers_le).mpr hw₁S₁)
  ·
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hxE⟩, hxw⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxw
    obtain ⟨hxN, hxE'⟩ := (w.mem_Ehat _).mp hxE
    have h2 : wb ^ j ∈ w.Ebar D.lev.range := by rw [← hw₁pow]; exact hxE'
    exact mem_bot.mpr (hone _ (zpow_mem hw₁Y j) (by rw [hw₁pow, hwbE j h2]))
  ·
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp htwb
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, hinjY _ (zpow_mem hw₁Y j) _ htY ?_⟩
    rw [hw₁pow, hj]
  ·
    intro v hv
    have hvN : v ∈ w.N := WData.V_le_N hR hW w hv
    obtain ⟨a, ha, y, hy, hvay⟩ := hdec v hvN
    have hyv : w.projBar ⟨y, hYN hy⟩ = w.projBar ⟨v, hvN⟩ := by
      rw [w.projBar_eq_iff]
      change y⁻¹ * v ∈ w.W
      rw [hvay, show y⁻¹ * (a * y) = y⁻¹ * a * y⁻¹⁻¹ by group]
      exact (mem_normalizer_iff.mp (inv_mem (hYN hy)) a).mp ha
    have hvVb : w.projBar ⟨v, hvN⟩ ∈ w.Vbar := ⟨⟨v, hvN⟩, mem_subgroupOf.mpr hv, rfl⟩
    have hyT : y ∈ T := (hmemT y).mpr ⟨hy, by rw [hyv]; exact mem_sup_left hvVb⟩
    refine ⟨?_, (w.mem_Ehat _).mpr ⟨hvN, hVE hvVb⟩⟩
    rw [hvay]
    exact hS'S₁ (mul_mem (mem_sup_left ha) (mem_sup_right hyT))

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree
