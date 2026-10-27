module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldCore

public noncomputable section

namespace CFSG.ComponentClassification.GHarris.E16

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X]

abbrev gM (A : Subgroup X) : Subgroup X := normalClosure (A : Set X)

@[expose] def gP (A : Subgroup X) : Subgroup X :=
  (CFSG.Open.pCore 2 (gM A)).map (gM A).subtype

@[expose] def gL (A : Subgroup X) : Subgroup X := (goldschmidtLayer (gM A)).map (gM A).subtype

@[expose] def gComp (A K : Subgroup X) : Prop :=
  ∃ K' : Subgroup (gM A), CFSG.Open.IsComponentOf K' ⊤ ∧ K'.map (gM A).subtype = K

omit [Finite X] in
theorem gP_normal (A : Subgroup X) : (gP A).Normal := by
  have : (CFSG.Open.pCore 2 (gM A)).Characteristic := by
    infer_instance
  exact ConjAct.normal_of_characteristic_of_normal

omit [Finite X] in
theorem gL_normal (A : Subgroup X) : (gL A).Normal := by
  have : (goldschmidtLayer (gM A)).Characteristic := Layer.characteristic _
  exact ConjAct.normal_of_characteristic_of_normal

theorem gP_comm_gL (A : Subgroup X) :
    ∀ p ∈ gP A, ∀ l ∈ gL A, p * l = l * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCore 2 (gM A) with hQ
  have hQn : Q.Normal := by
    rw [hQ]
    exact CFSG.pCore_normal
  have hQp : IsPGroup 2 Q := by
    rw [hQ]
    exact CFSG.pCore_isPGroup
  have : Group.IsNilpotent Q := hQp.isNilpotent
  have h := Layer.commutes_with_solvable_subnormal Q
    (Components.chain_of_mathlib_subnormal hQn.isSubnormal)
  rintro _ ⟨p, hp, rfl⟩ _ ⟨l, hl, rfl⟩
  have hc := (commutator_eq_bot_iff_le_centralizer.mp h) hl
  exact congrArg Subtype.val (mem_centralizer_iff.mp hc p hp)

omit [Finite X] in
theorem gL_isPerfect (A : Subgroup X) : Group.IsPerfect (gL A) := by
  have : Group.IsPerfect (Layer.subgroup (gM A)) := Layer.perfect _
  exact Group.IsPerfect.ofSurjective
    (f := ((Layer.subgroup (gM A)).equivMapOfInjective _ (subtype_injective _)).toMonoidHom)
    (MulEquiv.surjective _)

theorem oddCore_gM (hO : CFSG.pPrimeCore 2 X = ⊥) (A : Subgroup X) :
    CFSG.oddCore (gM A) = ⊥ := by
  have hX : componentClassificationOddCore X = ⊥ :=
    (CFSG.pPrimeCore_eq_bot_iff.mp hO) _ inferInstance
      (Nat.coprime_two_left.mpr (OddCore.odd_card X))
  have h := OddCore.normal_intersection X (gM A)
  rw [hX, inf_bot_eq] at h
  exact (map_eq_bot_iff_of_injective _ (subtype_injective _)).mp h

theorem gold_facts (hG : CFSG.Goldschmidt.TopStatement) (hO : CFSG.pPrimeCore 2 X = ⊥)
    (T : Sylow 2 X) {A : Subgroup X} (hAT : A ≤ T) (hAab : IsMulCommutative A)
    (hcl : ∀ a ∈ A, ∀ x : X, x⁻¹ * a * x ∈ (T : Subgroup X) → x⁻¹ * a * x ∈ A) :
    gM A = gP A ⊔ gL A ∧
      A = gP A ⊔ closure {t | t ∈ (T : Subgroup X) ⊓ gL A ∧ t ^ 2 = 1} ∧
      ∀ K' : Subgroup (gM A), CFSG.Open.IsComponentOf K' ⊤ →
        goldschmidtSimpleType (K' ⧸ center K') := by
  obtain ⟨h1, h2, h3⟩ := AschbacherTheorem3.goldschmidt_subgroup hG T hAT hAab hcl rfl
    (oddCore_gM hO A)
  refine ⟨?_, ?_, h3⟩
  · have h := congrArg (Subgroup.map (gM A).subtype) h1
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h.symm
  · have hAM : A ≤ gM A := le_normalClosure
    have h := congrArg (Subgroup.map (gM A).subtype) h2
    rw [map_subgroupOf_eq_of_le hAM, Subgroup.map_sup, MonoidHom.map_closure] at h
    refine h.trans (congrArg₂ (· ⊔ ·) rfl (congrArg Subgroup.closure ?_))
    ext x
    constructor
    · rintro ⟨y, ⟨⟨hyT, hyL⟩, hy2⟩, rfl⟩
      refine ⟨⟨mem_subgroupOf.mp hyT, ⟨y, hyL, rfl⟩⟩, ?_⟩
      change (y : X) ^ 2 = 1
      rw [← SubgroupClass.coe_pow, hy2, OneMemClass.coe_one]
    · rintro ⟨⟨hxT, ⟨y, hyL, rfl⟩⟩, hx2⟩
      refine ⟨y, ⟨⟨mem_subgroupOf.mpr hxT, hyL⟩, Subtype.ext ?_⟩, rfl⟩
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hx2

omit [Finite X] in
theorem gComp_le {A K : Subgroup X} (hK : gComp A K) : K ≤ gL A := by
  obtain ⟨K', hK', rfl⟩ := hK
  exact map_mono (Layer.component_le hK')

theorem gComp_comm {A K₁ K₂ : Subgroup X} (hK₁ : gComp A K₁) (hK₂ : gComp A K₂)
    (hne : K₁ ≠ K₂) : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
  obtain ⟨K₁', hK₁', rfl⟩ := hK₁
  obtain ⟨K₂', hK₂', rfl⟩ := hK₂
  have hne' : K₁' ≠ K₂' := fun h => hne (by rw [h])
  have h := LocalComponents.commute_of_ne K₁' K₂' hK₁' hK₂' hne'
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hc := (commutator_eq_bot_iff_le_centralizer.mp h) ha
  exact (congrArg Subtype.val (mem_centralizer_iff.mp hc b hb)).symm

omit [Finite X] in
theorem gL_eq_sSup (A : Subgroup X) : gL A = sSup {K | gComp A K} := by
  apply le_antisymm
  · rw [gL, goldschmidtLayer, map_le_iff_le_comap]
    refine sSup_le fun K' hK' => ?_
    rw [← map_le_iff_le_comap]
    exact le_sSup ⟨K', hK', rfl⟩
  · refine sSup_le fun K hK => ?_
    exact gComp_le hK

omit [Finite X] in
theorem mem_conj_iff {K : Subgroup X} {g y : X} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    change g⁻¹ * (g * k * g⁻¹) * g ∈ K
    rwa [show g⁻¹ * (g * k * g⁻¹) * g = k by group]
  · intro h
    exact ⟨_, h, by change g * (g⁻¹ * y * g) * g⁻¹ = y; group⟩

omit [Finite X] in
theorem gComp_conj {A K : Subgroup X} (hK : gComp A K) (g : X) :
    gComp A (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨K', hK', rfl⟩ := hK
  let φ : gM A ≃* gM A := MulAut.conjNormal g
  refine ⟨K'.map φ.toMonoidHom, (LocalComponents.equiv_iff φ K').mpr hK', ?_⟩
  have hφ : (gM A).subtype.comp φ.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (gM A).subtype :=
    MonoidHom.ext fun k => MulAut.conjNormal_apply g k
  rw [map_map, map_map, hφ]

omit [Finite X] in
theorem gComp_quasisimple {A K : Subgroup X} (hK : gComp A K) : CFSG.Open.IsQuasisimple K := by
  obtain ⟨K', hK', rfl⟩ := hK
  exact Components.quasisimple_of_equiv
    (K'.equivMapOfInjective _ (subtype_injective _)).symm hK'.2.2

omit [Finite X] in
theorem gComp_isSubnormal {A K : Subgroup X} (hK : gComp A K) : K.IsSubnormal := by
  obtain ⟨K', hK', rfl⟩ := hK
  exact (Components.mathlib_subnormal_of_chain hK'.2.1 Subgroup.IsSubnormal.top).trans'
    (inferInstance : (gM A).Normal).isSubnormal

theorem gComp_sylow {A K : Subgroup X} (hK : gComp A K) (T : Sylow 2 X) :
    ∃ Q : Sylow 2 K, (Q : Subgroup K).map K.subtype = (T : Subgroup X) ⊓ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T (gComp_isSubnormal hK)

omit [Finite X] in
theorem gComp_type {A K : Subgroup X}
    (hcomp : ∀ K' : Subgroup (gM A), CFSG.Open.IsComponentOf K' ⊤ →
      goldschmidtSimpleType (K' ⧸ center K'))
    (hK : gComp A K) (hZ : center K = ⊥) : goldschmidtSimpleType K := by
  obtain ⟨K', hK', rfl⟩ := hK
  let e : K' ≃* K'.map (gM A).subtype := K'.equivMapOfInjective _ (subtype_injective _)
  have hZ' : center K' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : e z ∈ center (K'.map (gM A).subtype) := by
      rw [mem_center_iff] at hz ⊢
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hz]
    rw [hZ, mem_bot] at h1
    exact mem_bot.mpr (e.injective (h1.trans (map_one e).symm))
  let e2 : K' ⧸ center K' ≃* K' :=
    (QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot
  exact AschbacherTheorem3.goldschmidtSimpleType_of_mulEquiv e.symm
    (AschbacherTheorem3.goldschmidtSimpleType_of_mulEquiv e2.symm (hcomp K' hK'))

end CFSG.ComponentClassification.GHarris.E16
