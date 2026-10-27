module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Aut
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped commutatorElement

section Model

theorem isCyclic_ringEquiv_of_unitaryFieldData {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) : IsCyclic (K ≃+* K) := by
  obtain ⟨σ, -, -, hσ, -⟩ := finite_field_automorphism_fixed_field_cardinality h.prime
    (by have := h.one_le; omega) h.card
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩

theorem exists_mulEquiv_gramSU {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : CFSG.Blueprint.LieModel X .PSU 4 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K),
      Nonempty (X ≃* gramSU h (miyamotoJ4 K)) := by
  rcases hX with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 f K :=
      ⟨Nat.prime_two, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) h
    obtain ⟨W, hW⟩ := exists_isGramHypTransport (r := 2) (ε := 0) h (miyamotoJ4 K)
      (miyamotoJ4_conjTranspose h) det_miyamotoJ4_ne_zero
    have e₁ := (hypPSUEquivStatedProj h hR (by norm_num)).symm
    have e₂ : hypPSU h 2 0 ≃* primeFormP h (miyamotoJ4 K) :=
      (gramHypProjEquiv (r := 2) (ε := 0) h (miyamotoJ4 K) hW).symm
    exact ⟨K, _, h, ⟨(e.trans e₁).trans (e₂.trans (miyamotoProjEquiv h).symm)⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
  {L : Subgroup G}

theorem center_eq_bot_of_mulEquiv_gramSU (η : L ≃* gramSU h (miyamotoJ4 K)) : center L = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have h1 : MulAut.conj (η z) = 1 := by
    refine MulEquiv.ext fun g => ?_
    obtain ⟨l, rfl⟩ := η.surjective g
    rw [MulAut.conj_apply, MulAut.one_apply, ← map_mul, ← map_inv, ← map_mul,
      ← mem_center_iff.1 hz l, mul_inv_cancel_right]
  exact η.map_eq_one_iff.1 ((conj_eq_one_iff h (η z)).1 h1)

theorem inf_centralizer_eq_bot_of_mulEquiv_gramSU (η : L ≃* gramSU h (miyamotoJ4 K)) :
    L ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : L) ∈ center L :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)
  rw [center_eq_bot_of_mulEquiv_gramSU h η, mem_bot] at hx
  exact mem_bot.2 (congrArg Subtype.val hx)

theorem isSylowOf_miyamotoPG (η : L ≃* gramSU h (miyamotoJ4 K)) :
    IsSylowOf 2 (miyamotoPG h L η) L := by
  obtain ⟨S, hS⟩ := exists_sylow_miyamotoPG h L η
  exact ⟨S, by rw [hS, subgroupOf_map_subtype, inf_eq_left.2 (miyamotoPull_le h L η _)]⟩

end Model

theorem commutatorElement_mul_mul_eq_of_commute {G : Type*} [Group G] {a b c d : G}
    (hcb : c * b = b * c) (hcd : c * d = d * c) (hda : d * a = a * d) :
    ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hda' : d * a⁻¹ = a⁻¹ * d := (Commute.inv_right (hda : Commute d a)).eq
  calc ⁅a * c, b * d⁆ = a * (c * b) * d * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = a * b * (c * d) * c⁻¹ * a⁻¹ * d⁻¹ * b⁻¹ := by rw [hcb]; group
    _ = a * b * (d * a⁻¹) * d⁻¹ * b⁻¹ := by rw [hcd]; group
    _ = ⁅a, b⁆ := by rw [hda', commutatorElement_def]; group

abbrev miyamotoZG {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
    (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) : Subgroup G :=
  miyamotoPull h L η (miyamotoZ h)

instance normal_zpowers_subgroupOf_centralizer_self {G : Type*} [Group G] (t : G) :
    ((zpowers t).subgroupOf (centralizer ({t} : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hn
  have hgt : (g : G) * t = t * g := mem_centralizer_singleton_iff.1 g.2
  have e : (g : G) * n * (g : G)⁻¹ = n := by
    rw [← hk, (Commute.zpow_right hgt k).eq, mul_inv_cancel_right]
  rw [coe_mul, coe_mul, coe_inv, e]
  exact hn

structure Setting {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q T : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  oddCore : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥
  setup : MiyamotoSetup h L η t Q T

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem two_le (hS : Setting h L η t Q T) : 2 ≤ f := hS.setup.1

theorem four_le (hS : Setting h L η t Q T) : 4 ≤ 2 ^ f :=
  (Nat.pow_le_pow_right two_pos hS.two_le).trans_eq' (by norm_num)

theorem standard (hS : Setting h L η t Q T) : standardComponentIsStandard L := hS.setup.2.1

theorem exists_isCyclic (hS : Setting h L η t Q T) :
    ∃ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) :=
  hS.setup.2.2.2.2.1

theorem t_mem (hS : Setting h L η t Q T) : t ∈ centralizer (L : Set G) :=
  hS.setup.2.2.2.2.2.1

theorem t_two (hS : Setting h L η t Q T) : orderOf t = 2 := hS.setup.2.2.2.2.2.2.1

theorem Q_le (hS : Setting h L η t Q T) : Q ≤ L ⊔ centralizer (L : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, hQ, -⟩ := hS.setup
  exact hQ

theorem Q_sylow (hS : Setting h L η t Q T) : IsSylowOf 2 Q (L ⊔ centralizer (L : Set G)) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨S, hSQ⟩, -⟩ := hS.setup
  exact ⟨S, by rw [hSQ, subgroupOf_map_subtype, inf_eq_left.2 hS.Q_le]⟩

theorem t_mem_Q (hS : Setting h L η t Q T) : t ∈ Q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, ht, -⟩ := hS.setup
  exact ht

theorem P_le_Q (hS : Setting h L η t Q T) : miyamotoPG h L η ≤ Q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hP, -⟩ := hS.setup
  exact hP

theorem T_le (hS : Setting h L η t Q T) : T ≤ centralizer ({t} : Set G) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hT, -⟩ := hS.setup
  exact hT

theorem T_sylow (hS : Setting h L η t Q T) : IsSylowOf 2 T (centralizer ({t} : Set G)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨S, hST⟩, -⟩ := hS.setup
  exact ⟨S, by rw [hST, subgroupOf_map_subtype, inf_eq_left.2 hS.T_le]⟩

theorem Q_le_T (hS : Setting h L η t Q T) : Q ≤ T := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hQT⟩ := hS.setup
  exact hQT

theorem inf_centralizer_eq_bot (_hS : Setting h L η t Q T) : L ⊓ centralizer (L : Set G) = ⊥ :=
  inf_centralizer_eq_bot_of_mulEquiv_gramSU h η

theorem t_ne_one (hS : Setting h L η t Q T) : t ≠ 1 := fun h1 => by
  have := hS.t_two
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem t_mul_t (hS : Setting h L η t Q T) : t * t = 1 := by
  rw [← sq, ← hS.t_two, pow_orderOf_eq_one]

theorem t_inv (hS : Setting h L η t Q T) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right hS.t_mul_t

theorem t_not_mem_L (hS : Setting h L η t Q T) : t ∉ L := fun htL => by
  have : t ∈ L ⊓ centralizer (L : Set G) := ⟨htL, hS.t_mem⟩
  rw [hS.inf_centralizer_eq_bot, mem_bot] at this
  exact hS.t_ne_one this

theorem card_zpowers_t (hS : Setting h L η t Q T) : Nat.card (zpowers t) = 2 := by
  rw [Nat.card_zpowers, hS.t_two]

theorem t_mem_T (hS : Setting h L η t Q T) : t ∈ T := hS.Q_le_T hS.t_mem_Q

theorem P_le_T (hS : Setting h L η t Q T) : miyamotoPG h L η ≤ T := hS.P_le_Q.trans hS.Q_le_T

theorem Q_le_centralizer (hS : Setting h L η t Q T) : Q ≤ centralizer ({t} : Set G) :=
  hS.Q_le_T.trans hS.T_le

theorem isPGroup_Q (hS : Setting h L η t Q T) : IsPGroup 2 Q := hS.Q_sylow.isPGroup

theorem isPGroup_T (hS : Setting h L η t Q T) : IsPGroup 2 T := hS.T_sylow.isPGroup

theorem isSylowOf_P (_hS : Setting h L η t Q T) : IsSylowOf 2 (miyamotoPG h L η) L :=
  isSylowOf_miyamotoPG h η

theorem Q_inf_L (hS : Setting h L η t Q T) : Q ⊓ L = miyamotoPG h L η := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hS.isSylowOf_P.eq_of_le (le_inf hS.P_le_Q (miyamotoPull_le h L η _)) inf_le_right
    hS.isPGroup_Q.to_inf_left

theorem A1_le_centralizer_zpowers (hS : Setting h L η t Q T) :
    miyamotoA1G h L η ≤ centralizer (zpowers t : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hat : t * a = a * t := (mem_centralizer_iff.1 hS.t_mem a (miyamotoPull_le h L η _ ha)).symm
  exact (Commute.zpow_left hat k).eq

theorem isElementaryAbelian_B1 (hS : Setting h L η t Q T) :
    CFSG.IsElementaryAbelian 2 (miyamotoB1 h L η t) := by
  have : CFSG.IsElementaryAbelian 2 (zpowers t) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hS.t_two, pow_orderOf_eq_one])
  have := isElementaryAbelian_miyamotoA1G h L η
  exact CFSG.IsElementaryAbelian.sup_of_le_centralizer hS.A1_le_centralizer_zpowers

theorem card_B1 (hS : Setting h L η t Q T) : Nat.card (miyamotoB1 h L η t) = 2 * (2 ^ f) ^ 4 := by
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers t)
    (miyamotoA1G h L η) fun x hx y hy =>
      mem_centralizer_iff.1 (hS.A1_le_centralizer_zpowers hy) x hx
  have hinf : zpowers t ⊓ miyamotoA1G h L η = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxt, hxA⟩
    rw [mem_bot]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    have hk : t ^ k = t ^ (k % 2) := by
      rw [← zpow_mod_orderOf, hS.t_two]
      norm_cast
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [hk, h0, zpow_zero]
    · rw [hk, h1, zpow_one] at hxA
      exact absurd (miyamotoPull_le h L η _ hxA) hS.t_not_mem_L
  rw [hinf, Subgroup.card_bot, mul_one, hS.card_zpowers_t, card_miyamotoA1G] at hc
  exact hc

theorem B1_le_Q (hS : Setting h L η t Q T) : miyamotoB1 h L η t ≤ Q :=
  sup_le ((zpowers_le).2 hS.t_mem_Q)
    ((miyamotoPull_mono h L η (miyamotoA1_le_P h)).trans hS.P_le_Q)

theorem centralizer_le_normalizer (hS : Setting h L η t Q T) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  (standard_involution_centralizer_normality hS.standard hS.t_mem hS.t_two).1

theorem L_le_centralizer (hS : Setting h L η t Q T) : L ≤ centralizer ({t} : Set G) :=
  (standard_involution_centralizer_normality hS.standard hS.t_mem hS.t_two).2.1

theorem t_mem_centralizer (_hS : Setting h L η t Q T) : t ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem isCyclic_sylow (hS : Setting h L η t Q T) (S : Sylow 2 (centralizer (L : Set G))) :
    IsCyclic (S : Subgroup (centralizer (L : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := hS.exists_isCyclic
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (centralizer (L : Set G)) S₀ S
  rw [Sylow.coe_subgroup_smul]
  exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap
    (S₀ : Subgroup (centralizer (L : Set G)))) (MonoidHom.subgroupMap_surjective _ _)

theorem kernel (hS : Setting h L η t Q T) :
    IsCyclic (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      IsPGroup 2 (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      (∀ x ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), orderOf x = 2 → x = t) ∧
      ((centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).subgroupOf
        (centralizer ({t} : Set G))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tc : centralizer (L : Set G) := ⟨t, hS.t_mem⟩ with htc
  have htc2 : orderOf tc = 2 := by rw [← orderOf_coe]; exact hS.t_two
  have hz : IsPGroup 2 (zpowers tc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htc2, pow_one])
  obtain ⟨S, hSt⟩ := hz.exists_le_sylow
  have htS : tc ∈ S := hSt (mem_zpowers _)
  have hSc := hS.isCyclic_sylow S
  obtain ⟨-, huniq, -, -, -, -, hR, hRn, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      hS.standard S hSc htS htc2 (hS.oddCore t hS.t_two)
  have hR' : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) =
      (S : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype := hR
  rw [hR']
  refine ⟨isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _),
    S.isPGroup'.map _, ?_, hRn⟩
  rintro _ ⟨y, hy, rfl⟩ hy2
  rw [Subgroup.subtype_apply, orderOf_coe] at hy2
  exact congrArg Subtype.val (huniq y hy hy2)

theorem isCyclic_kernel (hS : Setting h L η t Q T) :
    IsCyclic (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :=
  hS.kernel.1

theorem isPGroup_kernel (hS : Setting h L η t Q T) :
    IsPGroup 2 (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) :=
  hS.kernel.2.1

theorem t_mem_kernel (hS : Setting h L η t Q T) :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
  ⟨hS.t_mem, hS.t_mem_centralizer⟩

theorem zpowers_le_kernel (hS : Setting h L η t Q T) :
    zpowers t ≤ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
  (zpowers_le).2 hS.t_mem_kernel

theorem kernel_comm (hS : Setting h L η t Q T) {c d : G}
    (hc : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G))
    (hd : d ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) : c * d = d * c := by
  have := hS.isCyclic_kernel
  exact congrArg Subtype.val (mul_comm' (⟨c, hc⟩ :
    (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G)) ⟨d, hd⟩)

theorem eq_t_of_mem_kernel (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) (hx2 : orderOf x = 2) :
    x = t :=
  hS.kernel.2.2.1 x hx hx2

@[expose] def act (hS : Setting h L η t Q T) :
    centralizer ({t} : Set G) →* MulAut (gramSU h (miyamotoJ4 K)) :=
  (miyamotoAct h L η).comp (inclusion hS.centralizer_le_normalizer)

theorem act_apply (hS : Setting h L η t Q T) (x : centralizer ({t} : Set G)) :
    hS.act x = miyamotoAct h L η ⟨x, hS.centralizer_le_normalizer x.2⟩ :=
  rfl

theorem coe_symm_act_apply (hS : Setting h L η t Q T) (x : centralizer ({t} : Set G))
    (g : gramSU h (miyamotoJ4 K)) :
    ((η.symm (hS.act x g) : L) : G) = x * (η.symm g : G) * (x : G)⁻¹ :=
  coe_symm_miyamotoAct_apply h L η _ g

theorem act_eq_one_iff (hS : Setting h L η t Q T) (x : centralizer ({t} : Set G)) :
    hS.act x = 1 ↔ (x : G) ∈ centralizer (L : Set G) :=
  miyamotoAct_eq_one_iff h L η _

theorem act_of_mem (hS : Setting h L η t Q T) {l : G} (hl : l ∈ L) :
    hS.act ⟨l, hS.L_le_centralizer hl⟩ = MulAut.conj (η ⟨l, hl⟩) :=
  miyamotoAct_mem h L η ⟨l, hl⟩

@[expose] def fieldFactor (hS : Setting h L η t Q T) : centralizer ({t} : Set G) →* (K ≃+* K) :=
  (miyamotoFieldFactor h).comp hS.act

theorem fieldFactor_apply (hS : Setting h L η t Q T) (x : centralizer ({t} : Set G)) :
    hS.fieldFactor x = miyamotoFieldFactorG h L η ⟨x, hS.centralizer_le_normalizer x.2⟩ :=
  rfl

theorem exists_act_eq (hS : Setting h L η t Q T) (x : centralizer ({t} : Set G)) :
    ∃ s : gramSU h (miyamotoJ4 K),
      hS.act x = MulAut.conj s * miyamotoFieldAut h (hS.fieldFactor x) :=
  exists_eq_conj_mul_fieldAut h _

theorem fieldFactor_eq_one_iff (hS : Setting h L η t Q T) (x : centralizer ({t} : Set G)) :
    hS.fieldFactor x = 1 ↔ ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G),
      (x : G) = l * c := by
  rw [fieldFactor_apply, miyamotoFieldFactorG_eq_one_iff]
  constructor
  · rintro ⟨l, hl, c, hc, hx⟩
    refine ⟨l, hl, c, ⟨hc, ?_⟩, hx⟩
    have := mul_mem (inv_mem (hS.L_le_centralizer hl)) x.2
    rwa [show l⁻¹ * (x : G) = c by rw [hx]; group] at this
  · rintro ⟨l, hl, c, hc, hx⟩
    exact ⟨l, hl, c, hc.1, hx⟩

theorem fieldFactor_of_mem_L (hS : Setting h L η t Q T) {l : G} (hl : l ∈ L) :
    hS.fieldFactor ⟨l, hS.L_le_centralizer hl⟩ = 1 :=
  (hS.fieldFactor_eq_one_iff _).2 ⟨l, hl, 1, one_mem _, (mul_one l).symm⟩

theorem ker_fieldFactor (hS : Setting h L η t Q T) :
    hS.fieldFactor.ker = (L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))).subgroupOf
      (centralizer ({t} : Set G)) := by
  ext x
  rw [MonoidHom.mem_ker, fieldFactor_eq_one_iff, mem_subgroupOf]
  constructor
  · rintro ⟨l, hl, c, hc, hx⟩
    rw [hx]
    exact mul_mem (mem_sup_left hl) (mem_sup_right hc)
  · intro hx
    have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L
      (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))
      fun l hl c hc => mem_centralizer_iff.1 hc.1 l hl).2
    have hx' : (x : G) ∈ ((L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :
        Subgroup G) : Set G) := hx
    rw [hset] at hx'
    obtain ⟨l, hl, c, hc, hlc⟩ := hx'
    exact ⟨l, hl, c, hc, hlc.symm⟩

theorem commutator_L (hS : Setting h L η t Q T) : ⁅L, L⁆ = L := by
  have h1 : commutator L = ⊤ := hS.standard.1.1
  have h2 := congrArg (Subgroup.map L.subtype) h1
  rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2

theorem perfect_le (hS : Setting h L η t Q T) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPC : P ≤ centralizer ({t} : Set G)) : P ≤ L := by
  have := isCyclic_ringEquiv_of_unitaryFieldData h
  have hker : P ≤ (hS.fieldFactor.ker).map (centralizer ({t} : Set G)).subtype := by
    rw [← hP, commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, hPC ha⟩ : centralizer ({t} : Set G)), ⟨b, hPC hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' _ _
  have hdec : ∀ p ∈ P, ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G),
      p = l * c := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := hker hp
    exact (hS.fieldFactor_eq_one_iff x).1 hx
  rw [← hP, commutator_le]
  intro a ha b hb
  obtain ⟨l, hl, c, hc, rfl⟩ := hdec a ha
  obtain ⟨l', hl', c', hc', rfl⟩ := hdec b hb
  rw [commutatorElement_mul_mul_eq_of_commute (mem_centralizer_iff.1 hc.1 l' hl').symm
    (hS.kernel_comm hc hc') (mem_centralizer_iff.1 hc'.1 l hl).symm]
  have hll := commutator_mem_commutator hl hl'
  rwa [hS.commutator_L] at hll

end Setting

theorem exists_setting {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G} {f : ℕ} (hf : 2 ≤ f)
    (hL : standardComponentIsStandard L)
    (hcore : ∀ x : G, orderOf x = 2 → standardComponentOddCore (centralizer ({x} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hSc : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hm : CFSG.Blueprint.LieModel L .PSU 4 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K) (η : L ≃* gramSU h (miyamotoJ4 K))
      (t : G) (Q T : Subgroup G), Setting h L η t Q T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, h, ⟨η⟩⟩ := exists_mulEquiv_gramSU (by omega) hm
  obtain ⟨-, tc, htS, ht2, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_sylow_unique_involution
      hL S hSc
  set t : G := (tc : G) with htdef
  have ht2' : orderOf t = 2 := by rw [htdef, orderOf_coe]; exact ht2
  set SG : Subgroup G := (S : Subgroup (centralizer (L : Set G))).map
    (centralizer (L : Set G)).subtype with hSG
  have hSGC : SG ≤ centralizer (L : Set G) := map_subtype_le _
  have hSGsyl : IsSylowOf 2 SG (centralizer (L : Set G)) := ⟨S, rfl⟩
  have htSG : t ∈ SG := ⟨tc, htS, rfl⟩
  have hSGt : SG ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    have e : (⟨s, hs⟩ : (S : Subgroup (centralizer (L : Set G)))) * ⟨tc, htS⟩ =
        ⟨tc, htS⟩ * ⟨s, hs⟩ := mul_comm' _ _
    exact mem_centralizer_singleton_iff.2
      (congrArg (fun z : (S : Subgroup (centralizer (L : Set G))) =>
        ((z : centralizer (L : Set G)) : G)) e)
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ := inf_centralizer_eq_bot_of_mulEquiv_gramSU h η
  have hcomm : ∀ x ∈ L, ∀ y ∈ centralizer (L : Set G), x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.1 hy x hx
  have hcardLC : Nat.card (L ⊔ centralizer (L : Set G) : Subgroup G) =
      Nat.card L * Nat.card (centralizer (L : Set G)) := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute L _ hcomm).1
    rwa [hLC, Subgroup.card_bot, mul_one] at this
  set P := miyamotoPG h L η with hPdef
  have hPL : P ≤ L := miyamotoPull_le h L η _
  have hPsyl : IsSylowOf 2 P L := isSylowOf_miyamotoPG h η
  set Q : Subgroup G := P ⊔ SG with hQdef
  have hPSG : P ⊓ SG = ⊥ := le_bot_iff.1 ((inf_le_inf hPL hSGC).trans hLC.le)
  have hcardQ : Nat.card Q = Nat.card P * Nat.card SG := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute P SG
      fun x hx y hy => hcomm x (hPL hx) y (hSGC hy)).1
    rwa [hPSG, Subgroup.card_bot, mul_one] at this
  have hQLC : Q ≤ L ⊔ centralizer (L : Set G) := sup_le_sup hPL hSGC
  have hQsyl : IsSylowOf 2 Q (L ⊔ centralizer (L : Set G)) := by
    refine isSylowOf_of_card hQLC ?_
    rw [hcardQ, hPsyl.card_eq, hSGsyl.card_eq, hcardLC,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add]
  have hLt : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 tc.2 l hl)
  have hQt : Q ≤ centralizer ({t} : Set G) := sup_le (hPL.trans hLt) hSGt
  obtain ⟨T₀, hT₀⟩ :=
    (hQsyl.isPGroup.comap_subtype (K := centralizer ({t} : Set G))).exists_le_sylow
  set T : Subgroup G := (T₀ : Subgroup (centralizer ({t} : Set G))).map
    (centralizer ({t} : Set G)).subtype with hTdef
  have hTt : T ≤ centralizer ({t} : Set G) := map_subtype_le _
  have hQT : Q ≤ T := fun x hx => ⟨⟨x, hQt hx⟩, hT₀ hx, rfl⟩
  have hLn : ¬ L.Normal := fun hN => by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hb | htop
    · have hnt := hL.1.2.toNontrivial
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      refine hab (congrArg _ (Subtype.ext ?_))
      rw [(Subgroup.eq_bot_iff_forall L).1 hb _ a'.2, (Subgroup.eq_bot_iff_forall L).1 hb _ b'.2]
    · have hC : centralizer (L : Set G) = ⊥ := by
        rw [htop, coe_top, centralizer_univ]
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
        · exact hc
        · exfalso
          obtain ⟨a, b, hab⟩ := hnonab
          exact hab (mem_center_iff.1 (hc ▸ mem_top a : a ∈ center G) b).symm
      have heven := hL.2.1
      rw [hC, Subgroup.card_bot] at heven
      exact Nat.not_even_one heven
  have hevenG : Even (Nat.card G) := by
    have := hL.2.1
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 this).trans (Subgroup.card_subgroup_dvd_card _))
  have hpp : CFSG.pPrimeCore 2 G = ⊥ := by
    refine le_bot_iff.1 (sSup_le fun N hN => ?_)
    have := hN.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | htop
    · exact hb.le
    · exfalso
      have h1 := hN.2
      rw [htop, Subgroup.card_top] at h1
      exact (Nat.not_even_iff_odd.2 (Nat.coprime_two_left.1 h1)) hevenG
  refine ⟨K, _, h, η, t, Q, T, ‹IsSimpleGroup G›, hnonab, hcore, ?_⟩
  exact ⟨hf, hL, hLn, hpp, ⟨S, hSc⟩, tc.2, ht2', hQLC, hQsyl.exists_sylow_eq_subgroupOf,
    mem_sup_right htSG, le_sup_left, hTt,
    ⟨T₀, (comap_map_eq_self_of_injective (subtype_injective _) _).symm⟩, hQT⟩

end CFSG.LocalAnalysis.EvenBN.U4
