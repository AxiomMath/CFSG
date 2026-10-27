module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAutCore
public import CFSG.LocalAnalysis.OddStandard.GlueL34

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf HarrisLit.T1.SporRow
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def CTypeOrder (c : ℕ) : Prop :=
  OddLieOrder c ∨ (∃ n : ℕ, 7 ≤ n ∧ c = n.factorial / 2) ∨ c = 20160

theorem card_fusionZStar_eq (K : Type) [Group K] :
    Nat.card (K ⧸ Open.fusionZStar K) =
      Nat.card ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := by
  obtain ⟨e⟩ := GrSLit.nonempty_quotient_center_equiv_fusionZStar K
  exact (Nat.card_congr e.toEquiv).symm


theorem cTypeOrder_of_typC {K : Type} [Group K] (h : TypC K) :
    CTypeOrder (Nat.card (K ⧸ Open.fusionZStar K)) := by
  rcases h with ⟨t, n, p, f, hp, hp2, -, hL⟩ | ⟨n, hn, -, -, ⟨e⟩⟩ | ⟨hL, -⟩
  · exact Or.inl (oddLieOrder_of_lieModel hp hp2 hL)
  · refine Or.inr (Or.inl ⟨n, hn, ?_⟩)
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [card_fusionZStar_eq, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
      card_alternatingGroup, Fintype.card_fin]
  · exact Or.inr (Or.inr (by
      rw [card_fusionZStar_eq]
      exact OddStandard.GlueL34.card_eq_of_lieModel_psl34 hL))


structure Setting (Y : Type) [Group Y] (β : MulAut Y) (T : Subgroup Y) : Prop where
  quasisimple : IsQuasisimple Y
  oddCore : pPrimeCore 2 Y = ⊥
  inv : ∀ y, β (β y) = y
  le : T ≤ fixedSubgroup β
  comp : IsPComponent 2 (T.subgroupOf (fixedSubgroup β))
  center_ne : center (↥T ⧸ pPrimeCore 2 ↥T) ≠ ⊥
  typC : TypC ↥T

theorem map_pPrimeCore_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : (pPrimeCore 2 A).map e.toMonoidHom = pPrimeCore 2 B := by
  refine le_antisymm (GrSLit.map_pPrimeCore_le_pPrimeCore _ e.surjective) ?_
  have h1 := GrSLit.map_pPrimeCore_le_pPrimeCore e.symm.toMonoidHom e.symm.surjective
  intro x hx
  exact ⟨e.symm x, h1 (mem_map_of_mem _ hx), by simp⟩

@[expose] noncomputable def quotOddCoreEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (e : A ≃* B) : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B :=
  QuotientGroup.congr _ _ e (map_pPrimeCore_mulEquiv e)

namespace Setting

variable {Y : Type} [Group Y] {β : MulAut Y} {T : Subgroup Y}

theorem commutator_eq (h : Setting Y β T) : ⁅T, T⁆ = T := by
  have h1 := Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect h.comp)
  have h2 := congrArg (Subgroup.map (fixedSubgroup β).subtype) h1
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.le] at h2

theorem ne_bot (h : Setting Y β T) : T ≠ ⊥ := by
  rintro rfl
  apply h.center_ne
  have : Subsingleton ↥(⊥ : Subgroup Y) := by
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [mem_bot] at ha hb
    subst ha hb
    rfl
  exact Subgroup.eq_bot_of_subsingleton _

theorem eq_top_of_eq_one [Finite Y] (h : Setting Y β T) (hβ : β = 1) : T = ⊤ := by
  have hF : fixedSubgroup β = ⊤ := by
    subst hβ
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff]
    simp
  have hsub : T.IsSubnormal := by
    have h1 : (T.subgroupOf (fixedSubgroup β)).IsSubnormal := h.comp.choose_spec.2.1
    exact IsSubnormal.trans h.le h1 (hF ▸ IsSubnormal.top)
  have hs : IsSimpleGroup (Y ⧸ center Y) := h.quasisimple.2.1
  rcases (hsub.map (QuotientGroup.mk'_surjective (center Y))).eq_bot_or_top_of_isSimpleGroup hs
    with hb | ht
  · exfalso
    apply h.ne_bot
    have hTZ : T ≤ center Y := by
      intro x hx
      have : QuotientGroup.mk' (center Y) x ∈ T.map (QuotientGroup.mk' (center Y)) :=
        mem_map_of_mem _ hx
      rw [hb, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    rw [← h.commutator_eq, eq_bot_iff]
    rw [commutator_le]
    intro a ha b hb'
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact mem_center_iff.mp (hTZ hb') a
  · apply GrSLit.eq_top_of_sup_center_eq_top (Group.isPerfect_def.1 h.quasisimple.1)
    rw [eq_top_iff]
    intro y _
    have hy : QuotientGroup.mk' (center Y) y ∈ T.map (QuotientGroup.mk' (center Y)) := by
      rw [ht]
      exact mem_top _
    obtain ⟨t, ht', hty⟩ := hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hty
    have : y = t * (t⁻¹ * y) := by group
    rw [this]
    exact mul_mem (mem_sup_left ht') (mem_sup_right hty)

theorem isQuasisimple_quot [Finite Y] (h : Setting Y β T) :
    IsQuasisimple (T ⧸ pPrimeCore 2 T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ h.comp
  exact LocalCores.isQuasisimple_of_mulEquiv
    (quotOddCoreEquiv (subgroupOfEquivOfLe h.le)) hq

theorem card_ge [Finite Y] (h : Setting Y β T) : 120 ≤ Nat.card T := by
  have hq := h.isQuasisimple_quot
  set Q := T ⧸ pPrimeCore 2 T
  have h60 : 60 ≤ Nat.card (Q ⧸ center Q) :=
    GroupTheory.nonabelian_simple_order_at_least_sixty hq.2.1 hq.2.2
  have h2 : 2 ≤ Nat.card (center Q) := by
    have : Nontrivial (center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 h.center_ne
    exact Finite.one_lt_card
  have hQ : Nat.card Q = Nat.card (Q ⧸ center Q) * Nat.card (center Q) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hT : Nat.card T = Nat.card Q * Nat.card (pPrimeCore 2 T) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hO : 1 ≤ Nat.card (pPrimeCore 2 T) := Nat.card_pos
  nlinarith

end Setting

abbrev Quot (Y : Type) [Group Y] : Type :=
  (Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)

@[expose] noncomputable def rho (Y : Type) [Group Y] : Y →* Quot Y :=
  (QuotientGroup.mk' (center (Y ⧸ pPrimeCore 2 Y))).comp (QuotientGroup.mk' (pPrimeCore 2 Y))

theorem rho_surjective (Y : Type) [Group Y] : Function.Surjective (rho Y) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem ker_rho {Y : Type} [Group Y] (hO : pPrimeCore 2 Y = ⊥) : (rho Y).ker = center Y := by
  ext y
  rw [MonoidHom.mem_ker, rho, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_center_iff, mem_center_iff]
  constructor
  · intro h g
    have h1 := h (QuotientGroup.mk' (pPrimeCore 2 Y) g)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, hO, mem_bot, inv_mul_eq_one] at h1
    exact h1
  · intro h g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 Y) g
    rw [← map_mul, ← map_mul, h g]

@[expose] noncomputable def equivQuotOddCore {Y : Type*} [Group Y] (hO : pPrimeCore 2 Y = ⊥) :
    Y ≃* Y ⧸ pPrimeCore 2 Y :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)

theorem isQuasisimple_quot_oddCore {Y : Type} [Group Y] (hq : IsQuasisimple Y)
    (hO : pPrimeCore 2 Y = ⊥) : IsQuasisimple (Y ⧸ pPrimeCore 2 Y) :=
  LocalCores.isQuasisimple_of_mulEquiv (equivQuotOddCore hO) hq

@[expose] noncomputable def quotEquiv {Y : Type} [Group Y] (hO : pPrimeCore 2 Y = ⊥) :
    Quot Y ≃* Y ⧸ center Y :=
  (QuotientGroup.quotientKerEquivOfSurjective (rho Y) (rho_surjective Y)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_rho hO))

theorem isSimpleGroup_quot {Y : Type} [Group Y] (hq : IsQuasisimple Y) (hO : pPrimeCore 2 Y = ⊥) :
    IsSimpleGroup (Quot Y) :=
  (isQuasisimple_quot_oddCore hq hO).2.1

theorem nonabelian_quot {Y : Type} [Group Y] (hq : IsQuasisimple Y) (hO : pPrimeCore 2 Y = ⊥) :
    ∃ a b : Quot Y, a * b ≠ b * a :=
  (isQuasisimple_quot_oddCore hq hO).2.2

theorem exists_image {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y}
    (h : Setting Y β T) (hT : T ≠ ⊤) :
    ∃ σ : MulAut (Quot Y), ProperFixedComponent σ (T.map (rho Y)) ∧
      Nonempty (T ⧸ Open.fusionZStar T ≃* (T.map (rho Y)) ⧸ Open.fusionZStar (T.map (rho Y))) := by
  have hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 Y).index := by
    rw [h.oddCore, index_bot]
    calc (pPrimeCore 2 T).index ≤ Nat.card T :=
          Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
      _ < Nat.card (⊤ : Subgroup Y) := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hT)
      _ = Nat.card Y := Subgroup.card_top
  obtain ⟨σ, -, hσ, hPF, hP, hPne, he⟩ :=
    GrSLit.exists_simple_fixed_component_image (isQuasisimple_quot_oddCore h.quasisimple h.oddCore)
      β h.inv h.le h.comp hlt
  have hmap : (T.map (QuotientGroup.mk' (pPrimeCore 2 Y))).map
      (QuotientGroup.mk' (center (Y ⧸ pPrimeCore 2 Y))) = T.map (rho Y) := by
    rw [Subgroup.map_map]
    rfl
  rw [hmap] at hPF hP hPne he
  exact ⟨σ, ⟨hσ, hPF, hP, hPne⟩, he⟩

theorem pPrimeCore_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : pPrimeCore 2 A = ⊥) : pPrimeCore 2 B = ⊥ := by
  have h1 := GrSLit.map_pPrimeCore_le_pPrimeCore e.symm.toMonoidHom e.symm.surjective
  rw [h, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1 h1

theorem isPGroup_center_of_pPrimeCore_eq_bot {X : Type*} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥) : IsPGroup 2 (center X) := by
  intro z
  obtain ⟨i, m, hm, him⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  refine ⟨i, ?_⟩
  set w := z ^ 2 ^ i with hw
  have hwo : orderOf w = m := by
    rw [hw, orderOf_pow_of_dvd (by positivity) (by rw [him]; exact dvd_mul_right _ _), him,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hwN : (zpowers ((w : center X) : X)).Normal := by
    constructor
    intro n hn g
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    have hc := Subgroup.mem_center_iff.mp (zpow_mem w.2 k) g
    rw [hc, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k
  have hcop : Nat.Coprime 2 (Nat.card (zpowers ((w : center X) : X))) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hwo, Nat.coprime_two_left]
    exact hm
  have hle : zpowers ((w : center X) : X) ≤ CFSG.pPrimeCore 2 X := le_sSup ⟨hwN, hcop⟩
  rw [hO] at hle
  exact Subtype.ext (mem_bot.mp (hle (mem_zpowers _)))

theorem pPrimeCore_eq_bot_of_isPComponent {H : Type*} [Group H] [Finite H] {L : Subgroup H}
    (hL : IsPComponent 2 L) (hcore : CFSG.oddCore H = ⊥) : pPrimeCore 2 L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 L hL.choose_spec.2.1,
    ← Sporadic.HeldB.oddCore_eq_pPrimeCore_two', hcore, bot_subgroupOf]

theorem isQuasisimple_of_isPComponent {H : Type*} [Group H] [Finite H] {L : Subgroup H}
    (hL : IsPComponent 2 L) (hO : pPrimeCore 2 L = ⊥) : IsQuasisimple L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LocalCores.isQuasisimple_of_mulEquiv (equivQuotOddCore hO).symm
    (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 L hL)

structure Image {Y : Type} [Group Y] (β : MulAut Y) (T : Subgroup Y) (σ : MulAut (Quot Y)) :
    Prop where
  proper : ProperFixedComponent σ (T.map (rho Y))
  compP : IsComponent ((T.map (rho Y)).subgroupOf (fixedSubgroup σ))
  compT : IsComponent (T.subgroupOf (fixedSubgroup β))
  oddCoreP : pPrimeCore 2 (T.map (rho Y)) = ⊥
  oddCoreT : pPrimeCore 2 T = ⊥
  quasiP : IsQuasisimple (T.map (rho Y))
  quasiT : IsQuasisimple T
  card : Nat.card (T ⧸ center T) = Nat.card (T.map (rho Y) ⧸ center (T.map (rho Y)))
  fus : Nonempty (T ⧸ Open.fusionZStar T ≃* (T.map (rho Y)) ⧸ Open.fusionZStar (T.map (rho Y)))
  quotP : Nonempty ((T.map (rho Y)) ⧸ Open.fusionZStar (T.map (rho Y)) ≃*
    ((T.map (rho Y)).subgroupOf (fixedSubgroup σ)) ⧸
      center ((T.map (rho Y)).subgroupOf (fixedSubgroup σ)))
  centerT : center T ≠ ⊥

theorem exists_image_of_oddCore {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y}
    (h : Setting Y β T) (hT : T ≠ ⊤)
    (hfree : ∀ σ : MulAut (Quot Y), orderOf σ = 2 → CFSG.oddCore (fixedSubgroup σ) = ⊥) :
    ∃ σ : MulAut (Quot Y), Image β T σ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (Quot Y) := isSimpleGroup_quot h.quasisimple h.oddCore
  obtain ⟨σ, hP, ⟨eT⟩⟩ := exists_image h hT
  set P := T.map (rho Y) with hPdef
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => hP.1 y) hP.ne_one
  have hcore := hfree σ hσ2
  obtain ⟨hcompP, hquotP⟩ := hP.isComponent_of_oddCore hcore
  have hOL := pPrimeCore_eq_bot_of_isPComponent hP.2.2.1 hcore
  have hOP : pPrimeCore 2 P = ⊥ := pPrimeCore_eq_bot_of_mulEquiv (subgroupOfEquivOfLe hP.2.1) hOL
  have hOT : pPrimeCore 2 T = ⊥ := by
    have h1 := GrSLit.map_pPrimeCore_le_pPrimeCore ((rho Y).subgroupMap T)
      ((rho Y).subgroupMap_surjective T)
    rw [hOP, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
    have hZ2 : IsPGroup 2 (center Y) := isPGroup_center_of_pPrimeCore_eq_bot h.oddCore
    rw [eq_bot_iff]
    intro x hx
    have hxk : x ∈ ((rho Y).subgroupMap T).ker := h1 hx
    rw [MonoidHom.mem_ker] at hxk
    have hxZ : (x : Y) ∈ center Y := by
      rw [← ker_rho h.oddCore, MonoidHom.mem_ker]
      exact congrArg Subtype.val hxk
    obtain ⟨k, hk⟩ := hZ2 ⟨x, hxZ⟩
    have hk' : (x : Y) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hodd : Odd (Nat.card (pPrimeCore 2 T)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hord : orderOf (⟨x, hx⟩ : pPrimeCore 2 T) = orderOf (x : Y) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    have hdvd : orderOf (x : Y) ∣ Nat.card (pPrimeCore 2 T) :=
      hord ▸ orderOf_dvd_natCard _
    obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk')
    rw [hj'] at hdvd
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 ((dvd_pow_self 2 hj0).trans hdvd))
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj'
    rw [mem_bot]
    exact Subtype.ext hj'
  have hOLT : pPrimeCore 2 (T.subgroupOf (fixedSubgroup β)) = ⊥ :=
    pPrimeCore_eq_bot_of_mulEquiv (subgroupOfEquivOfLe h.le).symm hOT
  have hqLT := isQuasisimple_of_isPComponent h.comp hOLT
  have hqT : IsQuasisimple T := LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe h.le) hqLT
  have hqP : IsQuasisimple P :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hP.2.1) hcompP.1
  have hZT : Open.fusionZStar T = center T :=
    fusionZStar_eq_center_of_quasisimple hqT (by
      have := LocalCores.isQuasisimple_nontrivial hqT
      rw [hOT]; exact bot_ne_top)
  have hZP : Open.fusionZStar P = center P :=
    fusionZStar_eq_center_of_quasisimple hqP (by
      have := LocalCores.isQuasisimple_nontrivial hqP
      rw [hOP]; exact bot_ne_top)
  have hcard : Nat.card (T ⧸ center T) = Nat.card (P ⧸ center P) := by
    rw [← hZT, ← hZP]
    exact Nat.card_congr eT.toEquiv
  have hcT : center T ≠ ⊥ := by
    intro hc
    apply h.center_ne
    have e1 : T ≃* T ⧸ pPrimeCore 2 T := equivQuotOddCore hOT
    rw [← Subgroup.map_center_eq e1, hc, Subgroup.map_bot]
  exact ⟨σ, ⟨hP, hcompP, ⟨hqLT, h.comp.choose_spec.2.1⟩, hOP, hOT, hqP, hqT, hcard, ⟨eT⟩,
    hquotP, hcT⟩⟩

theorem isElementaryAbelian_center_of_card_le_two {K : Type*} [Group K] [Finite K]
    (h : Nat.card (center K) ≤ 2) : IsElementaryAbelian 2 (center K) := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun z => ?_
  have h1 : z ^ Nat.card (center K) = 1 := pow_card_eq_one'
  have h0 : 0 < Nat.card (center K) := Nat.card_pos
  interval_cases hc : Nat.card (center K)
  · rw [pow_one] at h1
    rw [h1, one_pow]
  · exact h1

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor
