module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MRowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.E6Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3B
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Seitz29Cat

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.Monster.Existence CFSG.Monster.Existence.Compat
  CFSG.Open CFSG.EvenSporadicStandard.Induction CFSG.Monster.GMS

abbrev BIsK : GroupClass := IsKPinned .B (· = 2 * ordTwistedE6 2)

@[expose] def BabyQuotient : Prop :=
  ∀ (u : Carrier .B) (K : Subgroup (Carrier .B)),
    PairShape (· = 2 * ordTwistedE6 2) (Carrier .B) ⊤ K u →
      LieModel (↥K ⧸ center ↥K) .twistedE6 0 2 1

@[expose] def E6CoverRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    LieModel (X ⧸ center X) .twistedE6 0 2 1 → 3 ≤ CFSG.pRank 2 X

@[expose] def E6InvolutionFixed : Prop :=
  ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
    LieModel (K₂ ⧸ center K₂) .twistedE6 0 2 1 → ∀ α : MulAut K₂, α ≠ 1 → α * α = 1 →
      ¬ Group.IsSolvable ↥(fixSubgroup α) ∨ ¬ ElemBound 4 ↥(fixSubgroup α) ∨
        ¬ TwoSubgroupsAbelian ↥(fixSubgroup α)

@[expose] def E6FourNoEvenCover : Prop :=
  ∀ (N : Type) [Group N], LieModel N .E6 0 2 2 → ¬ HasEvenCover N

structure BHyp31Inputs : Prop where
  cover : BabyCoverFacts
  mult : OddMultTrivial .B
  pair : BTwoAPair
  quotient : BabyQuotient
  bRank : BCoverRank
  e6Rank : E6CoverRank
  e6Fixed : E6InvolutionFixed
  e6Four : E6FourNoEvenCover
  noCover : MonsterNoCover
  evenB : EvenCoverOutHered [.M] .B

section BPairData

theorem finite_carrier_b (F : TwoAFacts) : Finite (Carrier .B) := by
  have h : Nat.card (Carrier .B) = monsterBabyOrder := F.b_card
  exact Nat.finite_of_card_ne_zero (by rw [h]; unfold monsterBabyOrder; norm_num)

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff Q).2.2.1.2 h

theorem babyCentOrder_zero : babyCentOrder 0 = 4 * ordTwistedE6 2 := by
  unfold babyCentOrder ordTwistedE6
  norm_num

theorem eq_zero_of_le_babyCentOrder {k : Fin 4} (h : ordTwistedE6 2 ≤ babyCentOrder k) : k = 0 := by
  fin_cases k
  · rfl
  all_goals
    exfalso
    unfold babyCentOrder ordTwistedE6 at h
    norm_num at h

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup in
theorem bPair_data (F : TwoAFacts) (hf : BabyCoverFacts) (bq : BabyQuotient)
    {u : Carrier .B} {K : Subgroup (Carrier .B)}
    (h : PairShape (· = 2 * ordTwistedE6 2) (Carrier .B) ⊤ K u) :
    CFSG.IsQuasisimple ↥K ∧ Nat.card (center ↥K) = 2 ∧
      LieModel (↥K ⧸ center ↥K) .twistedE6 0 2 1 ∧
        Nat.card ↥(centralizer ({u} : Set (Carrier .B))) = 4 * ordTwistedE6 2 ∧
          (K.subgroupOf (⊤ ⊓ centralizer ({u} : Set (Carrier .B)))).index = 2 := by
  have := finite_carrier_b F
  have hcov := hf.cover (Carrier .B) ⊤ K u ⟨Subgroup.topEquiv⟩ h
  have h0 := h
  obtain ⟨-, hu2, -, hKu, hcard⟩ := h
  have hKC : K ≤ ⊤ ⊓ centralizer ({u} : Set (Carrier .B)) := fun k hk =>
    ⟨mem_top _, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  let φ := Subgroup.subgroupOfEquivOfLe hKC
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ (isQuasisimple_of_open hcov.quasisimple), ?_,
    bq u K h0, ?_, hcov.index_eq⟩
  · rw [← card_center_of_mulEquiv' φ]
    exact hcov.card_center
  · have h1 := Subgroup.index_mul_card (K.subgroupOf (⊤ ⊓ centralizer ({u} : Set (Carrier .B))))
    rw [hcov.index_eq, Nat.card_congr φ.toEquiv] at h1
    rw [Nat.card_congr (MulEquiv.subgroupCongr
      (top_inf_eq (centralizer ({u} : Set (Carrier .B))))).toEquiv] at h1
    omega

end BPairData

section BKData

theorem normal_of_index_le_two {H : Type} [Group H] [Finite H] {N : Subgroup H}
    (hidx : N.index ≤ 2) : N.Normal := by
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    infer_instance
  · exact Subgroup.normal_of_index_eq_two h2

theorem eq_commutator_of_perfect_of_index_le_two {H : Type} [Group H] [Finite H]
    {C K : Subgroup H} (hKC : K ≤ C) (hidx : (K.subgroupOf C).index ≤ 2)
    (hperf : Group.IsPerfect ↥K) : K = ⁅C, C⁆ := by
  apply le_antisymm
  · calc K = ⁅K, K⁆ := (Subgroup.isPerfect_iff.1 hperf).symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hKC hKC
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hN : (K.subgroupOf C).Normal := normal_of_index_le_two hidx
    have hcomm : IsMulCommutative (↥C ⧸ K.subgroupOf C) :=
      isMulCommutative_of_card_le_four' (by
        have : Nat.card (↥C ⧸ K.subgroupOf C) = (K.subgroupOf C).index := rfl
        omega)
    have h1 : ((⟨x, hx⟩ : ↥C) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥C)⁻¹ * (⟨y, hy⟩ : ↥C)⁻¹) ∈
        K.subgroupOf C := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hcomm.is_comm.comm (QuotientGroup.mk ⟨x, hx⟩)]
      group
    exact mem_subgroupOf.1 h1

theorem even_ordTwistedE6_two : Even (ordTwistedE6 2) := by
  unfold ordTwistedE6
  decide

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup in
theorem pairShape_top_conj {H : Type} [Group H] {P : ℕ → Prop} {K : Subgroup H} {u : H} (c : H)
    (h : PairShape P H ⊤ K u) :
    PairShape P H ⊤ (K.map (MulAut.conj c).toMonoidHom) (c * u * c⁻¹) := by
  obtain ⟨-, hu2, -, hKu, hP⟩ := h
  refine ⟨mem_top _, ?_, le_top, ?_, ?_⟩
  · have := MulEquiv.orderOf_eq (MulAut.conj c) u
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hu2
  · rintro _ ⟨k, hk, rfl⟩
    have h1 := hKu k hk
    show (c * k * c⁻¹) * (c * u * c⁻¹) = (c * u * c⁻¹) * (c * k * c⁻¹)
    calc (c * k * c⁻¹) * (c * u * c⁻¹) = c * (k * u) * c⁻¹ := by group
      _ = c * (u * k) * c⁻¹ := by rw [h1]
      _ = (c * u * c⁻¹) * (c * k * c⁻¹) := by group
  · rwa [Subgroup.card_map_of_injective (MulAut.conj c).injective]

variable (F : TwoAFacts) (hf : BabyCoverFacts) (bq : BabyQuotient)

include F hf bq

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup in
theorem bIsK_data {X : Type} [Group X] (hX : BIsK X) :
    CFSG.IsQuasisimple X ∧ Nat.card (center X) = 2 ∧ Nat.card X = 2 * ordTwistedE6 2 ∧
      LieModel (X ⧸ center X) .twistedE6 0 2 1 := by
  obtain ⟨u, K, hP, ⟨e⟩⟩ := hX
  obtain ⟨hq, hz, hl, -⟩ := bPair_data F hf bq hP
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_, ?_, ?_⟩
  · rw [card_center_of_mulEquiv' e]
    exact hz
  · rw [Nat.card_congr e.toEquiv]
    exact hP.2.2.2.2
  · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (quotientCenterEquiv' e.symm) hl

theorem bIsK_card_cq {X : Type} [Group X] (hX : BIsK X) :
    Nat.card (X ⧸ center X) = ordTwistedE6 2 := by
  obtain ⟨-, hz, hc, -⟩ := bIsK_data F hf bq hX
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
  rw [hz, hc] at h1
  omega

theorem bIsK_oddCore {X : Type} [Group X] (hX : BIsK X) : CFSG.oddCore X = ⊥ := by
  obtain ⟨hq, hz, hc, -⟩ := bIsK_data F hf bq hX
  have : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; unfold ordTwistedE6; norm_num)
  have : IsSimpleGroup (X ⧸ center X) := hq.2.1
  refine oddCore_eq_bot_of_card_center_two ?_ hz
  rw [bIsK_card_cq F hf bq hX]
  exact even_ordTwistedE6_two

theorem bIsK_iso (t3 : BabyTableIII) {X Y : Type} [Group X] [Group Y] (hX : BIsK X)
    (hY : BIsK Y) : Nonempty (X ≃* Y) := by
  have := finite_carrier_b F
  obtain ⟨u, K, hP, ⟨eX⟩⟩ := hX
  obtain ⟨v, K', hP', ⟨eY⟩⟩ := hY
  obtain ⟨hq, -, -, hCu, hidx⟩ := bPair_data F hf bq hP
  obtain ⟨hq', -, -, hCv, hidx'⟩ := bPair_data F hf bq hP'
  have hKC : K ≤ ⊤ ⊓ centralizer ({u} : Set (Carrier .B)) := fun k hk =>
    ⟨mem_top _, mem_centralizer_singleton_iff.2 (hP.2.2.2.1 k hk)⟩
  have hKC' : K' ≤ ⊤ ⊓ centralizer ({v} : Set (Carrier .B)) := fun k hk =>
    ⟨mem_top _, mem_centralizer_singleton_iff.2 (hP'.2.2.2.1 k hk)⟩
  have hKcomm : K =
      ⁅centralizer ({u} : Set (Carrier .B)), centralizer ({u} : Set (Carrier .B))⁆ := by
    have := eq_commutator_of_perfect_of_index_le_two hKC hidx.le hq.1
    rwa [top_inf_eq] at this
  have hKcomm' : K' =
      ⁅centralizer ({v} : Set (Carrier .B)), centralizer ({v} : Set (Carrier .B))⁆ := by
    have := eq_commutator_of_perfect_of_index_le_two hKC' hidx'.le hq'.1
    rwa [top_inf_eq] at this
  have hcu : BabyInv 0 u := ⟨hP.2.1, hCu.trans babyCentOrder_zero.symm⟩
  have hcv : BabyInv 0 v := ⟨hP'.2.1, hCv.trans babyCentOrder_zero.symm⟩
  obtain ⟨c, hc⟩ : ∃ c : Carrier .B, c * u * c⁻¹ = v := isConj_iff.1 (t3.2 0 u v hcu hcv)
  have hmap : K.map (MulAut.conj c).toMonoidHom = K' := by
    rw [hKcomm, hKcomm', Subgroup.map_commutator]
    have h1 := map_centralizer_equiv (MulAut.conj c) u
    have h2 : (MulAut.conj c) u = v := by rw [MulAut.conj_apply]; exact hc
    rw [h2] at h1
    rw [MulEquiv.toMonoidHom_eq_coe, h1]
  exact ⟨eX.trans ((K.equivMapOfInjective (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).trans ((MulEquiv.subgroupCongr hmap).trans eY.symm))⟩

end BKData

section BLink

theorem exists_not_commute_of_simple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hp : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
  exact hp (IsSimpleGroup.prime_card (α := X))

theorem card_centralizer_subgroupOf_le_two {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    {u : G} (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hC : ∀ c ∈ L, (∀ k ∈ K, c * k = k * c) → c = 1 ∨ c = u) :
    Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2 := by
  let u' : ↥L := ⟨u, hu⟩
  have hz2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hxk : ∀ x : ↥L, (∀ k ∈ (K.subgroupOf L : Subgroup ↥L), k * x = x * k) →
      x ∈ zpowers u' := by
    intro x hx
    have h1 : ∀ k ∈ K, (x : G) * k = k * (x : G) := fun k hk =>
      (congrArg Subtype.val (hx ⟨k, hKL hk⟩ (mem_subgroupOf.2 hk))).symm
    rcases hC (x : G) x.2 h1 with h | h
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show x = u' from Subtype.ext h]
      exact mem_zpowers u'
  calc Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L))
      ≤ Nat.card ↥(zpowers u') := Subgroup.card_le_of_le fun x hx =>
        hxk x fun k hk => (mem_centralizer_iff.1 hx k hk)
    _ = 2 := by rw [Nat.card_zpowers, hz2]

variable (F : TwoAFacts) (hf : BabyCoverFacts) (bq : BabyQuotient)

include F hf bq in
theorem bLink (hB : AllInner NativeSporadic.B) (t3 : BabyTableIII) (hmult : OddMultTrivial .B)
    {G : Type} [Group G] [Finite G] {L K₁ T : Subgroup G} {s : G} (hcov : OddCover .B L)
    (hdata : Sol78Link5bData K₁ L T s) (hq : CFSG.IsQuasisimple ↥K₁)
    (hK : BIsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    ∃ l : G, l ∈ L ∧ orderOf l = 2 ∧ (∀ k ∈ K₁, k * l = l * k) ∧
      Nat.card ↥K₁ = 2 * ordTwistedE6 2 ∧ IsSporadic ↥L .B ∧ AllInner ↥L := by
  have hLB : IsSporadic ↥L .B := hcov.isSporadic_of_mult hmult
  obtain ⟨e⟩ := hLB
  have hinL : AllInner ↥L := AllInner.of_mulEquiv e.symm hB
  have hZL : center ↥L = ⊥ := hcov.center_eq_bot hmult
  have hKL : K₁ ≤ L := hdata.le_left
  have : Group.IsPerfect ↥K₁ := hq.1
  obtain ⟨e₃⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁))
    (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']
      exact oddCore_le_center hq)
  have hne : K₁ ≠ L := by
    rintro rfl
    have h1 : Nat.card (↥K₁ ⧸ center ↥K₁) = monsterBabyOrder := card_isSporadic_b F hcov.2.2
    rw [Nat.card_congr e₃.toEquiv, bIsK_card_cq F hf bq hK] at h1
    unfold monsterBabyOrder ordTwistedE6 at h1
    norm_num at h1
  obtain ⟨l, hlL, hl2, hlK⟩ := exists_involution_of_link hdata hq hne hinL hZL
  refine ⟨l, hlL, hl2, hlK, ?_, ⟨e⟩, hinL⟩
  have hquot : Nat.card (↥K₁ ⧸ CFSG.oddCore ↥K₁) = 2 * ordTwistedE6 2 :=
    (bIsK_data F hf bq hK).2.2.1
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K₁)
  rw [hquot] at h4
  have hOodd : Odd (Nat.card (CFSG.oddCore ↥K₁)) := odd_card_oddCore' ↥K₁
  have hfin := finite_carrier_b F
  let lB : Carrier .B := e ⟨l, hlL⟩
  have hlB2 : orderOf lB = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hl2
  have hle : (K₁.subgroupOf L).map e.toMonoidHom ≤ centralizer ({lB} : Set (Carrier .B)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    show e x * e ⟨l, hlL⟩ = e ⟨l, hlL⟩ * e x
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hlK x (mem_subgroupOf.1 hx)))
  have hdvd : Nat.card ↥K₁ ∣ Nat.card ↥(centralizer ({lB} : Set (Carrier .B))) := by
    have h5 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at h5
  obtain ⟨k, -, hkC⟩ := t3.1 lB hlB2
  have hCk : Nat.card ↥(centralizer ({lB} : Set (Carrier .B))) = babyCentOrder k := hkC
  have hordpos : 0 < ordTwistedE6 2 := by unfold ordTwistedE6; norm_num
  have hKge : 2 * ordTwistedE6 2 ≤ Nat.card ↥K₁ := by
    rw [h4]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hk0 : k = 0 := by
    apply eq_zero_of_le_babyCentOrder
    rw [← hCk]
    exact (by omega : ordTwistedE6 2 ≤ Nat.card ↥K₁).trans (Nat.le_of_dvd Nat.card_pos hdvd)
  subst hk0
  rw [hCk, babyCentOrder_zero, h4] at hdvd
  have h6 : Nat.card (CFSG.oddCore ↥K₁) ∣ 2 := by
    refine Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < 2 * ordTwistedE6 2) ?_
    rw [show 2 * ordTwistedE6 2 * 2 = 4 * ordTwistedE6 2 by ring]
    exact hdvd
  have h7 : Nat.card (CFSG.oddCore ↥K₁) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h6 with h | h
    · exact h
    · rw [h] at hOodd
      exact absurd hOodd (by decide)
  rw [h4, h7, mul_one]

include F hf bq in
theorem stdRow_b (hB : AllInner NativeSporadic.B) (t3 : BabyTableIII) (hmult : OddMultTrivial .B)
    (G : Type) [Group G] [Finite G] (L K₁ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.B], OddCover s' L) (_ : T ≠ ⊥)
    (hdata : Sol78Link5bData K₁ L T s) (hq : CFSG.IsQuasisimple ↥K₁)
    (hK : BIsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 := by
  obtain ⟨s', hs', hcov⟩ := hL
  rw [List.mem_singleton] at hs'
  subst hs'
  obtain ⟨l, hlL, hl2, hlK, hcard, hLB, hinL⟩ := bLink F hf bq hB t3 hmult hcov hdata hq hK
  have hcovB := hf.cover G L K₁ l hLB ⟨hlL, hl2, hdata.le_left, hlK, hcard⟩
  obtain ⟨e⟩ := hLB
  have hsimple : IsSimpleGroup ↥L := @MulEquiv.isSimpleGroup _ _ _ _ F.b_simple e
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    refine exists_not_commute_of_simple hsimple ?_
    rw [Nat.card_congr e.toEquiv]
    have h : Nat.card (Carrier .B) = monsterBabyOrder := F.b_card
    rw [h]
    unfold monsterBabyOrder
    norm_num
  have hloc := solomonLocal_of_idx2Cover hsimple hnab (outTwo_of_allInner hinL) hlL hl2
    hdata.le_left hlK hcovB
  exact ⟨solStd_of_standardComponentIsStandard hloc.standard_in_L, hloc.autCentralizer_two⟩

include F hf bq in
theorem autC_b (hB : AllInner NativeSporadic.B) (t3 : BabyTableIII) (hmult : OddMultTrivial .B)
    (G : Type) [Group G] [Finite G] (L K₁ N₀ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.B], OddCover s' L) (_ : T ≠ ⊥)
    (hdata : Sol78Link5bData K₁ L T s) (hq : CFSG.IsQuasisimple ↥K₁)
    (hK : BIsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) (hcan : CanLoc K₁ N₀) :
    Group.IsSolvable ↥(autCentralizer L N₀) ∧ twoAdic (autCentralizer L N₀) ≤ 1 ∧
      ElemBound 2 ↥(autCentralizer L N₀) ∧
        (True → ∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g) := by
  obtain ⟨s', hs', hcov⟩ := hL
  rw [List.mem_singleton] at hs'
  subst hs'
  obtain ⟨l, hlL, hl2, hlK, hcard, hLB, hinL⟩ := bLink F hf bq hB t3 hmult hcov hdata hq hK
  have hcovB := hf.cover G L K₁ l hLB ⟨hlL, hl2, hdata.le_left, hlK, hcard⟩
  have hcent := card_centralizer_subgroupOf_le_two hlL hl2 hdata.le_left
    (central_eq_of_idx2Cover hlL hl2 hcovB).2
  have hN₀ : N₀ = K₁ :=
    canLoc_eq_of_even hcan (even_card_center_of_quot hq (bIsK_data F hf bq hK).2.1)
  subst hN₀
  have hinn : ∀ α : MulAut ↥L, ∃ c : ↥L, ∀ x, α x = c * x * c⁻¹ := fun α => by
    obtain ⟨g, hg⟩ := hinL α
    exact ⟨g, fun x => by rw [hg]; rfl⟩
  have hcardA : Nat.card ↥(autCentralizer L N₀) ≤ 2 :=
    (Subgroup.card_le_of_le (autCentralizer_le_map_centralizer (K := N₀) hinn)).trans
      ((Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans hcent)
  exact ⟨isSolvable_autCentralizer_of_card_le (hcardA.trans (by norm_num)),
    twoAdic_le_one_of_card_le_two _ hcardA, elemBound_of_card_le hcardA,
    fun _ α _ => hinL α⟩

include F hf bq in
theorem sec_b (G : Type) [Group G] [Finite G] (K₁ N₀ : Subgroup G)
    (hq : CFSG.IsQuasisimple ↥K₁) (hK : BIsK (↥K₁ ⧸ CFSG.oddCore ↥K₁)) (hcan : CanLoc K₁ N₀) :
    ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
      (True → TwoSubgroupsAbelian
        ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))))) := by
  rintro ⟨hs, -⟩
  have hN₀ : N₀ = K₁ :=
    canLoc_eq_of_even hcan (even_card_center_of_quot hq (bIsK_data F hf bq hK).2.1)
  subst hN₀
  rw [Subgroup.subgroupOf_self, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hs
  exact not_isSolvable_cq_of_isQuasisimple hq
    (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := ↥N₀ ⧸ center ↥N₀)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := ↥N₀ ⧸ center ↥N₀)).symm.injective)

include F hf bq in
theorem fourA_b (hB : AllInner NativeSporadic.B) (t3 : BabyTableIII) (hmult : OddMultTrivial .B)
    (hfix : E6InvolutionFixed) : FourAFacts BIsK [.B] :=
  fourAFacts_of_lamProfile True 1 2 (by norm_num)
    (fun G _ _ L K₁ N₀ T s hL hT hdata hq hK hcan =>
      autC_b F hf bq hB t3 hmult G L K₁ N₀ T s hL hT hdata hq hK hcan)
    (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ => by
      refine not_lamProfile_of_not_fix True (2 * 2) (fun α h1 h2 hL => ?_)
      have hE6 : LieModel (K₂ ⧸ center K₂) .twistedE6 0 2 1 :=
        CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm (bIsK_data F hf bq hX).2.2.2
      rcases hfix K₂ hperf hE6 α h1 h2 with h | h | h
      · exact h hL.1
      · exact h hL.2.1
      · exact h (hL.2.2 trivial))
    (fun G _ _ K₁ N₀ hq hK hcan => sec_b F hf bq G K₁ N₀ hq hK hcan)

end BLink

section BReach

theorem reachRow_b
    (hLie : Sol78Hyp12LieHered) (F : TwoAFacts) (mf : MonsterFacts (Carrier .M))
    (mi : MonsterInvolutions (Carrier .M)) (t3 : BabyTableIII) (uniq : E6TwoUnique)
    (inp : BHyp31Inputs) :
    ReachRow BIsK [.B] [.M] []
      (fun X _ => LieModel X .twistedE6 0 2 1 ∨ IsSporadic X .B ∨ IsSporadic X .M) where
  iso := fun X Y _ _ e h => by
    rcases h with h | h | h
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
    · obtain ⟨f⟩ := h
      exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
    · obtain ⟨f⟩ := h
      exact Or.inr (Or.inr ⟨e.symm.trans f⟩)
  fi23 := fun s hs => by
    rcases List.mem_append.1 hs with h | h
    · rw [List.mem_singleton] at h
      subst h
      exact fi23Excl_b F
    · rw [List.mem_singleton] at h
      subst h
      exact fi23Excl_m F mf
  fi23_lo := fun s hs => absurd hs List.not_mem_nil
  K_reach := fun X _ hX => Or.inl (bIsK_data F inp.cover inp.quotient hX).2.2.2
  K_quot := fun X _ hX => isKPinned_of_mulEquiv
    (quotientOddCoreEquiv (bIsK_oddCore F inp.cover inp.quotient hX)).symm hX
  K_not_sporadic := fun X _ hX s hs h => by
    have hcq := bIsK_card_cq F inp.cover inp.quotient hX
    rcases List.mem_append.1 hs with hs | hs
    · rw [List.mem_singleton] at hs
      subst hs
      have := card_isSporadic_b F h
      rw [hcq] at this
      unfold ordTwistedE6 monsterBabyOrder at this
      norm_num at this
    · rw [List.mem_singleton] at hs
      subst hs
      have := card_isSporadic_m mf h
      rw [hcq] at this
      unfold ordTwistedE6 monsterOrder at this
      norm_num at this
  K_odd_lo := fun _ _ _ _ s hs => absurd hs List.not_mem_nil
  lo := Or.inl fun s hs => absurd hs List.not_mem_nil
  K_iso := fun X Y _ _ hX hY _ _ => bIsK_iso F inp.cover inp.quotient t3 hX hY
  K_cq := fun X Y _ _ hX hY => by
    obtain ⟨e⟩ := bIsK_iso F inp.cover inp.quotient t3 hX hY
    exact ⟨quotientCenterEquiv' e⟩
  not_exc := fun X _ h => by
    rcases h with h | h | h
    · exact notExc_of_card_group (c := 53492380) (F.e6_card X h)
        (by unfold ordTwistedE6; norm_num) (by unfold ordTwistedE6; norm_num)
        (by unfold ordTwistedE6; norm_num)
    · exact sporadicNotExc_b F X h
    · exact sporadicNotExc_m mf X h
  sp_not_exc := fun s hs => by
    rcases List.mem_append.1 hs with h | h
    · rw [List.mem_singleton] at h
      subst h
      exact sporadicNotExc_b F
    · rw [List.mem_singleton] at h
      subst h
      exact sporadicNotExc_m mf
  rank := fun X _ _ hq hR hodd => by
    rcases hR with hE | hB' | hM
    · exact inp.e6Rank X hq hE
    · exact inp.bRank X hq hB'
    · exfalso
      have hZ : center X = ⊥ := inp.noCover X hq hM
      exact hodd (by rw [hZ, Subgroup.card_bot]; exact odd_one) ⟨.M, by simp, hM⟩
  up_reach := fun s hs X _ h => by
    rw [List.mem_singleton] at hs
    subst hs
    exact Or.inr (Or.inr h)
  closure := fun Y _ _ hUY N' hN hidx hkp P hsol hq hR hnS _ hev hscope => by
    have hE6 : LieModel (↥P ⧸ center ↥P) .twistedE6 0 2 1 := by
      rcases hR with h | h | h
      · exact h
      · exact absurd ⟨.B, by simp, h⟩ hnS
      · exact absurd ⟨.M, by simp, h⟩ hnS
    by_cases hodd : Odd (Nat.card ↥(center ↥P))
    · obtain ⟨u₀, K₀, hP₀⟩ := inp.pair
      have hK₀ : BIsK ↥K₀ := ⟨u₀, K₀, hP₀, ⟨MulEquiv.refl _⟩⟩
      have hKeven : KEven BIsK := fun X _ hX => by
        rw [(bIsK_data F inp.cover inp.quotient hX).2.1]
        exact even_two
      obtain ⟨e⟩ := uniq _ _ hE6 (bIsK_data F inp.cover inp.quotient hK₀).2.2.2
      have hEC := hev hKeven ↥K₀ hK₀ ⟨e⟩ hodd
      have hcat : CFSG.Blueprint.Catalog ↥N' := by
        rcases hscope with h | h | h
        · exact h
        · exact absurd (even_center_of_klike hq h hKeven) (Nat.not_even_iff_odd.2 hodd)
        · exact absurd ⟨e⟩ (h ↥K₀ hK₀)
      rcases seitz29OddCat_holds Y N' hN hidx hcat hEC P hsol hq hodd hE6 with h | h | h | h
      · exact Or.inl h
      · exact absurd hEC (inp.e6Four ↥N' h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl
        ((hLie Y hUY N' hN hidx hkp P hsol hq (Nat.not_odd_iff_even.1 hodd)).2 hE6))
  notR := fun Y _ _ N hN hidx hkp ⟨L, hL, s, hs, hcov⟩ hR => by
    rw [List.mem_singleton] at hs
    subst hs
    have hcardLB : monsterBabyOrder ≤ Nat.card ↥L := by
      have h1 : Nat.card (↥L ⧸ center ↥L) = monsterBabyOrder := card_isSporadic_b F hcov.2.2
      have h2 : Nat.card (↥L ⧸ center ↥L) ≤ Nat.card ↥L :=
        Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
      omega
    obtain ⟨T, hT, hTp, hLT⟩ := hL
    have hle : Nat.card ↥L ≤ Nat.card Y := Subgroup.card_le_card_group L
    rcases hR with hR | hR | hR
    ·
      have hcardN : Nat.card ↥N = ordTwistedE6 2 := F.e6_card ↥N hR
      have h1 := Subgroup.card_mul_index N
      have hY : Nat.card Y ≤ 2 * ordTwistedE6 2 := by
        rw [← h1, hcardN]
        exact Nat.mul_le_mul_left _ hidx
      have : monsterBabyOrder ≤ 2 * ordTwistedE6 2 := hcardLB.trans (hle.trans hY)
      unfold monsterBabyOrder ordTwistedE6 at this
      norm_num at this
    ·
      obtain ⟨e⟩ := hR
      have hNtop : N = ⊤ := eq_top_of_allInner hN (AllInner.of_mulEquiv e.symm mf.baby_allInner)
      have hcardY : Nat.card Y = monsterBabyOrder := by
        have : Nat.card ↥N = Nat.card Y := by rw [hNtop]; exact Subgroup.card_top
        rw [← this]
        exact card_isSporadic_b F ⟨e⟩
      have hLtop : L = ⊤ := Subgroup.eq_top_of_card_eq L (by omega)
      have hcen : center Y = ⊥ := center_eq_bot_of_fStarSimple hN
      apply hT
      rw [eq_bot_iff]
      intro t ht
      have hz : t ∈ center Y := Subgroup.mem_center_iff.2 fun g =>
        (mem_centralizer_iff.1 (hLT.1 (hLtop ▸ mem_top g)) t ht).symm
      rw [hcen] at hz
      exact hz
    ·
      obtain ⟨e⟩ := hR
      have hNtop : N = ⊤ := eq_top_of_allInner hN (AllInner.of_mulEquiv e.symm mf.allInner)
      let eY : Y ≃* Carrier .M :=
        ((MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv).symm.trans e
      obtain ⟨t, htT, ht2⟩ := exists_involution_of_isPGroup hTp hT
      have hLC : L ≤ centralizer ({t} : Set Y) := fun x hx =>
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hLT.1 hx) t htT).symm
      have hfinM := finite_carrier_m mf
      have ht2' : orderOf (eY t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
      have hL'C : L.map eY.toMonoidHom ≤ centralizer ({eY t} : Set (Carrier .M)) := by
        rw [← map_centralizer_equiv eY t]
        exact Subgroup.map_mono hLC
      have hcardL' : Nat.card ↥(L.map eY.toMonoidHom) = Nat.card ↥L :=
        Subgroup.card_map_of_injective eY.injective
      have hcardL : Nat.card ↥L = monsterBabyOrder * Nat.card (center ↥L) := by
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L)
        rwa [card_isSporadic_b F hcov.2.2] at h1
      have h17 : (17 : ℕ) ∣ Nat.card ↥L := by
        have h1 : Nat.card (↥L ⧸ center ↥L) ∣ Nat.card ↥L :=
          Subgroup.card_quotient_dvd_card (center ↥L)
        rw [card_isSporadic_b F hcov.2.2] at h1
        exact (by unfold monsterBabyOrder; norm_num : (17 : ℕ) ∣ monsterBabyOrder).trans h1
      rcases mi.small (eY t) ht2' with hbig | hsmall
      · obtain ⟨hA, hC, -⟩ := mf.twoA (eY t) ht2' hbig
        have hLle : Nat.card ↥L ≤ 2 * monsterBabyOrder := by
          have := Subgroup.card_le_of_le hL'C
          rwa [hC, hcardL'] at this
        have hBpos : 0 < monsterBabyOrder := by unfold monsterBabyOrder; norm_num
        have hZpos : 0 < Nat.card (center ↥L) := Nat.card_pos
        have hZodd : Odd (Nat.card (center ↥L)) := hcov.2.1
        have hZ1 : Nat.card (center ↥L) = 1 := by
          rw [hcardL] at hLle
          have hZle : Nat.card (center ↥L) ≤ 2 := by nlinarith
          rcases (by omega : Nat.card (center ↥L) = 1 ∨ Nat.card (center ↥L) = 2) with h | h
          · exact h
          · rw [h] at hZodd
            exact absurd hZodd (by decide)
        have hcardLB' : Nat.card ↥L = monsterBabyOrder := by rw [hcardL, hZ1, mul_one]
        have hidx2 : ((L.map eY.toMonoidHom).subgroupOf
            (centralizer ({eY t} : Set (Carrier .M)))).index ≤ 2 := by
          have h1 := Subgroup.index_mul_card
            ((L.map eY.toMonoidHom).subgroupOf (centralizer ({eY t} : Set (Carrier .M))))
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL'C).toEquiv, hcardL', hcardLB',
            hC] at h1
          nlinarith
        have htop := eq_top_of_perfect_of_index_le_two hA.1 hidx2
        have h2 : Nat.card ↥((L.map eY.toMonoidHom).subgroupOf
            (centralizer ({eY t} : Set (Carrier .M)))) =
            Nat.card ↥(centralizer ({eY t} : Set (Carrier .M))) := by
          rw [htop]
          exact Subgroup.card_top
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL'C).toEquiv, hcardL', hcardLB', hC] at h2
        omega
      · refine hsmall (h17.trans ?_)
        rw [← hcardL']
        exact Subgroup.card_dvd_of_le hL'C
  pair_into := fun Y _ _ _ N' hN hidx hkp P hsol hq hR hnS _ _ ⟨s, hs, hN'B⟩ => by
    rw [List.mem_singleton] at hs
    subst hs
    have hE6 : LieModel (↥P ⧸ center ↥P) .twistedE6 0 2 1 := by
      rcases hR with h | h | h
      · exact h
      · exact absurd ⟨.B, by simp, h⟩ hnS
      · exact absurd ⟨.M, by simp, h⟩ hnS
    obtain ⟨e⟩ := hN'B
    have hNtop : N' = ⊤ := eq_top_of_allInner hN (AllInner.of_mulEquiv e.symm mf.baby_allInner)
    let eY : Y ≃* Carrier .B :=
      ((MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv).symm.trans e
    obtain ⟨-, t, ht2, hc⟩ := hsol
    have hPC : P ≤ centralizer ({t} : Set Y) := hc.1
    have hfinB := finite_carrier_b F
    have ht2' : orderOf (eY t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
    have hP'C : P.map eY.toMonoidHom ≤ centralizer ({eY t} : Set (Carrier .B)) := by
      rw [← map_centralizer_equiv eY t]
      exact Subgroup.map_mono hPC
    have hcardP' : Nat.card ↥(P.map eY.toMonoidHom) = Nat.card ↥P :=
      Subgroup.card_map_of_injective eY.injective
    have hcardP : Nat.card ↥P = ordTwistedE6 2 * Nat.card (center ↥P) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥P)
      rwa [F.e6_card _ hE6] at h1
    have hordpos : 0 < ordTwistedE6 2 := by unfold ordTwistedE6; norm_num
    have hZpos : 0 < Nat.card (center ↥P) := Nat.card_pos
    obtain ⟨k, -, hkC⟩ := t3.1 (eY t) ht2'
    have hCk : Nat.card ↥(centralizer ({eY t} : Set (Carrier .B))) = babyCentOrder k := hkC
    have hge : ordTwistedE6 2 ≤ babyCentOrder k := by
      rw [← hCk]
      have := Subgroup.card_le_of_le hP'C
      rw [hcardP', hcardP] at this
      nlinarith
    have hk0 : k = 0 := eq_zero_of_le_babyCentOrder hge
    subst hk0
    obtain ⟨u₀, K₀, hP₀⟩ := inp.pair
    obtain ⟨-, -, -, hCu₀, -⟩ := bPair_data F inp.cover inp.quotient hP₀
    have hbi₀ : BabyInv 0 u₀ := ⟨hP₀.2.1, hCu₀.trans babyCentOrder_zero.symm⟩
    obtain ⟨c, hcc⟩ : ∃ c : Carrier .B, c * u₀ * c⁻¹ = eY t :=
      isConj_iff.1 (t3.2 0 u₀ (eY t) hbi₀ ⟨ht2', hkC⟩)
    have hPK := pairShape_top_conj (P := (· = 2 * ordTwistedE6 2)) c hP₀
    rw [hcc] at hPK
    obtain ⟨hqK, -, -, -, hidxK⟩ := bPair_data F inp.cover inp.quotient hPK
    have hKC : K₀.map (MulAut.conj c).toMonoidHom ≤
        ⊤ ⊓ centralizer ({eY t} : Set (Carrier .B)) := fun k hk =>
      ⟨mem_top _, mem_centralizer_singleton_iff.2 (hPK.2.2.2.1 k hk)⟩
    have hKcomm : K₀.map (MulAut.conj c).toMonoidHom =
        ⁅centralizer ({eY t} : Set (Carrier .B)), centralizer ({eY t} : Set (Carrier .B))⁆ := by
      have := eq_commutator_of_perfect_of_index_le_two hKC hidxK.le hqK.1
      rwa [top_inf_eq] at this
    have : Group.IsPerfect ↥P := hq.1
    have hP'perf : Group.IsPerfect ↥(P.map eY.toMonoidHom) := Group.IsPerfect.map eY.toMonoidHom
    have hP'K : P.map eY.toMonoidHom ≤ K₀.map (MulAut.conj c).toMonoidHom := by
      calc P.map eY.toMonoidHom = ⁅P.map eY.toMonoidHom, P.map eY.toMonoidHom⁆ :=
            (Subgroup.isPerfect_iff.1 hP'perf).symm
        _ ≤ ⁅centralizer ({eY t} : Set (Carrier .B)), centralizer ({eY t} : Set (Carrier .B))⁆ :=
            Subgroup.commutator_mono hP'C hP'C
        _ = K₀.map (MulAut.conj c).toMonoidHom := hKcomm.symm
    have hKcard : Nat.card ↥(K₀.map (MulAut.conj c).toMonoidHom) = 2 * ordTwistedE6 2 :=
      hPK.2.2.2.2
    have hPeq : P.map eY.toMonoidHom = K₀.map (MulAut.conj c).toMonoidHom := by
      have h1 := Subgroup.index_mul_card
        ((P.map eY.toMonoidHom).subgroupOf (K₀.map (MulAut.conj c).toMonoidHom))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'K).toEquiv, hcardP', hcardP,
        hKcard] at h1
      have hidx2 : ((P.map eY.toMonoidHom).subgroupOf
          (K₀.map (MulAut.conj c).toMonoidHom)).index ≤ 2 := by
        nlinarith
      have htop := eq_top_of_perfect_of_index_le_two hqK.1 hidx2
      exact le_antisymm hP'K (Subgroup.subgroupOf_eq_top.1 htop)
    have hZ2 : Nat.card (center ↥P) = 2 := by
      have h1 := hcardP
      rw [← hcardP', hPeq, hKcard] at h1
      exact (Nat.eq_of_mul_eq_mul_left hordpos (by linarith : ordTwistedE6 2 * 2 =
        ordTwistedE6 2 * Nat.card (center ↥P))).symm
    have : Finite ↥P := inferInstance
    have : IsSimpleGroup (↥P ⧸ center ↥P) := hq.2.1
    have hO : CFSG.oddCore ↥P = ⊥ := by
      refine oddCore_eq_bot_of_card_center_two ?_ hZ2
      rw [F.e6_card _ hE6]
      exact even_ordTwistedE6_two
    exact ⟨eY t, K₀.map (MulAut.conj c).toMonoidHom, hPK, ⟨(quotientOddCoreEquiv hO).trans
      ((P.equivMapOfInjective eY.toMonoidHom eY.injective).trans
        (MulEquiv.subgroupCongr hPeq))⟩⟩

theorem factorial_div_two_ne_aux {n₀ N : ℕ} (h1 : n₀.factorial / 2 < N)
    (h2 : N < (n₀ + 1).factorial / 2) (n : ℕ) : n.factorial / 2 ≠ N := by
  intro h
  rcases Nat.lt_or_ge n₀ n with hn | hn
  · have : (n₀ + 1).factorial ≤ n.factorial := Nat.factorial_le hn
    have : (n₀ + 1).factorial / 2 ≤ n.factorial / 2 := Nat.div_le_div_right this
    omega
  · have : n.factorial ≤ n₀.factorial := Nat.factorial_le hn
    have : n.factorial / 2 ≤ n₀.factorial / 2 := Nat.div_le_div_right this
    omega

theorem thm24Hex_of_orders (lo : LieModelOrders) {s : TauCeti.SporadicName} {N : ℕ}
    (hs : ∀ (Y : Type) [Group Y], IsSporadic Y s → Nat.card Y = N)
    (hN : 251596800 < N) (halt : ∀ n : ℕ, n.factorial / 2 ≠ N) : Thm24Hex s := by
  intro X _ hq hodd hX
  have hcq : Nat.card (X ⧸ center X) = N := hs _ hX
  have hZfin : Finite ↥(center X) := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have hQfin : Finite (X ⧸ center X) := Nat.finite_of_card_ne_zero (by omega)
  have : Finite X := Finite.of_subgroup_quotient (center X)
  have hle : Nat.card (X ⧸ center X) ≤ Nat.card X :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  obtain ⟨hP, hS, hG⟩ := lo
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rintro ⟨n, hn5, ⟨e⟩⟩
    have h4 : 4 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    have hZ : Nat.card (center X) = 1 := by
      rw [card_center_of_mulEquiv' e, alternatingGroup.center_eq_bot h4, Subgroup.card_bot]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center X)
    rw [hcq, hZ, mul_one] at h1
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h2 : Nat.card X = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
    exact halt n (by omega)
  · have := hP X h
    omega
  · have := hS X h
    omega
  · have := hG X h
    omega

theorem thm24Hex_b (lo : LieModelOrders) (F : TwoAFacts) : Thm24Hex .B :=
  thm24Hex_of_orders lo (fun _ _ h => card_isSporadic_b F h)
    (by unfold monsterBabyOrder; norm_num)
    (factorial_div_two_ne_aux (n₀ := 31) (by unfold monsterBabyOrder; decide)
      (by unfold monsterBabyOrder; decide))

theorem hyp31RowFacts_b
    (hLie : Sol78Hyp12LieHered) (F : TwoAFacts)
    (mf : MonsterFacts (Carrier .M))
    (mi : MonsterInvolutions (Carrier .M))
    (mrank : ∀ (X : Type) [Group X] [Finite X], IsSporadic X .M → 3 ≤ CFSG.pRank 2 X)
    (t3 : BabyTableIII) (uniq : E6TwoUnique) (lo : LieModelOrders) (inp : BHyp31Inputs) :
    Hyp31RowFacts BIsK [.B] [.M] [] where
  reach := ⟨_, reachRow_b hLie F mf mi t3 uniq inp⟩
  evenOut := fun s hs => by
    rw [List.mem_singleton] at hs
    subst hs
    exact inp.evenB
  up :=
    { fi23 := fun s hs => by
        rw [List.mem_singleton] at hs
        subst hs
        exact fi23Excl_m F mf
      not_exc := fun s hs => by
        rw [List.mem_singleton] at hs
        subst hs
        exact sporadicNotExc_m mf
      odd := fun s hs X _ _ hq hX => by
        rw [List.mem_singleton] at hs
        subst hs
        have hZ : center X = ⊥ := inp.noCover X hq hX
        rw [hZ, Subgroup.card_bot]
        exact odd_one
      rank := fun s hs X _ _ hq hX => by
        rw [List.mem_singleton] at hs
        subst hs
        have hZ : center X = ⊥ := inp.noCover X hq hX
        obtain ⟨f⟩ := hX
        exact mrank X ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
          QuotientGroup.quotientBot).symm.trans f⟩ }
  thm24 := fun s hs => by
    rw [List.mem_singleton] at hs
    subst hs
    exact Or.inr ⟨by simp, thm24Hex_b lo F⟩
  std_row := fun G _ _ L K₁ T s hL hT hdata hq hK =>
    stdRow_b F inp.cover inp.quotient mf.baby_allInner t3 inp.mult G L K₁ T s hL hT hdata hq hK
  four_a := fourA_b F inp.cover inp.quotient mf.baby_allInner t3 inp.mult inp.e6Fixed

end BReach

end CFSG.EvenSporadicStandard.Induction.Hyp
