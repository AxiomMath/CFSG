module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharMain
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable
public import CFSG.Timmesfeld.Orders.ExceptionalWeyl
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

section Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem pinnedX_pow
    (α : Fin τ.rank → ℤ) (c : K) (n : ℕ) : pinnedX τ K α c ^ n = pinnedX τ K α (n • c) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, pinnedX_zero]
  | succ n ih => rw [pow_succ, ih, ← pinnedX_add, succ_nsmul]

theorem heightSeries_pow_eq_one
    {p : ℕ} [CharP K p] {h : ℤ}
    (hcomm : ∀ x ∈ heightSeries τ K h, ∀ y ∈ heightSeries τ K h, x * y = y * x)
    {x : (Module.End K (RootModule τ K))ˣ} (hx : x ∈ heightSeries τ K h) : x ^ p = 1 := by
  have hcl : heightSeries τ K h = Subgroup.closure
      {g | ∃ α ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ h ≤ height α},
        ∃ c : K, pinnedX τ K α c = g} := rootSpan_eq_closure K _
  rw [hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, -, c, rfl⟩ := hg
    rw [pinnedX_pow, show p • c = 0 by simp [nsmul_eq_mul, CharP.cast_eq_zero], pinnedX_zero]
  | one => exact one_pow p
  | mul a b ha hb iha ihb =>
    have hab : Commute a b := hcomm a (hcl ▸ ha) b (hcl ▸ hb)
    rw [hab.mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

variable {p : ℕ} [hp : Fact p.Prime]

theorem rankThreeCent_of_height
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K p] {G : Type} [Group G] [Finite G]
    (e : G ≃* AdjointQuotient τ K) {m : ℤ} (hm : 1 ≤ m) {Nm Nm1 : ℕ}
    (hNm : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ m ≤ height α}.ncard = Nm)
    (hNm1 : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ m + 1 ≤ height α}.ncard = Nm1)
    (hNtop : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ m + m ≤ height α}.ncard = 0)
    (hdiff : p ^ 2 * Nat.card K ^ Nm1 ≤ Nat.card K ^ Nm) (h3 : 3 ≤ Nm) : RankThreeCent p G := by
  have hXC : posUnipotent τ K ≤ adjointGroup τ K := posUnipotent_le_adjointGroup
  obtain ⟨hU, hidx⟩ := isPGroup_and_not_dvd_index p hXC card_posUnipotent
  have hAX : heightSeries τ K m ≤ posUnipotent τ K := heightSeries_le_posUnipotent m
  have hAC : heightSeries τ K m ≤ adjointGroup τ K := hAX.trans hXC
  have hBA : heightSeries τ K (m + 1) ≤ heightSeries τ K m := heightSeries_antitone (by omega)
  have hBC : heightSeries τ K (m + 1) ≤ adjointGroup τ K := hBA.trans hAC
  have hS : {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α ∧ m + m ≤ height α} = ∅ :=
    (Set.ncard_eq_zero ((finite_setOf_isRoot τ).subset fun α hα => hα.1)).mp hNtop
  have hbot : heightSeries τ K (m + m) = ⊥ := by
    unfold heightSeries rootSpan
    rw [hS]
    simp
  have hcommA : ∀ x ∈ heightSeries τ K m, ∀ y ∈ heightSeries τ K m, x * y = y * x := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ ⁅heightSeries τ K m, heightSeries τ K m⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    have h2 := commutator_heightSeries_le (τ := τ) K m m h1
    rw [hbot, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hexp : ∀ x ∈ heightSeries τ K m, x ^ p = 1 := fun x hx => heightSeries_pow_eq_one hcommA hx
  let π0 : ↥(adjointGroup τ K) →* AdjointQuotient τ K :=
    QuotientGroup.mk' (Subgroup.center ↥(adjointGroup τ K))
  let π : ↥(adjointGroup τ K) →* G := e.symm.toMonoidHom.comp π0
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcen : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : ∀ u ∈ (posUnipotent τ K).subgroupOf (adjointGroup τ K), π u = 1 → u = 1 := by
    intro u _ hu
    have h1 : π0 u = 1 := e.symm.injective (hu.trans (map_one e.symm).symm)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hcen, Subgroup.mem_bot] at h1
    exact h1
  have hAU : (heightSeries τ K m).subgroupOf (adjointGroup τ K) ≤
      (posUnipotent τ K).subgroupOf (adjointGroup τ K) := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hAX hx
  have hBA' : (heightSeries τ K (m + 1)).subgroupOf (adjointGroup τ K) ≤
      (heightSeries τ K m).subgroupOf (adjointGroup τ K) := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hBA hx
  have hAab : IsElemAbelian p ((heightSeries τ K m).subgroupOf (adjointGroup τ K)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact hcommA _ a.2 _ b.2
    · apply Subtype.ext
      exact hexp _ hx
  have hcomm : ∀ u ∈ (posUnipotent τ K).subgroupOf (adjointGroup τ K),
      ∀ a ∈ (heightSeries τ K m).subgroupOf (adjointGroup τ K), u * a * u⁻¹ * a⁻¹ ∈
        (heightSeries τ K (m + 1)).subgroupOf (adjointGroup τ K) := by
    intro u hu a ha
    rw [Subgroup.mem_subgroupOf] at hu ha ⊢
    exact commutator_posUnipotent_heightSeries_le m (Subgroup.commutator_mem_commutator hu ha)
  have hcardA : Nat.card ((heightSeries τ K m).subgroupOf (adjointGroup τ K)) =
      Nat.card K ^ Nm := by
    rw [card_subgroupOf_of_le hAC, (positive_root_height_series τ K).2.2.2.2.2.2 m hm, hNm]
  have hcardB : Nat.card ((heightSeries τ K (m + 1)).subgroupOf (adjointGroup τ K)) =
      Nat.card K ^ Nm1 := by
    rw [card_subgroupOf_of_le hBC, (positive_root_height_series τ K).2.2.2.2.2.2 (m + 1)
      (by omega), hNm1]
  have hpq : p ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos (prime_dvd_card (K := K) p)
  refine rankThreeCent_of_witness_map π hπ hU hidx hAU hBA' hAab hcomm ?_ (Or.inl ?_) hinj
  · rw [hcardA, hcardB, mul_comm]
    exact hdiff
  · rw [hcardA]
    calc p ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hpq 3
      _ ≤ Nat.card K ^ Nm := Nat.pow_le_pow_right Nat.card_pos h3

theorem hdiff_of {p q a b k : ℕ} (hab : a = b + k) (hk : p ^ 2 ≤ q ^ k) :
    p ^ 2 * q ^ b ≤ q ^ a := by
  calc p ^ 2 * q ^ b = q ^ b * p ^ 2 := mul_comm _ _
    _ ≤ q ^ b * q ^ k := Nat.mul_le_mul_left _ hk
    _ = q ^ a := by rw [hab, pow_add]


theorem inExc_f4 :
    InExc .F4 := by
  intro p f hp hp5 hf G _ _ hmodel
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := charP_of_card_eq_prime_pow hf hK
  have hpq : p ≤ Nat.card K := by
    rw [hK]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  refine rankThreeCent_of_height (τ := Tag.F4) e (m := 6) (by norm_num) (Nm := 8)
    (Nm1 := 6) ?_ ?_ ?_ (hdiff_of (by norm_num : 8 = 6 + 2) ?_) (by norm_num)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.F4)
      fun α => 0 < height α ∧ (6 : ℤ) ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.F4)
      fun α => 0 < height α ∧ (6 : ℤ) + 1 ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.F4)
      fun α => 0 < height α ∧ (6 : ℤ) + 6 ≤ height α).trans (by decide +kernel)
  · calc p ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hpq 2
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_right Nat.card_pos (by norm_num)

theorem inExc_e6 :
    InExc .E6 := by
  intro p f hp hp5 hf G _ _ hmodel
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := charP_of_card_eq_prime_pow hf hK
  have hpq : p ≤ Nat.card K := by
    rw [hK]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  refine rankThreeCent_of_height (τ := Tag.E6) e (m := 6) (by norm_num) (Nm := 11)
    (Nm1 := 8) ?_ ?_ ?_ (hdiff_of (by norm_num : 11 = 8 + 3) ?_) (by norm_num)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E6)
      fun α => 0 < height α ∧ (6 : ℤ) ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E6)
      fun α => 0 < height α ∧ (6 : ℤ) + 1 ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E6)
      fun α => 0 < height α ∧ (6 : ℤ) + 6 ≤ height α).trans (by decide +kernel)
  · calc p ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hpq 2
      _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_right Nat.card_pos (by norm_num)

theorem inExc_e7 :
    InExc .E7 := by
  intro p f hp hp5 hf G _ _ hmodel
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := charP_of_card_eq_prime_pow hf hK
  have hpq : p ≤ Nat.card K := by
    rw [hK]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  refine rankThreeCent_of_height (τ := Tag.E7) e (m := 9) (by norm_num) (Nm := 18)
    (Nm1 := 14) ?_ ?_ ?_ (hdiff_of (by norm_num : 18 = 14 + 4) ?_) (by norm_num)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E7)
      fun α => 0 < height α ∧ (9 : ℤ) ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E7)
      fun α => 0 < height α ∧ (9 : ℤ) + 1 ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E7)
      fun α => 0 < height α ∧ (9 : ℤ) + 9 ≤ height α).trans (by decide +kernel)
  · calc p ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hpq 2
      _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_right Nat.card_pos (by norm_num)

theorem inExc_e8 :
    InExc .E8 := by
  intro p f hp hp5 hf G _ _ hmodel
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := charP_of_card_eq_prime_pow hf hK
  have hpq : p ≤ Nat.card K := by
    rw [hK]
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  refine rankThreeCent_of_height (τ := Tag.E8) e (m := 15) (by norm_num) (Nm := 32)
    (Nm1 := 28) ?_ ?_ ?_ (hdiff_of (by norm_num : 32 = 28 + 4) ?_) (by norm_num)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E8)
      fun α => 0 < height α ∧ (15 : ℤ) ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E8)
      fun α => 0 < height α ∧ (15 : ℤ) + 1 ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E8)
      fun α => 0 < height α ∧ (15 : ℤ) + 15 ≤ height α).trans (by decide +kernel)
  · calc p ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hpq 2
      _ ≤ Nat.card K ^ 4 := Nat.pow_le_pow_right Nat.card_pos (by norm_num)

theorem inG2Two :
    InG2Two := by
  intro p f hp hp5 hf G _ _ hmodel _
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K p := charP_of_card_eq_prime_pow (by omega) hK
  refine rankThreeCent_of_height (τ := Tag.G2) e (m := 3) (by norm_num) (Nm := 3)
    (Nm1 := 2) ?_ ?_ ?_ (hdiff_of (by norm_num : 3 = 2 + 1) ?_) (by norm_num)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.G2)
      fun α => 0 < height α ∧ (3 : ℤ) ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.G2)
      fun α => 0 < height α ∧ (3 : ℤ) + 1 ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.G2)
      fun α => 0 < height α ∧ (3 : ℤ) + 3 ≤ height α).trans (by decide +kernel)
  · rw [pow_one, hK]
    exact Nat.pow_le_pow_right hp.pos hf


theorem rankThreeCent_of_twistedHeight
    {f : ℕ} (hf : 1 ≤ f) {t : TwistTag} (hord : 0 < t.order) {G : Type} [Group G] [Finite G]
    (h : TwistedChevalleyModel G t (p ^ f)) {m : ℤ} (hm : 1 ≤ m) {Nm Nm1 : ℕ}
    (hNm : {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ m ≤ height α}.ncard = Nm)
    (hNm1 : {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ m + 1 ≤ height α}.ncard =
      Nm1)
    (hNtop : {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ m + m ≤ height α}.ncard = 0)
    (hdiff : p ^ 2 * (p ^ f) ^ Nm1 ≤ (p ^ f) ^ Nm) (h3 : 3 ≤ Nm) : RankThreeCent p G := by
  obtain ⟨K, hKf, hKfin, σ, hKcard, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card t hp.out hf h
  haveI : CharP K p := charP_of_card_eq_prime_pow (f := f * t.order)
    (Nat.mul_pos (by omega) hord) (by rw [hKcard, pow_mul])
  have hσs : Function.Surjective σ.toRingHom := σ.surjective
  have hσ' : ∀ c, σ.toRingHom c = c ^ (p ^ f) := hσ
  have hq : ∀ a, Nat.card (orbitField t K σ.toRingHom a) = (p ^ f) ^ (t.orbit a).card :=
    CFSG.Timmesfeld.ExceptionalOrders.card_orbitField hp.out hf hKcard hσ'
  set C₀ := graphFixedRootGroup t K σ.toRingHom with hC₀
  have hAX : heightSeries t.tag K m ⊓ twistedFixedGroup t K σ.toRingHom ≤
      graphFixedPosUnipotent t K σ.toRingHom := inf_le_inf_right _ (heightSeries_le_posUnipotent m)
  have hAC : heightSeries t.tag K m ⊓ twistedFixedGroup t K σ.toRingHom ≤ C₀ :=
    hAX.trans (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom)
  have hBA : heightSeries t.tag K (m + 1) ⊓ twistedFixedGroup t K σ.toRingHom ≤
      heightSeries t.tag K m ⊓ twistedFixedGroup t K σ.toRingHom :=
    inf_le_inf_right _ (heightSeries_antitone (by omega))
  have hBC : heightSeries t.tag K (m + 1) ⊓ twistedFixedGroup t K σ.toRingHom ≤ C₀ :=
    hBA.trans hAC
  have hS : {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ m + m ≤ height α} = ∅ :=
    (Set.ncard_eq_zero ((finite_setOf_isRoot t.tag).subset fun α hα => hα.1)).mp hNtop
  have hbot : heightSeries t.tag K (m + m) = ⊥ := by
    unfold heightSeries rootSpan
    rw [hS]
    simp
  have hcommA : ∀ x ∈ heightSeries t.tag K m, ∀ y ∈ heightSeries t.tag K m, x * y = y * x := by
    intro x hx y hy
    have h1 : ⁅x, y⁆ ∈ ⁅heightSeries t.tag K m, heightSeries t.tag K m⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    have h2 := commutator_heightSeries_le (τ := t.tag) K m m h1
    rw [hbot, Subgroup.mem_bot] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hexp : ∀ x ∈ heightSeries t.tag K m, x ^ p = 1 := fun x hx =>
    heightSeries_pow_eq_one hcommA hx
  have hU := isPGroup_graphFixedPosUnipotent_subgroupOf (K := K) (t := t) (σ := σ.toRingHom) p
  have hidx := not_dvd_index_graphFixedPosUnipotent (K := K) (t := t) (σ := σ.toRingHom) p hσs
  have hAU : (heightSeries t.tag K m ⊓ twistedFixedGroup t K σ.toRingHom).subgroupOf C₀ ≤
      (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf C₀ := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hAX hx
  have hBA' : (heightSeries t.tag K (m + 1) ⊓ twistedFixedGroup t K σ.toRingHom).subgroupOf C₀ ≤
      (heightSeries t.tag K m ⊓ twistedFixedGroup t K σ.toRingHom).subgroupOf C₀ := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hBA hx
  have hAab : IsElemAbelian p
      ((heightSeries t.tag K m ⊓ twistedFixedGroup t K σ.toRingHom).subgroupOf C₀) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact hcommA _ (Subgroup.mem_inf.mp a.2).1 _ (Subgroup.mem_inf.mp b.2).1
    · apply Subtype.ext
      exact hexp _ (Subgroup.mem_inf.mp hx).1
  have hcomm : ∀ u ∈ (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf C₀,
      ∀ a ∈ (heightSeries t.tag K m ⊓ twistedFixedGroup t K σ.toRingHom).subgroupOf C₀,
      u * a * u⁻¹ * a⁻¹ ∈
        (heightSeries t.tag K (m + 1) ⊓ twistedFixedGroup t K σ.toRingHom).subgroupOf C₀ := by
    intro u hu a ha
    rw [Subgroup.mem_subgroupOf] at hu ha ⊢
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.mp ha
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact commutator_posUnipotent_heightSeries_le m (Subgroup.commutator_mem_commutator hu1 ha1)
    · exact mul_mem (mul_mem (mul_mem hu2 ha2) (inv_mem hu2)) (inv_mem ha2)
  have hcardA : Nat.card ((heightSeries t.tag K m ⊓ twistedFixedGroup t K σ.toRingHom).subgroupOf
      C₀) = (p ^ f) ^ Nm := by
    rw [card_subgroupOf_of_le hAC]
    have := CFSG.Timmesfeld.ExceptionalOrders.card_rootSpan_inf_twistedFixedGroup (t := t)
      (K := K) (σ := σ.toRingHom) (q := p ^ f) hσs hq
      (S := {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ m ≤ height α})
      (fun α hα => ⟨hα.1, hα.2.1⟩)
      (fun α hα => ⟨hα.1.permLattice t.cartan_perm, by
        rw [height_permLattice]; exact hα.2⟩) heightSeriesSet_closed
    rw [hNm] at this
    exact this
  have hcardB : Nat.card ((heightSeries t.tag K (m + 1) ⊓
      twistedFixedGroup t K σ.toRingHom).subgroupOf C₀) = (p ^ f) ^ Nm1 := by
    rw [card_subgroupOf_of_le hBC]
    have := CFSG.Timmesfeld.ExceptionalOrders.card_rootSpan_inf_twistedFixedGroup (t := t)
      (K := K) (σ := σ.toRingHom) (q := p ^ f) hσs hq
      (S := {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α ∧ m + 1 ≤ height α})
      (fun α hα => ⟨hα.1, hα.2.1⟩)
      (fun α hα => ⟨hα.1.permLattice t.cartan_perm, by
        rw [height_permLattice]; exact hα.2⟩) heightSeriesSet_closed
    rw [hNm1] at this
    exact this
  have hpq : p ≤ p ^ f := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.out.pos hf
  refine rankThreeCent_of_witness_map e.symm.toMonoidHom e.symm.surjective hU hidx hAU hBA' hAab
    hcomm ?_ (Or.inl ?_) (fun u _ hu => e.symm.injective (hu.trans (map_one e.symm).symm))
  · rw [hcardA, hcardB, mul_comm]
    exact hdiff
  · rw [hcardA]
    calc p ^ 3 ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hpq 3
      _ ≤ (p ^ f) ^ Nm := Nat.pow_le_pow_right (pow_pos hp.out.pos f) h3

theorem inExc_twistedE6 :
    InExc .twistedE6 := by
  intro p f hp hp5 hf G _ _ hmodel
  obtain ⟨hadm, hm⟩ := hmodel
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≤ p ^ f := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  refine rankThreeCent_of_twistedHeight hf (t := TwistTag.E6) (by decide) hm (m := 6)
    (by norm_num) (Nm := 11) (Nm1 := 8) ?_ ?_ ?_ (hdiff_of (by norm_num : 11 = 8 + 3) ?_)
    (by norm_num)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E6)
      fun α => 0 < height α ∧ (6 : ℤ) ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E6)
      fun α => 0 < height α ∧ (6 : ℤ) + 1 ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.E6)
      fun α => 0 < height α ∧ (6 : ℤ) + 6 ≤ height α).trans (by decide +kernel)
  · calc p ^ 2 ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hpq 2
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_right (pow_pos hp.pos f) (by norm_num)

theorem inExc_trialityD4 :
    InExc .trialityD4 := by
  intro p f hp hp5 hf G _ _ hmodel
  obtain ⟨hadm, hm⟩ := hmodel
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : p ≤ p ^ f := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  refine rankThreeCent_of_twistedHeight hf (t := TwistTag.D4) (by decide) hm (m := 3)
    (by norm_num) (Nm := 5) (Nm1 := 2) ?_ ?_ ?_ (hdiff_of (by norm_num : 5 = 2 + 3) ?_)
    (by norm_num)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.D4)
      fun α => 0 < height α ∧ (3 : ℤ) ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.D4)
      fun α => 0 < height α ∧ (3 : ℤ) + 1 ≤ height α).trans (by decide +kernel)
  · exact (CFSG.Timmesfeld.ExceptionalOrders.ncard_setOf_isRoot_and (τ := Tag.D4)
      fun α => 0 < height α ∧ (3 : ℤ) + 3 ≤ height α).trans (by decide +kernel)
  · calc p ^ 2 ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hpq 2
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_right (pow_pos hp.pos f) (by norm_num)

end Chevalley

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
