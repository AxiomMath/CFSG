module

public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Basic
public import CFSG.LieType.Chevalley.RootLocalComponentFree
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
import CFSG.LieType.BorelTits.Classical

public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

section Datum

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isCharacteristicP_centralizer_of_rootWeightDatum (D : RootWeightDatum K) {z : ↥D.group}
    (hz : orderOf z = 2) :
    CFSG.IsCharacteristicP 2 (Subgroup.centralizer ({z} : Set ↥D.group)) := by
  have hp := isPGroup_zpowers_of_orderOf_eq_two hz
  have h := D.defining_characteristic_root_local_groups_component_free 2 (Subgroup.zpowers z) hp.1
    hp.2 (Subgroup.centralizer ((Subgroup.zpowers z : Subgroup ↥D.group) : Set ↥D.group))
    (Or.inr rfl)
  have heq := centralizer_zpowers_eq z
  rw [heq] at h
  exact h.1

theorem noNonsolvableClassical_of_rootWeightDatum (D : RootWeightDatum K) :
    NoNonsolvableClassical ↥D.group := by
  have : Finite (ModGL D.tag K) := finite_modGL
  exact NoNonsolvableClassical.of_isCharacteristicP fun _ hz =>
    isCharacteristicP_centralizer_of_rootWeightDatum D hz

end Datum

theorem noNonsolvableClassical_adjointQuotient (τ : Tag) {K : Type} [Field K] [Finite K]
    [CharP K 2] : NoNonsolvableClassical (AdjointQuotient τ K) := by
  have hc : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let e : AdjointQuotient τ K ≃* ↥(adjointGroup τ K) :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  exact NoNonsolvableClassical.of_mulEquiv e
    (noNonsolvableClassical_of_rootWeightDatum (RootWeightDatum.ordinary τ : RootWeightDatum K))

theorem ringEquiv_pow_apply {K : Type} [Field K] {q : ℕ} (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q)
    (k : ℕ) (c : K) : (σ ^ k) c = c ^ (q ^ k) := by
  induction k generalizing c with
  | zero => simp
  | succ k ih => rw [pow_succ', RingAut.mul_apply, hσ, ih, ← pow_mul, pow_succ]

theorem noNonsolvableClassical_graphFixedRootGroup (t : TwistTag) {K : Type} [Field K] [Finite K]
    [CharP K 2] (σ : K ≃+* K) (hσ : σ ^ t.order = 1) :
    NoNonsolvableClassical ↥(graphFixedRootGroup t K σ.toRingHom) :=
  noNonsolvableClassical_of_rootWeightDatum (RootWeightDatum.fixed t σ hσ : RootWeightDatum K)

theorem noNonsolvableClassical_derivedCentralQuotient_twistedFixedGroup (t : TwistTag) {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ t.order)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    NoNonsolvableClassical (DerivedCentralQuotient (twistedFixedGroup t K σ)) := by
  have hKp : Nat.card K = 2 ^ (f * t.order) := by rw [hK, ← pow_mul]
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hKp
  obtain ⟨-, -, hder, -⟩ := finite_fixed_root_group_perfect t Nat.prime_two hf K hK σ hσ
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hc : Subgroup.center ↥(graphFixedRootGroup t K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot hsurj
  let e₁ : ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ ≃* ↥(graphFixedRootGroup t K σ) :=
    MulEquiv.subgroupCongr hder
  have hcH : Subgroup.center ↥⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e₁ x ∈ Subgroup.center ↥(graphFixedRootGroup t K σ) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := e₁.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx w]
    rw [hc, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (e₁.injective (by rw [h1, map_one]))
  let e : DerivedCentralQuotient (twistedFixedGroup t K σ) ≃*
      ↥(graphFixedRootGroup t K σ) :=
    ((QuotientGroup.quotientMulEquivOfEq hcH).trans QuotientGroup.quotientBot).trans e₁
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, hsurj⟩
  have hσ' : σ' ^ t.order = 1 := by
    ext c
    have h1 := ringEquiv_pow_apply σ' (q := 2 ^ f) hσ t.order c
    rw [h1]
    have := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rfl
  exact NoNonsolvableClassical.of_mulEquiv e (noNonsolvableClassical_graphFixedRootGroup t σ' hσ')

theorem noNonsolvableClassical_of_untwistedChevalleyModel {X : Type} [Group X] {τ : Tag} {f : ℕ}
    (h : UntwistedChevalleyModel X τ (2 ^ f)) : NoNonsolvableClassical X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq hK
  exact NoNonsolvableClassical.of_mulEquiv e (noNonsolvableClassical_adjointQuotient τ)

theorem noNonsolvableClassical_of_twistedChevalleyModel {X : Type} [Group X] {t : TwistTag}
    {f : ℕ} (hf : 1 ≤ f) (h : TwistedChevalleyModel X t (2 ^ f)) : NoNonsolvableClassical X := by
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  exact NoNonsolvableClassical.of_mulEquiv e
    (noNonsolvableClassical_derivedCentralQuotient_twistedFixedGroup t hf hK σ hσ)

theorem noNonsolvableClassical_of_chevalleyExceptionalModel {X : Type} [Group X]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {f : ℕ}
    (h : ChevalleyExceptionalModel X t 2 f) : NoNonsolvableClassical X := by
  obtain ⟨⟨-, hf, -⟩, hmodel⟩ := h
  cases t <;> first
    | exact hmodel.elim
    | exact noNonsolvableClassical_of_untwistedChevalleyModel hmodel
    | exact noNonsolvableClassical_of_twistedChevalleyModel hf hmodel

end CFSG.ClassicalInvolution
