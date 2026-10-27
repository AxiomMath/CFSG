module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQOrd
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderLargeRee

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FQ

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions
    large_Ree_full_inner_field_automorphism_normal_form)
open CFSG.RankThree.Chevalley.SteinbergBT (card_fixSubfield)

open CFSG.HardMathSupport.Lang.Coordinator CFSG.Assembly


theorem ree_card_fixedSubgroup {R : Type} [Group R] [Finite R] {f : ℕ}
    (hR : ReeTitsModel R .twistedF4 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (α : MulAut R)
    (hαp : α ^ p = 1) (hαin : α ∉ inner R) :
    ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) = lieOrderNumerator .twistedF4 0 (2 ^ f₀) := by
  obtain ⟨a, F, _, _, _, hfa, hFcard, ⟨e⟩⟩ :
      ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F F4.prime),
        f = 2 * a + 1 ∧ Nat.card F = 2 ^ f ∧ Nonempty (R ≃* F4.reeGamma F a) := by
    obtain ⟨-, -, -, -, -, -, hmain⟩ :=
      large_Ree_model_field_outer_group_and_inner_involutions R 2 f hR
    obtain ⟨-, a, hfa, F, _, _, hFcard, he⟩ := hR
    have : CharP F F4.prime := by
      have : Fintype F := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
        rw [← Nat.card_eq_fintype_card, hFcard])
    obtain ⟨⟨e⟩, -⟩ := hmain a F hfa hFcard he
    exact ⟨a, F, inferInstance, inferInstance, this, hfa, hFcard, ⟨e⟩⟩
  have hf3 : 3 ≤ f := hR.1.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hFcard
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (F4.reeGamma F a) := Finite.of_equiv R e.toEquiv
  set α' : MulAut (F4.reeGamma F a) := MulAut.congr e α with hα'
  have hα'p : α' ^ p = 1 := by rw [hα', ← map_pow, hαp, map_one]
  have hα'inn : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (F4.reeGamma F a) :=
    fun h => hαin ((congr_mem_inner_iff e α).mp h)
  obtain ⟨-, hNF, ⟨Ψ, hΨ⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha F hK
  obtain ⟨⟨x, β⟩, hxβ, -⟩ := hNF α'
  have hΨα : Ψ ⟨x, β⟩ = α' := by rw [hΨ x β]; exact hxβ.symm
  let Θ : MulAut (F4.reeGamma F a) →* (F ≃+* F) :=
    SemidirectProduct.rightHom.comp Ψ.symm.toMonoidHom
  have hΘα : Θ α' = β := by
    show SemidirectProduct.rightHom (Ψ.symm α') = β
    rw [← hΨα, MulEquiv.symm_apply_apply]
    rfl
  have hβp : β ^ p = 1 := by
    rw [← hΘα, ← map_pow, hα'p, map_one]
  have hone : F4.reeGammaFieldAut F a 1 = 1 := by rw [← reeGammaFieldAutHom_apply, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα'inn
    rw [h, hone, mul_one] at hxβ
    exact ⟨x, hxβ.symm⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj a hK hp β hβord α'
    hα'p ⟨x, hxβ⟩
  obtain ⟨b, hbp, hbcard, hfix⟩ := largeRee_fixed_data_of_odd hK hp hp2 β hβord
  have : Finite (fixSubfield β) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP (fixSubfield β) F4.prime := by
    have : Fintype (fixSubfield β) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (p := 2) (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hbcard])
  have hcard1 : Nat.card (fixedSubgroup α) = Nat.card (fixedSubgroup α') :=
    (card_fixedSubgroup_congr e α).symm
  have hcard2 : Nat.card (fixedSubgroup α') =
      Nat.card (fixedSubgroup (F4.reeGammaFieldAut F a β)) :=
    (card_fixedSubgroup_eq_of_intertwine (MulAut.conj g : _ ≃* _) _ α' fun y => by
      rw [hg]
      simp [MulAut.mul_apply]
      group).symm
  have hFix : fixedSubgroup (F4.reeGammaFieldAut F a β) =
      (F4.reeGammaFieldAut F a β).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  have hcard3 : Nat.card (fixedSubgroup (F4.reeGammaFieldAut F a β)) =
      Nat.card (F4.reeGamma (fixSubfield β) b) := by
    rw [hFix]
    refine (Nat.card_congr (((F4.reeGammaFieldAut F a β).toMonoidHom.eqLocus
        (MonoidHom.id _)).equivMapOfInjective (F4.reeGamma F a).subtype
        (F4.reeGamma F a).subtype_injective |>.trans
        (MulEquiv.subgroupCongr hfix)).toEquiv).trans ?_
    exact Nat.card_congr ((F4.reeGamma (fixSubfield β) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := F4.tag) (fixSubfield β).subtype)).symm.toEquiv
  refine ⟨2 * b + 1, by rw [mul_comm, hbp, hfa], ?_⟩
  rw [hcard1, hcard2, hcard3]
  have hord := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    b (fixSubfield β) hbcard).1
  have hq2 : 2 ≤ 2 ^ (2 * b + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hord, reeF4_order_eq_numerator _ hq2]

theorem stOrderBody_ree {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I F : Set (MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)))) (hF : InnFree p F) :
    StOrderBody p (LargeEvenCenterQuot (LargeEvenTwF4H a K)) I F := by
  intro f hf hord
  have hR : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H a K)) .twistedF4 2 (2 * a + 1) :=
    ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩, a, rfl,
      CFSG.StandardType.reeTitsRelationModel_largeEven a hK⟩
  have hL : CFSG.Blueprint.LieModel (LargeEvenCenterQuot (LargeEvenTwF4H a K)) .twistedF4 0 2
      (2 * a + 1) := Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))
  have hcard := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hL
  have hfin : Finite (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    obtain ⟨r, hr, h⟩ := (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedF4'
      (e := 2 * a + 1) (by omega)).two
    show CFSG.Open.ordTwistedF4 _ ≠ 0
    rw [h]
    exact (Nat.mul_pos (by positivity) hr.pos).ne'
  have hαp : f ^ p = 1 := hord ▸ pow_orderOf_eq_one f
  obtain ⟨f₀, hf0, hfix⟩ := ree_card_fixedSubgroup hR hp hp2 f hαp (fun h => hF f hf hord h)
  have hf1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf0; omega
    · exact h0
  have h1 : fixNum f = CFSG.Open.ordTwistedF4 (2 ^ f₀) := by
    rw [fixNum_eq_card_fixSub]
    exact hfix
  rw [h1, hcard]
  show twoPart (CFSG.Open.ordTwistedF4 (2 ^ f₀)) ^ p =
    twoPart (CFSG.Open.ordTwistedF4 (2 ^ (2 * a + 1)))
  rw [twoPart_of_profile (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedF4' hf1),
    twoPart_of_profile (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordTwistedF4'
      (e := 2 * a + 1) (by omega)), ← pow_mul]
  congr 1
  rw [hf0]
  ring

end FQ

end CFSG.LocalAnalysis.GLTheoremA
