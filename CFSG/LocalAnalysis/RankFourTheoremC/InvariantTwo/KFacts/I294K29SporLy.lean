module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporWit
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporOut
public import CFSG.RankThree.PartOne.KS.LyFiveCore
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.RankThree.Native CFSG.Sporadic.Ly
open scoped commutatorElement

section CertificateInstances



theorem lyJ_factorization_five : (Nat.card J).factorization 5 = 6 := by
  rw [card_J, Nat.factorization_def _ Nat.prime_five,
    show (51765179004000000 : ℕ) = 5 ^ 6 * 3312971456256 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem lyCxJ_factorization_five :
    (Nat.card (centralizer ({lyFiveXJ} : Set J))).factorization 5 = 6 := by
  rw [CFSG.RankThree.PartOne.LyFive.lyFive_card_x, Nat.factorization_def _ Nat.prime_five,
    show (2250000 : ℕ) = 5 ^ 6 * 144 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem rankThreeWitness_xJ_pow (e : ℕ) : RankThreeWitness 5 (lyFiveXJ ^ e) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C := centralizer ({lyFiveXJ} : Set J)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 C))
  have hP : Nat.card (P.map C.subtype) = 5 ^ (Nat.card J).factorization 5 := by
    rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity,
      lyCxJ_factorization_five, lyJ_factorization_five]
  refine Or.inl ⟨Sylow.ofCard _ hP, ?_⟩
  rw [Sylow.coe_ofCard]
  rintro _ ⟨c, -, rfl⟩
  have hc := Subgroup.mem_centralizer_singleton_iff.1 c.2
  exact Subgroup.mem_centralizer_singleton_iff.2 ((Commute.pow_right hc e).eq)

theorem rankThreeWitness_yJ_pow (e : ℕ) (he1 : 1 ≤ e) (he4 : e ≤ 4) :
    RankThreeWitness 5 ((lyFiveVJ 0 * lyFiveVJ 1) ^ e) := by
  have h := lyFiveQRelJ
  have hv0 := FiveQRel.v_mem (x := lyFiveXJ) (v := lyFiveVJ) 0
  have hv1 := FiveQRel.v_mem (x := lyFiveXJ) (v := lyFiveVJ) 1
  have hy : (lyFiveVJ 0 * lyFiveVJ 1) ^ e ∈ fiveQ lyFiveXJ lyFiveVJ :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ hv0 hv1) e
  refine Or.inr (Or.inl ⟨fiveQ lyFiveXJ lyFiveVJ, zpowers lyFiveXJ, fun y hy' => h.pow_five_of_mem hy',
    ?_, ?_, ?_, ?_, ?_, hy, ?_⟩)
  · rintro _ ⟨k, rfl⟩
    exact Subgroup.zpow_mem _ FiveQRel.x_mem k
  · intro z hz y hy'
    exact (h.zpowers_comm hz hy').eq
  · rw [Nat.card_zpowers, h.orderOf_x]
  · intro y hy' w hw
    have := h.comm_mem hy' hw
    rwa [commutatorElement_def] at this
  · rw [h.card_fiveQ]; norm_num
  · intro hz
    have h0 := (h.coord_eq_zero_iff ⟨_, hy⟩).2 hz
    have hq : (⟨(lyFiveVJ 0 * lyFiveVJ 1) ^ e, hy⟩ : fiveQ lyFiveXJ lyFiveVJ) =
        (⟨lyFiveVJ 0, hv0⟩ * ⟨lyFiveVJ 1, hv1⟩) ^ e := rfl
    have hc0 : h.coord ⟨lyFiveVJ 0, hv0⟩ = Pi.single 0 1 := by
      have := h.coord_nf 0 (Pi.single 0 1)
      convert this using 2
      simp [fiveNF, Pi.single_apply, show (1 : ZMod 5).val = 1 from rfl]
    have hc1 : h.coord ⟨lyFiveVJ 1, hv1⟩ = Pi.single 1 1 := by
      have := h.coord_nf 0 (Pi.single 1 1)
      convert this using 2
      simp [fiveNF, Pi.single_apply, show (1 : ZMod 5).val = 1 from rfl]
    have hcoord : h.coord ⟨_, hy⟩ = e • (Pi.single 0 1 + Pi.single 1 1) := by
      have := congrArg Multiplicative.toAdd (map_pow h.coordHom (⟨lyFiveVJ 0, hv0⟩ *
        ⟨lyFiveVJ 1, hv1⟩) e)
      rw [← hq, map_mul] at this
      change h.coord _ = _ at this
      rw [this]
      change e • (h.coord _ + h.coord _) = _
      rw [hc0, hc1]
    rw [hcoord] at h0
    have h00 := congrFun h0 0
    simp at h00
    interval_cases e <;> revert h00 <;> decide


theorem sporadicClassWitnessNative_Ly_five :
    ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier .Ly) →
      ∀ x : S, orderOf x = 5 → RankThreeWitness 5 x := by
  intro S _ _ ⟨e⟩ x hx
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨f, -⟩ : ∃ f : S ≃* J, f = e.trans lyEquivJ := ⟨_, rfl⟩
  have hfx : orderOf (f x) = 5 := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨g, r, hr, k, hk1, hk4, hg⟩ := CFSG.RankThree.PartOne.LyFive.lyFive_cover_J (f x) hfx
  have hw : RankThreeWitness 5 (r ^ k) := by
    rcases hr with rfl | hr
    · exact rankThreeWitness_xJ_pow k
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      exact rankThreeWitness_yJ_pow k hk1 hk4
  rw [← hg] at hw
  exact @RankThreeWitness.of_mulEquiv S J _ inferInstance _ 5 _ f x (RankThreeWitness.of_conj g hw)


end CertificateInstances

section CertificateInstancesNative


theorem sporadicClassWitnessAt_Ly_five : SporadicClassWitnessAt .Ly 5 :=
  sporadicClassWitnessAt_of_native sporadicClassWitnessNative_Ly_five

end CertificateInstancesNative

end CFSG.LocalAnalysis.RankFourTheoremC
