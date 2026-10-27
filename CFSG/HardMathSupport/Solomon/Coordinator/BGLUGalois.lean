module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUTheta
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Module

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem efix_eq_fixedPoints (g : K ≃+* K) :
    Efix g = FixedPoints.subfield (Subgroup.zpowers (g : RingAut K)) K := by
  ext x
  rw [mem_Efix]
  constructor
  · intro hx
    rintro ⟨y, hy⟩
    have hle : Subgroup.zpowers (g : RingAut K) ≤ MulAction.stabilizer (RingAut K) x := by
      rw [Subgroup.zpowers_le]
      exact hx
    exact hle hy
  · intro hx
    exact hx ⟨g, Subgroup.mem_zpowers g⟩

theorem finrank_efix (g : K ≃+* K) : finrank (Efix g) K = orderOf (g : RingAut K) := by
  have := Fintype.ofFinite (Subgroup.zpowers (g : RingAut K))
  have h := FixedPoints.finrank_eq_card (Subgroup.zpowers (g : RingAut K)) K
  rw [← efix_eq_fixedPoints] at h
  rw [h, ← Nat.card_eq_fintype_card, Nat.card_zpowers]

theorem natCard_eq_pow_orderOf (g : K ≃+* K) :
    Nat.card K = Nat.card (Efix g) ^ orderOf (g : RingAut K) := by
  rw [← finrank_efix, ← Module.natCard_eq_pow_finrank (K := Efix g) (V := K)]

variable (ι ρ : K ≃+* K) in
@[expose] def kfix : Subfield K := Efix ι ⊓ Efix ρ

omit [Finite K] in
theorem orderOf_of_involution (ι : K ≃+* K) (hι2 : ∀ x, ι (ι x) = x) (hne : ∃ x, ι x ≠ x) :
    orderOf (ι : RingAut K) = 2 := by
  apply orderOf_eq_prime
  · ext x
    show ι (ι x) = x
    exact hι2 x
  · intro h
    obtain ⟨x, hx⟩ := hne
    apply hx
    have := congrArg (fun g : RingAut K => g x) h
    exact this

omit [Finite K] in
theorem rho3_apply (ρ : K ≃+* K) (h : orderOf (ρ : RingAut K) = 3) (x : K) :
    ρ (ρ (ρ x)) = x := by
  have h1 : (ρ : RingAut K) ^ 3 = 1 := by
    rw [← h]; exact pow_orderOf_eq_one _
  have := congrArg (fun g : RingAut K => g x) h1
  exact this

omit [Finite K] in
theorem orderOf_mul_six (ι ρ : K ≃+* K) (hι2 : orderOf (ι : RingAut K) = 2)
    (hρ3 : orderOf (ρ : RingAut K) = 3) (hcomm : ∀ x, ρ (ι x) = ι (ρ x)) :
    orderOf ((ι : RingAut K) * ρ) = 6 := by
  have hc : Commute (ι : RingAut K) ρ := by
    ext x
    exact (hcomm x).symm
  rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hι2, hρ3]; norm_num), hι2, hρ3]

omit [Finite K] in
theorem efix_mul_eq (ι ρ : K ≃+* K) (hι2 : ∀ x, ι (ι x) = x) (hρ3 : ∀ x, ρ (ρ (ρ x)) = x)
    (hcomm : ∀ x, ρ (ι x) = ι (ρ x)) :
    Efix ((ι : RingAut K) * ρ) = kfix ι ρ := by
  ext x
  rw [kfix, Subfield.mem_inf, mem_Efix, mem_Efix, mem_Efix]
  constructor
  · intro hx
    have hx' : ι (ρ x) = x := hx
    have h1 : ρ x = ι x := by
      have := congrArg ι hx'
      rwa [hι2] at this
    have h2 : ρ (ρ x) = x := by rw [h1, hcomm, hx']
    have h3 : ρ x = x := by
      have := hρ3 x
      rwa [h2] at this
    exact ⟨by rw [← h1]; exact h3, h3⟩
  · rintro ⟨h1, h2⟩
    show ι (ρ x) = x
    rw [h2, h1]

theorem galois_counts (ι ρ : K ≃+* K) (hι2 : ∀ x, ι (ι x) = x) (hne : ∃ x, ι x ≠ x)
    (hρ3 : orderOf (ρ : RingAut K) = 3) (hcomm : ∀ x, ρ (ι x) = ι (ρ x)) :
    Nat.card (Efix ι) = Nat.card (kfix ι ρ) ^ 3 ∧
      Nat.card (Efix ρ) = Nat.card (kfix ι ρ) ^ 2 ∧
      Nat.card K = Nat.card (Efix ι) ^ 2 := by
  have h2 := orderOf_of_involution ι hι2 hne
  have h6 := orderOf_mul_six ι ρ h2 hρ3 hcomm
  have e6 := natCard_eq_pow_orderOf ((ι : RingAut K) * ρ)
  rw [efix_mul_eq ι ρ hι2 (rho3_apply ρ hρ3) hcomm, h6] at e6
  have eι := natCard_eq_pow_orderOf ι
  have eρ := natCard_eq_pow_orderOf ρ
  rw [h2] at eι
  rw [hρ3] at eρ
  set a := Nat.card (kfix ι ρ)
  set e := Nat.card (Efix ι)
  set f := Nat.card (Efix ρ)
  refine ⟨?_, ?_, eι⟩
  · have : e ^ 2 = (a ^ 3) ^ 2 := by rw [← eι, e6]; ring
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this
  · have : f ^ 3 = (a ^ 2) ^ 3 := by rw [← eρ, e6]; ring
    exact (Nat.pow_left_injective (by norm_num : 3 ≠ 0)) this

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
