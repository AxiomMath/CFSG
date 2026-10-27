module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiOppositeRootCenter
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiRootA
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem le_inner_of_isPGroup_two {H : Type*} [Group H] (hodd : Odd (Nat.card (Outer H)))
    (P : Subgroup (MulAut H)) (hP : IsPGroup 2 P) : P ≤ inner H := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have h1 : orderOf (x : Outer H) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one])
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer H)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h3 : orderOf (x : Outer H) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 (orderOf_dvd_natCard _)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).1 h3

variable {a : ℕ} {K : Type} [Field K]

theorem suzuki_tits_pow_four_ne_one (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {φ : K ≃+* K} (hφ : ∀ x, φ x = x ^ 2 ^ (a + 1)) : φ ^ 4 ≠ 1 := by
  obtain ⟨-, -, hθθ, -⟩ := suzuki_frobenius_exponents a K hK
  intro h4
  have hψ : ∀ x : K, (φ ^ 2) x = x ^ 2 := fun x => by
    rw [sq, RingAut.mul_apply, hφ, hφ, hθθ]
  have hx : ∀ x : K, x ^ 4 = x := fun x => by
    have h := ringAut_pow_apply_of_sq hψ 2 x
    rw [← pow_mul, h4, RingAut.one_apply] at h
    norm_num at h
    exact h.symm
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K (by norm_num : 1 < 4)
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (Polynomial.X ^ 4 - Polynomial.X : Polynomial K) (f := id) Function.injective_id
    (fun x => by simp [hx x])
    (by
      rw [hdeg, hcard]
      calc 4 < 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hP, Polynomial.natDegree_zero] at hdeg
  omega

theorem odd_card_outer_suzukiGroup
    (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Odd (Nat.card (Outer (suzukiGroup a K))) := by
  obtain ⟨hchar, ⟨φ, hφ⟩, -⟩ := suzuki_frobenius_exponents a K hK
  let _ : Module (ZMod 2) K := (ZMod.algebra K 2).toModule
  obtain ⟨-, -, hres, -, -, hcardKer, hcardAut, -⟩ := suzuki_two_A_automorphism_solvable (K := K)
    (by omega : 1 ≤ 2 * a + 1) hK φ (suzuki_tits_pow_four_ne_one ha hK hφ)
  obtain ⟨ι, -, -, hι0⟩ := Suzuki_root_A_isomorphism hK φ hφ
  obtain ⟨-, -, -, -, -, hprod, -⟩ := Suzuki_model_opposite_root_interface ha hK
  set U' := (suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom
  set C := pairAutSubgroup (suzukiU a K) U'
  set Ψ := suzukiQuotAction (K := K) (φ := φ)
  let f : C →* LinearMap.GeneralLinearGroup (ZMod 2) K :=
    Ψ.comp ((MulAut.congr ι).toMonoidHom.comp (pairAutRestrict (suzukiU a K) U'))
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_one f).2 fun β hβ => ?_
    have hα : ∀ x, (Ψ (MulAut.congr ι (pairAutRestrict (suzukiU a K) U' β)) :
        K →ₗ[ZMod 2] K) x = ((1 : Kˣ) : K) * (1 : K ≃+* K) x := fun x => by
      change ((f β : LinearMap.GeneralLinearGroup (ZMod 2) K) : K →ₗ[ZMod 2] K) x = _
      rw [hβ]
      simp
    have hQ : ∀ b : K, (β : MulAut (suzukiGroup a K)) (suzukiSElt a K 0 b) =
        suzukiSElt a K 0 b := by
      intro b
      have h1 : ι.symm ⟨0, b⟩ = ⟨suzukiSElt a K 0 b, suzukiSElt_mem_suzukiU a K 0 b⟩ :=
        ι.symm_apply_eq.2 (hι0 b).symm
      have h2 : pairAutRestrict (suzukiU a K) U' β (ι.symm ⟨0, b⟩) = ι.symm ⟨0, b⟩ := by
        rw [ι.eq_symm_apply]
        refine (hres _ 1 1 hα b).trans (BinExt.ext rfl ?_)
        change ((1 : Kˣ) : K) * φ ((1 : Kˣ) : K) * (1 : K ≃+* K) b = b
        rw [Units.val_one, map_one, one_mul, one_mul]
        rfl
      rw [h1] at h2
      exact congrArg Subtype.val h2
    exact Subtype.ext (CFSG.ShultStronglyClosedTI.suzuki_opposite_root_center_action_faithful
      ha hK β β.2.1 β.2.2 hQ)
  have hcardRange : Nat.card Ψ.range = (2 ^ (2 * a + 1) - 1) * (2 * a + 1) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Ψ).toEquiv, hcardKer, hcardAut] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (h.symm.trans (by ring))
  have hCdvd : Nat.card C ∣ (2 ^ (2 * a + 1) - 1) * (2 * a + 1) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, ← hcardRange]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨β, rfl⟩
    exact ⟨_, rfl⟩
  have hodd : Odd ((2 ^ (2 * a + 1) - 1) * (2 * a + 1)) := by
    have h1 : 2 ^ (2 * a + 1) = 2 * 2 ^ (2 * a) := by rw [pow_succ, mul_comm]
    have h2 : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
    refine Nat.odd_mul.2 ⟨Nat.odd_iff.2 (by omega), ⟨a, rfl⟩⟩
  let π : C →* Outer (suzukiGroup a K) :=
    (QuotientGroup.mk' (inner (suzukiGroup a K))).comp C.subtype
  have hπ : Function.Surjective π := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (suzukiGroup a K)) q
    obtain ⟨g, β, hβ, rfl⟩ := hprod α
    refine ⟨⟨β, hβ⟩, ?_⟩
    change ((β : MulAut (suzukiGroup a K)) : Outer (suzukiGroup a K)) =
      ((MulAut.conj g * β : MulAut (suzukiGroup a K)) : Outer (suzukiGroup a K))
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner (suzukiGroup a K))
      (MulAut.conj g)).2 ⟨g, rfl⟩, one_mul]
  exact (hodd.of_dvd_nat hCdvd).of_dvd_nat (Subgroup.card_dvd_of_surjective hπ)

theorem suzuki_outer_automorphism_group_has_odd_order (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Odd (Nat.card (Outer (suzukiGroup a K))) ∧
      ∀ P : Subgroup (MulAut (suzukiGroup a K)), IsPGroup 2 P → P ≤ inner (suzukiGroup a K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hodd := odd_card_outer_suzukiGroup ha hK
  exact ⟨hodd, le_inner_of_isPGroup_two hodd⟩

theorem suzukiOuterOdd : SuzukiOuterOdd := by
  intro m hm
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  have h := (suzuki_outer_automorphism_group_has_odd_order hm hK).1
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK)).toEquiv] at h
  exact h

end CFSG.ProperTwoGeneratedCore.HighRankPair
