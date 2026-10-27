module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverTorus

public section

namespace CFSG.ProperTwoGeneratedCore.BenderFacts

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

theorem card_sq_eq_congr {A B : Type*} [Group A] [Group B] (θ : A ≃* B) (z : A) :
    Nat.card {x : A // x ^ 2 = z} = Nat.card {y : B // y ^ 2 = θ z} :=
  Nat.card_congr
    { toFun := fun x => ⟨θ x, by rw [← map_pow, x.2]⟩
      invFun := fun y => ⟨θ.symm y, by rw [← map_pow, y.2, MulEquiv.symm_apply_apply]⟩
      left_inv := fun x => Subtype.ext (θ.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (θ.apply_symm_apply y) }

theorem nonempty_sylow_mulEquiv_of_mulEquiv {p : ℕ} [Fact p.Prime] {J G : Type*} [Group J]
    [Group G] [Finite J] (e : J ≃* G) (R : Sylow p J) (P : Sylow p G) :
    Nonempty ((R : Subgroup J) ≃* (P : Subgroup G)) := by
  have : Finite G := Finite.of_equiv _ e.toEquiv
  set R' : Sylow p G := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective R
  have hR' : (R' : Subgroup G) = (R : Subgroup J).map e.toMonoidHom := rfl
  exact ⟨((R : Subgroup J).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr hR'.symm).trans (Sylow.equiv R' P))⟩

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)

theorem suzukiCoverRootElement_sq (hm : 0 < m) (a b : K) :
    suzukiCoverRootElement m a b ^ 2 = suzukiCoverRootElement m 0 (a * suzukiCoverTits m a) := by
  rw [pow_two, suzukiCoverRootElement_mul m hm, CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, zero_add]

theorem existsUnique_mul_suzukiCoverTits_eq {r : K} (hr : r ≠ 0) :
    ∃! a : K, a * suzukiCoverTits m a = r := by
  obtain ⟨x, hx⟩ := (suzukiCoverNorm_bijective m).2 (Units.mk0 r hr)
  have hx' : (x : K) * suzukiCoverTits m (x : K) = r := by
    rw [← suzukiCoverNorm_coe, hx, Units.val_mk0]
  refine ⟨x, hx', fun a ha => ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact hr ha.symm
  have hu : Units.mk0 a ha0 = x := by
    apply (suzukiCoverNorm_bijective m).1
    apply Units.ext
    rw [suzukiCoverNorm_coe, suzukiCoverNorm_coe, Units.val_mk0, ha, hx']
  rw [← hu, Units.val_mk0]

theorem exists_eq_suzukiCoverRootElement_of_sq_eq_one (hm : 0 < m)
    {z : suzukiCoverRoot m} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    ∃ r : K, r ≠ 0 ∧ z = suzukiCoverRootElement m 0 r := by
  obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective m z
  rw [suzukiCoverRootElement_sq m hm, ← suzukiCoverRootElement_zero_zero] at hz2
  have ha : a * suzukiCoverTits m a = 0 :=
    (suzukiCoverRootElement_injective m _ _ _ _ hz2).2
  have ha0 : a = 0 := by
    rcases mul_eq_zero.mp ha with h | h
    · exact h
    · exact (map_eq_zero_iff _ (suzukiCoverTits m).injective).mp h
  subst ha0
  refine ⟨b, fun hb => hz1 ?_, rfl⟩
  rw [hb, suzukiCoverRootElement_zero_zero]

theorem card_sq_eq_suzukiCoverRootElement (hm : 0 < m) {r : K} (hr : r ≠ 0) :
    Nat.card {x : suzukiCoverRoot m // x ^ 2 = suzukiCoverRootElement m 0 r} =
      2 ^ (2 * m + 1) := by
  obtain ⟨a₀, ha₀, huniq⟩ := existsUnique_mul_suzukiCoverTits_eq m hr
  have hroot : ∀ a b : K, suzukiCoverRootElement m a b ^ 2 = suzukiCoverRootElement m 0 r ↔
      a = a₀ := by
    intro a b
    rw [suzukiCoverRootElement_sq m hm]
    constructor
    · intro h
      exact huniq a (suzukiCoverRootElement_injective m _ _ _ _ h).2
    · rintro rfl
      rw [ha₀]
  rw [← GaloisField.card 2 (2 * m + 1) (by omega)]
  refine Nat.card_congr
    { toFun := fun x => ((((x.1 : SuzukiMatrixGroup m) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) 0 2)
      invFun := fun b => ⟨suzukiCoverRootElement m a₀ b, (hroot a₀ b).mpr rfl⟩
      left_inv := fun x => ?_
      right_inv := fun b => ?_ }
  · obtain ⟨a, b, hab⟩ := suzukiCoverRootElement_surjective m x.1
    have ha : a = a₀ := (hroot a b).mp (hab ▸ x.2)
    apply Subtype.ext
    simp only
    rw [← hab, ha]
    simp [SuzukiRootGL, SuzukiRootMatrix]
  · simp [SuzukiRootGL, SuzukiRootMatrix]

theorem card_sq_eq_of_mem_suzukiCoverRoot (hm : 0 < m) {z : suzukiCoverRoot m} (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) : Nat.card {x : suzukiCoverRoot m // x ^ 2 = z} = 2 ^ (2 * m + 1) := by
  obtain ⟨r, hr, rfl⟩ := exists_eq_suzukiCoverRootElement_of_sq_eq_one m hm hz1 hz2
  exact card_sq_eq_suzukiCoverRootElement m hm hr

theorem card_sq_eq_of_mulEquiv_suzukiMatrixGroup (hm : 0 < m) {J : Type*} [Group J]
    (e : J ≃* SuzukiMatrixGroup m) (R : Sylow 2 J) {z : (R : Subgroup J)} (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) : Nat.card {x : (R : Subgroup J) // x ^ 2 = z} = 2 ^ (2 * m + 1) := by
  have : Finite J := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨θ⟩ : Nonempty ((R : Subgroup J) ≃* suzukiCoverRoot m) :=
    nonempty_sylow_mulEquiv_of_mulEquiv e R (suzukiCoverSylow m hm)
  rw [card_sq_eq_congr θ z]
  refine card_sq_eq_of_mem_suzukiCoverRoot m hm (fun h => hz1 ?_) ?_
  · exact θ.injective (h.trans (map_one θ).symm)
  · rw [← map_pow, hz2, map_one]

end CFSG.ProperTwoGeneratedCore.BenderFacts
