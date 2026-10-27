module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoFrame
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open scoped MatrixGroups
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh


variable {K : Type} [Field K]

theorem frameHom_pairwise_commute (σ : K →+* K) :
    Pairwise fun i j : Fin 4 => ∀ (x y : SL(2, RingHom.eqLocusField σ (RingHom.id K))),
      Commute (frameHom σ i x) (frameHom σ j y) :=
  fun _ _ hij x y => frameHom_commute σ hij x y

@[expose] def frameMap (σ : K →+* K) :
    (Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K))) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
  MonoidHom.noncommPiCoprod (frameHom σ) (frameHom_pairwise_commute σ)

theorem commute_frameMap_torusG (σ : K →+* K)
    (y : Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K)))
    (t : ↥(normOne σ) × ↥(normOne σ)) : Commute (frameMap σ y) (torusG σ t) := by
  rw [frameMap, MonoidHom.noncommPiCoprod_apply]
  exact (Finset.noncommProd_commute _ _ _ (torusG σ t) fun j _ =>
    torusG_commute_frame σ (frameHom_mem_rootPair σ) t j (y j)).symm

@[expose] def frameTorusMap (σ : K →+* K) :
    (Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K))) × (↥(normOne σ) × ↥(normOne σ)) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
  MonoidHom.noncommCoprod (frameMap σ) (torusG σ) (commute_frameMap_torusG σ)

theorem frameTorusMap_apply (σ : K →+* K)
    (y : Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K)))
    (t : ↥(normOne σ) × ↥(normOne σ)) :
    frameTorusMap σ (y, t) = frameMap σ y * torusG σ t := rfl

theorem frameMap_mulSingle (σ : K →+* K) (i : Fin 4)
    (x : SL(2, RingHom.eqLocusField σ (RingHom.id K))) :
    frameMap σ (Pi.mulSingle i x) = frameHom σ i x := by
  rw [frameMap, MonoidHom.noncommPiCoprod_mulSingle]

theorem commute_frameHom_frameMap (σ : K →+* K) (i : Fin 4)
    (z : SL(2, RingHom.eqLocusField σ (RingHom.id K)))
    (w : Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K))) (hw : w i = 1) :
    Commute (frameHom σ i z) (frameMap σ w) := by
  rw [frameMap, MonoidHom.noncommPiCoprod_apply]
  refine Finset.noncommProd_commute _ _ _ (frameHom σ i z) fun j _ => ?_
  show Commute (frameHom σ i z) (frameHom σ j (w j))
  by_cases hj : j = i
  · rw [hj, hw, map_one]
    exact Commute.one_right _
  · exact frameHom_commute σ (Ne.symm hj) z (w j)

theorem sq_eq_one_of_central_SL2 {F : Type} [Field F] (g : SL(2, F))
    (hg : ∀ z : SL(2, F), g * z = z * g) : g ^ 2 = 1 := by
  have hc : g ∈ Subgroup.center SL(2, F) := Subgroup.mem_center_iff.2 fun z => (hg z).symm
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  rw [Fintype.card_fin] at hr
  rw [pow_two]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hrx, ← map_mul, ← pow_two, hr, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem frameTorus_eq_one_of_pow_coprime {G : Type*} [Group G] {a b : ℕ} (g : G)
    (ha : g ^ a = 1) (hb : g ^ b = 1) (hab : Nat.Coprime a b) : g = 1 := by
  have h := pow_gcd_eq_one.2 ⟨ha, hb⟩
  rw [show Nat.gcd a b = 1 from hab, pow_one] at h
  exact h

theorem frameMap_coord_comm (σ : K →+* K)
    (y : Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K)))
    (t : ↥(normOne σ) × ↥(normOne σ))
    (hΦ' : frameMap σ y * torusG σ t = 1) (i : Fin 4)
    (z : SL(2, RingHom.eqLocusField σ (RingHom.id K))) : y i * z = z * y i := by
  have hsplit : y = Pi.mulSingle i (y i) * Function.update y i 1 := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Pi.mul_apply, Pi.mulSingle_eq_same, Function.update_self, mul_one]
    · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj, one_mul]
  have hfy : frameMap σ y = frameHom σ i (y i) * frameMap σ (Function.update y i 1) := by
    have h := congrArg (frameMap σ) hsplit
    rw [map_mul (frameMap σ), frameMap_mulSingle] at h
    exact h
  have h1 : frameHom σ i (y i) * (frameMap σ (Function.update y i 1) * torusG σ t) = 1 := by
    rw [← mul_assoc, ← hfy]
    exact hΦ'
  have h2 : frameHom σ i (y i) = (frameMap σ (Function.update y i 1) * torusG σ t)⁻¹ :=
    eq_inv_of_mul_eq_one_left h1
  have hcomm : Commute (frameHom σ i z)
      (frameMap σ (Function.update y i 1) * torusG σ t) :=
    (commute_frameHom_frameMap σ i z (Function.update y i 1)
      (by rw [Function.update_self])).mul_right
      (torusG_commute_frame σ (frameHom_mem_rootPair σ) t i z).symm
  have hc2 : Commute (frameHom σ i z) (frameHom σ i (y i)) := by
    rw [h2]
    exact hcomm.inv_right
  apply frameHom_injective σ i
  rw [map_mul (frameHom σ i), map_mul (frameHom σ i)]
  exact hc2.symm.eq

theorem frameTorusMap_eq_one_of_pow (σ : K →+* K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (x : (Fin 4 → SL(2, RingHom.eqLocusField σ (RingHom.id K))) ×
      (↥(normOne σ) × ↥(normOne σ))) {m : ℕ} (hx : x ^ (p ^ m) = 1)
    (hΦ : frameTorusMap σ x = 1) : x = 1 := by
  obtain ⟨y, t⟩ := x
  have hΦ' : frameMap σ y * torusG σ t = 1 := (frameTorusMap_apply σ y t).symm.trans hΦ
  have hym : y ^ (p ^ m) = 1 := by
    have h := congrArg Prod.fst hx
    rw [Prod.pow_fst, Prod.fst_one] at h
    exact h
  have htpow : t ^ (p ^ m) = 1 := by
    have h := congrArg Prod.snd hx
    rw [Prod.pow_snd, Prod.snd_one] at h
    exact h
  have hcop2 : Nat.Coprime 2 (p ^ m) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 (by omega))
  have hcop3 : Nat.Coprime 3 (p ^ m) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).2 (by omega))
  have hyi : ∀ i, y i = 1 := fun i => by
    have hpow : y i ^ (p ^ m) = 1 := by
      have h := congrFun hym i
      rw [Pi.pow_apply, Pi.one_apply] at h
      exact h
    exact frameTorus_eq_one_of_pow_coprime (y i)
      (sq_eq_one_of_central_SL2 (y i) (fun z => frameMap_coord_comm σ y t hΦ' i z)) hpow hcop2
  have hy1 : y = 1 := funext hyi
  rw [hy1, map_one (frameMap σ), one_mul] at hΦ'
  have ht3 : t ^ 3 = 1 := torusG_ker_pow_three σ hΦ'
  have ht1 : t = 1 := frameTorus_eq_one_of_pow_coprime t ht3 htpow hcop3
  exact Prod.ext hy1 ht1

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive
