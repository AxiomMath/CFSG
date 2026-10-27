module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma elem2_two_sq (e : Elem2 2) : e ^ 2 = 1 := by
  rw [pow_two, ← ofAdd_toAdd e, ← ofAdd_add, ← two_smul (ZMod 2),
    show (2 : ZMod 2) = 0 from rfl, zero_smul, ofAdd_zero]

private lemma prod_fst_pow {M N : Type*} [Monoid M] [Monoid N] (x : M × N) (n : ℕ) :
    (x ^ n).1 = x.1 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Prod.fst_mul, ih]

private lemma prod_snd_pow {M N : Type*} [Monoid M] [Monoid N] (x : M × N) (n : ℕ) :
    (x ^ n).2 = x.2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Prod.snd_mul, ih]

theorem sq_eq_one_of_centralizes_sym7 {H : Type} [Group H] {S : Subgroup H}
    (hS : IsShapeSym 7 ↥S)
    (h7 : ∀ x : H, orderOf x = 7 → IsShapeCentralizerSeven (Subgroup.centralizer ({x} : Set H)))
    {y : H} (hy : ∀ s ∈ S, y * s = s * y) : y ^ 2 = 1 := by
  classical
  obtain ⟨φ⟩ := hS
  let w₀ : Equiv.Perm (Fin 7) := finRotate 7
  have hw₀ : orderOf w₀ = 7 := by
    change orderOf (finRotate 7) = 7
    rw [Equiv.Perm.IsCycle.orderOf (isCycle_finRotate (n := 5)), support_finRotate]
    simp
  let w : H := ((φ.symm w₀ : ↥S) : H)
  have hw_mem : w ∈ S := (φ.symm w₀).2
  have hw : orderOf w = 7 := by
    change orderOf (((φ.symm w₀ : ↥S) : H)) = 7
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hw₀
  let C : Subgroup H := Subgroup.centralizer ({w} : Set H)
  have hCshape : IsShapeCentralizerSeven ↥C := h7 w hw
  obtain ⟨ψ⟩ := hCshape
  have hwC : w ∈ C := by
    change w ∈ Subgroup.centralizer ({w} : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rfl
  have hyC : y ∈ C := by
    change y ∈ Subgroup.centralizer ({w} : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hy w hw_mem).symm
  let w' : C := ⟨w, hwC⟩
  let y' : C := ⟨y, hyC⟩
  have hw'ord : orderOf w' = 7 := by
    rw [← Subgroup.orderOf_coe w']
    exact hw
  have hpair7 : (ψ w') ^ 7 = 1 := by
    have h : orderOf (ψ w') = 7 := by rw [MulEquiv.orderOf_eq, hw'ord]
    rw [← orderOf_dvd_iff_pow_eq_one, h]
  have hb7 : (ψ w').2 ^ 7 = 1 := by
    simpa [prod_snd_pow] using congrArg Prod.snd hpair7
  have hb2 : (ψ w').2 ^ 2 = 1 := elem2_two_sq _
  have hb_one : (ψ w').2 = 1 := by
    have hb_odd : (ψ w').2 ^ 7 = (ψ w').2 := by
      change (ψ w').2 ^ (2 * 3 + 1) = (ψ w').2
      rw [pow_add, pow_mul, hb2, one_pow, one_mul, pow_one]
    rw [← hb_odd, hb7]
  have ha_ne : (ψ w').1 ≠ 1 := by
    intro ha1
    have hpair_one : ψ w' = 1 := by
      apply Prod.ext
      · simpa using ha1
      · simpa using hb_one
    have hw'_one : w' = 1 := ψ.injective (by rw [hpair_one, map_one])
    rw [hw'_one] at hw'ord
    simp at hw'ord
  have hcard7 : Nat.card (Multiplicative (ZMod 7)) = 7 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have he4 : (ψ y').2 ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, elem2_two_sq]
  have hmem : (ψ (y' ^ 4)).1 ∈ Submonoid.powers ((ψ w').1) := by
    rw [powers_eq_top_of_prime_card hcard7 ha_ne]
    exact Submonoid.mem_top _
  obtain ⟨k, hk⟩ :=
    (Submonoid.mem_powers_iff ((ψ (y' ^ 4)).1) ((ψ w').1)).mp hmem
  have hpair_eq : (ψ w') ^ k = ψ (y' ^ 4) := by
    apply Prod.ext
    · rw [prod_fst_pow, map_pow, prod_fst_pow]
      rw [map_pow, prod_fst_pow] at hk
      exact hk
    · rw [prod_snd_pow, hb_one, one_pow]
      rw [map_pow, prod_snd_pow, he4]
  have hwpow_eq : w' ^ k = y' ^ 4 := by
    apply ψ.injective
    rw [map_pow]
    exact hpair_eq
  have hy4_in_S : y ^ 4 ∈ S := by
    have hval : w ^ k = y ^ 4 := by
      have := congrArg Subtype.val hwpow_eq
      simpa [w', y', Subgroup.coe_pow] using this
    rw [← hval]
    exact S.pow_mem hw_mem k
  have hy4_comm : ∀ s ∈ S, y ^ 4 * s = s * y ^ 4 := by
    intro s hs
    have hcomm : Commute y s := hy s hs
    exact (hcomm.pow_left 4).eq
  let t : ↥S := ⟨y ^ 4, hy4_in_S⟩
  have ht_center : t ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact (hy4_comm (s : H) s.2).symm
  have hphi_center : φ t ∈ Subgroup.center (Equiv.Perm (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro p
    have h := Subgroup.mem_center_iff.mp ht_center (φ.symm p)
    calc p * φ t = φ (φ.symm p) * φ t := by rw [MulEquiv.apply_symm_apply]
      _ = φ (φ.symm p * t) := by rw [map_mul]
      _ = φ (t * φ.symm p) := by rw [h]
      _ = φ t * φ (φ.symm p) := by rw [map_mul]
      _ = φ t * p := by rw [MulEquiv.apply_symm_apply]
  have hphi_one : φ t = 1 := by
    refine CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating (α := Fin 7)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) ?_
    intro x hx
    exact (Subgroup.mem_center_iff.mp hphi_center x).symm
  have ht_one : t = 1 := φ.injective (by rw [hphi_one, map_one])
  have hy4_one : y ^ 4 = 1 := by
    have := congrArg Subtype.val ht_one
    simpa [t] using this
  have hy'4 : y' ^ 4 = 1 := by
    apply Subtype.ext
    simpa [y', Subgroup.coe_pow] using hy4_one
  have hmap4 : (ψ y') ^ 4 = 1 := by
    rw [← map_pow, hy'4, map_one]
  have hz4 : (ψ y').1 ^ 4 = 1 := by
    simpa [prod_fst_pow] using congrArg Prod.fst hmap4
  have hz7 : (ψ y').1 ^ 7 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one]
    have hdvd := orderOf_dvd_natCard ((ψ y').1)
    rwa [hcard7] at hdvd
  have hz_one : (ψ y').1 = 1 := by
    have h4 : orderOf ((ψ y').1) ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hz4
    have h7' : orderOf ((ψ y').1) ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hz7
    have hone : orderOf ((ψ y').1) ∣ 1 := by
      have := Nat.dvd_gcd h4 h7'
      simpa using this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  have hy'2 : y' ^ 2 = 1 := by
    apply ψ.injective
    rw [map_pow, map_one]
    apply Prod.ext
    · simp [prod_fst_pow, hz_one]
    · simp [prod_snd_pow, elem2_two_sq]
  have : y ^ 2 = 1 := by
    have := congrArg Subtype.val hy'2
    simpa [y', Subgroup.coe_pow] using this
  exact this

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
