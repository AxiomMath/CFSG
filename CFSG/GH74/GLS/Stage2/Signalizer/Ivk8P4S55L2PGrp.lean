module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2DickMain

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Dick

open Subgroup CFSG CFSG.Glauberman.Dickson CFSG.BenderSuzuki.MatrixGroups

theorem false_of_odd_group_exp_two {J H₂ G₂ : Type*} [Group J] [Group H₂] [Group G₂]
    (e : J ≃* H₂) (τ : H₂ →* G₂) (hexp : ∀ g : G₂, g ^ 2 = 1) (hnt : ∃ w : H₂, τ w ≠ 1)
    (hodd : ∀ x : J, ∃ n : ℕ, Odd n ∧ x ^ n = 1) : False := by
  let σ : J →* G₂ := τ.comp e.toMonoidHom
  have htriv := hom_trivial_of_odd_gens σ hexp (S := Set.univ) (by simp) (by
    intro s _
    obtain ⟨n, hn, hsn⟩ := hodd s
    refine ⟨n, hn, ?_⟩
    simp only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_pow, ← map_pow, hsn, map_one, map_one])
  obtain ⟨w, hw⟩ := hnt
  apply hw
  have := htriv (e.symm w)
  simpa [σ] using this

theorem card_dvd_pgroup_aux {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hH : IsPGroup p H) {q : ℕ} (hq : q.Prime) (hqd : q ∣ Nat.card H) : q = p := by
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rw [hn] at hqd
  exact (Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (hq.dvd_of_dvd_pow hqd)

theorem pgroup_comm {F : Type} [Field F] [Finite F] {r f p : ℕ}
    [hr : Fact r.Prime] (hr2 : r ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hrp : r ≠ p)
    (hF : Nat.card F = r ^ f) (H : Subgroup (PSL2MatrixGroup F)) (hH : IsPGroup p ↥H) :
    ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : ∀ x : ↥H, ∃ n : ℕ, Odd n ∧ x ^ n = 1 := by
    intro x
    obtain ⟨k, hk⟩ := hH x
    exact ⟨p ^ k, (hp.odd_of_ne_two hp2).pow, hk⟩
  have hcomm : (∀ a b : ↥H, a * b = b * a) → ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
    intro h x hx y hy
    exact congrArg Subtype.val (h ⟨x, hx⟩ ⟨y, hy⟩)
  rcases dickson_psl2_subgroup_list hF H with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, hm1, -, -, -, E, C, hEn, hEel, hEcard, -⟩ | ⟨m, hmf, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩
  · exact hcomm (fun a b => hel.toIsMulCommutative.is_comm.comm a b)
  · exact hcomm (fun a b => (IsCyclic.commGroup (α := ↥H)).mul_comm a b)
  ·
    exfalso
    have hz0 : z ≠ 0 := by omega
    have : NeZero z := ⟨hz0⟩
    have h2 : 2 ∣ Nat.card H := by
      rw [Nat.card_congr e.toEquiv]
      have : Nat.card (DihedralGroup z) = 2 * z := by
        rw [Nat.card_eq_fintype_card]
        exact DihedralGroup.card
      rw [this]
      exact dvd_mul_right 2 z
    exact hp2 (card_dvd_pgroup_aux hH Nat.prime_two h2).symm
  ·
    exfalso
    have h2 : 2 ∣ Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    exact hp2 (card_dvd_pgroup_aux hH Nat.prime_two h2).symm
  ·
    exfalso
    have h2 : 2 ∣ Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
    exact hp2 (card_dvd_pgroup_aux hH Nat.prime_two h2).symm
  ·
    exfalso
    have h2 : 2 ∣ Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    exact hp2 (card_dvd_pgroup_aux hH Nat.prime_two h2).symm
  ·
    exfalso
    have hE : r ∣ Nat.card H := by
      have h1 : Nat.card E ∣ Nat.card H := Subgroup.card_subgroup_dvd_card E
      rw [hEcard] at h1
      exact (dvd_pow_self r (by omega)).trans h1
    exact hrp (card_dvd_pgroup_aux hH hr.out hE)
  ·
    exfalso
    have hf0 : f ≠ 0 := by
      rintro rfl
      have : Nat.card F = 1 := by simpa using hF
      exact absurd this (Finite.one_lt_card (α := F)).ne'
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hf0 (Nat.eq_zero_of_zero_dvd hmf)
    have hK : Nat.card (GaloisField r m) = r ^ m := GaloisField.card r m hm0
    have h1 := MaxUp.card_psl2_odd hK hr2
    have hodd' : Odd (r ^ m) := (hr.out.odd_of_ne_two hr2).pow
    have h2 : 2 ∣ (r ^ m) ^ 2 - 1 := by
      have : Odd ((r ^ m) ^ 2) := hodd'.pow
      have h3 : Even ((r ^ m) ^ 2 - 1) := Nat.Odd.sub_odd this odd_one
      exact even_iff_two_dvd.mp h3
    have hr' : r ∣ Nat.card (PSL2MatrixGroup (GaloisField r m)) := by
      rw [h1, Nat.mul_div_assoc _ h2]
      exact Dvd.dvd.mul_right (dvd_pow_self r hm0) _
    have : r ∣ Nat.card H := by rw [Nat.card_congr e.toEquiv]; exact hr'
    exact hrp (card_dvd_pgroup_aux hH hr.out this)
  ·
    exfalso
    have hchar : ringChar (GaloisField r m) ≠ 2 := by
      rw [ringChar.eq (GaloisField r m) r]
      exact hr2
    exact false_of_odd_group_exp_two e (pglSq (GaloisField r m)) sqrQuot_sq
      (pglSq_nontrivial _ hchar) hodd

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Dick
