module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93G2Sylow
public import CFSG.LargeExtraspecial.AS35WLocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.Blueprint CFSG.LargeExtraspecial Subgroup

private theorem eq_three_of_sq_dvd_card_M {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : (p ^ f) ^ 2 ∣ Nat.card S.M) : p ^ f = 3 := by
  have h' : (p ^ f) ^ 2 ∣ 2 ^ 8 * 3 ^ 2 * 5 := h.trans (S.card_M_dvd_of_width_two hw)
  have h1 : p ^ 2 ∣ 2 ^ 8 * 3 ^ 2 * 5 :=
    (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 2).trans h'
  have hp3 : p = 3 := by
    have h2 : p ∣ 2 ^ 8 * 3 ^ 2 * 5 := (dvd_pow_self p two_ne_zero).trans h1
    have h3 : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 := by
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h4 | h4
      · rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
        · exact Or.inl (hp.dvd_of_dvd_pow h5)
        · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h5))
      · exact Or.inr (Or.inr h4)
    rcases h3 with h3 | h3 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h3
      subst this
      exact absurd h1 (by norm_num)
  subst hp3
  rcases Nat.lt_or_ge f 2 with hf2 | hf2
  · obtain rfl : f = 1 := by omega
    rfl
  · exfalso
    have : 3 ^ 4 ∣ (3 ^ f) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by omega)
    have := this.trans h'
    norm_num at this

private theorem false_of_cube_dvd_card_M {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 2) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : (p ^ f) ^ 3 ∣ Nat.card S.M) : False := by
  have h' : (p ^ f) ^ 3 ∣ 2 ^ 8 * 3 ^ 2 * 5 := h.trans (S.card_M_dvd_of_width_two hw)
  have h1 : p ^ 3 ∣ 2 ^ 8 * 3 ^ 2 * 5 := by
    refine (pow_dvd_pow_of_dvd ?_ 3).trans h'
    exact dvd_pow_self p (by omega)
  have h2 : p ^ 3 ≤ 2 ^ 8 * 3 ^ 2 * 5 := Nat.le_of_dvd (by norm_num) h1
  have h3 : p ≤ 22 := by
    by_contra hc
    push Not at hc
    have : 23 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hc 3
    omega
  interval_cases p <;> revert hp hp2 h1 <;> decide

private theorem thirtyTwo_dvd_card_M {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 2) : 32 ∣ Nat.card S.M := by
  have h1 : Nat.card S.QG ∣ Nat.card S.M := Subgroup.card_dvd_of_le S.QG_le_M
  rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw] at h1
  norm_num at h1
  exact h1

theorem not_lieModel_G2_of_ne_three
    {G : Type} [Group G] [Finite G] (S : Setting G) (hw : S.width = 2) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : LieModel G .G2 0 p f) (h3 : p ^ f ≠ 3) : False := by
  have hc := CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt.g2_cent_card hp hp2 h S.z S.orderOf_z
  apply h3
  apply eq_three_of_sq_dvd_card_M S hw hp hp2 hf
  change (p ^ f) ^ 2 ∣ Nat.card ↥(Subgroup.centralizer ({S.z} : Set G))
  rw [hc, pow_two]
  exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _)

theorem lieModel_G2_three_one {G : Type} [Group G] {p f : ℕ} (hp : p.Prime)
    (h : LieModel G .G2 0 p f) (h3 : p ^ f = 3) : LieModel G .G2 0 3 1 := by
  have hf : 1 ≤ f := by
    by_contra hf
    push Not at hf
    obtain rfl : f = 0 := by omega
    rw [pow_zero] at h3
    norm_num at h3
  obtain ⟨rfl, rfl⟩ := CFSG.GH74.Generic.eq_three_of_pow_eq_three hp hf h3
  exact h

theorem not_lieModel_trialityD4
    {G : Type} [Group G] [Finite G] (S : Setting G) (hw : S.width = 2) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : LieModel G .trialityD4 0 p f) : False := by
  have hc := CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt.d4_cent_card hp hp2 h S.z S.orderOf_z
  exact false_of_cube_dvd_card_M S hw hp hp2 hf (by
    change (p ^ f) ^ 3 ∣ Nat.card ↥(Subgroup.centralizer ({S.z} : Set G))
    rw [hc]
    exact (dvd_mul_right _ _).trans (dvd_mul_right _ _))

theorem not_lieModel_twistedG2
    {G : Type} [Group G] [Finite G] (S : Setting G) (hw : S.width = 2) {f : ℕ}
    (h : LieModel G .twistedG2 0 3 f) : False := by
  obtain ⟨-, hR⟩ := CFSG.Blueprint.LieModel.reeTitsModel h (by decide)
  have h8 := CFSG.GH74.GLS.IVK.GHInv.ordProj_two_card_centralizer_ree hR S.orderOf_z
  have h5 : 2 ^ 5 ∣ Nat.card S.M := by
    have h32 := thirtyTwo_dvd_card_M S hw
    norm_num at h32 ⊢
    exact h32
  have h5' : 2 ^ 5 ∣ Nat.card ↥(Subgroup.centralizer ({S.z} : Set G)) := h5
  have hdvd : 2 ^ 5 ∣ ordProj[2] (Nat.card ↥(Subgroup.centralizer ({S.z} : Set G))) :=
    (Nat.prime_two.pow_dvd_iff_dvd_ordProj (Nat.card_pos.ne')).1 h5'
  rw [h8] at hdvd
  norm_num at hdvd

end CFSG.GF2Type.Aschbacher1977
