module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2Family
public import CFSG.RankThree.PartOne.N143X.PRankTorus

public section


open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator

theorem false_of_isElemAbelian_sq_of_cyclic {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {T : Subgroup X} [IsCyclic T] (hidx : ¬ p ∣ T.index) {E : Subgroup X}
    (hE : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hP : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE x.1 x.2)⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.N143X.exists_conj_map_le_of_not_dvd_index' hidx hP
  let φ : E →* T := MonoidHom.codRestrict ((MulAut.conj g).toMonoidHom.comp E.subtype) T
    (fun x => hg ⟨x, x.2, rfl⟩)
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  have hcyc : IsCyclic E := isCyclic_of_injective φ hφ
  obtain ⟨x, hx⟩ := hcyc.exists_ofOrder_eq_natCard
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hE x x.2))
  rw [hx, hcard] at h1
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at h3
  omega


theorem false_of_isElemAbelian_sq_cyclotomic (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (hp1 : ¬ p ∣ Nat.card K ^ 2 - 1)
    {E : Subgroup ↥(adjointGroup .G2 K)} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have := ExceptionsTransport.finite_adjointGroup_G2 K
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvdC : p ∣ Nat.card ↥(adjointGroup .G2 K) := by
    have : p ∣ Nat.card E := by rw [hcard]; exact dvd_pow_self p two_ne_zero
    exact this.trans (Subgroup.card_subgroup_dvd_card E)
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, CFSG.Open.ordG2] at hdvdC
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (Nat.card K : ℤ) := ⟨_, rfl⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvdZ : (p : ℤ) ∣ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
    have h6 : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq1
    have h := Int.natCast_dvd_natCast.2 hdvdC
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at h
    rw [hQ]
    exact h
  have hqZ : ¬ (p : ℤ) ∣ Q := fun h => hpK (by rw [hQ] at h; exact_mod_cast h)
  have h1Z : ¬ (p : ℤ) ∣ Q ^ 2 - 1 := fun h => hp1 (by
    have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq1
    have h' : (p : ℤ) ∣ ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]
      rw [← hQ]
      exact h
    exact Int.natCast_dvd_natCast.1 h')
  have hfac : Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) =
      Q ^ 6 * ((Q ^ 2 - 1) * ((Q ^ 2 + Q + 1) * (Q ^ 2 - Q + 1))) * (Q ^ 2 - 1) := by ring
  rw [hfac] at hdvdZ
  have key : (p : ℤ) ∣ Q ^ 2 + Q + 1 ∨ (p : ℤ) ∣ Q ^ 2 - Q + 1 := by
    rcases hpZ.dvd_or_dvd hdvdZ with h | h
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact absurd (hpZ.dvd_of_dvd_pow h) hqZ
      · rcases hpZ.dvd_or_dvd h with h | h
        · exact absurd h h1Z
        · exact hpZ.dvd_or_dvd h
    · exact absurd h h1Z
  rcases key with h | h
  ·
    have hd : ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + (2 * 2 - 3) * Nat.card K + 1 := by push_cast; ring
    have hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) := by
        push_cast
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    obtain ⟨T, hcyc, hTcard, -⟩ := cyclotomic_core K (k := 2) (Or.inr rfl) g2rot_two_g2a
      g2rot_two_g2r _ hd hp (by omega)
    have := hcyc
    exact false_of_isElemAbelian_sq_of_cyclic hp
      (not_dvd_index_of_card_eq K (k := 2) (Or.inr rfl) _ hd hp (by omega) hpd T hTcard) hE hcard
  ·
    have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
    have hd : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + (2 * 1 - 3) * Nat.card K + 1 := by
      push_cast [Nat.cast_sub hle]
      ring
    have hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hle]
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    obtain ⟨T, hcyc, hTcard, -⟩ := cyclotomic_core K (k := 1) (Or.inl rfl) g2rot_one_g2a
      g2rot_one_g2r _ hd hp (by omega)
    have := hcyc
    exact false_of_isElemAbelian_sq_of_cyclic hp
      (not_dvd_index_of_card_eq K (k := 1) (Or.inl rfl) _ hd hp (by omega) hpd T hTcard) hE hcard

theorem g2NativePlaneGenCyclic : G2NativePlaneGenCyclic := by
  intro K _ _ _ p hp hp5 hpK hp1 E₁ hE hcard
  exact (false_of_isElemAbelian_sq_cyclotomic K hp hp5 hpK hp1 hE.2 hcard).elim

end CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
