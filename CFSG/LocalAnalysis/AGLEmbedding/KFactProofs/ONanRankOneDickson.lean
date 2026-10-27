module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.AGLEmbedding

open CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxUp

section Shapes

theorem psl2GF_nonsolvable_shape {p a : ℕ} [Fact p.Prime]
    (ha : a ≠ 0) (A : Subgroup (PSL2GF p a)) (hA : ¬ Group.IsSolvable A) :
    ((p = 5 ∨ (p ^ a) ^ 2 ≡ 1 [MOD 5]) ∧ Nonempty (A ≃* alternatingGroup (Fin 5))) ∨
    (∃ m, m ∣ a ∧ Nonempty (A ≃* PSL2GF p m)) ∨
    (∃ m, 2 * m ∣ a ∧ Nonempty (A ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  have hF : Nat.card (GaloisField p a) = p ^ a := GaloisField.card p a ha
  rcases dickson_psl2_subgroup_list hF A with
    ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ | ⟨z, hz2, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h5, ⟨e⟩⟩ |
      ⟨m, t, -, -, -, -, E, C, hE, hEel, -, hCcyc, -, -, hsup, -, -⟩ | ⟨m, hm, ⟨e⟩⟩ |
      ⟨m, hm, ⟨e⟩⟩
  · exact absurd (Group.isSolvable_of_comm fun x y => hel.1.is_comm.comm x y) hA
  · have : IsCyclic A := hcyc
    let _ : CommGroup A := IsCyclic.commGroup
    exact absurd (inferInstance : Group.IsSolvable A) hA
  · have : NeZero z := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact absurd (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective) hA
  · have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact absurd (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective) hA
  · have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact absurd (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective) hA
  · exact Or.inl ⟨h5, ⟨e⟩⟩
  · exfalso
    have hEs : Group.IsSolvable E := Group.isSolvable_of_comm fun x y => hEel.1.is_comm.comm x y
    have hcomm : commutator A ≤ E := Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => by
      rw [commutatorElement_def]
      exact overgroup_comm_mem E C hCcyc hsup g₁ g₂
    have hq : IsMulCommutative (A ⧸ E) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
    have hqs : Group.IsSolvable (A ⧸ E) := Group.isSolvable_of_comm fun x y => hq.is_comm.comm x y
    exact hA (Group.isSolvable_of_subgroup_quotient E)
  · exact Or.inr (Or.inl ⟨m, hm, ⟨e⟩⟩)
  · exact Or.inr (Or.inr ⟨m, hm, ⟨e⟩⟩)

end Shapes

section Arithmetic

theorem coprime_pow_pow_sub_one {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (a : ℕ) :
    Nat.Coprime (p ^ a) (p ^ k - 1) := by
  refine Nat.Coprime.pow_left a ?_
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have h1 : p ∣ p ^ k := dvd_pow_self p hk
  have h2 : p ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub h1 h
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  rw [show p ^ k - (p ^ k - 1) = 1 by omega] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

theorem le_of_pow_dvd_card_psl2GF {p a m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : m ≠ 0)
    (h : p ^ a ∣ Nat.card (PSL2GF p m)) : a ≤ m := by
  have hp : p.Prime := Fact.out
  have h2 : 2 ∣ p ^ (2 * m) - 1 := by
    have hodd : Odd (p ^ (2 * m)) := (hp.odd_of_ne_two hp2).pow
    exact (Nat.Odd.sub_odd hodd odd_one).two_dvd
  rw [card_psl2_galoisField hp2 hm, Nat.mul_div_assoc _ h2] at h
  have hc : Nat.Coprime (p ^ a) ((p ^ (2 * m) - 1) / 2) :=
    Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd h2) (coprime_pow_pow_sub_one hp (by omega) a)
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hc.dvd_of_dvd_mul_right h)

theorem le_of_pow_dvd_card_pgl2GF {p a m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (h : p ^ a ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) : a ≤ m := by
  have hp : p.Prime := Fact.out
  rw [card_pgl2_galoisField hm] at h
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp
    ((coprime_pow_pow_sub_one hp (by omega) a).dvd_of_dvd_mul_right h)

end Arithmetic

section Overgroups

theorem psl2GF_eq_top_of_dvd_card {p a : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (ha : a ≠ 0) (Y : Subgroup (PSL2GF p a)) (hdvd : p ^ a ∣ Nat.card Y)
    (hY : ¬ Group.IsSolvable Y) : Y = ⊤ := by
  have hp : p.Prime := Fact.out
  rcases psl2GF_nonsolvable_shape ha Y hY with ⟨-, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  ·
    have h60 : Nat.card Y = 60 := (Nat.card_congr e.toEquiv).trans card_alternatingFive'
    rw [h60] at hdvd
    have hpd : p ∣ 2 * 2 * 3 * 5 := (dvd_pow_self p ha).trans hdvd
    have hp35 : p = 3 ∨ p = 5 := by
      rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)
    have ha1 : a = 1 := by
      by_contra hne
      have hsq : p ^ 2 ∣ 60 := (pow_dvd_pow p (by omega : 2 ≤ a)).trans hdvd
      rcases hp35 with rfl | rfl <;> norm_num at hsq
    subst ha1
    have hG : Nat.card (PSL2GF p 1) = p ^ 1 * (p ^ (2 * 1) - 1) / 2 := card_psl2_galoisField hp2 ha
    have hle : Nat.card Y ≤ Nat.card (PSL2GF p 1) := Subgroup.card_le_card_group Y
    rcases hp35 with rfl | rfl
    · norm_num at hG
      omega
    · norm_num at hG
      exact Subgroup.eq_top_of_card_eq Y (by omega)
  · have hm0 : m ≠ 0 := fun h0 => ha (zero_dvd_iff.mp (h0 ▸ hm))
    have hcard : Nat.card Y = Nat.card (PSL2GF p m) := Nat.card_congr e.toEquiv
    have hle : a ≤ m := le_of_pow_dvd_card_psl2GF hp2 hm0 (hcard ▸ hdvd)
    have hma : m = a := le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hm) hle
    subst hma
    exact Subgroup.eq_top_of_card_eq Y hcard
  · have hm0 : m ≠ 0 := fun h0 => ha (zero_dvd_iff.mp (by simpa [h0] using hm))
    have hcard : Nat.card Y = Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) :=
      Nat.card_congr e.toEquiv
    have hle : a ≤ m := le_of_pow_dvd_card_pgl2GF hm0 (hcard ▸ hdvd)
    have h2m : 2 * m ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hm
    exfalso
    omega

end Overgroups

section Transport

theorem eq_top_of_dvd_card_of_equiv_psl2GF {p a : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (ha : a ≠ 0) {K : Type*} [Group K] [Finite K] (e : K ≃* PSL2GF p a)
    (Y : Subgroup K) (hdvd : p ^ a ∣ Nat.card Y) (hY : ¬ Group.IsSolvable Y) : Y = ⊤ := by
  let eY : Y ≃* Y.map e.toMonoidHom := Y.equivMapOfInjective e.toMonoidHom e.injective
  have hYs : ¬ Group.IsSolvable (Y.map e.toMonoidHom) := fun h =>
    hY (Group.isSolvable_of_surjective (f := eY.symm.toMonoidHom) eY.symm.surjective)
  have hmap : Y.map e.toMonoidHom = ⊤ :=
    psl2GF_eq_top_of_dvd_card hp2 ha _ ((Nat.card_congr eY.toEquiv) ▸ hdvd) hYs
  refine Subgroup.eq_top_of_card_eq Y ?_
  rw [Nat.card_congr eY.toEquiv, hmap, Subgroup.card_top, Nat.card_congr e.toEquiv]

theorem eq_top_of_sylow_le_of_equiv_psl2GF {p a : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (ha : a ≠ 0) {K : Type*} [Group K] [Finite K] (e : K ≃* PSL2GF p a)
    (Y : Subgroup K) (T : Sylow p K) (hTY : (T : Subgroup K) ≤ Y)
    (hY : ¬ Group.IsSolvable Y) : Y = ⊤ := by
  have hp : p.Prime := Fact.out
  have hT : Nat.card (T : Subgroup K) = p ^ a := by
    have hP := (psl2GF_sylow p a (Nat.one_le_iff_ne_zero.mpr ha)
      (default : Sylow p (PSL2GF p a))).2
    rw [Sylow.card_eq_multiplicity] at hP
    rw [Sylow.card_eq_multiplicity T, Nat.card_congr e.toEquiv]
    rw [Nat.pow_right_injective hp.two_le hP]
  refine eq_top_of_dvd_card_of_equiv_psl2GF hp2 ha e Y ?_ hY
  rw [← hT]
  exact Subgroup.card_dvd_of_le hTY

end Transport

end CFSG.AGLEmbedding
