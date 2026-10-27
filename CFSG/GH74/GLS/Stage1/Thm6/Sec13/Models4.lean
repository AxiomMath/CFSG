module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Models3

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

theorem SylSU34_comm_central (u v w : SylSU34) : ⁅u, v⁆ * w = w * ⁅u, v⁆ := by
  apply Subtype.ext
  exact UT3.comm_central u.1 v.1 w.1

theorem SylSU34_central_a (z : SylSU34) (hz : ∀ w : SylSU34, z * w = w * z) :
    (z : UT3 (GaloisField 2 4)).a = 0 := by
  have key : ∀ a' : GaloisField 2 4, (z : UT3 (GaloisField 2 4)).a * a' ^ 4 -
      a' * (z : UT3 (GaloisField 2 4)).b = 0 := by
    intro a'
    obtain ⟨c', hc'⟩ := exists_tau_eq a'
    let w : SylSU34 := ⟨⟨a', a' ^ 4, c'⟩, (mem_SylSU34_iff _).2 ⟨rfl, by
      show c' + c' ^ 4 + a' * a' ^ 4 = 0
      linear_combination hc' + (a' * a' ^ 4) * gf16_char2⟩⟩
    have h := congrArg Subtype.val (hz w)
    have := UT3.commutator_eq (z : UT3 (GaloisField 2 4)) (w : UT3 (GaloisField 2 4))
    have h1 : ⁅(z : UT3 (GaloisField 2 4)), (w : UT3 (GaloisField 2 4))⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 h
    rw [this] at h1
    have := congrArg UT3.c h1
    simpa using this
  have hz' := ((mem_SylSU34_iff _).1 z.2).1
  by_contra hne
  have hall : ∀ a' : GaloisField 2 4, a' ^ 4 = a' := by
    intro a'
    have k1 := key 1
    have k2 := key a'
    rw [hz'] at k2 k1
    simp at k1
    have hz4 : (z : UT3 (GaloisField 2 4)).a ^ 4 = (z : UT3 (GaloisField 2 4)).a := by
      linear_combination (-1 : GaloisField 2 4) * k1
    have : (z : UT3 (GaloisField 2 4)).a * (a' ^ 4 - a') = 0 := by
      rw [hz4] at k2
      linear_combination k2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hne
    · linear_combination h
  have hcard : Nat.card {c : GaloisField 2 4 // c ^ 4 = c} = 16 := by
    have : Nat.card {c : GaloisField 2 4 // c ^ 4 = c} = Nat.card (GaloisField 2 4) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [this]
    have := GaloisField.card 2 4 (by norm_num)
    simpa using this
  have := gf16_card_fix4_le
  omega

theorem SylSU34_central_card (Z : Subgroup SylSU34)
    (hZ : ∀ z ∈ Z, ∀ w : SylSU34, z * w = w * z) : Nat.card Z ≤ 4 := by
  have ha : ∀ z ∈ Z, (z : UT3 (GaloisField 2 4)).a = 0 := fun z hz => SylSU34_central_a z (hZ z hz)
  have hker : ∀ z ∈ Z, (z : UT3 (GaloisField 2 4)).c + (z : UT3 (GaloisField 2 4)).c ^ 4 = 0 := by
    intro z hz
    have h := ((mem_SylSU34_iff _).1 z.2).2
    rw [ha z hz] at h
    simpa using h
  have hinj : Function.Injective (fun z : Z =>
      (⟨(z.1 : UT3 (GaloisField 2 4)).c, hker z.1 z.2⟩ : tauHom.ker)) := by
    intro z z' h
    have hc : (z.1 : UT3 (GaloisField 2 4)).c = (z'.1 : UT3 (GaloisField 2 4)).c := by
      simpa using congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    have hb : ∀ y ∈ Z, (y : UT3 (GaloisField 2 4)).b = 0 := by
      intro y hy
      rw [((mem_SylSU34_iff _).1 y.2).1, ha y hy]; simp
    ext
    · rw [ha z.1 z.2, ha z'.1 z'.2]
    · rw [hb z.1 z.2, hb z'.1 z'.2]
    · exact hc
  exact le_trans (Nat.card_le_card_of_injective _ hinj) (le_of_eq card_ker_tau)

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

