module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphProd
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
import CFSG.GH74.Exceptional.LinearFourTwo
import CFSG.LargeExtraspecial.S45QLin
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SymmetricGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight

open Subgroup

theorem pCore_eq_bot_of_isSimpleGroup_of_dvd_card {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] {p r : ℕ} [hp : Fact p.Prime] (hr : r.Prime) (hrp : r ≠ p)
    (hd : r ∣ Nat.card G) : CFSG.pCore p G = ⊥ := by
  haveI : (CFSG.pCore p G).Normal := CFSG.pCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore p G) with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p) (G := G)).exists_card_eq
    rw [h, Subgroup.card_top] at hn
    rw [hn] at hd
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp.out).1 (hr.dvd_of_dvd_pow hd))

section GeneralLinear

variable {K : Type} [Field K] [Finite K]

theorem natCard_gl_fin (hK : Nat.card K = 2) (n : ℕ) :
    Nat.card (GL (Fin n) K) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  haveI := Fintype.ofFinite K
  rw [Matrix.card_GL_field, Fintype.card_eq_nat_card, hK]

theorem natCard_gl_fin_of_le_one (hK : Nat.card K = 2) {n : ℕ} (hn : n ≤ 1) :
    Nat.card (GL (Fin n) K) = 1 := by
  rw [natCard_gl_fin hK]
  interval_cases n <;> simp

theorem natCard_gl_fin_three (hK : Nat.card K = 2) : Nat.card (GL (Fin 3) K) = 168 := by
  rw [natCard_gl_fin hK]
  simp [Fin.prod_univ_succ]

theorem natCard_gl_fin_four (hK : Nat.card K = 2) : Nat.card (GL (Fin 4) K) = 20160 := by
  rw [natCard_gl_fin hK]
  simp [Fin.prod_univ_succ]

theorem isSimpleGroup_gl_fin (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup (GL (Fin n) K) :=
  haveI := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two hn
  (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hK n).isSimpleGroup

theorem pCore_gl_fin_eq_bot (hK : Nat.card K = 2) {n : ℕ} (hn3 : 3 ≤ n) (hn4 : n ≤ 4) (p : ℕ)
    [Fact p.Prime] (hp7 : p ≠ 7) : CFSG.pCore p (GL (Fin n) K) = ⊥ := by
  haveI := isSimpleGroup_gl_fin hK hn3
  refine pCore_eq_bot_of_isSimpleGroup_of_dvd_card (r := 7) (by norm_num) (Ne.symm hp7) ?_
  interval_cases n
  · rw [natCard_gl_fin_three hK]
    norm_num
  · rw [natCard_gl_fin_four hK]
    norm_num

theorem prodFactor_gl_fin (hK : Nat.card K = 2) {n : ℕ} (hn : n ≤ 4) :
    Prod.ProdFactor (GL (Fin n) K) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · haveI : Subsingleton (GL (Fin n) K) :=
      (Nat.card_eq_one_iff_unique.1 (natCard_gl_fin_of_le_one hK (by omega))).1
    exact Or.inr ⟨Subgroup.eq_bot_of_subsingleton _, Subgroup.eq_bot_of_subsingleton _⟩
  · rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      haveI := Fintype.ofFinite K
      exact Or.inl (TauCeti.nonempty_mulEquiv_permFinThree
        (by rw [Fintype.card_eq_nat_card, hK]))
    · exact Or.inr ⟨pCore_gl_fin_eq_bot hK h3 hn 2 (by norm_num),
        pCore_gl_fin_eq_bot hK h3 hn 3 (by norm_num)⟩

theorem two_le_of_mulEquiv_perm_three (hK : Nat.card K = 2) {n : ℕ}
    (e : GL (Fin n) K ≃* Equiv.Perm (Fin 3)) : 2 ≤ n := by
  by_contra h
  have h1 := natCard_gl_fin_of_le_one hK (n := n) (by omega)
  have h6 := SymThree.card_eq_six_of_mulEquiv e
  omega

end GeneralLinear

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.AltEight
