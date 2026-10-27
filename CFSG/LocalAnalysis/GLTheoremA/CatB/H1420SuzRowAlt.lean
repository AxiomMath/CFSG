module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowU43
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem factorial_half_ne_u43 (m : ℕ) : m.factorial / 2 ≠ 3265920 := by
  intro h
  by_cases hm : m ≤ 10
  · interval_cases m <;> simp [Nat.factorial] at h
  · have h11 : Nat.factorial 11 ≤ m.factorial := Nat.factorial_le (by omega)
    have : Nat.factorial 11 = 39916800 := by decide
    omega

private theorem card_pSimple_alt_of_down (hAD : KDAltDown) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1)
    {J : Subgroup S}
    (hJ : GLAPComponent p (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J) :
    ∃ m : ℕ, Nat.card (PSimple p J) = m.factorial / 2 := by
  obtain ⟨hI, ⟨eP⟩⟩ := chevQ_transport hp e hJ
  have hα : (MulAut.congr e β) ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hα1 : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨m, hm, -, ⟨eA⟩⟩ := hAD n p hn hp hp2 _ hα hα1 _ hI
  have hm5 : 5 ≤ m := le_trans (le_max_left 5 p) hm
  exact ⟨m, by rw [Nat.card_congr eP.toEquiv, Nat.card_congr eA.toEquiv,
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m (by omega)]⟩

theorem suzRow_alt_of_facts {z : ℕ} (hAD : KDAltDown) {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn : 5 ≤ n) (e : S ≃* alternatingGroup (Fin n)) {β : MulAut S} {J : Subgroup S}
    (hcore : I1420CoreP 3 (S8.isU4of 3) z β J) : False := by
  obtain ⟨-, -, hβp, hβ1, -, hJ, hT, -⟩ := hcore
  obtain ⟨m, hm⟩ := card_pSimple_alt_of_down hAD Nat.prime_three (by norm_num) hn e hβp hβ1 hJ
  exact factorial_half_ne_u43 m (hm.symm.trans (card_eq_of_isU4of_three hT))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
