module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420CoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup sporOrd)

private theorem card_pSimple_alt (hAD : KDAltDown) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n) (e : S ≃* alternatingGroup (Fin n))
    {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) {J : Subgroup S}
    (hJ : GLAPComponent p (fixSubgroup β) J) :
    ∃ m : ℕ, Nat.card (PSimple p J) = m.factorial / 2 := by
  obtain ⟨hI, ⟨eP⟩⟩ := chevQ_transport hp e hJ
  have hα : (MulAut.congr e β) ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hα1 : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨m, hm, -, ⟨eA⟩⟩ := hAD n p hn hp hp2 _ hα hα1 _ hI
  have hm5 : 5 ≤ m := le_trans (le_max_left 5 p) hm
  exact ⟨m, by rw [Nat.card_congr eP.toEquiv, Nat.card_congr eA.toEquiv,
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m (by omega)]⟩

private theorem factorial_half_ne_fi24 (m : ℕ) : m.factorial / 2 ≠ sporOrd .Fi24Prime := by
  intro h
  rw [show sporOrd .Fi24Prime = 1255205709190661721292800 by
    norm_num [sporOrd, orderFi24Prime]] at h
  rcases le_or_gt m 24 with hm | hm
  · have h1 : m.factorial ≤ (24).factorial := Nat.factorial_le hm
    have h24 : (24).factorial = 620448401733239439360000 := by decide +kernel
    omega
  · have h1 : (25).factorial ≤ m.factorial := Nat.factorial_le hm
    have h25 : (25).factorial = 15511210043330985984000000 := by decide +kernel
    omega

private theorem factorial_half_ne_hn (m : ℕ) : m.factorial / 2 ≠ sporOrd .HN := by
  intro h
  rw [show sporOrd .HN = 273030912000000 by norm_num [sporOrd, orderHN]] at h
  rcases le_or_gt m 17 with hm | hm
  · have h1 : m.factorial ≤ (17).factorial := Nat.factorial_le hm
    have h17 : (17).factorial = 355687428096000 := by decide +kernel
    omega
  · have h1 : (18).factorial ≤ m.factorial := Nat.factorial_le hm
    have h18 : (18).factorial = 6402373705728000 := by decide +kernel
    omega

theorem i1420Alt_holds
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hAD : CFSG.LocalAnalysis.GLTheoremA.KDAltDown) : I1420Alt := by
  intro p z s ht S _ _ n hn e β J hcore
  obtain ⟨-, -, hβp, hβ1, -, hJ, ⟨eT⟩, -⟩ := hcore
  have hT : Nat.card (PSimple p J) = sporOrd s := (Nat.card_congr eT.toEquiv).trans (hOrd s)
  rcases ht with ⟨rfl, -, rfl⟩ | ⟨rfl, -, rfl⟩
  · obtain ⟨m, hm⟩ := card_pSimple_alt hAD Nat.prime_three (by norm_num) hn e hβp hβ1 hJ
    exact factorial_half_ne_fi24 m (hm.symm.trans hT)
  · obtain ⟨m, hm⟩ := card_pSimple_alt hAD Nat.prime_five (by norm_num) hn e hβp hβ1 hJ
    exact factorial_half_ne_hn m (hm.symm.trans hT)

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
