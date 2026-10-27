module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420CoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup SporadicOrdersTable sporOrd)

private theorem card_pSimple_alt_of_down (hAD : KDAltDown) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1)
    {J : Subgroup S} (hJ : GLAPComponent p (fixSubgroup β) J) :
    ∃ m : ℕ, Nat.card (PSimple p J) = m.factorial / 2 := by
  obtain ⟨hI, ⟨eP⟩⟩ := chevQ_transport hp e hJ
  have hα : (MulAut.congr e β) ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hα1 : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨m, hm, -, ⟨eA⟩⟩ := hAD n p hn hp hp2 _ hα hα1 _ hI
  have hm5 : 5 ≤ m := le_trans (le_max_left 5 p) hm
  exact ⟨m, by rw [Nat.card_congr eP.toEquiv, Nat.card_congr eA.toEquiv,
    CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt m (by omega)]⟩

theorem i1420AltSpor_holds {p z : ℕ} {s : TauCeti.SporadicName} (hp : p.Prime) (hp2 : p ≠ 2)
    (hOrd : SporadicOrdersTable) (hAD : KDAltDown) (hs : ∀ m : ℕ, m.factorial / 2 ≠ sporOrd s)
    {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n) (e : S ≃* alternatingGroup (Fin n))
    {β : MulAut S} {J : Subgroup S} (hcore : I1420Core p z s β J) : False := by
  obtain ⟨-, -, hβp, hβ1, -, hJ, ⟨eT⟩, -⟩ := hcore
  obtain ⟨m, hm⟩ := card_pSimple_alt_of_down hAD hp hp2 hn e hβp hβ1 hJ
  exact hs m (hm.symm.trans ((Nat.card_congr eT.toEquiv).trans (hOrd s)))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
