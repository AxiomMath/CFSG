module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Model

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

@[expose] def centralizerSubtypeEquiv {M : Type*} [Group M] (R : Subgroup M) (x : ↥R) :
    ↥(centralizer ({x} : Set ↥R)) ≃* ↥(centralizer ({(x : M)} : Set M) ⊓ R) where
  toFun c := ⟨(c.1 : M), mem_inf.2 ⟨by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2), c.1.2⟩⟩
  invFun c := ⟨⟨c.1, (mem_inf.1 c.2).2⟩, by
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).1)⟩
  left_inv c := rfl
  right_inv c := rfl
  map_mul' a b := rfl

theorem mulAut_hs_equiv_R (M : HS100Model) : Nonempty (MulAut (Carrier .HS) ≃* ↥hs100R) := by
  obtain ⟨φ⟩ := M.equiv (Carrier .HS) ⟨MulEquiv.refl _⟩
  obtain ⟨e, -⟩ := M.aut
  exact ⟨(MulAut.congr φ).trans e.symm⟩

theorem hs100R_five_centralizer
    {x : ↥hs100R} (hx : orderOf x = 5)
    (h3 : 3 ∣ Nat.card ↥(centralizer ({x} : Set ↥hs100R))) :
    Nonempty (↥(centralizer ({x} : Set ↥hs100R)) ≃*
      Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) := by
  have hx' : orderOf (x : Equiv.Perm (Fin 100)) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have h3' : 3 ∣ Nat.card ↥(centralizer ({(x : Equiv.Perm (Fin 100))} :
      Set (Equiv.Perm (Fin 100))) ⊓ hs100R) := by
    rwa [← Nat.card_congr (centralizerSubtypeEquiv hs100R x).toEquiv]
  obtain ⟨e⟩ := hs100_five_centralizer x.2 hx' h3'
  exact ⟨(centralizerSubtypeEquiv hs100R x).trans e⟩

end CFSG.EvenSporadicStandard.HSStd
