module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreeBase
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree

open Equiv

theorem not_isSimpleGroup_perm_fin_three : ¬ IsSimpleGroup (Perm (Fin 3)) := by
  intro h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 3)) with h1 | h1
  · have h2 := card_alternatingGroup_fin_three
    rw [h1, Subgroup.card_bot] at h2
    omega
  · have h2 := card_alternatingGroup_fin_three
    rw [h1, Subgroup.card_top, card_perm_fin_three] at h2
    omega

theorem false_of_isSimpleGroup_of_isSubnormal {Q : Type*} [Group Q] [IsSimpleGroup Q]
    {X : Subgroup Q} (hX : X.IsSubnormal) (eX : X ≃* Perm (Fin 3)) : False := by
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hX with h | h
  · have h6 := card_eq_six_of_mulEquiv eX
    rw [h, Subgroup.card_bot] at h6
    omega
  · have e : Q ≃* Perm (Fin 3) :=
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h.symm)).trans eX
    exact not_isSimpleGroup_perm_fin_three e.symm.isSimpleGroup

theorem isSimpleGroup_of_mulEquiv_lie_B {Q : Type} [Group Q] {k : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hk : 3 ≤ k) {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hd : d.1 = .B k q) (e : Q ≃* (TauCeti.CFSGIndex.lie d).Group) : IsSimpleGroup Q := by
  obtain ⟨d, hv⟩ := d
  obtain rfl : d = .B k q := hd
  have hq' : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq
  have hp : q.p = 2 :=
    (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
      (hq' ▸ dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos))
  exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp Q k q.p
    q.exponent (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hp hk e)

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.SymThree
