module

public import CFSG.ClassicalInvolution.AschTight.E3OddGen
public import CFSG.ClassicalInvolution.Q3.Q3T6AutConj
public import CFSG.ClassicalInvolution.AschTight.Lemma33
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

theorem Aut.isOddPrimePower_card_zmod_three :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod 3)) :=
  ⟨3, 1, Nat.prime_three, by decide, le_rfl, by simp⟩

theorem sl2Three_mulAut_isPGroup_exists_closure_pair {H : Subgroup (MulAut SL(2, ZMod 3))}
    (hH : IsPGroup 2 H) : ∃ a b : MulAut SL(2, ZMod 3), Subgroup.closure {a, b} = H := by
  have hH' : IsPGroup 2 (H.map (mulAutEquivPGL2 : MulAut SL(2, ZMod 3) →* PGL(2, ZMod 3))) :=
    hH.map _
  obtain ⟨a, b, hab⟩ :=
    exists_closure_pair_eq_of_isPGroup_pgl2 Aut.isOddPrimePower_card_zmod_three hH'
  refine ⟨mulAutEquivPGL2.symm a, mulAutEquivPGL2.symm b, ?_⟩
  have h := congrArg (Subgroup.map (mulAutEquivPGL2.symm : PGL(2, ZMod 3) →*
    MulAut SL(2, ZMod 3))) hab
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, Subgroup.map_map] at h
  have hid : (mulAutEquivPGL2.symm : PGL(2, ZMod 3) →* MulAut SL(2, ZMod 3)).comp
      (mulAutEquivPGL2 : MulAut SL(2, ZMod 3) →* PGL(2, ZMod 3)) = MonoidHom.id _ := by
    ext x
    simp
  rw [hid, Subgroup.map_id] at h
  simpa using h

end CFSG.ClassicalInvolution.Q3.Q3T6
