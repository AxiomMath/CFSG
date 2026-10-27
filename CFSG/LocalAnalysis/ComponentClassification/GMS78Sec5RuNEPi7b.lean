module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNEChecks
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmWords

public section

namespace CFSG.ComponentClassification.GMS78.RuNE

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj
open CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm

abbrev Pi7b : Type := PG 7 pi7bRels

theorem card_pi7b_le :
    Finite Pi7b ∧ Nat.card Pi7b ≤ 145926144000 :=
  card_pi7bRels

noncomputable def pi7bToJ :
    Pi7b →* J CFSG.Sporadic.Ru.Native.ruData :=
  PresentedGroup.toGroup (f := fun i : Fin 7 => pi7Img i.val) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [lift_mk_eq_wordProd]
    exact pi7b_rels w hw

theorem pi7bToJ_of (i : Fin 7) :
    pi7bToJ (PresentedGroup.of i) = pi7Img i.val :=
  PresentedGroup.toGroup.of _

theorem range_eq_closure_of {α H : Type*} [Group H] {rels : Set (FreeGroup α)}
    (φ : PresentedGroup rels →* H) :
    φ.range = Subgroup.closure (Set.range fun a => φ (PresentedGroup.of a)) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  rfl

theorem pi7bToJ_surjective :
    Function.Surjective pi7bToJ := by
  have e : (fun i : Fin 7 => pi7bToJ (PresentedGroup.of i)) =
      fun i => pi7ToJ (PresentedGroup.of i) :=
    funext fun i => by rw [pi7bToJ_of, pi7ToJ_of]
  have h : pi7bToJ.range = pi7ToJ.range := by
    rw [range_eq_closure_of, range_eq_closure_of, e]
  exact MonoidHom.range_eq_top.1 (h.trans (MonoidHom.range_eq_top.2 pi7ToJ_surjective))

theorem pi7bToJ_bijective :
    Function.Bijective pi7bToJ := by
  have := card_pi7b_le.1
  exact pi7bToJ_surjective.bijective_of_nat_card_le
    (card_pi7b_le.2.trans CFSG.Sporadic.Bridge.Ru.card_J.ge)

noncomputable def pi7bEquivJ :
    Pi7b ≃* J CFSG.Sporadic.Ru.Native.ruData :=
  MulEquiv.ofBijective pi7bToJ pi7bToJ_bijective

noncomputable def pi7bEquivRu :
    Pi7b ≃* Blueprint.NativeSporadic.Ru :=
  pi7bEquivJ.trans CFSG.Sporadic.Bridge.Ru.nativeEquiv.symm

theorem pi7Word_eq_one_of_mem_pi7bRels
    {r : List (Fin 7 × Bool)} (hr : r ∈ pi7bRels) : pi7Word r = 1 := by
  apply pi7ToJ_bijective.1
  rw [map_one, pi7ToJ_pi7Word]
  exact pi7b_rels r hr

end CFSG.ComponentClassification.GMS78.RuNE
