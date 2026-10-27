module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeFinal
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Schreier.NormalThree CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1Block
  CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271 CFSG.LieType.Multipliers.U43


section Generic

variable {Good : ∀ (T : Type) [Group T], Prop}
  (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
  (hU : ∀ (T : Type) [Group T], T ≃* X₀ → Good T)
  (hA9 : Good ↥(alternatingGroup (Fin 9)))
  (hS : ∀ (T : Type) [Group T], Nat.card T = 448345497600 →
    Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group) → Good T)

include hGood hU hA9 hS in
theorem tabCo1_centShapeRk_three_good
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group)) :
    CentShapeRk 3 Good (fun _ _ => True) ↥GA := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hk3
  obtain ⟨g, x, hx, hcases⟩ := tabCo1_census_three k (orderOf_eq_prime hk3 hk1)
  have hshape : ShapeRkAt 3 Good (fun _ _ => True) x := by
    rcases hcases with h | h | h | h
    · exact Or.inl (tabCo1_threeC x h)
    · obtain ⟨J, hJC, hJn, hq, hp3, hZ3, hcent, ⟨eJ⟩⟩ := threeB_data h
      exact shapeRkAt_of_subgroup_data_quasi Nat.prime_three hGood hRk GA x J hJC hJn hq hp3 hZ3
        hcent (hU _ eJ) trivial
    · obtain ⟨hx1, hx3, hxy, hM, hy1⟩ := moore_data (x := (x : GL24)) h
      have hpres := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 9)
        (by norm_num) mooreM hM).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hy1⟩
      obtain ⟨-, ⟨e⟩⟩ := hpres
      set L : Subgroup GL24 := Subgroup.closure (mooreM '' Set.Icc 1 (9 - 2)) with hL
      have hLC : L ≤ Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨j, ⟨hj1, hj7⟩, rfl⟩
        exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (hxy j hj1 (by omega)).symm, mooreM_mem j⟩
      obtain ⟨hs, hnab, hcardL⟩ := alt9_subgroup_data e
      have hbound : Nat.card ↥(Subgroup.centralizer ({(x : GL24)} : Set GL24) ⊓ GA) ≤
          3 * Nat.card ↥L := by
        rw [← card_centralizer_GA_eq_inf GA x, hcardL]
        exact TabCo1ThreeDRoot.card_cent_threeD_root_le x h
      exact shapeRkAt_of_bound Nat.prime_three hGood hRk GA x L hLC hs hnab
        (by rw [hcardL]; norm_num) hx1 hx3 hbound (hGood _ _ e hA9) trivial
    · obtain ⟨J, hJC, hJn, hq, hp3, hcard3, hcent, hqcard, ⟨eJ⟩⟩ := threeA_data (hb) h
      have hZp : IsPGroup 3 ↥(Subgroup.center ↥J) :=
        IsPGroup.of_card (n := 1) (by rw [hcard3]; norm_num)
      exact shapeRkAt_of_subgroup_data_quasi Nat.prime_three hGood hRk GA x J hJC hJn hq hp3 hZp
        hcent (hS _ hqcard ⟨eJ⟩) trivial
  rw [hx]
  exact @shapeRkAt_conj ↥GA (Subgroup.toGroup GA) inferInstance 3 Nat.prime_three _ _ hGood hRk x
    hshape g

end Generic

end CFSG.HardMathSupport.Dickson.I271.TabCo1
