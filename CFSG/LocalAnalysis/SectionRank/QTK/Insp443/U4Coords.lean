module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.C35Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspU4
public import CFSG.Quasithin.Recognition.St84.Gen.U4qVFact

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem KConfig.exists_u4_coords
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X) {m : ℕ}
    (hU : CFSG.Quasithin.IsPSU 4 2 m X) {L V MK : Subgroup X} (hc : KConfig X L V MK) :
    ∃ (K : Type) (_ : Field K) (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m K)
      (e : X ≃* CFSG.ClassicalGroups.UnitaryFlag.hypSU h 2 0),
      MK.map e.toMonoidHom = CFSG.Quasithin.H13.U4Par.parP h ∨
        MK.map e.toMonoidHom = CFSG.Quasithin.H13.U4Par.parP2 h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup X := hXs
  have hEven : CFSG.Blueprint.EvenLieType X :=
    ⟨.PSU, 4, m, hU.1, Or.inl ⟨by decide, hU⟩⟩
  have hRad : CFSG.Quasithin.SmithC27.IsRadicalParabolic (⊤ : Subgroup X) :=
    CFSG.Quasithin.C22Pf.isRadicalParabolic_c224_holds X (Or.inl hEven)
  have hU2 : IsPGroup 2 (pCoreOf 2 MK) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥MK)) MK.subtype
  have hU_ne : pCoreOf 2 MK ≠ ⊥ := by
    refine fun hbot => hc.ne_bot ?_
    have hVL : pCoreOf 2 L ≤ pCoreOf 2 MK :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hc.le_MK)
        (hc.MK_le_normalizer.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
        (IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) L.subtype)
    exact le_bot_iff.mp (hc.le_pCoreOf.trans (hVL.trans_eq hbot))
  have hEq : pCoreOf 2 (⊤ ⊓ Subgroup.normalizer ((pCoreOf 2 MK : Subgroup X) : Set X)) =
      pCoreOf 2 MK := by
    rw [top_inf_eq, hc.normalizer_pCoreOf_MK]
  have hpar : IsParabolic2 (⊤ : Subgroup X) MK := by
    have hp := hRad (pCoreOf 2 MK) le_top hU_ne hU2 hEq
    rwa [top_inf_eq, hc.normalizer_pCoreOf_MK] at hp
  obtain ⟨-, S, hS, hNS⟩ := hpar
  have hNS' : Subgroup.normalizer (S : Set X) ≤ MK := by
    have := hNS
    rwa [top_inf_eq] at this
  obtain ⟨K, hKfield, hKm, ⟨e₀⟩⟩ :=
    CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel (Y := X) (Or.inl ⟨by decide, hU⟩)
  letI : Field K := hKfield
  haveI : Finite (hypSU hKm 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU hKm
  have hUs : CFSG.QuasithinUnique.IsSylowTwoOf (hypUnitriangular hKm 2 0) ⊤ :=
    CFSG.Quasithin.H13.U4Par.isSylowTwoOf_hypUnitriangular hKm
  obtain ⟨e, he⟩ := CFSG.Quasithin.H13.Ch4.U4A.exists_equiv_sylow e₀ hUs hS
  have hB : hypBorel hKm 2 0 ≤ MK.map e.toMonoidHom := by
    have hmap : (Subgroup.normalizer (S : Set X)).map e.toMonoidHom =
        Subgroup.normalizer
          ((S.map e.toMonoidHom : Subgroup (hypSU hKm 2 0)) : Set (hypSU hKm 2 0)) :=
      Subgroup.map_normalizer_eq_of_bijective S (f := e.toMonoidHom) e.bijective
    rw [he, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypUnitriangular hKm
      (by norm_num) (by norm_num)] at hmap
    rw [← hmap]
    exact Subgroup.map_mono hNS'
  obtain ⟨c, hcT, hc0⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_mem_traceZero_ne_zero' hKm
  set I := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.overgroupCuts 0 hKm c hcT
      (MK.map e.toMonoidHom) with hIdef
  obtain ⟨hI, hAI, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_Borel_overgroups hKm
      (by norm_num) (by norm_num) hcT hc0 (MK.map e.toMonoidHom) hB
  rw [← hIdef] at hI hAI
  refine ⟨K, hKfield, hKm, e, ?_⟩
  by_cases h1 : 1 ∈ I
  · by_cases h2 : 2 ∈ I
    ·
      exfalso
      have hle : ∀ d ∈ I,
          MK.map e.toMonoidHom ≤
            CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isoStabilizer hKm 2 0
              (hypFlag hKm 2 0 d) := by
        intro d hd g hg
        rw [hAI] at hg
        exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_isoStabilizer.mpr
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_flagStabilizer.mp hg d hd)
      have hle12 : MK.map e.toMonoidHom ≤
          CFSG.Quasithin.H13.U4Par.parP hKm ⊓ CFSG.Quasithin.H13.U4Par.parP2 hKm :=
        le_inf (hle 1 h1) (hle 2 h2)
      have hLne : L ≠ ⊥ := fun hL =>
        hc.ne_bot (le_bot_iff.mp (hc.le_pCoreOf.trans
          (by rw [hL]; exact CFSG.LieType.BorelTits.pCoreOf_le 2 ⊥)))
      have hLmap_perf : Group.IsPerfect ↥(L.map e.toMonoidHom) := by
        let : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hc.perfect
        exact Group.IsPerfect.map e.toMonoidHom
      have hLmap_ne : L.map e.toMonoidHom ≠ ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective L e.injective).not.mpr hLne
      haveI : Nontrivial ↥(L.map e.toMonoidHom) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hLmap_ne
      let : Group.IsPerfect ↥(L.map e.toMonoidHom) := hLmap_perf
      have hsolv : Group.IsSolvable ↥(L.map e.toMonoidHom) := by
        haveI : Group.IsSolvable ↥(CFSG.Quasithin.H13.U4Par.parP hKm ⊓
            CFSG.Quasithin.H13.U4Par.parP2 hKm) :=
          CFSG.Quasithin.F112R.isSolvable_parP_inf_parP2 hKm
        haveI : Group.IsSolvable
            ↥((L.map e.toMonoidHom).subgroupOf
              (CFSG.Quasithin.H13.U4Par.parP hKm ⊓
                CFSG.Quasithin.H13.U4Par.parP2 hKm)) := inferInstance
        exact Group.isSolvable_of_surjective
          (f := (Subgroup.subgroupOfEquivOfLe
            (Subgroup.map_mono hc.le_MK |>.trans hle12)).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe
            (Subgroup.map_mono hc.le_MK |>.trans hle12)).surjective
      exact Group.IsPerfect.not_isSolvable ↥(L.map e.toMonoidHom) hsolv
    ·
      left
      have hI1 : I = {1} := by
        ext i
        rw [Set.mem_singleton_iff]
        constructor
        · intro hi
          obtain ⟨hi1, hi2⟩ := hI hi
          by_contra hne
          have h2' : i = 2 := by omega
          exact h2 (h2' ▸ hi)
        · intro hi
          subst hi
          exact h1
      rw [hAI, hI1, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.flagStabilizer_singleton]
  · by_cases h2 : 2 ∈ I
    ·
      right
      have hI2 : I = {2} := by
        ext i
        rw [Set.mem_singleton_iff]
        constructor
        · intro hi
          obtain ⟨hi1, hi2⟩ := hI hi
          by_contra hne
          have h1' : i = 1 := by omega
          exact h1 (h1' ▸ hi)
        · intro hi
          subst hi
          exact h2
      rw [hAI, hI2, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.flagStabilizer_singleton]
    ·
      exfalso
      have hI0 : I = ∅ := by
        ext i
        constructor
        · intro hi
          obtain ⟨hi1, hi2⟩ := hI hi
          have h12 : i = 1 ∨ i = 2 := by omega
          rcases h12 with rfl | rfl
          · exact absurd hi h1
          · exact absurd hi h2
        · intro hi
          exact absurd hi (Set.notMem_empty i)
      have htop : MK.map e.toMonoidHom = ⊤ := by
        rw [hAI, hI0, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.flagStabilizer_empty]
      have hMKtop : MK = ⊤ := by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
        exact htop
      exact hc.MK_ne_top hMKtop

end CFSG.SectionRank.QTK.Insp443

end
