module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.C35Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspU4
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieRed

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.Sec53F.BA
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem KConfig.exists_u5_coords
    {X : Type} [Group X] [Finite X] (hXs : IsSimpleGroup X) {f : ℕ}
    (hU : CFSG.Quasithin.IsPSU 5 2 f X) {L V MK : Subgroup X} (hc : KConfig X L V MK) :
    ∃ (K : Type) (_ : Field K) (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)
      (e : X ≃* CFSG.ClassicalGroups.UnitaryFlag.hypPSU h 2 1),
      MK.map e.toMonoidHom = CFSG.Quasithin.H13.Sec53F.Unit.u5PtP h ∨
        MK.map e.toMonoidHom = CFSG.Quasithin.H13.Sec53F.Unit.u5LnP h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup X := hXs
  have hEven : CFSG.Blueprint.EvenLieType X :=
    ⟨.PSU, 5, f, hU.1, Or.inl ⟨by decide, hU⟩⟩
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
    CFSG.Quasithin.H13.F431.Un.OL5.exists_model5 (D := X) (Or.inl ⟨by decide, hU⟩)
  letI : Field K := hKfield
  haveI : Finite (hypPSU hKm 2 1) := CFSG.Quasithin.H13.Sec53F.Unit.finite_hypPSU_five hKm
  have hUs : CFSG.QuasithinUnique.IsSylowTwoOf (hypProjUnitriangular hKm 2 1) ⊤ :=
    CFSG.Quasithin.H13.Sec53F.Unit.u5_sylow hKm
  obtain ⟨e, he⟩ := CFSG.Quasithin.H13.Ch4.U4A.exists_equiv_sylow e₀.symm hUs hS
  have hB : hypProjBorel hKm 2 1 ≤ MK.map e.toMonoidHom := by
    have hmap : (Subgroup.normalizer (S : Set X)).map e.toMonoidHom =
        Subgroup.normalizer
          ((S.map e.toMonoidHom : Subgroup (hypPSU hKm 2 1)) : Set (hypPSU hKm 2 1)) :=
      Subgroup.map_normalizer_eq_of_bijective S (f := e.toMonoidHom) e.bijective
    rw [he, CFSG.Quasithin.H13.Sec53F.Unit.normalizer_hypProjUnitriangular_five] at hmap
    rw [← hmap]
    exact Subgroup.map_mono hNS'
  set A : Subgroup (hypSU hKm 2 1) :=
    (MK.map e.toMonoidHom).comap (hypProj hKm 2 1) with hAdef
  have hBA : hypBorel hKm 2 1 ≤ A := by
    rw [hAdef]
    refine Subgroup.map_le_iff_le_comap.mp ?_
    exact hB
  have hc1 : (1 : K) ∈ hKm.traceZero := by
    have := hKm.charP
    rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
    exact CharTwo.add_self_eq_zero (1 : K)
  set I := overgroupCuts 1 hKm 1 hc1 A with hIdef
  obtain ⟨hI, hAI, -, -⟩ :=
    unitary_Borel_overgroups hKm (r := 2) (ε := 1) (by norm_num) (by norm_num) hc1 one_ne_zero
      A hBA
  rw [← hIdef] at hI hAI
  refine ⟨K, hKfield, hKm, e, ?_⟩
  have hMA : MK.map e.toMonoidHom = (flagStabilizer hKm 2 1 I).map (hypProj hKm 2 1) := by
    rw [← Subgroup.map_comap_eq_self_of_surjective (hypProj_surjective hKm 2 1)
      (MK.map e.toMonoidHom), ← hAdef, hAI]
  by_cases h1 : 1 ∈ I
  · by_cases h2 : 2 ∈ I
    ·
      exfalso
      have hle : ∀ d ∈ I,
          MK.map e.toMonoidHom ≤ projIsoStabilizer hKm 2 1 (hypFlag hKm 2 1 d) := by
        intro d hd
        rw [hMA]
        refine Subgroup.map_mono ?_
        exact fun g hg => mem_flagStabilizer.mp hg d hd
      have hle12 : MK.map e.toMonoidHom ≤ u5PtP hKm ⊓ u5LnP hKm :=
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
      have hleL : L.map e.toMonoidHom ≤ hypProjBorel hKm 2 1 :=
        (Subgroup.map_mono hc.le_MK).trans
          (hle12.trans (le_of_eq (u5PtP_inf_u5LnP (h := hKm))))
      haveI : Group.IsSolvable ↥(hypProjBorel hKm 2 1) := by
        rw [← CFSG.Quasithin.H13.Sec53F.Unit.normalizer_hypProjUnitriangular_five]
        exact (borelBase_u5 hKm).isSolvable_B
      have hsolv : Group.IsSolvable ↥(L.map e.toMonoidHom) := by
        haveI : Group.IsSolvable
            ↥((L.map e.toMonoidHom).subgroupOf (hypProjBorel hKm 2 1)) := inferInstance
        exact Group.isSolvable_of_surjective
          (f := (Subgroup.subgroupOfEquivOfLe hleL).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hleL).surjective
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
      rw [hMA, hI1, flagStabilizer_singleton]
      rfl
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
      rw [hMA, hI2, flagStabilizer_singleton]
      rfl
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
        rw [hMA, hI0, flagStabilizer_empty,
          Subgroup.map_top_of_surjective (hypProj hKm 2 1) (hypProj_surjective hKm 2 1)]
      have hMKtop : MK = ⊤ := by
        apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
        rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
        exact htop
      exact hc.MK_ne_top hMKtop

end CFSG.SectionRank.QTK.Insp443

end
