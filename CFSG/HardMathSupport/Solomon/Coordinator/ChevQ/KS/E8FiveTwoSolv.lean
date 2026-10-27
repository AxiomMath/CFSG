module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoWeyl
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveA4Weyl
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSolvable
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyOrder
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq
  CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
open CFSG.RankThree.E6 (charVal)

set_option linter.unusedSectionVars false

section Solvable


@[expose] def planeFamily {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    Fin 2 → Fin Tag.E8.rank → Lˣ :=
  ![fun k => griessU hζ ^ czVec k, fun k => griessU hζ ^ cxVec k]

theorem rootDiagUnit_planeFamily_zero {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    rootDiagUnit Tag.E8 (planeFamily hζ 0) = griessZ hζ := rfl

theorem rootDiagUnit_planeFamily_one {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    rootDiagUnit Tag.E8 (planeFamily hζ 1) = griessX hζ := rfl

theorem planeFamily_kernel {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    familyKernel (planeFamily hζ) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun α ⟨hα, hχ⟩ => ?_
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα
  have key : ∀ c : Fin Tag.E8.rank → ℕ, rootChar (fun k => griessU hζ ^ c k) (e8RootVec m) = 1 →
      (∑ k, (c k : ℤ) * e8RootVec m k) % 5 = 0 := by
    intro c h
    rw [rootChar_powVec] at h
    have h2 := (orderOf_dvd_iff_zpow_eq_one (G := Lˣ) (x := griessU hζ)
      (i := ∑ k, (c k : ℤ) * e8RootVec m k)).2 h
    rw [← (griessU_prim hζ).eq_orderOf] at h2
    exact Int.emod_eq_zero_of_dvd h2
  exact plane_regular_data m (key czVec (hχ 0)) (key cxVec (hχ 1))

theorem planeFamily_stab {L : Type} [Field L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {w : WeylGroup Tag.E8} (hw : w ∈ familyStabilizer (planeFamily hζ)) :
    w ∈ dualWeylStabilizer (fun i => ((czVec i : ℕ) : ZMod 5)) ⊓
      dualWeylStabilizer (fun i => ((cxVec i : ℕ) : ZMod 5)) := by
  have hord : orderOf (griessU hζ) = 5 := (griessU_prim hζ).eq_orderOf.symm
  refine Subgroup.mem_inf.2 ⟨mem_dualWeylStabilizer.2 fun v => ?_,
    mem_dualWeylStabilizer.2 fun v => ?_⟩
  · exact (rootChar_eq_rootChar_iff hord czVec (planeFamily hζ 0) (fun _ => rfl) _ _).1 (hw 0 v)
  · exact (rootChar_eq_rootChar_iff hord cxVec (planeFamily hζ 1) (fun _ => rfl) _ _).1 (hw 1 v)

theorem charVal_natCast_eq' (k : Fin Tag.E8.rank → ℕ) (l : Fin Tag.E8.rank → ℤ) :
    charVal (fun i => ((k i : ℕ) : ZMod 5)) l = (((∑ i, (k i : ℤ) * l i : ℤ)) : ZMod 5) := by
  simp only [charVal, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem plane_regular_charVal : ∀ α, IsRoot Tag.E8 α →
    charVal (fun i => ((czVec i : ℕ) : ZMod 5)) α = 0 →
      charVal (fun i => ((cxVec i : ℕ) : ZMod 5)) α = 0 → False := by
  intro α hα h₀ h₁
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hα
  rw [charVal_natCast_eq', ZMod.intCast_zmod_eq_zero_iff_dvd] at h₀ h₁
  exact plane_regular_data m (Int.emod_eq_zero_of_dvd h₀) (Int.emod_eq_zero_of_dvd h₁)

theorem isSolvable_familyCentralizer_plane {L : Type} [Field L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ 5) :
    Group.IsSolvable ↥(familyCentralizer Tag.E8 L (planeFamily hζ)) := by
  classical
  set H := dualWeylStabilizer (fun i => ((czVec i : ℕ) : ZMod 5)) ⊓
    dualWeylStabilizer (fun i => ((cxVec i : ℕ) : ZMod 5)) with hH
  haveI hHs : Group.IsSolvable ↥H := isSolvable_inf_dualWeylStabilizer plane_regular_charVal
  have hgroup : familyGroup (K := L) (planeFamily hζ) = torusGroup Tag.E8 L := by
    rw [familyGroup, planeFamily_kernel hζ, rootSpan]
    simp
  have hmono : ∀ g : familyCentralizer Tag.E8 L (planeFamily hζ),
      ∃ w ∈ H, ∃ m ∈ torusGroup Tag.E8 L,
        (g : ModGL Tag.E8 L) = m * canonicalRep (coxeterSystem Tag.E8) L w := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := familyCentralizer_le_mul Tag.E8 L (planeFamily hζ) g.2
    rw [hgroup] at hm
    exact ⟨w, planeFamily_stab hζ hw, m, hm, hmg⟩
  have hmem : ∀ g : familyCentralizer Tag.E8 L (planeFamily hζ),
      (g : ModGL Tag.E8 L) ∈ monomialSubgroup Tag.E8 L := by
    intro g
    obtain ⟨w, -, m, hm, hmg⟩ := hmono g
    rw [hmg]
    exact mul_mem (Subgroup.mem_sup_left hm)
      (canonicalRep_mem_monomialSubgroup' w)
  let ψ : familyCentralizer Tag.E8 L (planeFamily hζ) →* monomialSubgroup Tag.E8 L :=
    MonoidHom.codRestrict (Subgroup.subtype _) _ hmem
  have hψ : Function.Injective ψ := by
    intro g g' h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  obtain ⟨ρ, hρmaps, hsolv⟩ := isSolvable_comap_weylQuotient Tag.E8 L H
  have hρψ : ∀ g, ρ (ψ g) ∈ H := by
    intro g
    obtain ⟨w, hw, m, hm, hmg⟩ := hmono g
    have h1 : MapsRootLines (ψ g : (Module.End L (RootModule Tag.E8 L))ˣ) (1 * w) := by
      have e : (ψ g : (Module.End L (RootModule Tag.E8 L))ˣ) =
          m * canonicalRep (coxeterSystem Tag.E8) L w := hmg
      rw [e]
      exact (mapsRootLines_of_mem_torusGroup hm).mul (mapsRootLines_canonicalRep w)
    rw [(hρmaps (ψ g)).unique h1, one_mul]
    exact hw
  let ψ' : familyCentralizer Tag.E8 L (planeFamily hζ) →* ↥(H.comap ρ) :=
    ψ.codRestrict (H.comap ρ) hρψ
  haveI := hsolv
  refine Group.isSolvable_of_isSolvable_injective (f := ψ') ?_
  intro g g' h
  have h' : ψ g = ψ g' := congrArg Subtype.val h
  exact hψ h'

end Solvable

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
