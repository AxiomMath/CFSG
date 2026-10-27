module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCType
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.GroupTheory.WeirSylow
open scoped commutatorElement

section Quasi

theorem isQuasisimple_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ¬ ∀ x y : G, x * y = y * x) : CFSG.Open.IsQuasisimple G ∧ Subgroup.center G = ⊥ := by
  have hZ : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exact (hna fun x y => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)).elim
  have hperf : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · refine (hna fun x y => ?_).elim
      have h1 : ⁅x, y⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rwa [commutatorElement_eq_one_iff_mul_comm] at h1
    · exact h
  have e : G ⧸ Subgroup.center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨⟨hperf, e.isSimpleGroup⟩, hZ⟩

end Quasi

section Comp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_component (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {lJ lI : List (V × V)}
    (hl : IsFrame Q (lJ ++ lI)) (hJ : lJ ≠ [])
    (hd : finrank (ZMod 2) (perpL Q lI) = 4 ∨ finrank (ZMod 2) (perpL Q lI) = 6)
    (hts : ¬ IsPlusType (Q.comp (perpL Q lI).subtype)) :
    ∃ L : Subgroup (V ≃ₗ[ZMod 2] V),
      L ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ⊓
        Subgroup.centralizer (torus Q lI : Set (V ≃ₗ[ZMod 2] V)) ∧
      (∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ⊓
        Subgroup.centralizer (torus Q lI : Set (V ≃ₗ[ZMod 2] V)), ∀ x ∈ L, g * x * g⁻¹ ∈ L) ∧
      CFSG.Open.IsQuasisimple ↥L ∧ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  have hlI : IsFrame Q lI := hl.sublist (List.sublist_append_right _ _)
  have hW : IsCompl (Wspan lI) (perpOf Q (Wspan lI)) := hlI.isCompl
  have hndU : (QuadraticMap.polarBilin (Q.restrict (perpOf Q (Wspan lI)))).Nondegenerate :=
    nondeg_comp_subtype (hlI.perpL_nondeg hQ)
  have hd' : finrank (ZMod 2) (perpOf Q (Wspan lI)) = 4 ∨ finrank (ZMod 2) (perpOf Q (Wspan lI)) = 6 :=
    hd
  have hts2 : ¬ IsPlusType (Q.comp (perpOf Q (Wspan lI)).subtype) := hts
  have hts' : ∀ U' : Submodule (ZMod 2) (perpOf Q (Wspan lI)),
      finrank (ZMod 2) U' = finrank (ZMod 2) (perpOf Q (Wspan lI)) / 2 →
      ∃ u ∈ U', (Q.restrict (perpOf Q (Wspan lI))) u ≠ 0 := by
    intro U' hU'
    by_contra hno
    push Not at hno
    exact hts2 ⟨U', by omega, fun x hx => hno x hx⟩
  obtain ⟨hsimple, -, hnc, -, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (Q.restrict (perpOf Q (Wspan lI))) hndU hd' hts'
  obtain ⟨e⟩ := commutator_fixW_equiv (Q := Q) hW
  haveI : IsSimpleGroup ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ := e.isSimpleGroup
  have hna : ¬ ∀ x y : ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆, x * y = y * x := by
    intro h
    apply hnc
    intro x y
    apply e.symm.injective
    rw [map_mul, map_mul, h]
  obtain ⟨hqs, hZ⟩ := isQuasisimple_of_simple_nonabelian hna
  have hperp : ∀ q ∈ lI, ∀ p ∈ lJ, PairPerp Q p q :=
    fun q hq p hp => (List.pairwise_append.1 hl.perp).2.2 p hp q hq
  refine ⟨⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆, ?_, ?_, hqs, ?_⟩
  · exact le_inf (Subgroup.commutator_mono fixW_le_orthogonalGroup fixW_le_orthogonalGroup)
      ((Subgroup.commutator_le_self _).trans (fixW_le_centralizer_torus hlI))
  · intro g hg x hx
    exact commutator_fixW_conj hlI (Subgroup.commutator_le_self _ hg.1) hg.2 hx
  ·
    obtain ⟨p, lJ', rfl⟩ := List.exists_cons_of_ne_nil hJ
    have hp : MinusPair Q p.1 p.2 := hl.pair p (by simp)
    have hpp : ∀ q ∈ lI, PairPerp Q p q := fun q hq => hperp q hq p (by simp)
    have hmem : ∀ x : V, (∀ q ∈ lI, polar Q x q.1 = 0 ∧ polar Q x q.2 = 0) →
        x ∈ perpOf Q (Wspan lI) := by
      intro x hx
      exact (mem_perpL_iff lI x).2 (fun q hq => ⟨by rw [polar_comm]; exact (hx q hq).1, by
        rw [polar_comm]; exact (hx q hq).2⟩)
    have h1 : p.1 ∈ perpOf Q (Wspan lI) := hmem p.1 (fun q hq => ⟨(hpp q hq).1, (hpp q hq).2.1⟩)
    have h2 : p.2 ∈ perpOf Q (Wspan lI) :=
      hmem p.2 (fun q hq => ⟨(hpp q hq).2.2.1, (hpp q hq).2.2.2⟩)
    have hρ : rot Q p.1 p.2 ∈ ⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ :=
      rot_mem_commutator_of hp _ (reflect_mem_fixW h1) (reflect_mem_fixW h2)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : rot Q p.1 p.2 ≠ 1 := by
      intro h1
      have := rot_apply_left hp
      rw [h1] at this
      exact hp.ne this
    have hord : orderOf (rot Q p.1 p.2) = 3 := orderOf_eq_prime (rot_pow_three hp) hne
    have hdvd : 3 ∣ Nat.card ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard _ hρ
    have e2 : (↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ ⧸
        Subgroup.center ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆) ≃*
        ↥⁅fixW Q (Wspan lI), fixW Q (Wspan lI)⁆ :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    rw [Nat.card_congr e2.toEquiv]
    exact hdvd

end Comp


end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end
