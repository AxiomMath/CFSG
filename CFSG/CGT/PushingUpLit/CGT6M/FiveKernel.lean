module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveRankFour
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LocalAnalysis.SectionRank.OddCover.LinearThree
public import CFSG.RankThree.PartOne.S11c.UnitaryFiveLift
public import CFSG.Open.StatedAPI
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.PushingUpLit.CGT6M.FiveYSide
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.Foundations
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.RankThree.CentralExtension.InvariantComplement
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

section Classical

variable {L Q : Type} [Group L] [Finite L] [Group.IsPerfect L] [Group Q]

theorem not_five_dvd_card_ker_psl2_25 (π : L →* Q) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center L) (hQ : CFSG.Open.StatedClassicalModel Q .PSL 2 5 2) :
    ¬ 5 ∣ Nat.card π.ker := by
  obtain ⟨-, K, hKf, hKfin, hK25, ⟨e0⟩⟩ := hQ
  let e : Q ≃* StatedProj (StatedSL 2 K) := e0
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = 5 ^ 2 := hK25
  let π' : L →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (pslEquiv K).symm.toMonoidHom.comp (e.toMonoidHom.comp π)
  have hker : π'.ker = π.ker := by
    ext g
    simp only [MonoidHom.mem_ker, π', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  intro h5
  have h5' : 5 ∣ Nat.card π'.ker := by rw [hker]; exact h5
  have Cp : Sylow 5 π'.ker := default
  exact Sylow.ne_bot_of_dvd_card Cp h5'
    (psl_two_sylow_kernel_eq_bot (p := 5) (f := 2) (by norm_num) hK' (by norm_num) π'
      ((pslEquiv K).symm.surjective.comp (e.surjective.comp hπ)) (hker ▸ hK) Cp)

theorem det_eq_one_of_mem_statedSL_five {n : ℕ} {K : Type} [Field K] {g : GL (Fin n) K}
    (h : g ∈ StatedSL n K) : (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL h

theorem statedSL_three_five_mk_injective {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5) :
    Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))) := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  obtain ⟨r, hr⟩ := Subgroup.mem_subgroupOf.mp hg
  have hdet := det_eq_one_of_mem_statedSL_five g.2
  rw [← hr] at hdet
  have hr3 : r ^ 3 = 1 := by
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.det_smul] using hdet
  have : Fintype K := Fintype.ofFinite K
  have hr4 : r ^ 4 = 1 := by
    apply Units.ext
    have := FiniteField.pow_card_sub_one_eq_one (r : K) r.ne_zero
    rw [← Nat.card_eq_fintype_card, hK] at this
    simpa using this
  have hr1 : r = 1 := by
    calc r = r ^ 4 * (r ^ 3)⁻¹ := by group
      _ = 1 := by rw [hr3, hr4]; group
  apply Subtype.ext
  rw [← hr, hr1, map_one]
  rfl

theorem not_five_dvd_card_ker_psl3_5 (π : L →* Q) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center L) (hQ : CFSG.Open.StatedClassicalModel Q .PSL 3 5 1) :
    ¬ 5 ∣ Nat.card π.ker := by
  obtain ⟨-, K, hKf, hKfin, hK5, ⟨e0⟩⟩ := hQ
  let e : Q ≃* StatedProj (StatedSL 3 K) := e0
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK' : Nat.card K = 5 := by simpa using hK5
  let mk : StatedSL 3 K →* StatedProj (StatedSL 3 K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
  let f : StatedSL 3 K ≃* StatedProj (StatedSL 3 K) :=
    MulEquiv.ofBijective mk ⟨statedSL_three_five_mk_injective hK', QuotientGroup.mk'_surjective _⟩
  let π' : L →* StatedSL 3 K := f.symm.toMonoidHom.comp (e.toMonoidHom.comp π)
  have hker : π'.ker = π.ker := by
    ext g
    simp only [MonoidHom.mem_ker, π', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  intro h5
  have h5' : 5 ∣ Nat.card π'.ker := by rw [hker]; exact h5
  have Cp : Sylow 5 π'.ker := default
  exact Sylow.ne_bot_of_dvd_card Cp h5'
    (statedSL_three_sylow_kernel_eq_bot (p := 5) (by norm_num) hK' π'
      (f.symm.surjective.comp (e.surjective.comp hπ)) (hker ▸ hK) Cp)

theorem not_five_dvd_card_ker_psu3_5 (π : L →* Q) (hπ : Function.Surjective π)
    (hK : π.ker ≤ Subgroup.center L) (hQ : CFSG.Open.StatedClassicalModel Q .PSU 3 5 1) :
    ¬ 5 ∣ Nat.card π.ker :=
  CFSG.RankThree.PartOne.HNRed.not_five_dvd_card_ker (hQ : StatedClassicalModel Q .PSU 3 5 1) π
    hπ hK

end Classical

section Assembled

open CFSG.Blueprint

variable {V : Type} [CommGroup V] [Finite V] {L Q : Type} [Group L] [Finite L] [Group.IsPerfect L]
  [Group Q]

theorem false_of_five_element_rank_four_perfect
    (ρ : L →* MulAut V)
    (hρ : Function.Injective ρ) (hV : ∀ v : V, v ^ 2 = 1) (π : L →* Q)
    (hπ : Function.Surjective π) (hK : π.ker ≤ Subgroup.center L) {y : L} (hy1 : y ≠ 1)
    (hy5 : y ^ 5 = 1) (h16 : Nat.card V ≤ 2 ^ 4 * Nat.card ↥(fixSub (ρ y)))
    (hsp : NativeSporadic.IsSporadic Q .M12 ∨ NativeSporadic.IsSporadic Q .J1 ∨
      NativeSporadic.IsSporadic Q .J2 → Nat.Coprime (Nat.card π.ker) 55)
    (hQ : CFSG.Open.StatedClassicalModel Q .PSL 2 5 2 ∨
      CFSG.Open.StatedClassicalModel Q .PSL 3 5 1 ∨ CFSG.Open.StatedClassicalModel Q .PSU 3 5 1 ∨
      NativeSporadic.IsSporadic Q .M12 ∨ NativeSporadic.IsSporadic Q .J1 ∨
      NativeSporadic.IsSporadic Q .J2) : False := by
  rcases hQ with h | h | h | h | h | h
  · exact false_of_rank_four_psl2_25 ρ hρ hV π hπ hK hy1 hy5 h16
      (not_five_dvd_card_ker_psl2_25 π hπ hK h) h
  · exact false_of_rank_four_psl3_5 ρ hρ hV π hπ hK hy1 hy5 h16
      (not_five_dvd_card_ker_psl3_5 π hπ hK h) h
  · exact false_of_rank_four_psu3_5 ρ hρ hV π hπ hK hy1 hy5 h16
      (not_five_dvd_card_ker_psu3_5 π hπ hK h) h
  · obtain ⟨hK5, hK11⟩ := not_dvd_of_coprime_fifty_five (hsp (Or.inl h))
    exact false_of_rank_four_m12 ρ hρ hV π hπ hK hy1 hy5 h16 hK5 hK11 h
  · obtain ⟨hK5, hK11⟩ := not_dvd_of_coprime_fifty_five (hsp (Or.inr (Or.inl h)))
    exact false_of_rank_four_j1 ρ hρ hV π hπ hK hy1 hy5 h16 hK5 hK11 h
  · obtain ⟨hK5, -⟩ := not_dvd_of_coprime_fifty_five (hsp (Or.inr (Or.inr h)))
    exact false_of_rank_four_j2 ρ hρ hV π hπ hK hy1 hy5 h16 hK5 h

end Assembled

end CFSG.CGT.PushingUpLit.CGT6M
