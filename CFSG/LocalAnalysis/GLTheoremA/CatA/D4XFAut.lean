module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut
public import CFSG.LocalAnalysis.GLTheoremA.S9.L94Transport
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.Models.Transport
public import CFSG.RankThree.PartTwo.Census.Spin.Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4
public import Certificates.Certificate8171
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4XF

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9
  CFSG.ComponentClassification.OuterAutomorphisms

theorem subsingleton_ringEquiv_of_card_two {K₀ : Type} [Field K₀] (hK₀ : Nat.card K₀ = 2) :
    Subsingleton (K₀ ≃+* K₀) := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K₀)).mp hK₀
  have hx : ∀ x : K₀, x = 0 ∨ x = 1 := by
    intro x
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · exact Or.inr ((hy x hx0).trans (hy 1 one_ne_zero).symm)
  refine ⟨fun f g => RingEquiv.ext fun x => ?_⟩
  rcases hx x with rfl | rfl <;> simp

theorem d4two_aut_le {K : Type} [Group K] [Finite K] (h : catalogIs K S9.isD4two) :
    ∀ P : Subgroup (MulAut K), CFSG.Open.IsElemAbelian 3 P → ¬ P ≤ inner K → Nat.card P ≤ 3 ^ 3 := by
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := statedModel_of_d4two h
  have hK₀' : Nat.card K₀ = 2 := by rw [hK₀]; norm_num
  haveI : Finite K₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK₀']; norm_num)
  have hunits : Nat.card K₀ˣ = 1 := by
    rw [Nat.card_units, hK₀']
  have hu : Subsingleton K₀ˣ := (Nat.card_eq_one_iff_unique.1 hunits).1
  have hs : Subsingleton (K₀ ≃+* K₀) := subsingleton_ringEquiv_of_card_two hK₀'
  obtain ⟨Φ⟩ := equiv_triality_of_statedProj hu e
  have hdiv : ¬ 3 ∣ Nat.card (K₀ ≃+* K₀) := by
    rw [Nat.card_eq_one_iff_unique.2 ⟨hs, ⟨RingEquiv.refl K₀⟩⟩]
    norm_num
  have hrange : (CFSG.StandardType.AutOm.fieldAutP (K := K₀) 4).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_bot, Subsingleton.elim σ 1, map_one]
  intro P hP hPn
  obtain ⟨α, hαP, hαn⟩ := Set.not_subset.1 hPn
  have hα' : MulAut.congr Φ α ∉ inner (CFSG.StandardType.Triality.Om8 K₀) ⊔
      (CFSG.StandardType.AutOm.fieldAutP (K := K₀) 4).range := by
    rw [hrange, sup_bot_eq]
    intro hmem
    have hmem' : MulAut.congr Φ α ∈ (inner K).map (MulAut.congr Φ).toMonoidHom := by
      rw [inner_map_congr Φ]
      exact hmem
    obtain ⟨β, hβ, hβα⟩ := Subgroup.mem_map.1 hmem'
    have hβeq : β = α := (MulAut.congr Φ).injective hβα
    exact hαn (hβeq ▸ hβ)
  have hA := CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map (MulAut.congr Φ).toMonoidHom hP
  have hαA : MulAut.congr Φ α ∈ P.map (MulAut.congr Φ).toMonoidHom := Subgroup.mem_map_of_mem _ hαP
  have key := CFSG.StandardType.NbrGraphD4.card_le_27 hdiv hA hαA hα'
  rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.congr Φ))] at key
  simpa using key

end CFSG.LocalAnalysis.GLTheoremA.D4XF
