module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriFacts
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputsModel
public import CFSG.LocalAnalysis.StandardType.GGTriD4SchurHolds
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Holds


theorem triD4_datum {Γ : Type} [Group Γ] {J : Subgroup Γ} {lab : GLALabel} (h : LabelOf J lab)
    (htag : lab.tag = .triD4) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ lab.n ∧ Nat.card K = (2 ^ lab.n) ^ 3 ∧
      IsSimpleGroup (GGTriD4R lab.n K) ∧ (∃ a b : GGTriD4R lab.n K, a * b ≠ b * a) ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* GGTriD4R lab.n K) := by
  obtain ⟨hperf, lab', hΛ, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, hlabeq⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hlabeq
  obtain ⟨tag, rank, n⟩ := lab'
  simp only at htag
  subst htag
  obtain ⟨hn, -⟩ := hΛ
  dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨K, i1, i2, hK, hs', hna', θ', -⟩ := hraw
  exact ⟨K, i1, i2, hn, hK, hs', hna', ⟨θ'⟩⟩

theorem triD4Schur_holds : TriD4Schur := by
  intro Γ _ _ J lab hlab htag
  obtain ⟨K, _, _, hn, hK, hs, -, ⟨θ⟩⟩ := triD4_datum hlab htag
  exact ggTriD4SchurInput_holds lab.n hn K hK hs ↥J hlab.1 θ

theorem triD4_m3_le {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 3)
    (E : Subgroup (GGTriD4R n K)) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 2 := by
  have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (GGTriD4R n K) := Finite.of_equiv _ e.symm.toEquiv
  have h1 := TableBExcSmallRanks.card_lt_of_isElemAbelian_triD4 hn K hK σ hσ
    (CFSG.Open.IsElemAbelian.map hE e.toMonoidHom)
  rw [Subgroup.card_map_of_injective e.injective] at h1
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  rw [hk] at h1 ⊢
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp h1))

theorem triD4Rank_holds : TriD4Rank := by
  intro Γ _ _ J B lab hlab htag hZ hBN hBe
  obtain ⟨K, _, _, hn, hK, hs, hna, ⟨θ⟩⟩ := triD4_datum hlab htag
  have hperf : commutator ↥J = ⊤ := hlab.1
  have hker : (ggBeta J θ hBN).ker = (B ⊓ Subgroup.centralizer (J : Set Γ)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h1
      exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one J θ hperf (g := ⟨b, hBN b.2⟩) h1⟩
    · rintro ⟨-, hc⟩
      exact ggLAut_eq_one_of_mem_centralizer J θ (g := ⟨b, hBN b.2⟩) hc
  have hcardker : Nat.card (ggBeta J θ hBN).ker = Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Γ)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hrange : IsElemAbelian 3 (ggBeta J θ hBN).range :=
    isElemAbelian_range_of_isElemAbelian hBe _
  have h2 := TableB.card_range_mul_card_ker (ggBeta J θ hBN)
  rw [hcardker] at h2
  refine ⟨?_, fun hin => ?_⟩
  · have h3 := ggTriD4AutRankInput_holds lab.n hn K hK hs _ hrange
    calc Nat.card B = Nat.card (ggBeta J θ hBN).range *
          Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Γ)) := h2.symm
      _ ≤ 3 ^ 3 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Γ)) := Nat.mul_le_mul_right _ h3
  ·
    have hZR : Subgroup.center (GGTriD4R lab.n K) = ⊥ := by
      haveI := hs
      rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (GGTriD4R lab.n K)) with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨a, b, hab⟩ := hna
        have ha : a ∈ Subgroup.center (GGTriD4R lab.n K) := by rw [h1]; trivial
        exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
    have hinj := conj_injective_of_center_eq_bot hZR
    have hSinn : (ggBeta J θ hBN).range ≤ (MulAut.conj : GGTriD4R lab.n K →* MulAut (GGTriD4R lab.n K)).range := by
      rintro _ ⟨b, rfl⟩
      obtain ⟨a, haJ, hact⟩ := hin b b.2
      refine ⟨θ (QuotientGroup.mk (⟨a, haJ⟩ : ↥J)), ?_⟩
      ext r
      obtain ⟨q, rfl⟩ := θ.surjective r
      induction q using QuotientGroup.induction_on with
      | H j =>
        rw [ggBeta_eq, ggLAut_apply, MulAut.conj_apply]
        have h1 : (J.normalizerMonoidHom ⟨b, hBN b.2⟩ j : ↥J) = ⟨a, haJ⟩ * j * ⟨a, haJ⟩⁻¹ :=
          Subtype.ext (by rw [normalizerMonoidHom_coe]; exact hact j j.2)
        rw [h1, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv]
    set E : Subgroup (GGTriD4R lab.n K) :=
      (ggBeta J θ hBN).range.comap (MulAut.conj : GGTriD4R lab.n K →* MulAut (GGTriD4R lab.n K)) with hE
    have hEab : IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.comap hrange hinj
    have hEmap : E.map (MulAut.conj : GGTriD4R lab.n K →* MulAut (GGTriD4R lab.n K)) =
        (ggBeta J θ hBN).range := by
      rw [hE, Subgroup.map_comap_eq]
      exact inf_eq_right.2 hSinn
    have hEcard : Nat.card E = Nat.card (ggBeta J θ hBN).range := by
      rw [← hEmap]
      exact (Subgroup.card_map_of_injective hinj).symm
    have h3 := triD4_m3_le hn K hK E hEab
    rw [hEcard] at h3
    calc Nat.card B = Nat.card (ggBeta J θ hBN).range *
          Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Γ)) := h2.symm
      _ ≤ 3 ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set Γ)) := Nat.mul_le_mul_right _ h3

end Holds

end CFSG.LocalAnalysis.GLTheoremA
