module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenUniII
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAbs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldPlaneMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftU38
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.AGLEmbedding TauCeti
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
  CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

theorem exists_mulEquiv_unitarySU_cover
    {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hZ3 : Nat.card (Subgroup.center K) = 3) {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (h3 : 3 ∣ q.card + 1)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩).Group) :
    ∃ (p f : ℕ) (F : Type) (_ : Field F), UnitaryFieldData p f F ∧ 3 ∣ p ^ f + 1 ∧ 2 < p ^ f ∧
      Nonempty (unitarySU p f F 3 ≃* K) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hq3 : 3 ≤ q.card := hrange.2 rfl
  rw [TauCeti.PrimePower.card_def] at hq3 h3
  have hm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 3 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨-, F, _, _, hFcard, ⟨e'⟩⟩ := hm
  have hU : UnitaryFieldData q.p q.exponent F :=
    ⟨q.prime_p, q.exponent_pos, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hZK : Subgroup.center K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨ψ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary.exists_mulEquiv_unitarySU_three
    hU (by omega) hK.1 (e'.trans (unitaryPSUEquiv hU (by norm_num)).symm) hZK
  exact ⟨q.p, q.exponent, F, inferInstance, hU, h3, by omega, ⟨ψ⟩⟩

theorem subfieldDiagGenAll_of_certificates
    {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    (h3 : 3 ∣ p ^ f + 1) (hf3 : 3 ∣ f) : SubfieldDiagGenAll h :=
  subfieldDiagGenAll_of_cases h h3 hf3
    (fun h hq₀ K₀ hK₀ => subfieldDiagGen_of_four_le h rfl hq₀ K₀ hK₀)
    (fun h K₀ hK₀ => subfieldDiagGen_eight h K₀ hK₀)

theorem kGenTwoModAbFix_uniCover
    {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hZ3 : Nat.card (Subgroup.center K) = 3) {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (h3 : 3 ∣ q.card + 1)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩).Group) :
    KGenTwoModAbFix 3 K := by
  obtain ⟨p, f, F, _, h, h3', hq, ⟨ψ⟩⟩ := exists_mulEquiv_unitarySU_cover hK hZ3 hv h3 e
  exact kGenTwoModAbFix_of_equiv ψ fun E hE hcard hfix =>
    closure_fixSet_eq_top_unitary h h3' hq (subfieldDiagGenAll_of_certificates h h3') E hE hcard
      hfix

end CFSG.AGLEmbedding.KFactProofs.CoverThree
