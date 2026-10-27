module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Certificate13614

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

section Cent


variable {L : Type} [Field L]

theorem mem_torusGroup_of_mem_familyCentralizer_std' {τ : Tag} {ω : Lˣ}
    (hstd : familyKernel (famV (τ := τ) ω (Native.stdBasis τ.rank)) = ∅ ∧
      ∀ w ∈ familyStabilizer (famV (τ := τ) ω (Native.stdBasis τ.rank)), w = 1)
    {g : ModGL τ L} (hg : g ∈ familyCentralizer τ L (famV (τ := τ) ω (Native.stdBasis τ.rank))) :
    g ∈ torusGroup τ L := by
  obtain ⟨w, hw, m, hm, rfl⟩ := familyCentralizer_le_mul τ L _ hg
  rw [hstd.2 w hw, canonicalRep_one, mul_one]
  have hm' : m ∈ torusGroup τ L ⊔ rootSpan τ L (familyKernel (famV (τ := τ) ω
      (Native.stdBasis τ.rank))) := hm
  rw [hstd.1] at hm'
  have hbot : rootSpan τ L (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
  rwa [hbot, sup_bot_eq] at hm'

theorem mem_familyCentralizer_std' {τ : Tag} {ω : Lˣ} {g : ModGL τ L}
    (hgC : g ∈ adjointGroup τ L) (h : ∀ x : Fin τ.rank → ZMod 3, Commute (dV ω x) g) :
    g ∈ familyCentralizer τ L (famV (τ := τ) ω (Native.stdBasis τ.rank)) := by
  rw [mem_familyCentralizer]
  refine ⟨hgC, fun j => ?_⟩
  change dV ω (listVec τ.rank ((Native.stdBasis τ.rank).get j)) * g *
    (dV ω (listVec τ.rank ((Native.stdBasis τ.rank).get j)))⁻¹ = g
  rw [(h _).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem mem_torusGroup_of_commute_dV {ω : Lˣ}
    (hω : orderOf ω = 3) {g : ModGL Tag.E6 L}
    (hg : g ∈ adjointGroup Tag.E6 L) (h : ∀ x : Fin Tag.E6.rank → ZMod 3, Commute (dV ω x) g) :
    g ∈ torusGroup Tag.E6 L := by
  have hcert := Certificates.certificate13614
  unfold Native.e6FourCoreCheck at hcert
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  obtain ⟨-, hfull⟩ := hcert
  have hstd : familyKernel (famV (τ := .E6) ω (Native.stdBasis Tag.E6.rank)) = ∅ ∧
      ∀ w ∈ familyStabilizer (famV (τ := .E6) ω (Native.stdBasis Tag.E6.rank)), w = 1 :=
    famData0_of_famOK0 hω length_of_mem_stdBasis lt_of_mem_stdBasis hfull
  exact mem_torusGroup_of_mem_familyCentralizer_std' hstd (mem_familyCentralizer_std' hg h)

end Cent

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
