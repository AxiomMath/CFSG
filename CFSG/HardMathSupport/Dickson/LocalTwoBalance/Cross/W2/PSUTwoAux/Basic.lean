module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Balance

theorem commutator_mem_core {Mg : Type*} [Group Mg] {C : Subgroup Mg} {g k : Mg}
    (hg : g ∈ GLAPPrimeCoreOf 3 C) (hk : k ∈ C) : g * k * g⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 C := by
  have h2 : k * g⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 C :=
    gLAPPrimeCoreOf_conj_mem' k hk g⁻¹ ((GLAPPrimeCoreOf 3 C).inv_mem hg)
  have := (GLAPPrimeCoreOf 3 C).mul_mem hg h2
  simpa only [mul_assoc] using this

theorem coprime_orderOf_commutator_of_mem_localDeltaIn {Mg : Type*} [Group Mg] [Finite Mg]
    {H D : Subgroup Mg} {g : Mg} (hg : g ∈ localDeltaIn 3 H D) {d : Mg} (hd : d ∈ D) (hd1 : d ≠ 1)
    {k : Mg} (hkH : k ∈ H) (hkd : k * d = d * k) :
    Nat.Coprime 3 (orderOf (g * k * g⁻¹ * k⁻¹)) := by
  have h1 := le_core_of_mem_localDeltaIn hg hd hd1
  have hk : k ∈ H ⊓ Subgroup.centralizer ({d} : Set Mg) :=
    ⟨hkH, Subgroup.mem_centralizer_singleton_iff.2 hkd⟩
  exact (coprime_card_gLAPPrimeCoreOf' Nat.prime_three _).coprime_dvd_right
    (Subgroup.orderOf_dvd_natCard _ (commutator_mem_core h1 hk))

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
