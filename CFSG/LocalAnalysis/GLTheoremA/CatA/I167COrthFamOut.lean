module

public import CFSG.RankThree.PartOne.S11d.OutOrthogonal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.RankThree.PartOne.OutStructure

theorem i167COrth_outPChain {S : Type} [Group S] {p N a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : 4 ≤ N)
    (hS : (StatedClassicalModel S .POmegaPlus N 2 a ∧ (N = 4 → p ≠ 3)) ∨
      StatedClassicalModel S .POmegaMinus N 2 a) : OutPChain p S := by
  rcases hS with ⟨h, hp3⟩ | h
  · by_cases hN5 : 5 ≤ N
    · exact (outPNice_POmegaPlus_ge_five hp hp2 hN5 h).toChain
    · have hN4 : N = 4 := by omega
      have hp3' : 3 < p := by
        have h2 : 2 ≤ p := hp.two_le
        omega
      rw [hN4] at h
      exact outPChain_POmegaPlus_four hp hp3' h
  · exact (outPNice_POmegaMinus hp hp2 hN h).toChain

private theorem i167COrth_outer_cyclic_aux1 {S : Type} [Group S] {p : ℕ} (hp : p.Prime)
    {Bb : Subgroup (MulAut S)} {β β' : MulAut S} (hβ : β ∈ Bb) (hβ' : β' ∈ Bb)
    (hβp : β ^ p = 1) (hβ'p : β' ^ p = 1) (hcomm : Commute β β')
    (hout : ∀ s : S, (MulAut.conj s : MulAut S) ≠ β) {m : ℤ} (hm : β * β' ^ m ∈ Inn S) :
    ∃ (j : ℤ) (s : S), (MulAut.conj s : MulAut S) ∈ Bb ∧ β' = MulAut.conj s * β ^ j := by
  obtain ⟨s₁, hs₁⟩ := MonoidHom.mem_range.mp hm
  have hc : MulAut.conj s₁ ∈ Bb := by
    simpa only [hs₁] using Bb.mul_mem hβ (Bb.zpow_mem hβ' m)
  have hβ'pz : (β' : MulAut S) ^ (p : ℤ) = 1 := by rw [zpow_natCast, hβ'p]
  have hmnd : ¬ (p : ℤ) ∣ m := by
    rintro ⟨t, ht⟩
    refine hout s₁ ?_
    rw [hs₁, ht, zpow_mul, hβ'pz, one_zpow, mul_one]
  have hcop : IsCoprime m (p : ℤ) :=
    ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hmnd).symm
  obtain ⟨a, b, hab⟩ := hcop
  have hma : m * a = 1 + (p : ℤ) * (-b) := by rw [mul_comm m a, ← hab]; ring
  have hβ'eq : β' = (β' ^ m) ^ a := by
    rw [← zpow_mul, hma, zpow_add, zpow_one, zpow_mul, hβ'pz, one_zpow, mul_one]
  have hβ'm_split : β' ^ m = β⁻¹ * MulAut.conj s₁ := by
    rw [hs₁, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcommβc : Commute β (MulAut.conj s₁) := by
    rw [hs₁]
    exact (Commute.refl β).mul_right (hcomm.zpow_right m)
  have hstep : β' = β ^ (-a) * (MulAut.conj s₁) ^ a := by
    calc β' = (β' ^ m) ^ a := hβ'eq
      _ = (β⁻¹ * MulAut.conj s₁) ^ a := by rw [hβ'm_split]
      _ = β ^ (-a) * (MulAut.conj s₁) ^ a := by
          rw [hcommβc.inv_left.mul_zpow, inv_zpow, ← zpow_neg]
  refine ⟨-a, s₁ ^ a, ?_, ?_⟩
  · rw [map_zpow]
    exact Bb.zpow_mem hc a
  · rw [map_zpow]
    calc β' = β ^ (-a) * (MulAut.conj s₁) ^ a := hstep
      _ = (MulAut.conj s₁) ^ a * β ^ (-a) := (hcommβc.zpow_zpow (-a) a).eq

theorem i167COrth_outer_cyclic {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hO : OutPChain p S) {Bb : Subgroup (MulAut S)} (hBb : IsElemAbelian p Bb) {β : MulAut S}
    (hβ : β ∈ Bb) (hout : ∀ s : S, (MulAut.conj s : MulAut S) ≠ β) {β' : MulAut S} (hβ' : β' ∈ Bb) :
    ∃ (j : ℤ) (s : S), (MulAut.conj s : MulAut S) ∈ Bb ∧ β' = MulAut.conj s * β ^ j := by
  have hβp : β ^ p = 1 := hBb.2 β hβ
  have hβ'p : β' ^ p = 1 := hBb.2 β' hβ'
  have hcommββ' : Commute β β' := by
    have hsub : (⟨β, hβ⟩ : Bb) * ⟨β', hβ'⟩ = ⟨β', hβ'⟩ * ⟨β, hβ⟩ :=
      hBb.1.is_comm.comm _ _
    rw [commute_iff_eq]
    simpa using congrArg Subtype.val hsub
  rcases OutPChain.comparable hO hcommββ'.eq
    (by rw [pow_one, hβp]; exact Subgroup.one_mem _)
    (by rw [pow_one, hβ'p]; exact Subgroup.one_mem _) with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact i167COrth_outer_cyclic_aux1 hp hβ hβ' hβp hβ'p hcommββ' hout hm
  · obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hm
    refine ⟨-m, s, ?_, ?_⟩
    · rw [hs]
      exact Bb.mul_mem hβ' (Bb.zpow_mem hβ m)
    · rw [hs, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

end CFSG.LocalAnalysis.GLTheoremA.I167

end
