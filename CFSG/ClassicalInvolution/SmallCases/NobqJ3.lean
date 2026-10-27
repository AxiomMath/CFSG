module

public import CFSG.ClassicalInvolution.SmallCases.NobqArr
public import CFSG.ClassicalInvolution.SmallCases.NobqLists
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Sylow
public import CFSG.ClassicalInvolution.SmallCases.NobqJ3Inputs
public import Certificates.Certificate9303
public import Certificates.Certificate9309
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Check
public meta import CFSG.ClassicalInvolution.SmallCases.NobqArr
public import Certificates.Certificate3169
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.CentralizerOrbit
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Normalizer
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.SetOrbitTools
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import Mathlib

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier.Co3.Native CFSG.ClassicalInvolution.J3Data
  CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.J3Proof

theorem sylow_cqAll :
    all3 20520 sLevels (cqTestA 20520 abArr[0]! kWit) = true := by
  exact Certificates.certificate9303

theorem sChain_le_kChain :
    sChain.originalSubgroup ≤ kChain.originalSubgroup := by
  rw [sChain, ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact sGen_mem_K i hi

theorem sylow_witness :
    ∀ c ∈ sChain.originalSubgroup, c * c = pa →
    ∃ g ∈ kChain.originalSubgroup, (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧
      c * (g * c * g⁻¹) ≠ 1 ∧ c * (g * c * g⁻¹) ≠ pa := by
  have hgens : ∀ g ∈ [kStrong[0]!, kStrong[1]!],
      ∃ G ∈ kChain.originalSubgroup, Rep 20520 g G := by
    intro g hg
    rcases List.mem_pair.1 hg with h | h
    · rw [h]
      exact ⟨_, kGen_mem_K 0 (by norm_num), kGen_rep 0 (by norm_num)⟩
    · rw [h]
      exact ⟨_, kGen_mem_K 1 (by norm_num), kGen_rep 1 (by norm_num)⟩
  have hws := closureA_rep kChain.originalSubgroup _ hgens 4
  refine chain_forall_of_all3 (ofArrays_chainArrays sChain_ok) (by norm_num) sChain_ok
    (by show 3 ≤ 3; exact le_rfl) (fun i hi hi' => by
      have : i < 3 := hi'
      omega) ?_ sylow_cqAll
  intro t g ht hp hgg
  exact cqTestA_sound rep_pa ht hws hp hgg

theorem noUniqueInvNormal_J3P
    (hP : Nat.card P3 = 50232960) : NoUniqueInvNormal P3 := by
  have hS2 : IsPGroup 2 sChain.originalSubgroup :=
    IsPGroup.of_card (n := 7) (by rw [card_sChain]; norm_num)
  have hidx : ¬ 2 ∣ (sChain.originalSubgroup.subgroupOf P3).index := by
    have h := (sChain.originalSubgroup.subgroupOf P3).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sChain_le_P3).toEquiv, card_sChain, hP]
      at h
    omega
  have hidxK : ¬ 2 ∣ (sChain.originalSubgroup.subgroupOf kChain.originalSubgroup).index := by
    have h := (sChain.originalSubgroup.subgroupOf kChain.originalSubgroup).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sChain_le_kChain).toEquiv, card_sChain,
      card_kChain] at h
    omega
  refine noUniqueInvNormal_of_reps P3 [pa] ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact pa_mem
  · intro u hu ho
    obtain ⟨c, hc, hcu⟩ := cover_of_sylow P3 sChain.originalSubgroup hS2 hidx pa cover_S u hu ho
    exact ⟨pa, by simp, c, hc, hcu⟩
  · intro r hr hrP N
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact not_uniqueInvNormal_of_witness_sylow_ambient P3 _ hrP kChain.originalSubgroup
      sChain.originalSubgroup (centralizerIn_P3 hP) hS2 hidxK sylow_witness N

theorem noUniqueInvNormal_J3 :
    NoUniqueInvNormal CFSG.Blueprint.NativeSporadic.J3 :=
  NoUniqueInvNormal.of_mulEquiv nativeEquivP3 (noUniqueInvNormal_J3P card_P3)

end CFSG.ClassicalInvolution.Nobq
