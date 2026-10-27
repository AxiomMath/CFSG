module

public import Certificates.Certificate38603
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6

theorem uaCheck_holds : chkUa = true :=
  Certificates.certificate38603

structure UaFacts : Prop where
  ugens_size : ugens.size = 9
  uco_size : uco.size = 49
  ugens_lt : ∀ j < 9, ugens[j]! < 1953 ∧ inPlane 0 ugens[j]! = true
  uco_parts : ∀ k < 49, 0 < uco[k]! ∧ uco[k]! < 512
  uco_inj : ∀ k < 49, ∀ l < k, uco[l]! ≠ uco[k]!
  commute : ∀ p ∈ planePtsArr[0]!, ∀ q ∈ planePtsArr[0]!, (tvTab[p]!)[q]! = q
  word : ∀ k < 49, ∀ x < 1953, uaWord uco[k]! x = (tvTab[(planePtsArr[0]!)[k]!]!)[x]!
  faithful : ∀ a < 512, a ≠ 0 → ∃ x < 1953, uaWord a x ≠ x
  cent : ∀ q < 1953, (∀ p ∈ planePtsArr[0]!, (tvTab[p]!)[q]! = q) → inPlane 0 q = true
  onlyW : ∀ j < 1395, j ≠ 0 → ∃ p ∈ planePtsArr[0]!, planeImg p j ≠ j

theorem uaFacts : UaFacts := by
  have h := uaCheck_holds
  simp only [chkUa, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    List.mem_range, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, Bool.not_eq_true',
    Array.any_eq_true', Array.all_eq_false', beq_eq_false_iff_ne, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs1, hs2⟩, hug⟩, huc⟩, hcomm⟩, hword⟩, hfaith⟩, hcent⟩, honly⟩ := h
  refine ⟨hs1, hs2, fun j hj => ?_, fun k hk => (huc k hk).1, fun k hk => (huc k hk).2,
    hcomm, hword, fun a ha ha0 => (hfaith a ha).resolve_left ha0, fun q hq H => ?_,
    fun j hj hj0 => ?_⟩
  · have hj' : j < ugens.size := by rw [hs1]; exact hj
    rw [getElem!_pos ugens j hj']
    exact hug _ (Array.getElem_mem hj')
  · rcases hcent q hq with ⟨p, hp, hne⟩ | h
    · exact absurd (H p hp) hne
    · exact h
  · rcases honly j hj with h | h
    · exact absurd h hj0
    · obtain ⟨p, hp, hne⟩ := h
      exact ⟨p, hp, by simpa using hne⟩

end CFSG.GF2Type.SmithTypeE.LMod
