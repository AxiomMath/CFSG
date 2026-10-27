module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Clos
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import Certificates.Data.GH23Data

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open CFSG.OddStandard.SmallF3.HarrisU33.GH23Data
open CFSG.ComponentClassification.PresentationLocal

private lemma gh23Code_carmichaelPerm_mem (k : CarmichaelIndex 8) :
    gh23Code (carmichaelPerm k) ∈ topGens := by
  have hk : (k.1 : ℕ) = 2 ∨ (k.1 : ℕ) = 3 ∨ (k.1 : ℕ) = 4 ∨
      (k.1 : ℕ) = 5 ∨ (k.1 : ℕ) = 6 ∨ (k.1 : ℕ) = 7 := by
    have h2 : 2 ≤ (k.1 : ℕ) := k.2
    have h8 : (k.1 : ℕ) < 8 := k.1.isLt
    omega
  rcases hk with h | h | h | h | h | h
  · rw [show k = (⟨⟨2, by norm_num⟩, by norm_num⟩ : CarmichaelIndex 8) from by
        apply Subtype.ext; apply Fin.ext; exact h]
    decide +kernel
  · rw [show k = (⟨⟨3, by norm_num⟩, by norm_num⟩ : CarmichaelIndex 8) from by
        apply Subtype.ext; apply Fin.ext; exact h]
    decide +kernel
  · rw [show k = (⟨⟨4, by norm_num⟩, by norm_num⟩ : CarmichaelIndex 8) from by
        apply Subtype.ext; apply Fin.ext; exact h]
    decide +kernel
  · rw [show k = (⟨⟨5, by norm_num⟩, by norm_num⟩ : CarmichaelIndex 8) from by
        apply Subtype.ext; apply Fin.ext; exact h]
    decide +kernel
  · rw [show k = (⟨⟨6, by norm_num⟩, by norm_num⟩ : CarmichaelIndex 8) from by
        apply Subtype.ext; apply Fin.ext; exact h]
    decide +kernel
  · rw [show k = (⟨⟨7, by norm_num⟩, by norm_num⟩ : CarmichaelIndex 8) from by
        apply Subtype.ext; apply Fin.ext; exact h]
    decide +kernel

private lemma gh23_mem_range_of_code_mem {σ : Equiv.Perm (Fin 8)}
    (hσ : gh23Code σ ∈ topGens) :
    σ ∈ Set.range (fun k : CarmichaelIndex 8 => carmichaelPerm k) := by
  simp only [topGens, List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with h | h | h | h | h | h
  · exact ⟨⟨2, by norm_num⟩, by
      apply gh23_code_injective
      rw [h]
      decide +kernel⟩
  · exact ⟨⟨3, by norm_num⟩, by
      apply gh23_code_injective
      rw [h]
      decide +kernel⟩
  · exact ⟨⟨4, by norm_num⟩, by
      apply gh23_code_injective
      rw [h]
      decide +kernel⟩
  · exact ⟨⟨5, by norm_num⟩, by
      apply gh23_code_injective
      rw [h]
      decide +kernel⟩
  · exact ⟨⟨6, by norm_num⟩, by
      apply gh23_code_injective
      rw [h]
      decide +kernel⟩
  · exact ⟨⟨7, by norm_num⟩, by
      apply gh23_code_injective
      rw [h]
      decide +kernel⟩

theorem gh23_sub_topGens : gh23Sub topGens = alternatingGroup (Fin 8) := by
  have hset : {σ : Equiv.Perm (Fin 8) | gh23Code σ ∈ topGens} =
      Set.range (fun k : CarmichaelIndex 8 => carmichaelPerm k) := by
    ext σ
    exact ⟨fun hσ => gh23_mem_range_of_code_mem hσ, fun hσ => by
      obtain ⟨k, rfl⟩ := hσ
      exact gh23Code_carmichaelPerm_mem k⟩
  unfold gh23Sub
  rw [hset]
  have hmap : (Subgroup.closure (Set.range (carmichaelCycle (n := 8)))).map
      (alternatingGroup (Fin 8)).subtype =
      Subgroup.closure (Set.range (fun k : CarmichaelIndex 8 => carmichaelPerm k)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have htop : Subgroup.map (alternatingGroup (Fin 8)).subtype
      (⊤ : Subgroup (alternatingGroup (Fin 8))) = alternatingGroup (Fin 8) := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h := congrArg (Subgroup.map (alternatingGroup (Fin 8)).subtype)
    (closure_range_carmichaelCycle (n := 8) (by norm_num : 3 ≤ 8))
  rw [hmap, htop] at h
  exact h

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
