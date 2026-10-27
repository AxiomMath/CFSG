
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixPermTools
public import CFSG.Sporadic.HeldB.InnerRestrict
public import CFSG.Sporadic.HeldB.OuterCentRestrict
public import CFSG.Sporadic.HeldB.AutModelCore
public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerData
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.OuterCentCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterCentAux
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowData
public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.Sporadic.HeldB CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier

theorem rep_hfX : Rep 8330 hfXTab hfX := by
  rw [hfXTab, hfAUArrs_eq, hfX]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heLetter h hh).1)
    (fun h hh => (rep_heLetter h hh).2) (by rw [heOuterLetters_length]; exact hfSylow_check.2.2.2.1)

theorem tabRep_hfC1Tabs : ∀ j < hfC1Tabs.size, TabRep hfC1Tabs[j]! (heInnerCP1 j) := by
  intro j hj
  have hj9 : j < 9 := by simpa [hfC1Tabs] using hj
  have e : hfC1Tabs[j]! = heInnerC1 j := by
    rw [hfC1Tabs, getElem!_pos _ j (by simpa using hj9), Array.getElem_ofFn]
  have hs := hfSylow_check.1 j hj9
  rw [e] at hs ⊢
  exact tabRep_of_rep (rep_heInnerC1 hj9) hs

theorem tabRep_hfTTabs : ∀ j < hfTTabs.size, TabRep hfTTabs[j]! (hfTL j) := by
  intro j hj
  have hj5 : j < 5 := hfTTabs_size ▸ hj
  rw [hfTTabs, getElem!_pos _ j (by simpa using hj5), Array.getElem_ofFn]
  simp only [hfTL]
  by_cases h0 : j = 0
  · simp only [h0, ↓reduceIte]
    exact tabRep_of_rep rep_heT1 hfSylow_check.2.1
  · simp only [h0, ↓reduceIte]
    exact tabRep_wordTabS tabRep_hfC1Tabs _ fun i hi => by
      have := hfSylow_check.2.2.2.2.1 (j - 1) (by omega) i hi
      simpa [hfC1Tabs] using this

theorem tabRep_hfYLetterTabs : ∀ j < hfYLetterTabs.size, TabRep hfYLetterTabs[j]! (hfYL j) := by
  intro j hj
  have hj10 : j < 10 := by simpa [hfYLetterTabs] using hj
  rw [hfYLetterTabs, getElem!_pos _ j (by simpa using hj10), Array.getElem_ofFn]
  simp only [hfYL]
  by_cases h9 : j < 9
  · simp only [h9, ↓reduceIte]
    have := tabRep_hfC1Tabs j (by simpa [hfC1Tabs] using h9)
    rwa [hfC1Tabs, getElem!_pos _ j (by simpa using h9), Array.getElem_ofFn] at this
  · simp only [h9, ↓reduceIte]
    exact tabRep_of_rep rep_hfX hfSylow_check.2.2.1

theorem tabRep_hfYTab : TabRep hfYTab hfY :=
  tabRep_wordTabS tabRep_hfYLetterTabs _ fun j hj => by
    have := hfSylow_check.2.2.2.2.2.1 j hj
    simpa [hfYLetterTabs] using this

theorem tabRep_hfT0Tabs : ∀ j < hfT0Tabs.size, TabRep hfT0Tabs[j]! (hfT0L j) := by
  intro j hj
  have hj6 : j < 6 := hfT0Tabs_size ▸ hj
  rw [hfT0Tabs, getElem!_pos _ j (by simpa using hj6), Array.getElem_ofFn]
  simp only [hfT0L]
  by_cases h5 : j < 5
  · simp only [h5, ↓reduceIte]
    exact tabRep_hfTTabs j (hfTTabs_size ▸ h5)
  · simp only [h5, ↓reduceIte]
    exact tabRep_hfYTab

theorem hfTau_mem {i : ℕ} (hi : i < 4) : hfTau i ∈ heInnerGrp1 := by
  refine heInnerGrp1.list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact heInnerCP1_mem_grp1 (hfSylow_check.2.2.2.2.1 i hi j hj)

theorem hfTL_mem {j : ℕ} (hj : j < 5) : hfTL j ∈ heInnerGrp1 := by
  simp only [hfTL]
  split_ifs with h0
  · exact heT1P_mem_grp1
  · exact hfTau_mem (by omega)

theorem hfT_le_grp1 : hfT ≤ heInnerGrp1 := by
  rw [hfT, genGroup, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact hfTL_mem (hfTTabs_size ▸ hj)

theorem hfT_le_heP : hfT ≤ heP :=
  hfT_le_grp1.trans (heInnerGrp1_le.trans inf_le_left)

theorem hfT0_le_heAutGroup : hfT0 ≤ heAutGroup := by
  rw [hfT0, genGroup, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  simp only [hfT0L]
  split_ifs with h5
  · exact heP_le_heAutGroup (hfT_le_heP (subset_closure ⟨j, hfTTabs_size ▸ h5, rfl⟩))
  · exact hfY_mem

theorem hfY_not_mem : hfY ∉ heP := by
  rw [← mem_heP_iff_siftA tabRep_hfYTab.2, hfSylow_check.2.2.2.2.2.2.2.1]
  exact Bool.false_ne_true

theorem enumerates_hfT0 : Enumerates hfT0 hfT0Enum.tabs.toList :=
  enumerates_closure (genGroup_hA tabRep_hfT0Tabs) (genGroup_hgens tabRep_hfT0Tabs)
    hfSylow_check.2.2.2.2.2.2.2.2.1

theorem card_hfT0 : Nat.card hfT0 = 2048 := by
  rw [enumerates_hfT0.card, Array.length_toList, hfSylow_check.2.2.2.2.2.2.2.2.2.1]

theorem hfDelta32_points : PointsList 8330 32 hfDelta32 :=
  ⟨hfDelta32_check.1, hfDelta32_check.2.1, hfDelta32_check.2.2⟩

theorem hfT0_preserves :
    ∀ g ∈ hfT0, ∀ x : Fin 8330, (x : ℕ) ∈ hfDelta32 → (g x : ℕ) ∈ hfDelta32 :=
  genGroup_preserves (fun j hj => (tabRep_hfT0Tabs j hj).2) fun j hj =>
    hfSylow_check.2.2.2.2.2.2.2.2.2.2.1 j (hfT0Tabs_size ▸ hj)

theorem hfT_preserves :
    ∀ g ∈ hfT, ∀ x : Fin 8330, (x : ℕ) ∈ hfDelta32 → (g x : ℕ) ∈ hfDelta32 :=
  fun g hg => hfT0_preserves g (hfT_le_hfT0 hg)

@[expose] def hfPhi : hfT0 →* Equiv.Perm (Fin 32) := hfDelta32_points.restrHom hfT0 hfT0_preserves

@[expose] def hfPhiT : hfT →* Equiv.Perm (Fin 32) := hfDelta32_points.restrHom hfT hfT_preserves

theorem enumerates_hfPhi : Enumerates hfPhi.range hfT0Enum32.tabs.toList :=
  enumerates_range_restrHom hfDelta32_points hfT0_preserves (fun j hj => (tabRep_hfT0Tabs j hj).2)
    hfSylow_check32.2.2.1

theorem enumerates_hfPhiT : Enumerates hfPhiT.range hfTEnum32.tabs.toList :=
  enumerates_range_restrHom hfDelta32_points hfT_preserves (fun j hj => (tabRep_hfTTabs j hj).2)
    hfSylow_check32.1

theorem hfPhi_injective : Function.Injective hfPhi :=
  injective_of_card_range hfPhi (by
    rw [enumerates_hfPhi.card, Array.length_toList, hfSylow_check32.2.2.2.1, card_hfT0])

theorem hfPhiT_injective : Function.Injective hfPhiT := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker, hfPhiT, PointsList.restrHom_eq_one_iff] at hg
  have h1 : hfPhi ⟨g, hfT_le_hfT0 g.2⟩ = hfPhi 1 := by
    rw [map_one, hfPhi, PointsList.restrHom_eq_one_iff]
    exact hg
  have h2 := hfPhi_injective h1
  have h3 : (g : Equiv.Perm (Fin 8330)) = 1 := by
    have := congrArg Subtype.val h2
    simpa only [OneMemClass.coe_one] using this
  rw [Subgroup.mem_bot]
  exact Subtype.ext (by simpa only [OneMemClass.coe_one] using h3)

theorem card_hfT : Nat.card hfT = 1024 := by
  rw [Nat.card_congr (MonoidHom.ofInjective hfPhiT_injective).toEquiv, enumerates_hfPhiT.card,
    Array.length_toList, hfSylow_check32.2.1]

theorem hfT0_inf_heP : hfT0 ⊓ heP = hfT := by
  have hle : hfT ≤ hfT0 ⊓ heP := le_inf hfT_le_hfT0 hfT_le_heP
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_hfT]
  have hdvd : Nat.card ↥(hfT0 ⊓ heP) ∣ 2 ^ 11 := by
    rw [show (2 : ℕ) ^ 11 = 2048 by norm_num, ← card_hfT0]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hge : 1024 ≤ Nat.card ↥(hfT0 ⊓ heP) := card_hfT ▸ Subgroup.card_le_of_le hle
  have hne : Nat.card ↥(hfT0 ⊓ heP) ≠ 2048 := by
    intro h
    have hEq : hfT0 ⊓ heP = hfT0 :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, card_hfT0])
    exact hfY_not_mem (Subgroup.mem_inf.1 (hEq.symm ▸ hfY_mem_hfT0 : hfY ∈ hfT0 ⊓ heP)).2
  rw [hk'] at hge hne ⊢
  have hk10 : 10 ≤ k := by
    by_contra h
    push Not at h
    have : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk11 : k ≠ 11 := fun h => hne (by rw [h]; norm_num)
  have : k = 10 := by omega
  rw [this]
  norm_num

end CFSG.ComponentClassification.GrSLit.HeldFix
