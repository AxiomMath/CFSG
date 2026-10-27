
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
public import Certificates.Data.CFSGNative.PSL3Four.Certificate
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Mathlib

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.PSL3Four CFSG.PSL3Four.Native

theorem tabRep_g₁ : TabRep g₁T g₁ := by unfold TabRep; decide

theorem tabRep_g₂ : TabRep g₂T g₂ := by unfold TabRep; decide

theorem tabRep_g₃ : TabRep g₃T g₃ := by unfold TabRep; decide

theorem tabRep_g₄ : TabRep g₄T g₄ := by unfold TabRep; decide

theorem tabRep_g₅ : TabRep g₅T g₅ := by unfold TabRep; decide

theorem tabRep_g₆ : TabRep g₆T g₆ := by unfold TabRep; decide

theorem tabRep_r₁ : TabRep r₁T r₁ := by
  rw [r₁, sq]
  exact ((tabRep_g₁.comp tabRep_g₁).comp tabRep_g₂).comp tabRep_g₁

theorem tabRep_r₂ : TabRep r₂T r₂ := tabRep_g₅

theorem tabRep_r₃ : TabRep r₃T r₃ := tabRep_g₆

theorem tabRep_r₄ : TabRep r₄T r₄ := tabRep_g₅.comp tabRep_g₆

theorem gensS_cover : ∀ a ∈ ({g₁, g₂, g₃} : Set (Equiv.Perm (Fin 42))),
    ∃ j < gensS.size, TabRep gensS[j]! a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨0, by decide, tabRep_g₁⟩
  · exact ⟨1, by decide, tabRep_g₂⟩
  · exact ⟨2, by decide, tabRep_g₃⟩

theorem gensS_tabs : ∀ j < gensS.size,
    ∃ a ∈ ({g₁, g₂, g₃} : Set (Equiv.Perm (Fin 42))), TabRep gensS[j]! a := by
  intro j hj
  have hj' : j < 3 := hj
  interval_cases j
  · exact ⟨g₁, by simp, tabRep_g₁⟩
  · exact ⟨g₂, by simp, tabRep_g₂⟩
  · exact ⟨g₃, by simp, tabRep_g₃⟩

theorem gTabs_cover : ∀ a ∈ ({g₁, g₂, g₃, g₄, g₅, g₆} : Set (Equiv.Perm (Fin 42))),
    ∃ j < gTabs.size, TabRep gTabs[j]! a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, tabRep_g₁⟩
  · exact ⟨1, by decide, tabRep_g₂⟩
  · exact ⟨2, by decide, tabRep_g₃⟩
  · exact ⟨3, by decide, tabRep_g₄⟩
  · exact ⟨4, by decide, tabRep_g₅⟩
  · exact ⟨5, by decide, tabRep_g₆⟩

theorem gTabs_tabs : ∀ j < gTabs.size,
    ∃ a ∈ ({g₁, g₂, g₃, g₄, g₅, g₆} : Set (Equiv.Perm (Fin 42))), TabRep gTabs[j]! a := by
  intro j hj
  have hj' : j < 6 := hj
  interval_cases j
  · exact ⟨g₁, by simp, tabRep_g₁⟩
  · exact ⟨g₂, by simp, tabRep_g₂⟩
  · exact ⟨g₃, by simp, tabRep_g₃⟩
  · exact ⟨g₄, by simp, tabRep_g₄⟩
  · exact ⟨g₅, by simp, tabRep_g₅⟩
  · exact ⟨g₆, by simp, tabRep_g₆⟩

noncomputable abbrev enumS : Enum := enumBFS 42 gensS 20160

noncomputable abbrev enumR : Enum := enumBFS 42 gTabs 241920

noncomputable abbrev gInv : Array Tab := gTabs.map (invTab 42)

noncomputable abbrev orbitR (x : Tab) : Enum := orbitBFS 42 gTabs gInv x 1963

noncomputable abbrev centS (x : Tab) : Array Tab := centTabs 42 enumS.tabs x

noncomputable abbrev derived₁ : Array Tab × Array (ℕ × ℕ × ℕ × ℕ) :=
  derivedData 42 (centS r₄T) ((centS r₄T).map (invTab 42))

noncomputable abbrev derived₂ : Array Tab × Array (ℕ × ℕ × ℕ × ℕ) :=
  derivedData 42 derived₁.1 (derived₁.1.map (invTab 42))

noncomputable abbrev derived₃ : Array Tab × Array (ℕ × ℕ × ℕ × ℕ) :=
  derivedData 42 derived₂.1 (derived₂.1.map (invTab 42))

structure CertFacts : Prop where
  okS : enumOK 42 gensS enumS = true
  sizeS : enumS.tabs.size = 20160
  okR : enumOK 42 gTabs enumR = true
  sizeR : enumR.tabs.size = 241920
  normal : normalOK 42 enumS.tabs gTabs gInv gensS = true
  central : centralOK 42 enumR.tabs gensS = true
  orbit₁ : orbitOK 42 gTabs gInv r₁T (orbitR r₁T) = true
  orbit₂ : orbitOK 42 gTabs gInv r₂T (orbitR r₂T) = true
  orbit₃ : orbitOK 42 gTabs gInv r₃T (orbitR r₃T) = true
  orbit₄ : orbitOK 42 gTabs gInv r₄T (orbitR r₄T) = true
  size₁ : (orbitR r₁T).tabs.size = 315
  size₂ : (orbitR r₂T).tabs.size = 360
  size₃ : (orbitR r₃T).tabs.size = 1008
  size₄ : (orbitR r₄T).tabs.size = 280
  cover : coverOK 42 enumR.tabs
    #[(orbitR r₁T).tabs, (orbitR r₂T).tabs, (orbitR r₃T).tabs, (orbitR r₄T).tabs] = true
  disjoint : (allBelow 4 fun i => allBelow 4 fun j => i == j ||
    notInOK (#[(orbitR r₁T).tabs, (orbitR r₂T).tabs, (orbitR r₃T).tabs,
      (orbitR r₄T).tabs])[i]! rTabs[j]!) = true
  involution : (allBelow 4 fun i =>
    comp 42 rTabs[i]! rTabs[i]! == idTab 42 && !(rTabs[i]! == idTab 42)) = true
  notS₂ : notInOK enumS.tabs r₂T = true
  notS₃ : notInOK enumS.tabs r₃T = true
  notS₄ : notInOK enumS.tabs r₄T = true
  cent₁ : (centS r₁T).size = 64
  cent₂ : (centS r₂T).size = 168
  cent₃ : (centS r₃T).size = 60
  cent₄ : (centS r₄T).size = 72
  class₂ : classOK 42 (centS r₂T) ((centS r₂T).map (invTab 42))
    (classData 42 (centS r₂T) sizes₂) sizes₂ = true
  class₃ : classOK 42 (centS r₃T) ((centS r₃T).map (invTab 42))
    (classData 42 (centS r₃T) sizes₃) sizes₃ = true
  der₁ : derivedOK 42 (centS r₄T) ((centS r₄T).map (invTab 42)) derived₁.1 derived₁.2 = true
  derSize₁ : derived₁.1.size = 18
  der₂ : derivedOK 42 derived₁.1 (derived₁.1.map (invTab 42)) derived₂.1 derived₂.2 = true
  derSize₂ : derived₂.1.size = 9
  der₃ : derivedOK 42 derived₂.1 (derived₂.1.map (invTab 42)) derived₃.1 derived₃.2 = true
  derSize₃ : derived₃.1.size = 1

end CFSG.ComponentClassification.PSL3Four
