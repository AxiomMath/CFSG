module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecA
public import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

variable {n : ℕ} {A₀ : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
  {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} {cap : ℕ} {runs : List Run}
  {good : List (Array Table)}

theorem genOf_le_of_inCOK (hD : GroupData n A₀ pg gg sift) {T : Table} {t : Equiv.Perm (Fin n)}
    (hT : Rep n T t) {gs : List Table} (hgs : ∀ g ∈ gs, inCOK n sift T g = true) :
    genOf n gs ≤ A₀ ⊓ centralizer ({t} : Set _) := by
  rw [genOf, closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact (inCOK_spec hD hT (hgs g (by simpa using hg))).2.1

theorem permOK_of_inCOK {T g : Table} (h : inCOK n sift T g = true) : permOK n g = true := by
  rw [inCOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1.1

theorem invOK_of_inCOK {T g : Table} (h : inCOK n sift T g = true) :
    invOK n g (invT n g) = true := by
  rw [inCOK, Bool.and_eq_true] at h
  exact h.2

end CFSG.ComponentClassification.HarrisLit.P1
