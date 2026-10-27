module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.R0Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.IotaDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.EichlerDefs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open CFSG.EvenSporadicStandard.HNRecog.HaradaLA

theorem bilC_spec (k l : ℕ) : (bilC k l : ZMod 2) = bil (vecOfCode k) (vecOfCode l) := by
  simp only [bilC, bil, vecOfCode, ZMod.natCast_mod]
  push_cast
  rfl

theorem vecOfCode_one : vecOfCode 1 = Pi.single 0 1 := by
  decide +kernel

theorem mem_etaCodes_iff (u : ℕ) :
    u ∈ etaCodes ↔ u < 64 ∧ bil (vecOfCode u) (Pi.single 0 1) = 0 ∧ lam (vecOfCode u) = 0 := by
  have h : ∀ u : Fin 64, (u.val ∈ etaCodes ↔
      bil (vecOfCode u.val) (Pi.single 0 1) = 0 ∧ lam (vecOfCode u.val) = 0) := by
    decide +kernel
  constructor
  · intro hu
    have hlt : u < 64 := by
      have := (List.mem_filter.1 hu).1
      simpa using this
    exact ⟨hlt, (h ⟨u, hlt⟩).1 hu⟩
  · rintro ⟨hlt, hb⟩
    exact (h ⟨u, hlt⟩).2 hb

theorem eichC_spec {u x : ℕ} (hu : u ∈ etaCodes) (hx : x < 64) :
    vecOfCode (eichC 1 u x) = eichF (Pi.single 0 1) (vecOfCode u) (vecOfCode x) := by
  have h : ∀ u : Fin 64, ∀ x : Fin 64, u.val ∈ etaCodes →
      vecOfCode (eichC 1 u.val x.val) =
        eichF (Pi.single 0 1) (vecOfCode u.val) (vecOfCode x.val) := by
    decide +kernel
  exact h ⟨u, (mem_etaCodes_iff u).1 hu |>.1⟩ ⟨x, hx⟩ hu

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
