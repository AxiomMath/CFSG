module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitRowSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubtypeBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CayleySpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

@[expose] noncomputable def wordP (w : List ℕ) : ↥P1408 := ⟨elemW w, elemW_mem w⟩

@[expose] noncomputable def OrbRow.rowP (wy : List ℕ) (r : OrbRow) : ↥P1408 :=
  wordP r.conj * wordP wy * (wordP r.conj)⁻¹

theorem coe_wordP (w : List ℕ) : (wordP w : Equiv.Perm (Fin 1408)) = elemW w := rfl

theorem coe_rowP (wy : List ℕ) (r : OrbRow) :
    (r.rowP wy : Equiv.Perm (Fin 1408)) = r.repElem wy := rfl

theorem isConj_wordP_rowP (wy : List ℕ) (r : OrbRow) : IsConj (wordP wy) (r.rowP wy) :=
  isConj_iff.2 ⟨wordP r.conj, rfl⟩

theorem isConj_of_conjEqOK (hg : gensOK = true) {w : List ℕ} {tx ty : Table} {x y : ↥P1408}
    (hx : Rep 1408 tx (x : Equiv.Perm (Fin 1408))) (hy : Rep 1408 ty (y : Equiv.Perm (Fin 1408)))
    (h : conjEqOK w tx ty = true) : IsConj x y :=
  isConj_iff.2 ⟨wordP w, Subtype.ext (conjEqOK_spec hg hx hy h)⟩

theorem ncard_isConj_subtype {M : Type} [Group M] (P : Subgroup M) (t : ↥P) :
    {c : ↥P | IsConj t c}.ncard = (CFSG.Sporadic.SmallOddCore.conjClass P (t : M)).ncard := by
  have himg : Subtype.val '' {c : ↥P | IsConj t c} =
      CFSG.Sporadic.SmallOddCore.conjClass P (t : M) := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (isConj_iff_mem_conjClass P t c).1 hc
    · intro hx
      have hxP : x ∈ P := by
        obtain ⟨g, hg, rfl⟩ := hx
        exact P.mul_mem (P.mul_mem hg t.2) (P.inv_mem hg)
      exact ⟨⟨x, hxP⟩, (isConj_iff_mem_conjClass P t ⟨x, hxP⟩).2 hx, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
