module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Adapt
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Lattice
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Reg

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem rootChar_eq_one_of_commute_pinnedX {L : Type} [Field L] (c : Fin Tag.E6.rank → Lˣ)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β)
    (h : Commute (rootDiagUnit Tag.E6 c) (pinnedX Tag.E6 L β 1)) : rootChar c β = 1 := by
  have h1 := rootDiagUnit_conj_pinnedX c hβ (1 : L)
  rw [h.eq, mul_inv_cancel_right] at h1
  have h2 := pinnedX_injective Tag.E6 L β h1
  apply Units.ext
  simpa using h2.symm

theorem core_inner {L : Type} [Field L] [IsAlgClosed L]
    (a b : Fin Tag.E6.rank → Lˣ) (ha : ∀ i, a i ^ 3 = 1) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizer a) (hsh : rootChar a (e6Shift w) ≠ 1)
    {z : ModGL Tag.E6 L} (hz : z ∈ adjointGroup Tag.E6 L)
    (hker : ∀ β, IsRoot Tag.E6 β → rootChar a β = 1 → ∀ c : L, Commute z (pinnedX Tag.E6 L β c))
    (hy : Commute z (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w)) :
    z ^ 3 = 1 := by
  obtain ⟨b₃, hKr, hw₃, hsh₃⟩ := exists_triData a ha hw hsh
  have hzT : z ∈ torusGroup Tag.E6 L :=
    mem_torusGroup_of_commute_kernelRoots b₃ hw₃ hsh₃ hz fun β hβ c =>
      hker β ((hKr β).2 hβ).1 ((hKr β).2 hβ).2 c
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hzT
  have hcK : ∀ β ∈ kernelRoots (triChar b₃), rootChar c β = 1 := fun β hβ =>
    rootChar_eq_one_of_commute_pinnedX c ((hKr β).2 hβ).1
      (hker β ((hKr β).2 hβ).1 ((hKr β).2 hβ).2 1)
  have hbc : Commute (rootDiagUnit Tag.E6 c) (rootDiagUnit Tag.E6 b) := by
    show rootDiagUnit Tag.E6 c * rootDiagUnit Tag.E6 b =
      rootDiagUnit Tag.E6 b * rootDiagUnit Tag.E6 c
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hn : Commute (rootDiagUnit Tag.E6 c) (canonicalRep (coxeterSystem Tag.E6) L w) := by
    have e : canonicalRep (coxeterSystem Tag.E6) L w =
        (rootDiagUnit Tag.E6 b)⁻¹ *
          (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) := by
      group
    rw [e]
    exact hbc.inv_right.mul_right hy
  have hwc : w ∈ rootCharStabilizer c := by
    refine (conj_canonicalRep_eq_iff c w).1 ?_
    rw [mul_inv_eq_iff_eq_mul]
    exact hn.eq
  have hcube : ∀ i, c i ^ 3 = 1 := fun i => by
    have h := lattice_cube (rootCharHom3 c) b₃ hw₃ hsh₃ (fun β hβ => hcK β hβ)
      (fun v => hwc v) (Pi.single i 1)
    have e : rootCharHom3 c (Multiplicative.ofAdd (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = c i := by
      change rootChar c (Pi.single i 1) = c i
      simpa using rootChar_nsmul_single c i 1
    rwa [e] at h
  rw [rootDiagUnit_pow]
  have : c ^ 3 = 1 := funext fun i => by simpa using hcube i
  rw [this, rootDiagUnit_one]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis
