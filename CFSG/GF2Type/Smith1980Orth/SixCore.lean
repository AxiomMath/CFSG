module

public import CFSG.GF2Type.Smith1980Orth.SixAssembly
public import CFSG.GF2Type.Smith1980Orth.S3Count
public import CFSG.GF2Type.Smith1980Orth.FourOne
public import CFSG.GF2Type.Smith1980Orth.TwoRankSmall
public import CFSG.GF2Type.Smith1980Orth.Alt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

@[expose] def ODelta {G : Type} [Group G] (S : Setting G) : Prop :=
  ∀ k : G, k * S.z * k⁻¹ ∈ S.M → k * S.z * k⁻¹ ∉ S.QG → S.QG ⊓ S.Qa k ≠ ⊥

theorem twoRankSixBound : TwoRankSixBound :=
  fun _ hq _ hE h2 => card_le_sixteen_of_le_isometries hq hE h2

structure SixCore : Prop where
  types : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → ∀ D : S2Data S, D.OTypes
  e34a : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → OE34a S
  delta : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → ODelta S
  e421 : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), OrthData S →
    6 ≤ S.width → OE421Three S


theorem sixFusion_of_core (I : TimInputs) (C : SixCore) : SixFusion where
  types := C.types
  e34a := C.e34a
  e421 := C.e421
  e44 G _ _ _ S O hw := by
    refine oe44_of_fourOne S (fourOne_of S fun g => ?_)
    have O' := O.conjBy g
    have hw' : 6 ≤ (S.conjBy g).width := by rw [Setting.width_conjBy]; exact hw
    obtain ⟨D⟩ := exists_s2Data_of_six_le I O' hw' twoRankSixBound
    have hT := C.types G (S.conjBy g) O' hw' D
    have h34a := C.e34a G (S.conjBy g) O' hw'
    refine ⟨h34a, fun k hxM hxQ => ?_, fun w y hw hwM hwQ hy hyQ hyz => ?_⟩
    · exact D.odd_ncard_conj_mem_Dl hT hxM hxQ
        (h34a _ (isConj_iff.mpr ⟨k, rfl⟩) hxM hxQ) (C.delta G _ O' hw' k hxM hxQ)
    · rcases D.cl_commutator_mem hT hw hwM hwQ hy hyQ hyz with h | ⟨c, hc, hcQ, -, hcl⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, hc, hcQ, hcl⟩

theorem smith1980OrthogonalSix_of_core (I : TimInputs)
    (hHolt : CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) (hId : IdentInput)
    (C : SixCore) : Smith1980OrthogonalSixStatement :=
  smith1980OrthogonalSix_of_inputs I.hAS I.hDW hHolt altInput hId
    (sixInputs_of I twoRankSixBound (sixFusion_of_core I C))

end CFSG.GF2Type.Smith1980Orth
