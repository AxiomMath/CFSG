module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPLayer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NPGen

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup

section ConjOddQuot

variable {G : Type} [Group G]

@[expose] noncomputable def conjOn (D : Subgroup G) {n : G} (hn : n ∈ normalizer (D : Set G)) :
    MulAut ↥D :=
  Subgroup.normalizerMonoidHom D ⟨n, hn⟩

theorem coe_conjOn (D : Subgroup G) {n : G} (hn : n ∈ normalizer (D : Set G)) (d : ↥D) :
    ((conjOn D hn d : ↥D) : G) = n * d * n⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe D ⟨n, hn⟩ d

@[expose] noncomputable def conjOddQuot (D : Subgroup G) {n : G}
    (hn : n ∈ normalizer (D : Set G)) : OddQuot D ≃* OddQuot D :=
  QuotientGroup.congr (CFSG.oddCore ↥D) (CFSG.oddCore ↥D) (conjOn D hn)
    (map_oddCore_mulEquiv (conjOn D hn))

theorem conjOddQuot_oddProj (D : Subgroup G) {n : G} (hn : n ∈ normalizer (D : Set G))
    (d : ↥D) : conjOddQuot D hn (oddProj D d) = oddProj D (conjOn D hn d) :=
  rfl

theorem conjOddQuot_mem_center (D : Subgroup G) {n : G} (hn : n ∈ normalizer (D : Set G))
    {z : OddQuot D} (hz : z ∈ center (OddQuot D)) :
    conjOddQuot D hn z ∈ center (OddQuot D) := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := (conjOddQuot D hn).surjective g
  rw [← map_mul, ← map_mul, hz g']

end ConjOddQuot

end CFSG.EvenSporadicStandard.M12Std.Rbc
