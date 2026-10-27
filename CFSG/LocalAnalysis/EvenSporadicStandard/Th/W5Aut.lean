module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B : Subgroup G} {z : G}

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z)

include H W

theorem ThCyc.normalizer_W5_conj_mem {r : G}
    (hr : r ∈ normalizer ((W5 A t : Subgroup G) : Set G)) {a : G} (ha : a ∈ A) :
    r * a * r⁻¹ ∈ A := by
  obtain ⟨P, g, -, -, -, -, hgt⟩ := H.exists_fusing_z W
  exact H.W5_normalizer_mem W hgt hr ha

@[expose] noncomputable def actA (r : G) (hr : r ∈ normalizer ((W5 A t : Subgroup G) : Set G)) :
    MulAut ↥A where
  toFun a := ⟨r * a * r⁻¹, H.normalizer_W5_conj_mem W hr a.2⟩
  invFun a := ⟨r⁻¹ * a * r, by
    have := H.normalizer_W5_conj_mem W (inv_mem hr) a.2
    simpa using this⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

end

end CFSG.EvenSporadicStandard.ThStd
