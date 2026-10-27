module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.SymplecticPSp
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearIndex

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding TauCeti
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSp)

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem false_of_psp_model (h : E27Config X K R T z) (hz : z ∈ K) {r p f : ℕ}
    (hcl : StatedClassicalModel K .PSp r p f) (hp3 : p ≠ 3) (hq4 : 4 ≤ p ^ f) (hr : 2 ≤ r) :
    False := by
  obtain ⟨⟨hp, hf, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have hz3 : (⟨z, hz⟩ : K) ^ 3 = 1 := Subtype.ext (h.elem.2 z h.z_mem)
  have hz1 : (⟨z, hz⟩ : K) ≠ 1 := by
    intro h1
    apply h.z_not_mem
    have : z = 1 := congrArg Subtype.val h1
    rw [this]
    exact one_mem _
  have hz3' : (e ⟨z, hz⟩) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hz1' : e ⟨z, hz⟩ ≠ 1 := fun h1 => hz1 (e.injective (h1.trans (map_one e).symm))
  have hord : orderOf (e ⟨z, hz⟩) = 3 := orderOf_eq_prime hz3' hz1'
  refine false_of_perfect_in_K h hz (exists_perfect_of_equiv e ⟨z, hz⟩ ?_)
  exact exists_perfect_three_dvd_centralizer_psp hp hf hFcard hp3 hq4 hr hord

theorem false_of_typeC (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.C r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩)) (hp3 : q.p ≠ 3)
    (hq4 : 4 ≤ q.p ^ q.exponent) (hr : 2 ≤ r) : False := by
  obtain ⟨e⟩ := e
  exact false_of_psp_model h hz (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)
    hp3 hq4 hr

theorem false_of_typeB_even (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.B r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩)) (hp2 : q.p = 2)
    (hq4 : 4 ≤ q.p ^ q.exponent) (hr : 3 ≤ r) : False := by
  obtain ⟨e⟩ := e
  exact false_of_psp_model h hz
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp2 hr e)
    (by omega) hq4 (by omega)

theorem false_of_typeB2 (h : E27Config X K R T z) (hz : z ∈ K) {q : PrimePower}
    (hv : (LieTypeIndex.B 2 q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩)) (hp3 : q.p ≠ 3) : False := by
  obtain ⟨e⟩ := e
  have h4 : 4 ≤ q.p ^ q.exponent := by
    have := (TypeB2LieIndex.of q hv).four_le_fieldOrder
    simpa [ValidLieTypeIndex.fieldOrder] using this
  exact false_of_psp_model h hz
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hp3 h4 le_rfl

end CFSG.HardMathSupport.Malle.E27Lie
