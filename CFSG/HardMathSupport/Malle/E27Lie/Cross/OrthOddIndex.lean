module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.OrthOddModel
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearIndex
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding TauCeti
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedOmega StatedQuadOdd
  StatedQuadPlus StatedQuadMinus)
open CFSG.LieType.Universal.Spin (quadOdd quadPlus quadMinus coe_quadOdd coe_quadPlus coe_quadMinus
  nondegenerate_polarBilin_quadOdd nondegenerate_polarBilin_quadPlus
  nondegenerate_polarBilin_quadMinus_of_finite)

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem odd_field_facts {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (2 : F) ≠ 0 ∧ ((3 : ℕ) : F) ≠ 0 ∧ 4 ≤ Nat.card F := by
  have hchar : CharP F p := by
    have := Fintype.ofFinite F
    have : Fact p.Prime := ⟨hp⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hF])
  have hne4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  refine ⟨?_, ?_, ?_⟩
  · have : ((2 : ℕ) : F) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff F p]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
    simpa using this
  · rw [Ne, CharP.cast_eq_zero_iff F p]
    intro hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)
  · rw [hF]
    exact hp5.trans' (by omega) |>.trans (Nat.le_self_pow (by omega) p)

theorem false_of_pomega_equiv (h : E27Config X K R T z) (hz : z ∈ K)
    {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
    {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ0 : ⇑Q = Q₀)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (h2 : (2 : F) ≠ 0)
    (h3 : ((3 : ℕ) : F) ≠ 0) (hn : 7 ≤ Fintype.card ι) (hF : 4 ≤ Nat.card F)
    (e : ↥K ≃* StatedProj (StatedOmega Q₀)) : False := by
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
  exact exists_perfect_three_dvd_centralizer_pomega hQ0 hQ h2 h3 hn hF hord

theorem false_of_pomegaOdd_model (h : E27Config X K R T z) (hz : z ∈ K) {r p f : ℕ}
    (hcl : StatedClassicalModel K .POmegaOdd r p f) (hp3 : p ≠ 3) : False := by
  obtain ⟨⟨hp, hf, hr, hp2⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  obtain ⟨h2, h3, h4⟩ := odd_field_facts hp hf hFcard hp2 hp3
  refine false_of_pomega_equiv h hz (Q := quadOdd r F) (coe_quadOdd r F)
    (nondegenerate_polarBilin_quadOdd r F h2) h2 h3 ?_ h4 e
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  omega

theorem false_of_pomegaPlus_model (h : E27Config X K R T z) (hz : z ∈ K) {r p f : ℕ}
    (hcl : StatedClassicalModel K .POmegaPlus r p f) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : False := by
  obtain ⟨⟨hp, hf, hr⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  obtain ⟨h2, h3, h4⟩ := odd_field_facts hp hf hFcard hp2 hp3
  refine false_of_pomega_equiv h hz (Q := quadPlus r F) (coe_quadPlus r F)
    (nondegenerate_polarBilin_quadPlus r F) h2 h3 ?_ h4 e
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem false_of_pomegaMinus_model (h : E27Config X K R T z) (hz : z ∈ K) {r p f : ℕ}
    (hcl : StatedClassicalModel K .POmegaMinus r p f) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : False := by
  obtain ⟨⟨hp, hf, hr⟩, F, hF, hFin, hFcard, b, c, hbc, ⟨e⟩⟩ := hcl
  obtain ⟨h2, h3, h4⟩ := odd_field_facts hp hf hFcard hp2 hp3
  refine false_of_pomega_equiv h hz (Q := quadMinus r F b c) (coe_quadMinus r F b c)
    (nondegenerate_polarBilin_quadMinus_of_finite r F hbc) h2 h3 ?_ h4 e
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem false_of_typeB_odd (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.B r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩)) (hp2 : q.p ≠ 2)
    (hp3 : q.p ≠ 3) (hr : 3 ≤ r) : False := by
  obtain ⟨e⟩ := e
  exact false_of_pomegaOdd_model h hz
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr e) hp3

theorem false_of_typeD_odd (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.D r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩)) (hp2 : q.p ≠ 2)
    (hp3 : q.p ≠ 3) : False := by
  obtain ⟨e⟩ := e
  exact false_of_pomegaPlus_model h hz
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e) hp2 hp3

theorem false_of_typeTwistedD_odd (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ}
    {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩)) (hp2 : q.p ≠ 2)
    (hp3 : q.p ≠ 3) : False := by
  obtain ⟨e⟩ := e
  exact false_of_pomegaMinus_model h hz
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hp2 hp3

end CFSG.HardMathSupport.Malle.E27Lie
