module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.UnitaryPSU
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.LinearIndex
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti
open CFSG.HardMathSupport.Curtis.Coordinator
open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical CFSG.RankThree.UnitaryDescent

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem exists_primeFormP_of_twistedA' {S : Type} [Group S] (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) (hn4 : 4 ≤ r + 1) :
    ∃ (E : Type) (_ : Field E) (hU : UnitaryFieldData q.p q.exponent E),
      Nonempty (S ≃* primeFormP hU
        ((1 : GL (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E)) := by
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, E, _, _, hE, ⟨e'⟩⟩ := h
  have hU : UnitaryFieldData q.p q.exponent E := ⟨hℓ, hm, by rw [hE, ← pow_mul, mul_comm]⟩
  have hq' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := r + 1)) hn3 hq'
  exact ⟨E, inferInstance, hU, ⟨(e'.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm⟩⟩

theorem false_of_typeTwistedA (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)) (hp3 : q.p ≠ 3)
    (hr : (4 ≤ q.p ^ q.exponent ∧ 4 ≤ r + 1) ∨ (q.p ^ q.exponent = 2 ∧ 10 ≤ r + 1)) : False := by
  obtain ⟨e⟩ := e
  have hn4 : 4 ≤ r + 1 := by omega
  obtain ⟨E, _, hU, ⟨θ⟩⟩ := exists_primeFormP_of_twistedA' r q hv e hn4
  have := hU.finite
  have hz3 : (θ ⟨z, hz⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨z, hz⟩ : K) ^ 3 = 1 := Subtype.ext (h.elem.2 z h.z_mem)
    rw [this, map_one]
  refine false_of_perfect_in_K h hz (exists_perfect_of_equiv θ ⟨z, hz⟩ ?_)
  exact exists_perfect_three_dvd_centralizer_primeFormP (h := hU) hp3 hr hz3

end CFSG.HardMathSupport.Malle.E27Lie
