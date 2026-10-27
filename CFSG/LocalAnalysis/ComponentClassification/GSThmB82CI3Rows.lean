module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Cfg
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowExc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowAlt
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowX

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Foote5.OddLieCore.Exc in
theorem cfQPUJ6ThreeExc_holds :
    CFQPUJ6ThreeExc := by
  intro M _ _ p f hc hexc
  obtain ⟨-, hZ2, hp, hp2, hf, -, E, L, t, J, J₀, -, hLE, hLc, -, hLm, -, htt, htZ, hJle, hJc,
    hJm, -⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h9 := QPUJ6.five_le_pow_two_mul hp hp2 hf
  let eJ : ↥J ≃* ↥(J.subgroupOf (centralizer ({t} : Set M))) :=
    (Subgroup.subgroupOfEquivOfLe hJle).symm
  have hJm' : LieModel (↥(J.subgroupOf (centralizer ({t} : Set M))) ⧸
      pPrimeCore 2 ↥(J.subgroupOf (centralizer ({t} : Set M)))) .PSL 2 p (2 * f) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hJm
  rcases hexc with ⟨τ, r, e, hτ, hm⟩ | ⟨τ, r, e, hτ, hm⟩ | ⟨r, e, hm⟩
  ·
    by_cases hr2 : r = 2
    · subst hr2
      exact false_of_even_exceptional hZ2 (Or.inl ⟨τ, e, hτ, hm⟩) htt htZ hJc hJm'
    · exact noPSLTwoOddCentreComponent_of_mem hτ M hZ2 r e hm.1.1 hr2 hm.1
        (Or.inr (Or.inl ⟨rfl, hτ, hm⟩)) t htt htZ _ hJc p (2 * f) hp h9 hJm'
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl
    ·
      let eL : ↥(L.subgroupOf (QPUJ.autFixed E)) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLE
      obtain ⟨-, -, hq⟩ :=
        (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1 hLc
      have hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)) hq
      exact QPUJ6.false_of_twistedG2 lieOrderFormulasInput hZ2 hLq hp hp2 hf hLm hm
    · exact false_of_even_exceptional hZ2 (Or.inr (Or.inl ⟨r, e, Or.inl hm⟩)) htt htZ hJc hJm'
    · exact false_of_even_exceptional hZ2 (Or.inr (Or.inl ⟨r, e, Or.inr hm⟩)) htt htZ hJc hJm'
  · exact false_of_even_exceptional hZ2 (Or.inr (Or.inr ⟨r, e, hm⟩)) htt htZ hJc hJm'

open Equiv Equiv.Perm in
theorem cfQPUJ6ThreeAlt_holds :
    CFQPUJ6ThreeAlt := by
  rintro M _ _ p f hc ⟨n, -, ⟨e⟩⟩
  obtain ⟨-, hZ, hp, hp2, hf, -, E, L, t, J, J₀, -, -, -, -, hLie, -, ht, -, hJt, hJc, -, hJ₀L,
    -, hJ₀⟩ := hc
  exact QPUJ6.false_of_alternating CatLeafProof.lieOrderFormulasInput hZ e hp hp2 hf hLie ht hJt
    hJc hJ₀L hJ₀

open Assembly.LowTwoRank in
theorem cfQPUJ6ThreeCrossChar_holds :
    CFQPUJ6ThreeCrossChar := by
  intro M _ _ p f hc ⟨τ, n, r, f'', hr, hmod⟩
  obtain ⟨hq, hZ2, hp, hp2, hf, -, E, L, t, J, J₀, -, -, -, -, -, -, ht2, htZ, hJC, hJpc, hJLie,
    -⟩ := hc
  have h5 := QPUJ6.five_le_pow_two_mul hp hp2 hf
  by_cases hr2 : r = 2
  · subst hr2
    exact QPUJ6.false_of_even hq hZ2 ht2 htZ hJC hJpc h5 hJLie hmod
  · have : IsSimpleGroup (M ⧸ center M) := hq.2.1
    obtain ⟨hLie, hB, hG⟩ := QPUJ.Odd.family_facts (QPUJ.Odd.exists_mul_ne_quot hq) hr2 hmod
    exact QPUJ6.false_of_odd hq hZ2 ht2 htZ hJC hJpc hp hp2 h5 hJLie hr hr2 hmod.1 hLie hB hG

theorem cfQPUJ6Three_of_classical_spor
    (hC : CFQPUJ6ThreeClassical) (hSp : CFQPUJ6ThreeSpor) : CFQPUJ6Three :=
  cfQPUJ6Three_of_rows cfQPUJ6ThreeExc_holds cfQPUJ6ThreeAlt_holds hC cfQPUJ6ThreeCrossChar_holds
    hSp

end CFSG.ComponentClassification.GSThmB
