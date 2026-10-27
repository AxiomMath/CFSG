module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIURowsCom
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Even
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Odd

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Foote5.OddLieCore.Exc

namespace QPUJ6

theorem false_of_twistedG2 (hO : LieOrderFormulasInput) {M : Type} [Group M] [Finite M]
    (hZ2 : IsPGroup 2 (center M)) {L : Subgroup M} (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hLm : IsL4U4Mod4 (↥L ⧸ pPrimeCore 2 ↥L) p f) {r e : ℕ}
    (hS : ReeTitsModel (M ⧸ center M) .twistedG2 r e) : False := by
  have hZL := center_eq_bot_of_isQuasisimple_of_isSimpleGroup hLq (isSimpleGroup hLm)
  have hinj : Function.Injective ((QuotientGroup.mk' (center M)).comp L.subtype) := by
    refine (injective_iff_map_eq_one _).mpr fun l hl => ?_
    have hlZ : (l : M) ∈ center M := (QuotientGroup.eq_one_iff (l : M)).1 hl
    obtain ⟨k, hk⟩ := hZ2 ⟨_, hlZ⟩
    refine eq_one_of_mem_center_of_center_quot_eq_bot hZL hlZ (k := k) ?_
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h1
    exact h1
  have hdvd1 : Nat.card ↥L ∣ Nat.card (M ⧸ center M) := Subgroup.card_dvd_of_injective _ hinj
  have hdvd2 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) ∣ Nat.card ↥L :=
    Subgroup.card_quotient_dvd_card _
  have h16 := sixteen_dvd_card hO hp hp2 hf hLm
  obtain rfl : r = 3 := hS.1.2.2.2.1
  exact not_sixteen_dvd_card_of_lieModel_twistedG2 hO hS.1
    (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hS⟩))) (h16.trans (hdvd2.trans hdvd1))

end QPUJ6

theorem cfQPUJ6Exc_holds :
    CFQPUJ6Exc := by
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

end CFSG.ComponentClassification.GSThmB
