module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU5Blk
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LieType.ChevTwo.OutDataGen
public import CFSG.Quasithin.Vol2.F134J2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU5
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.Fischer
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem outTwoNilpConcl_su52 : CFSG.LieType.ChevTwo.OutTwoNilpConcl SU52 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (F4 ≃+* F4) := isCyclic_of_prime_card (p := 2) card_ringEquiv_F4
  have hker : fieldFactor.ker = CFSG.ComponentClassification.OuterAutomorphisms.inner SU52 := by
    ext α
    rw [MonoidHom.mem_ker, fieldFactor_eq_one_iff]
    exact ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩
  exact CFSG.LieType.ChevTwo.OutOddAbelian.outTwoNilpConcl
    (CFSG.LieType.ChevTwo.OutOddAbelian.of_ker_eq_inner fieldFactor hker)

theorem oddCoreFact_three_M5 : OddCoreFact 3 M5 := by
  have hZ : Subgroup.center M5 = ⊥ := center_M5_eq_bot
  have hinj := mulAutConj_injective_of_center_eq_bot hZ
  constructor
  · exact outTwoNilpConcl_of_mulEquiv equivM5 outTwoNilpConcl_su52
  · intro x hx
    have hx3 : x ^ 3 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    obtain ⟨t, ht⟩ := exists_conj_of_pow_three x hx3
    subst ht
    rw [innerAut_inf_centralizer_conj hZ t,
      card_gLAPPrimeCoreOf_map_of_injective 3 _ hinj (Subgroup.centralizer ({t} : Set M5))]
    have ht3 : t ^ 3 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      simpa only [hx] using pow_orderOf_eq_one (MulAut.conj t)
    have htrans : ∀ τ : M5 ≃* M5,
        Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({t} : Set M5))) =
          Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({τ t} : Set M5))) := by
      intro τ
      have h2 := card_gLAPPrimeCoreOf_map_of_injective (p := 3) (f := τ.toMonoidHom)
        (by simpa using τ.injective) (Subgroup.centralizer ({t} : Set M5))
      rw [CFSG.centralizer_singleton_map τ t] at h2
      exact h2.symm
    rcases normal_form t ht3 with h1 | ⟨τ, h | h⟩ | ⟨τ, d, hd, hcnt⟩
    · subst h1
      have hy : orderOf (MulAut.conj (1 : M5)) = 3 := hx
      rw [map_one] at hy
      simp at hy
    · rw [htrans τ, h]
      exact odd_card_centralizer_yM5
    · have hCinv : Subgroup.centralizer ({yM5⁻¹} : Set M5) =
          Subgroup.centralizer ({yM5} : Set M5) :=
        CFSG.Quasithin.F134.centralizer_inv_singleton yM5
      rw [htrans τ, h, hCinv]
      exact odd_card_centralizer_yM5
    · rw [htrans τ]
      exact odd_card_centralizer_diag hd hcnt

theorem oddCoreFact_three_of_twistedA4_two
    {S : Type} [Group S] [Finite S]
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid)
    (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 4 q, hv⟩).Group) :
    OddCoreFact 3 S := by
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs
      (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 4 q, hv⟩).Group
      CFSG.LocalAnalysis.GLTheoremA.S9.isU5two := by
    refine ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 4 q, hv⟩, ?_,
      ⟨MulEquiv.refl _⟩⟩
    show q.card = 2
    exact hq
  obtain ⟨eM⟩ := bridge_u5two_stated hcat
  have eT : S ≃* M5 := e.trans eM
  exact (oddCoreFact_congr (p := 3) eT).mpr oddCoreFact_three_M5

end CFSG.LocalAnalysis.GLTheoremA.KD1912
