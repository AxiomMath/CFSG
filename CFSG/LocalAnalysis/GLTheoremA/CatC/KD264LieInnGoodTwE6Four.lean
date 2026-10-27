module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3TwActor
import CFSG.RankThree.PartOne.KE.E6TwFourFinal
public import CFSG.RankThree.E6.RootLatticeTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Subgroup CFSG.Open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (weylMatrix e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false


theorem perfectCentralizerPlanes_twistedE6_four {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K]
    [Finite K] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ∣ (ℓ ^ f) ^ 2 + 1) : PerfectCentralizerPlanes p (twistedE6RootGroup K σ) := by
  classical
  have hp3 : 3 < p := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 := by exact_mod_cast hpd
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  set n : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L (e6F4U * e6NegRho) with hn
  have hcm : n ∈ monomialSubgroup Tag.E6 L :=
    canonicalRep_mem_monomialSubgroup L (e6F4U * e6NegRho)
  have hπ : weylQuotientHom Tag.E6 L ⟨n, hcm⟩ = e6F4U * e6NegRho :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hcm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x :=
    fun x => by
      rw [hπ]
      exact e6TwFour_weylImage x
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_tw_four_frame K hf hK σ hσ hp hp3 hpq L n hcm hnW
  intro E hE hEcard
  have hpg : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨c, hc⟩ := hconj E hpg
  obtain ⟨x, hxE, hx1, b, hb, hbi⟩ := e6_tw_four_exists_nonregular_at K σ hp L n g0 E hEcard
    hE.2 c hc ⟨0, by decide⟩
  have hxp : orderOf x = p := orderOf_eq_prime (hE.2 x hxE) hx1
  obtain ⟨hquasi, hpR⟩ := e6_tw_four_derived K hf hK σ hσ hp hp3 hordq hΦ L n hcm hnW g0 hg0C
    hg0 hperf hT hxp c (hc x hxE) hb ⟨_, hbi⟩
  refine ⟨x, hxE, hx1, ⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
    Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆, Subgroup.commutator_le_self _,
    ?_, (Nat.Prime.dvd_iff_not_coprime hp).2 hpR⟩
  haveI : Group.IsPerfect ↥(⁅Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ)),
    Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))⁆ :
      Subgroup (twistedE6RootGroup K σ)) := hquasi.1
  exact Subgroup.commutator_eq_self

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
