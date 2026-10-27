module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3Actor
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open scoped Matrix

section Four


theorem perfectCentralizerPlanes_adjointGroup_E6_four (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ Nat.card K ^ 2 + 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E6 K) := by
  classical
  have hp3 : 3 < p := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, f, hℓ, hcharK, hf, hK⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hcharK
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by exact_mod_cast hpd
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  set n : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L e6F4U with hn
  have hcm : n ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup L e6F4U
  have hπ : weylQuotientHom Tag.E6 L ⟨n, hcm⟩ = e6F4U :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e6F4U)
  have hnW : ∀ u, weylQuotientHom Tag.E6 L ⟨n, hcm⟩ • u = (weylMatrix e6F4U) *ᵥ u := fun u => by
    rw [hπ, weylMatrix_mulVec]
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_four_frame K hf hK hp hp3 hpq L n hcm hnW
  intro A hA hAcard
  have hAexp : ∀ q ∈ A, q ^ p = 1 := hA.2
  obtain ⟨c, hc⟩ := hconj A (IsPGroup.of_card hAcard)
  obtain ⟨q, hqA, hq1, b, hb, hbi⟩ :=
    e6_four_exists_nonregular_at K hp L n g0 A hAcard hAexp c hc ⟨0, by decide⟩
  have hqp : orderOf q = p := orderOf_eq_prime (hAexp q hqA) hq1
  obtain ⟨hquasi, hpR, -⟩ := e6_four_actor K hf hK hp hp3 hordq hΦ L n hcm hnW g0 hg0C hg0
    hperf hT hqp c (hc q hqA) hb ⟨_, hbi⟩
  refine ⟨q, hqA, hq1, ⁅Subgroup.centralizer ({q} : Set (adjointGroup Tag.E6 K)),
    Subgroup.centralizer ({q} : Set (adjointGroup Tag.E6 K))⁆, ?_, ?_, ?_⟩
  · exact Subgroup.commutator_le_self _
  · haveI : Group.IsPerfect ↥⁅Subgroup.centralizer ({q} : Set (adjointGroup Tag.E6 K)),
      Subgroup.centralizer ({q} : Set (adjointGroup Tag.E6 K))⁆ := hquasi.1
    exact Subgroup.commutator_eq_self
  · exact (Nat.Prime.dvd_iff_not_coprime hp).2 hpR

end Four

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
