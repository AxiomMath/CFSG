module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.Generic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TenFrame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelveAux.TenFamily
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


section Rigid

theorem e8Ten_rigidAt (K : Type) [Field K] [Finite K] {ℓ f : ℕ}
    [Fact ℓ.Prime] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 10)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E8TenFrame K L ℓ f p) {b : Fin Tag.E8.rank → Lˣ}
    (hb : rootDiagUnit Tag.E8 b ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hbp : ∀ i, b i ^ p = 1) (hb1 : b ≠ 1) (hne : (rootCharKernel b).Nonempty) :
    E8RigidAt K F.n (iterateFrobenius L ℓ f) p b := by
  classical
  obtain ⟨hp7', -, hΦ10, hdvd10⟩ := e8Ten_arith hp hp7 he
  have hp5 : 5 < p := by omega
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  have hbT : b ∈ fixedCharTuples (e8FiveM (-1)) Fr := by
    have h := hb
    rw [F.hT] at h
    obtain ⟨b', hb', hb'b⟩ := h
    have hbb : b' = b := rootDiagUnit_injective hb'b
    exact hbb ▸ hb'
  rcases e8Five_kernel_of_fixed (-1) (Or.inr rfl) Fr hFr hp hp5 (e8Five_hΦ_neg _ hΦ10) hbT hbp
      hb1 with hA | ⟨v, hSeq, -, hunit⟩
  · exfalso
    rw [hA] at hne
    exact Set.not_nonempty_empty hne
  · obtain ⟨P, hP, hP1, ⟨h₀, hh₀⟩, hpdvd⟩ := e8Ten_family hℓ hf (k := K) hK Fr hFr' F.n F.hnm
      F.hnW v (hunit rfl) (e8Ten_dvd_pow_five_add_one hdvd10)
    refine ⟨P (), ?_, ?_, ⟨e8Index 0, h₀, hh₀⟩, fun h => (hp.coprime_iff_not_dvd.1 h) hpdvd⟩
    · rw [hSeq]
      exact hP
    · rw [hSeq]
      exact hP1

end Rigid

section Main


theorem innerPlaneBalance_adjointE8_ten (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 10) :
    InnerPlaneBalance p (adjointGroup Tag.E8 K) := by
  classical
  obtain ⟨hp7', -, -, -⟩ := e8Ten_arith hp hp7 he
  obtain ⟨ℓ, f, hℓ, hcharK, hf, hK⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hcharK
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨F⟩ := exists_e8TenFrame K hf hK hp hp7 he L
  have hordW : ¬ p ∣ Nat.card (WeylGroup Tag.E8) :=
    not_dvd_card_weylGroup_E hp hp7' (Or.inr (Or.inr rfl))
  refine innerPlaneBalance_adjointE8_of_rigid hf hK hp hordW F.n F.g0 F.hg0C F.hg0 F.hperf
    F.hconj (fun j => (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) (fun j => IsRoot.basis j) ?_
    fun b hb hbp hb1 ⟨_, hj⟩ => e8Ten_rigidAt K hf hK hp hp7 he F hb hbp hb1 ⟨_, hj⟩
  have hrange : Set.range (fun j : Fin Tag.E8.rank => (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) =
      Set.range (Pi.basisFun ℤ (Fin Tag.E8.rank)) := by
    ext x
    simp [Pi.basisFun_apply]
  rw [hrange]
  exact (Pi.basisFun ℤ (Fin Tag.E8.rank)).span_eq

end Main

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
