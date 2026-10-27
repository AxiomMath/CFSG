module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCyclicAux1
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCyclicAux3
public import CFSG.RankThree.PartOne.KE6.Phi6A2A2
public import CFSG.Assembly.QuasithinDefs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Opposite
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveTorus
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartOne.TCX.E.D4Triality
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCyclic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section E6Exchange

open Matrix CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE6

theorem e6_exchange_13 : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ chainRoot chain13 i j = chainRoot chain56 i j := by
  decide +kernel

theorem e6_exchange_56 : ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.E6 TwClass.wordE6 *ᵥ chainRoot chain56 i j = chainRoot chain13 i j := by
  decide +kernel


open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

theorem e6X₂_cyclic (K : Type) [Field K] [Finite K] (w : WeylGroup Tag.E6)
    (hw : w = (coxeterSystem Tag.E6).wordProd TwClass.wordE6) (D : LangLevi Tag.E6 K w)
    (S : Set (Fin Tag.E6.rank → ℤ)) (hS : S = parabolicRoots Tag.E6 supportA2A2)
    {p : ℕ} (hp : p.Prime) (hord : orderOf (((Nat.card K ^ 2 : ℕ)) : ZMod p) = 3) :
    ∀ g : ↥(D.frame S), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(D.frame S))) := by
  classical
  subst hS
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓp, hcard⟩ := FiniteField.card K ℓ
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hKcard : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hσ : ∀ c, D.Fr c = c ^ (ℓ ^ (f : ℕ)) := fun c => by rw [D.hFr, hKcard]
  set n : ModGL Tag.E6 D.L := canonicalRep (coxeterSystem Tag.E6) D.L w with hn
  set Φ : ModGL Tag.E6 D.L →* ModGL Tag.E6 D.L := Units.map (entrywiseHom D.Fr) with hΦ
  let θ' : ModGL Tag.E6 D.L →* ModGL Tag.E6 D.L := (MulAut.conj n).toMonoidHom.comp Φ
  have hθ'app : ∀ x, θ' x = n * Φ x * n⁻¹ := fun x => rfl
  have hΦinj : Function.Injective Φ :=
    Units.map_injective (f := entrywiseHom D.Fr) (entrywise_injective (σ := D.Fr))
  have hθ'inj : Function.Injective θ' := fun x y h => by
    rw [hθ'app, hθ'app] at h
    exact hΦinj (mul_left_cancel (mul_right_cancel h))
  have hpin : ∀ {β : Fin Tag.E6.rank → ℤ}, IsRoot Tag.E6 β → ∃ ε : D.L, ε * ε = 1 ∧
      ∀ c : D.L, θ' (pinnedX Tag.E6 D.L β c) = pinnedX Tag.E6 D.L (w • β) (ε * D.Fr c) := by
    intro β hβ
    obtain ⟨ε, hε, hN⟩ := exists_canonicalRep_mul_pinnedX_mul_inv D.L w hβ
    refine ⟨ε, hε, fun c => ?_⟩
    have hσ' : Φ (pinnedX Tag.E6 D.L β c) = pinnedX Tag.E6 D.L β (D.Fr c) :=
      Units.ext (entrywise_pinnedX D.Fr β c)
    rw [hθ'app, hσ', hN]
  have hw13 : ∀ i j : Fin 3, i ≠ j → w • chainRoot chain13 i j = chainRoot chain56 i j := fun i j hij => by
    rw [hw, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
    exact e6_exchange_13 i j hij
  have hw56 : ∀ i j : Fin 3, i ≠ j → w • chainRoot chain56 i j = chainRoot chain13 i j := fun i j hij => by
    rw [hw, CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec]
    exact e6_exchange_56 i j hij
  have h12 : ∀ i j : Fin 3, i ≠ j → ∃ e : D.L, e * e = 1 ∧ ∀ c : D.L,
      θ' (pinnedX Tag.E6 D.L (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 D.L (chainRoot chain56 ((1 : Equiv.Perm (Fin 3)) i) ((1 : Equiv.Perm (Fin 3)) j))
          (e * D.Fr c) := fun i j hij => by
    obtain ⟨ε, hε, h⟩ := hpin (chainRoot13_mem_parabolicRoots hij).1
    exact ⟨ε, hε, fun c => by rw [h c, hw13 i j hij]; rfl⟩
  have h21 : ∀ i j : Fin 3, i ≠ j → ∃ e : D.L, e * e = 1 ∧ ∀ c : D.L,
      θ' (pinnedX Tag.E6 D.L (chainRoot chain56 i j) c) =
        pinnedX Tag.E6 D.L (chainRoot chain13 ((1 : Equiv.Perm (Fin 3)) i) ((1 : Equiv.Perm (Fin 3)) j))
          (e * D.Fr c) := fun i j hij => by
    obtain ⟨ε, hε, h⟩ := hpin (isRoot_chainRoot56 hij)
    exact ⟨ε, hε, fun c => by rw [h c, hw56 i j hij]; rfl⟩
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hFrs : Function.Surjective D.Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓp.pos (f : ℕ))
    exact ⟨x, by rw [hσ, hx]⟩
  obtain ⟨θ0, hθ0, a, b, hab⟩ := exists_exchanged_layer_pos (Fr := D.Fr) hFrs θ' hθ'inj 1 1 h12 h21
  have hcyc := exchange_cyclic hℓp f.pos hKcard D.Fr hσ twoA2MulSup twoA2MulSup_surjective
    (fun x => twoA2MulSup_eq_one_iff x.1 x.2) θ0 a b hab hp (by rw [← hKcard]; exact hord)
  have hQ : rootSpan Tag.E6 D.L (parabolicRoots Tag.E6 supportA2A2) =
      subsystemGroup Tag.E6 D.L support13 ⊔ subsystemGroup Tag.E6 D.L support56 :=
    rootSpan_supportA2A2
  let ι₁ : ↥(D.frame (parabolicRoots Tag.E6 supportA2A2)) →*
      ↥(subsystemGroup Tag.E6 D.L support13 ⊔ subsystemGroup Tag.E6 D.L support56) :=
    ((frameEmb D).comp (D.frame (parabolicRoots Tag.E6 supportA2A2)).subtype).codRestrict _
      (fun x => by
        rw [← hQ]
        exact ((mem_frame_iff' D _ x).1 x.2).2)
  have hι₁ : ∀ x, (ι₁ x : ModGL Tag.E6 D.L) = frameEmb D x := fun x => rfl
  let ι : ↥(D.frame (parabolicRoots Tag.E6 supportA2A2)) →* ↥(fixSubgroup θ0) :=
    ι₁.codRestrict (fixSubgroup θ0) (fun x => by
      show θ0 (ι₁ x) = ι₁ x
      apply Subtype.ext
      rw [hθ0, hι₁]
      exact mem_twistedFixedPoints.1 (frameEmb_twistedFixed D x))
  have hι : Function.Injective ι := fun x y h => by
    apply Subtype.ext
    apply frameEmb_injective D
    have h1 := congrArg Subtype.val (congrArg Subtype.val h)
    exact h1
  intro g hg
  exact isCyclic_centralizer_of_injective_hom_gen ι hι hcyc hg

theorem e6Six_S₂_eq :
    (TwClass.e6Six.S₂ : Set (Fin Tag.E6.rank → ℤ)) = parabolicRoots Tag.E6 supportA2A2 := by
  ext α
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  have h : ∀ i : Fin Tag.E6.rank, i.val ∈ TwClass.e6Six.J₂ ↔
      (i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) := by decide
  exact imp_congr_left (not_congr ((h i).trans (mem_supportA2A2 i).symm))

theorem planeCyclic_e6Six_X₂ (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) {p : ℕ} (hp : p.Prime)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = TwClass.e6Six.e) :
    ∀ g : ↥(TwClass.e6Six.X₂ D), orderOf g = p →
      IsCyclic ↥(Subgroup.centralizer ({g} : Set ↥(TwClass.e6Six.X₂ D))) := by
  have h2 : orderOf (((Nat.card K ^ 2 : ℕ)) : ZMod p) = 3 := by
    rw [Nat.cast_pow, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hord]
    change 6 / Nat.gcd 6 2 = 3
    norm_num
  exact e6X₂_cyclic K TwClass.e6Six.w rfl D TwClass.e6Six.S₂ e6Six_S₂_eq hp h2

end E6Exchange

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.PlaneCyclic
