module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three18
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three16

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2 CFSG.Open
  CFSG.RankThree.PartOne.KLR CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
  CFSG.HardMathSupport.Timmesfeld.Torality
open scoped Matrix MatrixGroups Pointwise


@[expose] def e7T3A2Word : List (Fin Tag.E7.rank) := [2, 3, 4, 5, 2, 1, 3, 4, 2, 1, 3]

@[expose] def e7T3A2Comp : E7T3Comp := { kind := 0, u := [0, 2], rot := false }

@[expose] def e7T3A2WordList : List (List ℤ) :=
  (e7StdRoots [0, 2]).map (lmulVec Tag.E7.rank (e7wl e7T3A2Word))

theorem e7T3A2Word_good : e7T3A2Comp.Good e7T3Word e7T3A2Word := by
  decide +kernel

private theorem e7T3A2WordList_eq : ∀ l ∈ e7T3A2WordList ++ e7T3A2List,
    l ∈ e7T3A2WordList ↔ l ∈ e7T3A2List := by
  decide +kernel

theorem sigmaSet_e7T3A2Word :
    sigmaSet ((coxeterSystem Tag.E7).wordProd e7T3A2Word) = e7T3A5SubA2 := by
  have himg : sigmaSet ((coxeterSystem Tag.E7).wordProd e7T3A2Word) =
      {α | ∃ l ∈ e7T3A2WordList, α = toVec Tag.E7.rank l} := by
    ext α
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rw [show CFSG.RankThree.PartOne.KE.support13 = e7T3J 0 from rfl] at hγ
      rw [parabolicRoots_e7T3J (kind := 0) (by norm_num)] at hγ
      obtain ⟨l, hl, rfl⟩ := hγ
      exact ⟨lmulVec Tag.E7.rank (e7wl e7T3A2Word) l,
        List.mem_map.2 ⟨l, hl, rfl⟩, by simp only [wordProd_smul_toVec7]⟩
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 hl
      refine ⟨toVec Tag.E7.rank l₀, ?_, by simp only [wordProd_smul_toVec7]⟩
      rw [show CFSG.RankThree.PartOne.KE.support13 = e7T3J 0 from rfl,
        parabolicRoots_e7T3J (kind := 0) (by norm_num)]
      exact ⟨l₀, hl₀, rfl⟩
  rw [himg, e7T3A5SubA2_eq_image]
  ext α
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, (e7T3A2WordList_eq l (List.mem_append_left _ hl)).1 hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, (e7T3A2WordList_eq l (List.mem_append_right _ hl)).2 hl, rfl⟩

theorem isQuasisimple_e7T3QLayer {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}
  (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hε : ε = 1 ∨ ε = -1)
  (hq2 : ε = -1 → 2 < ℓ ^ f) (n : ModGL Tag.E7 L) (hnm : n ∈ monomialSubgroup Tag.E7 L)
  (hnC : n ∈ adjointGroup Tag.E7 L)
  (hnW : ∀ x : Fin Tag.E7.rank → ℤ,
    weylQuotientHom Tag.E7 L ⟨n, hnm⟩ • x = (ε • e7T3W) *ᵥ x) :
    CFSG.IsQuasisimple ↥(rootSpan Tag.E7 L e7T3A5SubA2 ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨hg, hact⟩ := e7T3_comp_eps (L := L) hε hnW e7T3A2Word_good
  have hg' : (coxeterSystem Tag.E7).wordProd e7T3A2Comp.u ∈
      parabolicWeylGroup Tag.E7 CFSG.RankThree.PartOne.KE.support13 := by
    simpa [e7T3A2Comp, e7T3J] using hg
  obtain ⟨P, hP, hfac, -⟩ := e7_a2_factor hf hK hε hq2
    ((coxeterSystem Tag.E7).wordProd e7T3A2Word) n hnm
    ((coxeterSystem Tag.E7).wordProd e7T3A2Comp.u) hg' (fun α hα => by
      have h1 := hact α hα
      simpa [e7T3A2Comp, e7T3Beta, permLattice_one] using h1)
  have hP' : rootSpan Tag.E7 L e7T3A5SubA2 ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) = P := by
    rw [hP, sigmaSet_e7T3A2Word]
  rw [hP']
  exact hfac.quasi ()

theorem dvd_card_e7T3QLayer {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  [CharP K ℓ] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}
  (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
  (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
  (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) :
    p ∣ Nat.card ↥(rootSpan Tag.E7 L e7T3A5SubA2 ⊓
      twistedFixedPoints F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :=
  dvd_card_A5SubA2_inf_twistedFixedPoints F hf hK hp hp3 hε hpf

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
