module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8QTorus3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8QTorus5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three6

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section Certs


variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem exists_rank_three_qTorus_centralizer_normalizer_of_charTwo (hE6 : E6Layer Tag.E8)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ : ℓ = 2) (hf1 : f = 1)
    (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    (hnW : weylQuotientHom Tag.E8 L ⟨n, hnm⟩ = e8T3We ε)
    (g0 : ModGL Tag.E8 L) (hg0C : g0 ∈ adjointGroup Tag.E8 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g0 = g0 * n)
    (hperf : ∀ P : Subgroup (ModGL Tag.E8 L), Finite P → P ≤ adjointGroup Tag.E8 L →
      (∀ x ∈ P, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.E8 K L).range)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {x : adjointGroup Tag.E8 K} (hx : orderOf x = p) (c : adjointGroup Tag.E8 K)
    (hxframe : adjEmb Tag.E8 K L (c * x * c⁻¹) = g0 *
      rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card K : ZMod p) i).val) *
      g0⁻¹)
    {J : Subgroup (adjointGroup Tag.E8 K)}
    (hJx : J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))
    (hJn : (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)))).Normal)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) (hq3 : q = 3) :
    ∃ F : Subgroup (adjointGroup Tag.E8 K),
      F ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 K)) ∧
      F ≤ Subgroup.normalizer (J : Set (adjointGroup Tag.E8 K)) ∧
      IsElemAbelian q F ∧ 3 ≤ CFSG.Open.pRank q F := by
  classical
  subst hq3
  subst hℓ
  subst hf1
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Infinite L := IsAlgClosed.instInfinite
  set r : ZMod p := (Nat.card K : ZMod p) with hrdef
  have hr : r ^ 2 + (ε : ZMod p) * r + 1 = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1) p).2 hpf
    simpa [hrdef] using h
  have hS : ∃ u : WeylGroup Tag.E8, (fun γ => u • γ) '' rootCharKernel
      (fun i => ζ ^ (e8T3XColumn ε r i).val) = parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    obtain ⟨u, hu⟩ := exists_conj_rootKernel_e8T3XColumn_eq_e6Nodes hp hp3 hε hpf
    exact ⟨u, by rwa [CFSG.RankThree.PartOne.KLR.rootCharKernel_zetaPow_eq hζ]⟩
  have hh : g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 ∈
      twistedTorusOf n (Units.map (entrywiseHom (iterateFrobenius L 2 1))) := by
    rw [hxframe]
    have h : g0⁻¹ * (g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε r i).val) * g0⁻¹) * g0 =
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε r i).val) := by group
    rw [h]
    exact e8T3XColumn_mem_twistedTorus hζ (fun y => by rw [iterateFrobenius_def, hK]) hε hr
      (e8T3_twistedTorus n hnm hnW (iterateFrobenius L 2 1))
  have hb : rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε r i).val) =
      g0⁻¹ * adjEmb Tag.E8 K L (c * x * c⁻¹) * g0 := by
    rw [hxframe]
    group
  obtain ⟨F, hFx, hFel, hF3⟩ :=
    exists_rank_three_qTorus_centralizer_of_stdLayer (hE6 := hE6) (hε := hε) (K := K)
      (hf := hf) (hK := hK) (hp := hp) (hp3 := hp3) (hpf := hpf) (L := L) (n := n)
      (hnm := hnm) (hnW := hnW) (g0 := g0) (hg0C := hg0C) (hg0 := hg0) (hperf := hperf)
      (hT := e8T3_twistedTorus n hnm hnW (iterateFrobenius L 2 1)) (hx := hx) (c := c)
      (hh := hh) (b := fun i => ζ ^ (e8T3XColumn ε r i).val) (hb := hb) (hS := hS)
      (hq := hq) (hq2 := hq2) (hqp := hqp)
      (hprov := fun _ _ hm₁ hstd => exists_three_qTorus_stdLayer_charTwo hm₁ hstd)
  refine ⟨F, hFx, ?_, hFel, hF3⟩
  exact hFx.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJx).mp hJn)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
