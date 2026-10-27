module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three11
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.FrameLines
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three9
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2 CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
open scoped Matrix MatrixGroups Pointwise

section Selection

variable {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

theorem exists_mem_selection (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) {Ã : Subgroup (adjointGroup Tag.E7 K)}
    (hΩ : ∀ g ∈ Subgroup.centralizer (Ã : Set (adjointGroup Tag.E7 K)),
      orderOf g = p → g ∈ Ã)
    {c : adjointGroup Tag.E7 K}
    (hc : ∀ y ∈ Ã, F.g0⁻¹ * adjEmb Tag.E7 K L (c * y * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    ∃ x ∈ Ã, orderOf x = p ∧ psiC F.g0 c x =
      rootDiagUnit Tag.E7 (fun i => ζ ^
        (e7T3XColumn ε (Nat.card K : ZMod p) i).val) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htord : orderOf (rootDiagUnit Tag.E7 (fun i => ζ ^
      (e7T3XColumn ε (Nat.card K : ZMod p) i).val)) = p := by
    rw [orderOf_rootDiagUnit]
    exact e7T3XTuple_orderOf hp hζ
  obtain ⟨x₀, hx₀⟩ := exists_adjointGroup_e7T3XTuple F hf hK hp hp3 hε hpf hζ
  have hx₀ord : orderOf x₀ = p := by
    rw [← orderOf_injective (adjEmb Tag.E7 K L) adjEmb_injective x₀, hx₀]
    rw [show F.g0 * rootDiagUnit Tag.E7 (fun i => ζ ^
        (e7T3XColumn ε (Nat.card K : ZMod p) i).val) * F.g0⁻¹ =
        MulAut.conj F.g0 (rootDiagUnit Tag.E7 (fun i => ζ ^
          (e7T3XColumn ε (Nat.card K : ZMod p) i).val)) by
      simp [MulAut.conj_apply]]
    exact (orderOf_injective (MulAut.conj F.g0).toMonoidHom (MulAut.conj F.g0).injective
      (rootDiagUnit Tag.E7 (fun i => ζ ^
        (e7T3XColumn ε (Nat.card K : ZMod p) i).val))).trans htord
  have hxord : orderOf (c⁻¹ * x₀ * c) = p := by
    rw [show c⁻¹ * x₀ * c = MulAut.conj c⁻¹ x₀ by simp [MulAut.conj_apply]]
    exact (orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective
      x₀).trans hx₀ord
  have hxpsi : psiC F.g0 c (c⁻¹ * x₀ * c) = rootDiagUnit Tag.E7 (fun i => ζ ^
      (e7T3XColumn ε (Nat.card K : ZMod p) i).val) := by
    rw [psiC_apply]
    have hcx : c * (c⁻¹ * x₀ * c) * c⁻¹ = x₀ := by group
    rw [hcx, hx₀]
    group
  have hxcent : c⁻¹ * x₀ * c ∈ Subgroup.centralizer (Ã : Set (adjointGroup Tag.E7 K)) := by
    refine (Subgroup.mem_centralizer_iff (G := adjointGroup Tag.E7 K)).2 ?_
    intro y hy
    have hytor : psiC F.g0 c y ∈ torusGroup Tag.E7 L := (mem_twistedTorusOf.1 (hc y hy)).1
    have hcomm := rootDiagUnit_mul_comm_of_mem_torusGroup (τ := Tag.E7) (K := L)
      (fun i => ζ ^ (e7T3XColumn ε (Nat.card K : ZMod p) i).val) hytor
    apply psiC_injective F.g0 c
    calc psiC F.g0 c (y * (c⁻¹ * x₀ * c))
        = psiC F.g0 c y * psiC F.g0 c (c⁻¹ * x₀ * c) := map_mul _ _ _
      _ = psiC F.g0 c y * rootDiagUnit Tag.E7 (fun i => ζ ^
            (e7T3XColumn ε (Nat.card K : ZMod p) i).val) := by rw [hxpsi]
      _ = rootDiagUnit Tag.E7 (fun i => ζ ^
            (e7T3XColumn ε (Nat.card K : ZMod p) i).val) * psiC F.g0 c y := hcomm.symm
      _ = psiC F.g0 c (c⁻¹ * x₀ * c) * psiC F.g0 c y := by rw [hxpsi]
      _ = psiC F.g0 c ((c⁻¹ * x₀ * c) * y) := (map_mul _ _ _).symm
  exact ⟨c⁻¹ * x₀ * c, hΩ _ hxcent hxord, hxord, hxpsi⟩

end Selection

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
