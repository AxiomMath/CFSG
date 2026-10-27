module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PairFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyHex
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.RankThree.PartOne.KGD.D4A2Frame

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.RankThree.E6
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


@[expose] def PairInjectiveNegOne (τ : Tag) : Prop :=
  ∀ r₁ ∈ RootOps.pairTable τ, ∀ r₂ ∈ RootOps.pairTable τ,
    iform (RootOps.orbitCertRoot τ r₁.1) (RootOps.orbitCertRoot τ r₁.2.1) = -1 →
    iform (RootOps.orbitCertRoot τ r₂.1) (RootOps.orbitCertRoot τ r₂.2.1) = -1 →
      r₁.1 = r₂.1 ∧ r₁.2.1 = r₂.2.1

theorem pairInjectiveNegOne_D4 : PairInjectiveNegOne Tag.D4 := by
  unfold PairInjectiveNegOne
  decide +kernel

theorem exists_weyl_pair_negOne {τ : Tag} (hinj : PairInjectiveNegOne τ)
    {r s r' s' : Fin τ.rank → ℤ}
    (hr : IsRoot τ r) (hs : IsRoot τ s) (hr' : IsRoot τ r') (hs' : IsRoot τ s')
    (hne : r ≠ s) (hne' : r ≠ -s) (hne₂ : r' ≠ s') (hne₂' : r' ≠ -s')
    (h1 : iform r s = -1) (h2 : iform r' s' = -1) :
    ∃ w : WeylGroup τ, w • r = r' ∧ w • s = s' := by
  obtain ⟨row₁, hrow₁, w₁, h₁r, h₁s⟩ := PairFrame.exists_pairTable_row_gen hr hs hne hne'
  obtain ⟨row₂, hrow₂, w₂, h₂r, h₂s⟩ := PairFrame.exists_pairTable_row_gen hr' hs' hne₂ hne₂'
  have c₁ := iform_smul w₁ (RootOps.orbitCertRoot τ row₁.1) (RootOps.orbitCertRoot τ row₁.2.1)
  have c₂ := iform_smul w₂ (RootOps.orbitCertRoot τ row₂.1) (RootOps.orbitCertRoot τ row₂.2.1)
  rw [h₁r, h₁s] at c₁
  rw [h₂r, h₂s] at c₂
  obtain ⟨e₁, e₂⟩ := hinj row₁ hrow₁ row₂ hrow₂ (c₁.symm.trans h1) (c₂.symm.trans h2)
  refine ⟨w₂ * w₁⁻¹, ?_, ?_⟩
  · rw [mul_smul, ← h₁r, inv_smul_smul, e₁, h₂r]
  · rw [mul_smul, ← h₁s, inv_smul_smul, e₂, h₂s]

theorem d4rhoStd_transvection_sq {L : Type} [Field L] (i j : Fin 3) (hij : i ≠ j) :
    ∃ ε : L, ε * ε = 1 ∧ ∀ t : L, d4rhoStd L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.D4 L (chainRoot d4ChainA2 i j) (ε * t) := by
  obtain ⟨ε₀, hε₀, hfam⟩ := d4A2RootFamily_all (K := L) i j hij
  have hεε : (ε₀ : L) * (ε₀ : L) = 1 := by
    rcases hε₀ with rfl | rfl <;> simp
  refine ⟨ε₀, hεε, fun s => ?_⟩
  have hmem := pinnedX_mem_d4A2Group (chainRootA2_mem_parabolicRoots hij) ((ε₀ : L) * s)
  have hrep : d4A2Rep L ⟨pinnedX Tag.D4 L (chainRoot d4ChainA2 i j) ((ε₀ : L) * s), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij s := by
    apply Subtype.ext
    rw [coe_d4A2Rep, hfam, CFSG.LinearGroups.coe_transvection, ← mul_assoc, hεε, one_mul]
  rw [← hrep]
  exact d4rhoStd_d4A2Rep hmem

theorem exists_d4_signedFrame {L : Type} [Field L] {γ δ : Fin Tag.D4.rank → ℤ}
    (hγ : IsRoot Tag.D4 γ) (hδ : IsRoot Tag.D4 δ) (h : iform γ δ = -1) :
    ∃ (ρ' : SL(3, L) →* ModGL Tag.D4 L) (σ : Fin 3 → Fin 3 → Fin Tag.D4.rank → ℤ),
      IsSLFrame ρ' σ ∧ Function.Injective ρ' ∧ σ 0 1 = γ ∧ σ 1 2 = δ ∧
      ∀ (i j : Fin 3) (hij : i ≠ j), ∃ ε : L, ε * ε = 1 ∧ ∀ t : L,
        ρ' (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX Tag.D4 L (σ i j) (ε * t) := by
  have hsl : SimplyLacedTag Tag.D4 := Or.inl rfl
  have hγγ := iform_self_eq_two_of_simplyLaced hsl hγ
  have hδδ := iform_self_eq_two_of_simplyLaced hsl hδ
  have hne1 : γ ≠ δ := by
    intro e
    rw [← e, hγγ] at h
    omega
  have hne2 : γ ≠ -δ := by
    intro e
    have : iform γ δ = iform (-δ) δ := by rw [← e]
    rw [iform_neg_left', hδδ] at this
    omega
  have he0 : IsRoot Tag.D4 (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) := IsRoot.basis 0
  have he2 : IsRoot Tag.D4 (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) := IsRoot.basis 2
  obtain ⟨w, hw0, hw2⟩ := exists_weyl_pair_negOne pairInjectiveNegOne_D4 he0 he2 hγ hδ
    (by decide) (by decide) hne1 hne2 (by decide +kernel) h
  have hfr := (d4Std_frame (L := L)).transport w
  refine ⟨_, _, IsSLFrame.of_isA2Frame hfr, hfr.injective, ?_, ?_, ?_⟩
  · show w • _ = γ
    rw [chainRootA2_values.1, hw0]
  · show w • _ = δ
    rw [chainRootA2_values.2.1, hw2]
  · intro i j hij
    obtain ⟨ε₀, hε₀, hf⟩ := d4rhoStd_transvection_sq (L := L) i j hij
    obtain ⟨ε₁, hε₁, hc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w
      ((d4Std_frame (L := L)).isRoot i j hij)
    refine ⟨ε₁ * ε₀, by linear_combination (ε₁ * ε₁) * hε₀ + hε₁, fun t => ?_⟩
    show canonicalRep (coxeterSystem Tag.D4) L w * d4rhoStd L _ *
      (canonicalRep (coxeterSystem Tag.D4) L w)⁻¹ = _
    rw [hf, hc, mul_assoc]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
