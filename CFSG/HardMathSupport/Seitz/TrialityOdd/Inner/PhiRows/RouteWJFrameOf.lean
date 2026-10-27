module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryFrame

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

section FrameOf

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

@[expose] def d4phiFrameOfG0 (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hε : ε = 1 ∨ ε = -1) (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (n : ModGL TwistTag.D4.tag L) (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (w : WeylGroup TwistTag.D4.tag)
    (hnw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = w)
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    (g0 : ModGL TwistTag.D4.tag L) (hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L)
    (hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n) :
    D4PhiFrame ℓ f K σ ε p L := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr hn w hnw (d4T36M ε) hw
  have hrange := triEmb_range hℓ hf hK hσ Fr hFr
  refine ⟨hf, hK, hσ, hε, hp, hp3, hpd, n, hn, w, hnw, hw, g0, hg0C, hg0,
    fun P hPC hPF => ?_, fun Q hQ => ?_⟩
  · rw [hrange]
    exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
  · have hN : d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f) ≠ 0 := by
      have : 0 < d4T36d ε (ℓ ^ f) := (d4T36d_odd hε (by omega)).pos
      positivity
    have hZcard : Nat.card ((fixedCharTuples (d4T36M ε) Fr).map
        (rootDiagUnitHom TwistTag.D4.tag L)) = d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f) := by
      rw [Subgroup.card_map_of_injective rootDiagUnit_injective]
      exact d4T36_card hε (by omega) hℓq hFr
    have hCcard := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
      σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
    have hord : p ^ (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
        p ^ (d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f)).factorization p := by
      rw [hCcard]
      exact d4T36_ordProj hε hp hp3 hq2 hpd
    obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen 1 (triEmb K σ L)
      triEmb_injective (twistHom TwistTag.D4 L Fr) n g0 hg0C hg0 hp hp3 hN
      (fun X hX hXC hXF => triEmb_rational hℓ hf hK hσ Fr hFr X hXC hXF)
      ((fixedCharTuples (d4T36M ε) Fr).map (rootDiagUnitHom TwistTag.D4.tag L)) hT.symm.le hZcard
      hord
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => by rw [hT]; exact (mem_subtorusImage_iff _ _ _ _).1 (hc y hy)⟩

end FrameOf

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
