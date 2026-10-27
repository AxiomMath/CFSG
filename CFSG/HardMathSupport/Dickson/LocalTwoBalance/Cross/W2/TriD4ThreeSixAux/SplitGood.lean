module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodPoly
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwistedLineFix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRoot
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


section Tri

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem tri_shape (hrel : ∀ δ, IsRoot τ δ → S.ρ (S.ρ δ) = -S.ρ δ - δ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {ρ' : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hfr : IsSLFrame ρ' σ) (h01 : σ 0 1 = γ) (h12 : σ 1 2 = S.ρ γ) :
    (∀ i j, i ≠ j → S.ρ (σ i j) = σ (finRotate 3 i) (finRotate 3 j)) ∧
      frameRoots σ ⊆ rhoOrbitPM S.ρ γ := by
  have hργ : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have e1 : S.ρ (S.ρ γ) = -S.ρ γ - γ := hrel γ hγ
  have e2 : S.ρ (S.ρ (S.ρ γ)) = γ := by
    have h := hrel (S.ρ γ) hργ
    rw [h, e1]
    abel
  have e3 : S.ρ (-γ) = -S.ρ γ := S.frob.neg_eq γ
  have e4 : S.ρ (-S.ρ γ) = γ + S.ρ γ := by
    rw [S.frob.neg_eq, e1]
    abel
  have e5 : S.ρ (γ + S.ρ γ) = -γ := by
    have : γ + S.ρ γ = -S.ρ (S.ρ γ) := by rw [e1]; abel
    rw [this, S.frob.neg_eq, e2]
  have e6 : S.ρ (-(γ + S.ρ γ)) = γ := by
    rw [S.frob.neg_eq, e5, neg_neg]
  have h02 : σ 0 2 = γ + S.ρ γ := by rw [← hfr.add 0 1 2, h01, h12]
  have h10 : σ 1 0 = -γ := by rw [hfr.neg 0 1, h01]
  have h21 : σ 2 1 = -S.ρ γ := by rw [hfr.neg 1 2, h12]
  have h20 : σ 2 0 = -(γ + S.ρ γ) := by rw [hfr.neg 0 2, h02]
  have r0 : finRotate 3 0 = 1 := by decide
  have r1 : finRotate 3 1 = 2 := by decide
  have r2 : finRotate 3 2 = 0 := by decide
  refine ⟨fun i j hij => ?_, ?_⟩
  · fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    · show S.ρ (σ 0 1) = σ (finRotate 3 0) (finRotate 3 1)
      rw [r0, r1, h01, h12]
    · show S.ρ (σ 0 2) = σ (finRotate 3 0) (finRotate 3 2)
      rw [r0, r2, h02, e5, h10]
    · show S.ρ (σ 1 0) = σ (finRotate 3 1) (finRotate 3 0)
      rw [r1, r0, h10, e3, h21]
    · show S.ρ (σ 1 2) = σ (finRotate 3 1) (finRotate 3 2)
      rw [r1, r2, h12, e1, h20]
      abel_nf
    · show S.ρ (σ 2 0) = σ (finRotate 3 2) (finRotate 3 0)
      rw [r2, r0, h20, e6, h01]
    · show S.ρ (σ 2 1) = σ (finRotate 3 2) (finRotate 3 1)
      rw [r2, r1, h21, e4, h02]
  · rintro x ⟨i, j, hij, rfl⟩
    have i0 : (S.ρ : (Fin τ.rank → ℤ) → _)^[0] γ = γ := rfl
    have i1 : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] γ = S.ρ γ := rfl
    have i2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[2] γ = -S.ρ γ - γ := e1
    have n0 : (S.ρ : (Fin τ.rank → ℤ) → _)^[0] (-γ) = -γ := rfl
    have n1 : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] (-γ) = -S.ρ γ := e3
    have n2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[2] (-γ) = γ + S.ρ γ := by
      show S.ρ (S.ρ (-γ)) = _
      rw [e3, e4]
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | skip
    · exact ⟨0, Or.inl (h01.trans i0.symm)⟩
    · exact ⟨2, Or.inr (h02.trans n2.symm)⟩
    · exact ⟨0, Or.inr (h10.trans n0.symm)⟩
    · exact ⟨1, Or.inl (h12.trans i1.symm)⟩
    · exact ⟨2, Or.inl (by show σ 2 0 = _; rw [h20, i2]; abel)⟩
    · exact ⟨1, Or.inr (h21.trans n1.symm)⟩

end Tri

section Norm1

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem normElt_one' (g : ModGL τ L) : normElt S 1 g = g := by
  unfold normElt
  have : (Finset.univ : Finset (ZMod 1)) = {0} := Finset.univ_unique
  rw [this]
  simp [iterHom_zero]

end Norm1

theorem exists_ne_zero_one_of_three_le_card (k : Type) [Field k] (h : 3 ≤ Nat.card k) :
    ∃ t : k, t ≠ 0 ∧ t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hfin : Finite k := Nat.finite_of_card_ne_zero (by omega)
  have hsub : (Set.univ : Set k) ⊆ {0, 1} := by
    intro t _
    by_cases ht : t = 0
    · simp [ht]
    · simp [hcon t ht]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({0, 1} : Set k).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    simp
  rw [Set.ncard_univ] at h1
  omega

section Split

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem rootRankOneGroup_le_frame_range {ρ' : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hfr : IsSLFrame ρ' σ) :
    rootRankOneGroup τ L (σ 0 1) ≤ ρ'.range := by
  rw [rootRankOneGroup_eq_rootSpan_pair (hfr.isRoot 0 1 (by decide)), hfr.range]
  refine rootSpan_mono ?_
  rintro x (rfl | rfl)
  · exact ⟨0, 1, by decide, rfl⟩
  · exact ⟨1, 0, by decide, (hfr.neg 0 1).symm⟩

theorem isGoodRoot_of_splitFrame (hτ : τ ≠ .G2) (hsl : SimplyLacedTag τ) (hAlg : S.IsAlgebraic)
    (hp3 : p ≠ 3) (hpq : p ∣ S.D.q ^ 2 + S.D.q + 1)
    {ρ' : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hfr : IsSLFrame ρ' σ) (hinj : Function.Injective ρ')
    (hsign : ∀ (i j : Fin 3) (hij : i ≠ j), ∃ ε : L, ε * ε = 1 ∧ ∀ t : L,
      ρ' (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (σ i j) (ε * t))
    (hπ : ∀ i j, i ≠ j → S.ρ (σ i j) = σ (finRotate 3 i) (finRotate 3 j))
    (horb : frameRoots σ ⊆ rhoOrbitPM S.ρ (σ 0 1))
    (hpoly : S.D.q = 2 → ∀ (zu z : ModGL τ L), zu ∈ rootSpan τ L (frameRoots σ) →
      (∀ γ ∈ frameRoots σ,
        z * (zu * pinnedX τ L γ 1 * zu⁻¹) = (zu * pinnedX τ L γ 1 * zu⁻¹) * z) →
      ∀ g ∈ rootSpan τ L (frameRoots σ), Commute z g) :
    IsGoodRoot S (σ 0 1) := by
  classical
  obtain ⟨k, hk, hcl⟩ := twistedLine_exists_field S hAlg
  have hkfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact S.q_pos.ne')
  obtain ⟨⟨H, hH⟩, hYΓ, hYperf⟩ := splitLine_spec S (k := k) hk hfr hinj (finRotate 3) hπ
  set Y : Subgroup (ModGL τ L) := ρ'.range ⊓ S.D.step.eqLocus (MonoidHom.id _) with hY
  have hβ : IsRoot τ (σ 0 1) := hfr.isRoot 0 1 (by decide)
  have hYmem : ∀ Y' : SL(3, k),
      ρ' (H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y' * H⁻¹) ∈ Y := by
    intro Y'
    refine ⟨⟨_, rfl⟩, ?_⟩
    exact (hH _).2 ⟨Y', rfl⟩
  have hKY : ∀ (i j : Fin 3) (hij : i ≠ j) (t : k),
      ρ' H * pinnedX τ L (σ i j) (algebraMap k L t) * (ρ' H)⁻¹ ∈ Y := by
    intro i j hij t
    obtain ⟨ε, hε2, hε⟩ := hsign i j hij
    have hε1 : ε = 1 ∨ ε = -1 := mul_self_eq_one_iff.1 hε2
    rcases hε1 with rfl | rfl
    · have h := hYmem (Matrix.SpecialLinearGroup.transvection hij t)
      rw [splitLine_map_transvection, map_mul, map_mul, map_inv, hε] at h
      simpa using h
    · have h := hYmem (Matrix.SpecialLinearGroup.transvection hij (-t))
      rw [splitLine_map_transvection, map_mul, map_mul, map_inv, hε] at h
      simpa using h
  have hYspan : Y ≤ rootSpan τ L (rhoOrbitPM S.ρ (σ 0 1)) := by
    refine inf_le_left.trans ?_
    rw [hfr.range]
    exact rootSpan_mono horb
  have hpq' : p ∣ Nat.card k ^ 2 + Nat.card k + 1 := by rw [hk]; exact hpq
  obtain ⟨x, hxY, hxp⟩ := splitLine_exists_orderOf S hinj hH hp3 hpq'
  have hcomm : ∀ z : ModGL τ L, (∀ y ∈ Y, Commute z y) →
      ∀ x ∈ rootRankOneGroup τ L (σ 0 1), Commute z x := by
    intro z hz x hx
    have hx' : x ∈ ρ'.range := rootRankOneGroup_le_frame_range hfr hx
    by_cases hq3 : 3 ≤ S.D.q
    · have hk3 := exists_ne_zero_one_of_three_le_card k (by rw [hk]; exact hq3)
      exact splitLine_commute_range hτ hfr hk3 (fun Y' => hz _ (hYmem Y')) x hx'
    · have hq2 : S.D.q = 2 := by
        have := S.hqpow.1.one_lt
        omega
      have hzu : ρ' H ∈ rootSpan τ L (frameRoots σ) := hfr.range ▸ ⟨H, rfl⟩
      refine hpoly hq2 (ρ' H) z hzu ?_ x (hfr.range ▸ hx')
      rintro γ ⟨i, j, hij, rfl⟩
      have := hz _ (by simpa using hKY i j hij 1)
      exact this.eq
  have hfield : ∀ (r f j : ℕ) [ExpChar L r], r.Prime → S.D.q = r ^ f → 0 < j → j < f →
      ∀ z : ModGL τ L, ¬ ∀ y ∈ Y,
        z * Units.map (entrywiseHom (iterateFrobenius L r j)) y * z⁻¹ = y := by
    intro r f j _ hr hq' hj0 hjf z hz
    letI : Fintype k := Fintype.ofFinite k
    have hK : Fintype.card k = S.D.q ^ 1 := by
      rw [← Nat.card_eq_fintype_card, hk, pow_one]
    haveI : NeZero 1 := ⟨one_ne_zero⟩
    refine false_of_fixed_by_twist_of_norm (m := 1) S hτ (ρ' H) hβ (algebraMap k L) hK hr hq'
      (Or.inr hsl) hj0 hjf z (fun t => ?_)
    rw [normElt_one']
    exact hz _ (hKY 0 1 (by decide) t)
  exact ⟨hβ, Y, hYΓ, hYperf, hYspan, ⟨x, hxY, hxp⟩, hcomm, hfield⟩

end Split

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
