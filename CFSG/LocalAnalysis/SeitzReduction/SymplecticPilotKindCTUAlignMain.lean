module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignEdge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryTransportOdd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive
  exists_add_unitaryInvolution_eq)

section Field

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem exists_unitaryInvolution_ne_ctua (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ c : F, unitaryInvolution F 2 f c ≠ c := by
  obtain ⟨c, hc⟩ := (ctua_unitaryFieldData hF hf).exists_bar_ne
  refine ⟨c, ?_⟩
  rwa [unitaryInvolution_apply, ← (ctua_unitaryFieldData hF hf).bar_apply]

theorem exists_add_unitaryInvolution_add_one_ctua (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ c : F, c + unitaryInvolution F 2 f c + 1 = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq (K := F) (p := 2) (f := f) hF (a := 1)
    (map_one _)
  exact ⟨c, by rw [hc, CharTwo.add_self_eq_zero]⟩

end Field

section Align

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem exists_ctuParamAgree (hKc : Nat.card K = 2 ^ f) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hf : 2 ≤ f) (hN : 5 ≤ N) (P : ∀ k : Fin N, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k) :
    ∃ Q : ∀ k : Fin N, CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k, CtuParamAgree Q := by
  classical
  obtain ⟨o⟩ : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hex : ∀ k : Fin N, ∃ R : CtuParam ε hε (unitaryInvolution F 2 f) ι hι e k,
      ∀ (x : SU (unitaryInvolution F 2 f) (2 * N + ε))
        (hx : x ∈ ctuBlock (unitaryInvolution F 2 f) ε ({k, o} : Finset (Fin N))),
        R.Φ ⟨x, ctuBlock_pair_le_left _ k o hx⟩ = (P o).Φ ⟨x, ctuBlock_pair_le_right _ k o hx⟩ := by
    intro k
    by_cases hko : k = o
    · subst hko
      exact ⟨P k, fun x hx => rfl⟩
    · obtain ⟨ν, hν, b, h1⟩ := (P k).exists_twist_of_overlap hKc hF hf (by omega) hko (P o)
      have hT := ctuaTwist_admissible (N := N) (hε := hε) (ι := ι) (hι := hι)
        (hσ := unitaryInvolution_involutive hF) hν b
      refine ⟨(P k).twistBy hT.inv, fun x hx => ?_⟩
      rw [CtuParam.twistBy_Φ_apply]
      have hx' : (ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν
          b)⁻¹ x ∈ ctuBlock (unitaryInvolution F 2 f) ε ({k, o} : Finset (Fin N)) :=
        (hT.inv.mem_iff _ x).2 hx
      refine (h1 _ hx').trans (congrArg (P o).Φ (Subtype.ext ?_))
      change (ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b)
        ((ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b)⁻¹ x) = x
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  choose Q hQ using hex
  refine ⟨Q, fun k l x hx hx' => ?_⟩
  by_cases hkl : k = l
  · subst hkl
    rfl
  have hxkl := mem_ctuBlock_pair hx hx'
  have hagreeo : ∀ {m : Fin N} (y : SU (unitaryInvolution F 2 f) (2 * N + ε))
      (hy : y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N)))
      (hy' : y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({o} : Finset (Fin N))),
      (Q m).Φ ⟨y, hy⟩ = (P o).Φ ⟨y, hy'⟩ :=
    fun y hy hy' => hQ _ y (mem_ctuBlock_pair hy hy')
  by_cases hko : k = o
  · subst hko
    exact (hagreeo x hx hx).trans (hagreeo x hx' hx).symm
  by_cases hlo : l = o
  · subst hlo
    exact (hagreeo x hx hx').trans (hagreeo x hx' hx').symm
  obtain ⟨ν, hν, b, h1⟩ := (Q k).exists_twist_of_overlap hKc hF hf (by omega) hkl (Q l)
  have hT := ctuaTwist_admissible (N := N) (hε := hε) (ι := ι) (hι := hι)
    (hσ := unitaryInvolution_involutive hF) hν b
  set T := ctuaTwist hε (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) ν hν b
    with hTdef
  have hsub : ∀ m ∈ ({o, k, l} : Finset (Fin N)),
      ctuBlock (unitaryInvolution F 2 f) ε ({o, k, l} : Finset (Fin N)) ≤
        ctuBlock (unitaryInvolution F 2 f) ε ({m} : Finset (Fin N)) :=
    fun m hm => ctuBlock_anti (Finset.singleton_subset_iff.2 hm)
  have hfix : ∀ y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({o, k, l} : Finset (Fin N)), T y = y := by
    intro y hy
    have hTy : T y ∈ ctuBlock (unitaryInvolution F 2 f) ε ({o, k, l} : Finset (Fin N)) :=
      (hT.mem_iff _ y).2 hy
    have hyk := hsub k (by simp) hy
    have hyl := hsub l (by simp) hy
    have hyo := hsub o (by simp) hy
    have h2 := h1 y (mem_ctuBlock_pair hyk hyl)
    rw [hagreeo y hyk hyo, hagreeo (T y) (hsub l (by simp) hTy) (hsub o (by simp) hTy)] at h2
    have h3 := (P o).injOn_ctuBlock hF (by omega) (Ne.symm hko) (x := ⟨y, hyo⟩)
      (y := ⟨T y, hsub o (by simp) hTy⟩) hyk (hsub k (by simp) hTy) h2
    exact (congrArg (fun w : ctuBlock (unitaryInvolution F 2 f) ε ({o} : Finset (Fin N)) =>
      (w : SU (unitaryInvolution F 2 f) (2 * N + ε))) h3).symm
  have hcard : 2 ≤ ({o, k, l} : Finset (Fin N))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_three (a := o) (b := k) (c := l)
    omega
  have hT1 : T = 1 := ctuaTwist_eq_one_of_fix hν b (exists_unitaryInvolution_ne_ctua hF (by omega))
    (exists_add_unitaryInvolution_add_one_ctua hF) hcard hfix
  have hTx : T x = x := by rw [hT1, MulAut.one_apply]
  exact (h1 x hxkl).trans (congrArg (Q l).Φ (Subtype.ext hTx))

theorem ctuAlignInput_holds (ε : ℕ) (hε : ε ≤ 1) : CtuAlignInput ε hε := by
  intro G _ _ L N f K _ _ _ hN hKc hf e F _ _ _ hF ι hι hP
  exact exists_ctuParamAgree hKc hF hf hN fun k => (hP k).some

end Align

theorem spUnitaryParamCTInput_of_four (h4 : SpUnitaryParamCTFourInput) :
    SpUnitaryParamCTInput :=
  spUnitaryParamCTInput_of_align (ctuAlignInput_holds 0 (Nat.zero_le 1)) h4

theorem spUnitaryOddParamCTInput_of_four (h4 : SpUnitaryOddParamCTFourInput) :
    SpUnitaryOddParamCTInput :=
  spUnitaryOddParamCTInput_of_align (ctuAlignInput_holds 1 le_rfl) h4

end CFSG.SeitzReduction.SymplecticPilot
