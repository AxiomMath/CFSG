module

public import CFSG.ClassicalInvolution.Q3.Q3TWWFrameBP
public import CFSG.ClassicalInvolution.WeakCT.SpinOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameDLSubgroup

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.Q3.Q3Z
open scoped MatrixGroups

theorem weakCT_odd_subgroup_of_oddFramePair {n p f : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hq : IsQuasisimple (StatedSp 2 F))
    {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (fr : OddFramePair F n U) :
    ∃ Ψ : spinGroup (Spin.quadOdd n F) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (CurtisTits.rankOne (Spin.oddDatum n F).rootGroup k).map Ψ = U k := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h2 : (2 : F) ≠ 0 := by
    obtain ⟨hp, hf, -, hp2⟩ := hadm
    have hqc : (ringChar F).Prime := by
      rw [ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
      exact hp
    rw [Ne, ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hqc,
      ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
    exact hp2
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.oddDatum n F).isFiniteType
    (Dv := (Spin.oddDatum n F).divisible) rfl
  have hE := Steinberg.SpinOdd.chevalleyExtras (by omega : 2 ≤ n) O Steinberg.SpinOdd.commC
    (Steinberg.SpinOdd.commutatorFormula O)
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a.val + 2 = n := ⟨⟨n - 2, by omega⟩, by simp only; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b.val + 1 = n := ⟨⟨n - 1, by omega⟩, by simp only; omega⟩
  have hsq : ∀ k : Fin n,
      Steinberg.weylElement (Steinberg.SpinOdd.x n F) k 1 ^ 2 ∈ (Spin.torusB F k).range := by
    intro k
    have h := (Spin.oddDatum_isCTGroupDatum n F (Spin.oddDatum_iSup_eq_top n F h2 hn3)).sq_mem k
    have e := Steinberg.SpinOdd.weylElement_eq (n := n) (K := F) k 1
    rw [map_one, one_mul] at e
    rw [e]
    exact h
  have hcomm' : ∀ i j : Fin n, i ≠ j → ¬ edgeUp n i j → ¬ edgeUp n j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hne h1 h2' u hu v hv
    simp only [edgeUp] at h1 h2'
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm i j (by omega) u hu v hv
    · exact (hcomm j i (by omega) v hv u hu).symm
  have hψ : ∀ i j : Fin n, edgeUp n i j → ¬ (i = a ∧ j = b) →
      ∃ ψ : SL(3, F) →* G, ψ.comp (blk F 0) = fr.ρ i ∧ ψ.comp (blk F 1) = fr.ρ j := by
    intro i j hij hne
    simp only [edgeUp] at hij
    have hi : i.val + 2 < n := by
      have := j.2
      by_contra hcon
      exact hne ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    exact ⟨fr.ψ i hi, fr.ψ_zero i hi, fr.ψ_one i j hi hij.symm⟩
  obtain ⟨Ψ, hker, hrange, -, -, hblk⟩ :=
    CFSG.ComponentClassification.CatLeafProof.weakCT_of_frame_dl_subgroup
      (CurtisTits.curtisTitsConclusion_spinOdd hadm hF) (leviConePresented_spinOdd h2 hn3) hE rfl
      hq h2 (doubleBondDiagram_cartanB ha hb) (Spin.oddDatum_steinbergExtras h2).torus_iSupIndep
      hsq hcomm' (ρ := fr.ρ) fr.ρ_range (fr.ρ_inj a (by omega)) hψ
      ⟨fr.ψ4, fr.ψ4_long a ha, fr.ψ4_short b hb⟩
  exact ⟨Ψ, hker, hrange, hblk⟩

end CFSG.ClassicalInvolution.Q3.Q3TW
