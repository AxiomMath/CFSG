module

public import CFSG.ClassicalInvolution.WeakCT.DLDiagrams
public import CFSG.Timmesfeld.RankTwo.LeviData
public import CFSG.LieType.Steinberg.Classical.SpinOdd
public import CFSG.ClassicalInvolution.WeakCT.DoublyLaced

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)

section Diagram

theorem doubleBondDiagram_cartanB {n : ℕ} {a b : Fin n} (ha : a.val + 2 = n)
    (hb : b.val + 1 = n) : DoubleBondDiagram (Spin.cartanB n) (edgeUp n) a b where
  adj_ab := by simp only [edgeUp]; omega
  cartan_ba := by
    simp only [Spin.cartanB, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  cartan_ab := by
    simp only [Spin.cartanB, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  cartan_adj := by
    intro i j hij hn
    have hn' : ¬ (i.val = a.val ∧ j.val = b.val) := fun h => hn ⟨Fin.ext h.1, Fin.ext h.2⟩
    simp only [edgeUp] at hij
    simp only [Spin.cartanB, Matrix.of_apply, Fin.ext_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
  cartan_nadj := by
    intro i j hne hij hji
    simp only [edgeUp] at hij hji
    simp only [Spin.cartanB, Matrix.of_apply, Fin.ext_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
  neighbour := by
    intro i j hij hn
    have hn' : ¬ (i.val = a.val ∧ j.val = b.val) := fun h => hn ⟨Fin.ext h.1, Fin.ext h.2⟩
    simp only [edgeUp] at hij
    have hk : i.val + 2 < n := by
      have := j.2
      omega
    refine ⟨⟨i.val + 2, hk⟩, ?_⟩
    simp only [Spin.cartanB, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega

end Diagram

section Recognition

theorem weakCT_spinOdd {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F)
    {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : spinGroup (Spin.quadOdd n F) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (Spin.quadOdd n F))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaOdd n p f ∧
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
  have hroot : ∃ c : Fin n, edgeUp n ⟨0, by omega⟩ c ∨ edgeUp n c ⟨0, by omega⟩ :=
    ⟨⟨1, by omega⟩, Or.inl (by simp only [edgeUp])⟩
  have hpar : parentUp n b = a := Fin.ext (by simp only [parentUp]; omega)
  have hb0 : b ≠ ⟨0, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp only at this
    omega
  have hcomm' : ∀ i j : Fin n, i ≠ j → ¬ edgeUp n i j → ¬ edgeUp n j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hne h1 h2' u hu v hv
    simp only [edgeUp] at h1 h2'
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm i j (by omega) u hu v hv
    · exact (hcomm j i (by omega) v hv u hu).symm
  have hpair' : ∀ i j : Fin n, edgeUp n i j → ¬ (i = a ∧ j = b) →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hn
    simp only [edgeUp] at hij
    refine hpair i j hij ?_
    have := j.2
    by_contra hc
    exact hn ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  exact weakCT_doublyLaced (RingEquiv.refl F) (CurtisTits.curtisTitsConclusion_spinOdd hadm hF)
    (leviConePresented_spinOdd h2 hn3) hE rfl hq h2 (doubleBondDiagram_cartanB ha hb)
    (Spin.oddDatum_steinbergExtras h2).torus_iSupIndep hsq (rootedTree_edgeUp (n := n) (by omega))
    hroot hpar hb0 hgen hcomm' hpair' (hsp a b ha hb)

end Recognition

end CFSG.ClassicalInvolution.WeakCT
