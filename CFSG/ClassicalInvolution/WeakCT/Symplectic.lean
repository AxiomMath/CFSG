module

public import CFSG.ClassicalInvolution.WeakCT.DLDiagrams
public import CFSG.Timmesfeld.RankTwo.LeviData
public import CFSG.LieType.CurtisTits.Symplectic
public import CFSG.ClassicalInvolution.WeakCT.DoublyLaced

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)

section Diagram

theorem doubleBondDiagram_cartanC {n : ℕ} (hn : 3 ≤ n) {a b : Fin n} (ha : a.val + 1 = n)
    (hb : b.val + 2 = n) : DoubleBondDiagram (Symplectic.cartanC n) (edgeDown n) a b where
  adj_ab := by simp only [edgeDown]; omega
  cartan_ba := by
    simp only [Symplectic.cartanC, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  cartan_ab := by
    simp only [Symplectic.cartanC, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  cartan_adj := by
    intro i j hij hn'
    have hn'' : ¬ (i.val = a.val ∧ j.val = b.val) := fun h => hn' ⟨Fin.ext h.1, Fin.ext h.2⟩
    simp only [edgeDown] at hij
    simp only [Symplectic.cartanC, Matrix.of_apply, Fin.ext_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
  cartan_nadj := by
    intro i j hne hij hji
    simp only [edgeDown] at hij hji
    simp only [Symplectic.cartanC, Matrix.of_apply, Fin.ext_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
  neighbour := by
    intro i j hij hn'
    have hn'' : ¬ (i.val = a.val ∧ j.val = b.val) := fun h => hn' ⟨Fin.ext h.1, Fin.ext h.2⟩
    simp only [edgeDown] at hij
    by_cases hj : 0 < j.val
    · refine ⟨⟨j.val - 1, by have := j.2; omega⟩, ?_⟩
      simp only [Symplectic.cartanC, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    · have hk : i.val + 1 < n := by omega
      refine ⟨⟨i.val + 1, hk⟩, ?_⟩
      simp only [Symplectic.cartanC, Matrix.of_apply, Fin.ext_iff, true_or, ↓reduceIte]
      split_ifs <;> omega

end Diagram

section Recognition

theorem weylElement_sp_one {n : ℕ} {F : Type} [Field F] (k : Fin n) :
    Steinberg.weylElement (Steinberg.Sp.x n F) k 1 = Symplectic.weylRep n F k := by
  have h := Steinberg.Sp.weylElement_eq (n := n) (F := F) k 1
  have hc : Symplectic.corootVec n F k 1 = 1 := by
    funext a
    simp [Symplectic.corootVec]
  rw [hc, map_one, map_one, one_mul] at h
  exact h

theorem weakCT_symplectic {n p f : ℕ} (hadm : StatedLieAdmissible .PSp n p f) (hn : 3 ≤ n)
    (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ Nat.card F) {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      IsQuasisimple X ∧ Subgroup.center X = (Subgroup.center (StatedSp n F)).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .PSp n p f ∧
      ∀ k, (CurtisTits.rankOne (Symplectic.rootDatum n F).rootGroup k).map Ψ = U k := by
  have hp := hadm.1
  have hf := hadm.2.1
  have h2 : (2 : F) ≠ 0 := by
    have hqc : (ringChar F).Prime := by
      rw [ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
      exact hp
    rw [Ne, ClassicalGroups.Orthogonal.two_eq_zero_iff_ringChar_eq_two hqc,
      ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hF]
    exact hp2
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Symplectic.rootDatum n F).isFiniteType
    (Dv := (Symplectic.rootDatum n F).divisible) rfl
  have hE := Steinberg.Sp.chevalleyExtras (by omega : 2 ≤ n) O Steinberg.Sp.commC
    (Steinberg.Sp.commutatorFormula O)
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a.val + 1 = n := ⟨⟨n - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin n, b.val + 2 = n := ⟨⟨n - 2, by omega⟩, by simp only; omega⟩
  have hsq : ∀ k : Fin n,
      Steinberg.weylElement (Steinberg.Sp.x n F) k 1 ^ 2 ∈ Symplectic.torus n F k := by
    intro k
    rw [weylElement_sp_one]
    exact (Symplectic.isCTGroupDatum n F).sq_mem k
  have hroot : ∃ c : Fin n, edgeDown n ⟨n - 1, by omega⟩ c ∨ edgeDown n c ⟨n - 1, by omega⟩ :=
    ⟨⟨n - 2, by omega⟩, Or.inl (by simp only [edgeDown]; omega)⟩
  have hpar : parentDown n b = a := Fin.ext (by simp only [parentDown]; omega)
  have hb0 : b ≠ ⟨n - 1, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp only at this
    omega
  have hcomm' : ∀ i j : Fin n, i ≠ j → ¬ edgeDown n i j → ¬ edgeDown n j i →
      ∀ u ∈ U i, ∀ v ∈ U j, u * v = v * u := by
    intro i j hne h1 h2' u hu v hv
    simp only [edgeDown] at h1 h2'
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : i.val ≠ j.val) with hlt | hgt
    · exact hcomm i j (by omega) u hu v hv
    · exact (hcomm j i (by omega) v hv u hu).symm
  have hpair' : ∀ i j : Fin n, edgeDown n i j → ¬ (i = a ∧ j = b) →
      ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    intro i j hij hn'
    simp only [edgeDown] at hij
    obtain ⟨W, hW⟩ := hpair j i hij (by
      have := i.2
      by_contra hc
      exact hn' ⟨Fin.ext (by omega), Fin.ext (by omega)⟩)
    exact ⟨W, hW.symm⟩
  exact weakCT_doublyLaced (RingEquiv.refl F)
    (CurtisTits.curtisTitsConclusion_symplectic hadm hF hn)
    (leviConePresented_symplectic n F) hE rfl hq h2 (doubleBondDiagram_cartanC hn ha hb)
    (Symplectic.steinbergExtras n F).torus_iSupIndep hsq (rootedTree_edgeDown (n := n) (by omega))
    hroot hpar hb0 hgen hcomm' hpair' (hsp a b ha hb)

end Recognition

end CFSG.ClassicalInvolution.WeakCT
