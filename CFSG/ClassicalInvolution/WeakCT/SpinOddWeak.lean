module

public import CFSG.ClassicalInvolution.WeakCT.SpinOdd
public import CFSG.ClassicalInvolution.WeakCT.DLWeakFrame
public import CFSG.ClassicalInvolution.WeakCT.DLWeakPair

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair
  symplecticBlockPair_le_sup symplecticBlockPair_subgroupOf linearBlockStandardPair_subgroupOf
  linearBlockStandardPair_le_sup iSup_subgroupOf_eq_top)

section Recognition

theorem weakCT_spinOdd_of_pair {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F)
    {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockPair F W (U i) (U j)) :
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
  have hleaf : ∀ q : Fin n, (edgeUp n b q ∨ edgeUp n q b) → q = a := by
    intro q hq
    simp only [edgeUp] at hq
    have := q.2
    refine Fin.ext ?_
    omega
  exact weakCT_doublyLaced_leaf (RingEquiv.refl F)
    (CurtisTits.curtisTitsConclusion_spinOdd hadm hF) (leviConePresented_spinOdd h2 hn3) hE rfl hq
    h2 (doubleBondDiagram_cartanB ha hb) (Spin.oddDatum_steinbergExtras h2).torus_iSupIndep hsq
    (rootedTree_edgeUp (n := n) (by omega)) hroot hpar hb0 hleaf hgen hcomm' hpair' (hsp a b ha hb)

theorem weakCT_spinOdd_subgroup_of_pair {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F)
    {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockPair F W (U i) (U j)) :
    ∃ Ψ : spinGroup (Spin.quadOdd n F) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (CurtisTits.rankOne (Spin.oddDatum n F).rootGroup k).map Ψ = U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -, -, -, hblk⟩ := weakCT_spinOdd_of_pair hadm hF hq (X := ↥Gs)
    (fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hij hj => by
      obtain ⟨W, hW⟩ := hpair i j hij hj
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (fun i j hi hj => by
      obtain ⟨W, hW⟩ := hsp i j hi hj
      exact ⟨W.subgroupOf Gs, symplecticBlockPair_subgroupOf
        ((symplecticBlockPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro k
    rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]

end Recognition

end CFSG.ClassicalInvolution.WeakCT
