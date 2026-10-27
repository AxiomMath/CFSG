module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.CfgBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InExclusive

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

section Basic

variable {G : Type*} [Group G]

theorem mem_normalizer_blockU_of {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : g ∈ Subgroup.normalizer (blockU L : Set G) := by
  rw [← conjR_eq_self_iff]
  have hQ : conjR (blockQ L) g = blockQ L := by
    unfold blockQ
    rw [← conjR_pCoreOf, conjR_eq_of_mem_normalizer hg]
  have hL : conjR L g = L := conjR_eq_of_mem_normalizer hg
  have : conjR (⁅blockQ L, L⁆) g = ⁅conjR (blockQ L) g, conjR L g⁆ := by
    simp only [conjR_def]
    exact Subgroup.map_commutator _ _ _
  unfold blockU
  rw [this, hQ, hL]

theorem conjJoin_eq_of_normalizes {S X : Subgroup G}
    (hS : ∀ s ∈ S, s ∈ Subgroup.normalizer (X : Set G)) : conjJoin S X = X := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    rintro _ ⟨x, hx, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 (hS s s.2) x).1 hx
    simpa using this
  · have h1 : X.map (MulAut.conj ((1 : S) : G)).toMonoidHom ≤ conjJoin S X :=
      le_iSup (fun s : S => X.map (MulAut.conj (s : G)).toMonoidHom) 1
    intro x hx
    exact h1 ⟨x, hx, by simp⟩

end Basic

structure Lemma248Inputs : Prop where
  l246 : Lemma246Chi

section Data

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

structure Lin2Data (T M H S L : Subgroup G) (n : ℕ) : Prop where
  index_two : S.relIndex T = 2
  jT : thompsonJ S = thompsonJ T
  pCore_eq : pCoreOf 2 L = blockU L
  Q_eq : pCoreOf 2 H = blockD S L ⊔ blockU L
  D₀_elem : IsElemAbelian 2 (blockD S L)
  D₀_eq : blockD S L = S ⊓ Subgroup.centralizer (L : Set G)
  Q_max : IsMaxElemAbelian S (pCoreOf 2 H)
  D₀_inf : ∀ x ∈ T, x ∉ S → blockD S L ⊓ conjR (blockD S L) x = ⊥
  R_eq : ∀ x ∈ T, x ∉ S → thompsonJ S = blockD S L ⊔ blockU L ⊔ conjR (blockU L) x
  A_eq : ∀ x ∈ T, x ∉ S → ∀ A : Subgroup G,
    IsMaxElemAbelian S A ↔ A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x
  D₀_bound : Nat.card (blockD S L) ≤ 2 ^ n
  Q_cent : pCoreOf 2 H = thompsonJ S ⊓ Subgroup.centralizer (blockU L : Set G)
  RQ_index : (pCoreOf 2 H).relIndex (thompsonJ S) = 2 ^ n
  W_data : ∃ W : Subgroup G, ⁅blockU L, thompsonJ S⁆ = W ∧ W.relIndex (blockU L) = 2 ^ n ∧
    ∀ y ∈ thompsonJ S, y ∉ pCoreOf 2 H → ∀ u ∈ blockU L, (u ∈ W ↔ u * y = y * u)
  R_norm : thompsonJ S ≤ Subgroup.normalizer (L : Set G)
  R_sylow : IsSylowTwoOf (thompsonJ S) (L ⊔ thompsonJ S)
  norm_Q : Subgroup.normalizer (pCoreOf 2 H : Set G) ≤ Subgroup.normalizer (L : Set G)
  baum_eq : baum S = thompsonJ S

theorem Lemma248Inputs.data
    (E : Lemma248Inputs) (h : Lin2Cfg G T M H S L n D) :
    Lin2Data T M H S L n := by
  have hlin : ∃ m : ℕ, 1 < m ∧ IsLin2Type L m := ⟨n, h.one_lt, h.lin2⟩
  have h3 : ¬ IsAltType L 3 := lin2_not_alt h.one_lt h.lin2 (Or.inl rfl)
  have h5 : ¬ IsAltType L 5 := lin2_not_alt h.one_lt h.lin2 (Or.inr rfl)
  have hblU : conjJoin S (blockU L) = blockU L :=
    conjJoin_eq_of_normalizes fun s hs => mem_normalizer_blockU_of (h.S_le_normalizer hs)
  obtain ⟨-, hc3, -, -, hc6⟩ :=
    C56.c61_lin2 h.cs h.single h.one_lt h.lin2 h5
  have hT2 : S.relIndex T = 2 ∧ thompsonJ S = thompsonJ T := by
    rcases hc6 with ⟨h1, h2, -⟩ | ⟨h1, -⟩ | ⟨hh, -⟩
    · exact ⟨h1, h2⟩
    · exact absurd h1 h3
    · rcases hh with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 h5
      · exact absurd h1 h3
  have hc56 : C56_7Concl S H L T :=
    C56.c56_7_lin2 h.cs h.single h.one_lt h.lin2 h5 h.S_le_T le_rfl hT2.1
  obtain ⟨c1, c2, c3, c4, c5, c6, hx⟩ := hc56
  rw [h.single] at c1
  have hUO : pCoreOf 2 L = blockU L := by
    have : blockU0 S L = blockU L := hblU
    rw [← c1, this]
  have hbd : blockD S L = S ⊓ Subgroup.centralizer (L : Set G) := by
    unfold blockD
    rw [h.single]
  have hbound : Nat.card (blockD S L) ≤ 2 ^ n := by
    have := (hc3 h.single (Or.inl hlin)).2.2 n h.one_lt h.lin2
    exact this
  obtain ⟨hQc, hQi, W, hW1, hW2, hW3⟩ :=
    C56.c56_single_data naturalModuleStructure h.cs h.single h.one_lt h.lin2
  have hJ : baum S = thompsonJ S := c6
  obtain ⟨hRN, hRS⟩ := C56.baumann_single h.cs.minParabolic h.cs.block (Or.inl hlin)
    h.cs.thompson (C56.H_eq h.cs h.single) (C56.S_le_normalizer h.single)
  have hRN' : thompsonJ S ≤ Subgroup.normalizer (L : Set G) := hJ ▸ hRN
  refine ⟨hT2.1, hT2.2, hUO, ?_, ?_, hbd, c5, ?_, ?_, ?_, hbound, ?_, ?_, ⟨W, ?_, ?_, ?_⟩, hRN',
    ?_, ?_, hJ⟩
  · have : blockU0 S L = blockU L := hblU
    rw [c4, c3, this]
  · rw [← c3]; exact c2
  · intro x hx' hxS
    have := (hx x hx' hxS).1
    rwa [c3] at this
  · intro x hx' hxS
    have := (hx x hx' hxS).2.1
    rw [c3] at this
    have e : blockU0 S L = blockU L := hblU
    rw [e] at this
    rw [← hJ, this]
  · intro x hx' hxS A
    exact (hx x hx' hxS).2.2.1 h.single (Or.inr hlin) A
  · rw [← hJ]; exact hQc
  · rw [← hJ]; exact hQi
  · rw [← hJ]; exact hW1
  · exact hW2
  · intro y hy hyQ u hu
    rw [← hJ] at hy
    exact hW3 y hy hyQ u hu
  · rw [← hJ]; exact hRS
  · exact E.l246 G T M H S L h.cs h.single (Or.inl hlin)

end Data

end CFSG.QuasithinUnique.Lin2
