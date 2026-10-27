module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore

public section

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def LieCyclicParabolic : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y,
    IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
      J ≠ Subgroup.normalizer (T : Set Y) → J ≠ ⊤ → HasE9 Y ∨ Aut5Le Y

@[expose] def LieCyclicOrthogonal : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsOrthogonalTwo Y → HasE9 Y ∨ Aut5Le Y

section Types

variable {G : Type} [Group G] [Finite G]

theorem twoCore_le_of_hyp {M S : Subgroup G} (hA : Asc81bHyp M S) : pCoreOf 2 M ≤ S :=
  le_of_two_radical hA.twoRadical.1 hA.twoRadical.2.2
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M)
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    (inf_le_left.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))

omit [Finite G] in
theorem not_barM_le_blockPL {M S L : Subgroup G} (hQS : pCoreOf 2 M ≤ S)
    (hL : IsWeakSBlock M S L) :
    ¬ barM M L ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
  intro h
  apply hL.not_le_normalizer
  intro l hl
  have hlM : l ∈ M := hL.le hl
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈ barM M L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
  have h2 := barM_mono (inf_le_left : Subgroup.normalizer (S : Set G) ⊓ L ≤ _) (h h1)
  exact coe_mem_of_mk_mem_barM (hQS.trans Subgroup.le_normalizer) ⟨l, hlM⟩ h2

theorem aut5Le_of_nineThreeTwo (hP : LieCyclicParabolic) {M S L : Subgroup G}
    (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h2 : NineThreeTwo M S L) (hno : ¬ HasE9 ↥(barM M L)) : Aut5Le ↥(barM M L) := by
  have hq := hL.component.2.2
  have : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) := fun hsyl =>
    hS (isSylowTwoOf_inf_of_barM hL.le (twoCore_le_of_hyp hA) hA.twoRadical.isPGroup hsyl)
  obtain ⟨hcl, ⟨hJL, T, hT, hNT⟩, hO⟩ := h2
  set Lb := barM M L with hLb
  set Jb := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hJb
  set q := QuotientGroup.mk' (Subgroup.center ↥Lb) with hqdef
  have hT₁ := isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT
  have hN : ∀ z : ↥Lb,
      q z ∈ Subgroup.normalizer (((T.subgroupOf Lb).map q : Subgroup _) : Set _) →
        (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ Subgroup.normalizer (T : Set _) := fun z hz =>
    coe_mem_normalizer_of_subgroupOf hT.1 (mem_normalizer_of_mk_center_mem_normalizer hT₁ hz)
  have hSyl : IsSylowTwoOf ((T.subgroupOf Lb).map q) ⊤ :=
    isSylowTwoOf_map_top_of_surjective hT₁ (QuotientGroup.mk'_surjective _)
  have hle : Subgroup.normalizer (((T.subgroupOf Lb).map q : Subgroup _) : Set _) ≤
      (Jb.subgroupOf Lb).map q := by
    intro y hy
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr (hNT ⟨z.2, hN z hy⟩))
  have hne : (Jb.subgroupOf Lb).map q ≠
      Subgroup.normalizer (((T.subgroupOf Lb).map q : Subgroup _) : Set _) := by
    intro heq
    have hJN : Jb ≤ Subgroup.normalizer (T : Set _) := fun j hj => by
      refine hN ⟨j, hJL hj⟩ ?_
      rw [← heq]
      exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hj)
    have hTJ : T ≤ Jb := fun t ht => hNT ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
    have hTO : T ≤ barM M (S ⊓ L) := by
      rw [hO]
      exact normal_pGroup_le_pCoreOf 2 T Jb hTJ
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mpr hJN) hT.2.1
    refine hns ⟨barM_mono inf_le_right, by rw [hO]; exact pCoreOf_isPGroup 2 Jb,
      fun hd => hT.2.2 ?_⟩
    exact hd.trans (Subgroup.relIndex_dvd_of_le_left Lb hTO)
  have htop : (Jb.subgroupOf Lb).map q ≠ ⊤ := by
    intro htop
    have hZJ : Subgroup.center ↥Lb ≤ Jb.subgroupOf Lb := by
      intro z hz
      have hzc : (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
          Subgroup.centralizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨t, hT.1 ht⟩)
      exact Subgroup.mem_subgroupOf.mpr
        (hNT ⟨z.2, Subgroup.centralizer_le_normalizer _ hzc⟩)
    refine not_barM_le_blockPL (twoCore_le_of_hyp hA) hL (fun x hx => ?_)
    have hx' : q ⟨x, hx⟩ ∈ (Jb.subgroupOf Lb).map q := htop ▸ Subgroup.mem_top _
    obtain ⟨j, hj, hjx⟩ := hx'
    have hjz : j⁻¹ * ⟨x, hx⟩ ∈ Subgroup.center ↥Lb := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥Lb), MonoidHom.mem_ker, map_mul, map_inv,
        hjx, inv_mul_cancel]
    have hmem : (⟨x, hx⟩ : ↥Lb) ∈ Jb.subgroupOf Lb := by
      have := (Jb.subgroupOf Lb).mul_mem hj (hZJ hjz)
      simpa using this
    exact Subgroup.mem_subgroupOf.mp hmem
  rcases hP _ hcl _ _ hSyl hle hne htop with hE | hAut
  · exact absurd (hasE9_of_surjective (QuotientGroup.mk'_surjective _) hE) hno
  · exact aut5Le_of_center_quotient hAut

theorem five_le_of_perfect_mulEquiv_alternatingGroup {X : Type*} [Group X] [Group.IsPerfect X]
    [Nontrivial X] {m : ℕ} (e : X ≃* alternatingGroup (Fin m)) : 5 ≤ m := by
  by_contra h5
  have hsolv : Group.IsSolvable (alternatingGroup (Fin m)) :=
    alternatingGroup.isSolvable (by rw [Nat.card_fin]; omega)
  have : Group.IsSolvable X :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact Group.IsPerfect.not_isSolvable X this

theorem hasE9_of_nineThree_alt {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h : NineThreeFour M S L ∨ NineThreeFive M L ∨ NineThreeSix M S L ∨ NineThreeSeven M S L ∨
      NineThreeEight M S L) : HasE9 ↥(barM M L) := by
  have hq := hL.component.2.2
  have : Group.IsPerfect ↥(barM M L) := ⟨hq.1⟩
  have : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hq.2.toNontrivial
  have : Nontrivial ↥(barM M L) :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥(barM M L))).nontrivial
  have hquot : ∀ {N : ℕ}, 6 ≤ N →
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin N)) →
        HasE9 ↥(barM M L) := fun hN ⟨e⟩ =>
    hasE9_of_surjective (QuotientGroup.mk'_surjective _)
      (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup hN))
  have hself : ∀ {N : ℕ}, 6 ≤ N → Nonempty (↥(barM M L) ≃* alternatingGroup (Fin N)) →
      HasE9 ↥(barM M L) := fun hN ⟨e⟩ => hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup hN)
  rcases h with h4 | h5 | h6 | h7 | h8
  · obtain ⟨-, -, he, -, -⟩ := h4
    exact hquot le_rfl he
  · obtain ⟨-, he, -⟩ := h5
    exact hself (by norm_num) he
  · obtain ⟨-, n, he, -⟩ := h6
    obtain ⟨e⟩ := he
    have h5 := five_le_of_perfect_mulEquiv_alternatingGroup e
    exact hquot (by omega) ⟨e⟩
  · obtain ⟨-, n, he, -⟩ := h7
    obtain ⟨e⟩ := he
    have h5 := five_le_of_perfect_mulEquiv_alternatingGroup e
    exact hself (by omega) ⟨e⟩
  · obtain ⟨-, N, r, hN, -, -, -, -, he, -⟩ := h8
    obtain ⟨e⟩ := he
    have h5 := five_le_of_perfect_mulEquiv_alternatingGroup e
    obtain ⟨k, hk⟩ := hN
    exact hself (by omega) ⟨e⟩

theorem aut5Le_barM_of_nineThree (h93 : Asc81bNineThree) (hP : LieCyclicParabolic)
    (hO : LieCyclicOrthogonal) {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (hno : ¬ HasE9 ↥(barM M L)) : Aut5Le ↥(barM M L) := by
  rcases h93 G M S L hK hA hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact aut5Le_of_nineThreeTwo hP hA hL hS h2 hno
  · rcases hO _ h3.2.1 with hE | hAut
    · exact absurd hE hno
    · exact hAut
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inl h4)) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inl h5))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inl h6)))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inl h7))))) hno
  · exact absurd (hasE9_of_nineThree_alt hL (Or.inr (Or.inr (Or.inr (Or.inr h8))))) hno

omit [Finite G] in
theorem not_hasE9_barM {M L : Subgroup G} (h : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
    E ≤ barM M L → IsElemAbelian 3 E → Nat.card E ≤ 3) : ¬ HasE9 ↥(barM M L) := by
  rintro ⟨E, hE, hEc⟩
  have := h (E.map (barM M L).subtype) (Subgroup.map_subtype_le E) (isElemAbelian_map _ hE)
  rw [Subgroup.card_map_of_injective (barM M L).subtype_injective, hEc] at this
  norm_num at this

theorem blockCyclicFive_of_lie (h93 : Asc81bNineThree) (hP : LieCyclicParabolic)
    (hO : LieCyclicOrthogonal) {M S L : Subgroup G} (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h3 : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L → IsElemAbelian 3 E →
      Nat.card E ≤ 3)
    (V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (hVN : V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hV : IsElemAbelian 5 V) :
    (V ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex V ≤ 5 :=
  relIndex_le_five_of_aut5Le hVN hV
    (aut5Le_barM_of_nineThree h93 hP hO hK hA hL hX hS (not_hasE9_barM h3))

end Types

end CFSG.AGLEmbedding.BlockCyc
