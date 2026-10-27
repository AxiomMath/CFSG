module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldTwist
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)

local instance e8PilotAlignFieldTriangleNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

section Data

@[expose] def deltaHT : Fin (Tag.rank .E8) → ℤ := ![0, 1, 1, 2, 1, 0, 0, 0]

@[expose] def deltaTS : Fin (Tag.rank .E8) → ℤ := ![0, 1, 1, 2, 1, 1, 1, 0]

@[expose] def wordDeltaHT : List (Fin (Tag.rank .E8)) := [3, 1, 2, 3]

@[expose] def wordDeltaTS : List (Fin (Tag.rank .E8)) := [3, 1, 2, 3, 4, 5]

@[expose] def wordHT : List (Fin (Tag.rank .E8)) :=
  (wordDeltaHT ++ [4] ++ wordDeltaHT.reverse) ++ [5, 0] ++ (wordDeltaHT ++ [4] ++ wordDeltaHT.reverse)

@[expose] def wordTS : List (Fin (Tag.rank .E8)) :=
  (wordDeltaTS ++ [6] ++ wordDeltaTS.reverse) ++ [7, 0] ++ (wordDeltaTS ++ [6] ++ wordDeltaTS.reverse)

theorem wordProd_wordDeltaHT :
    (coxeterSystem .E8).wordProd wordDeltaHT • (Pi.single 4 1 : Fin (Tag.rank .E8) → ℤ) =
      deltaHT := by
  simp only [wordDeltaHT, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wordDeltaTS :
    (coxeterSystem .E8).wordProd wordDeltaTS • (Pi.single 6 1 : Fin (Tag.rank .E8) → ℤ) =
      deltaTS := by
  simp only [wordDeltaTS, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wordHT_single :
    (coxeterSystem .E8).wordProd wordHT • (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) =
      Pi.single 5 1 := by
  simp only [wordHT, wordDeltaHT, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wordTS_single :
    (coxeterSystem .E8).wordProd wordTS • (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) =
      Pi.single 7 1 := by
  simp only [wordTS, wordDeltaTS, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_pair_single {a b : Fin (Tag.rank .E8)}
    (hab : (a, b) = (0, 2) ∨ (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (5, 4) ∨
      (a, b) = (5, 6)) :
    (coxeterSystem .E8).wordProd [a, b] • (Pi.single a 1 : Fin (Tag.rank .E8) → ℤ) =
      Pi.single b 1 := by
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  rcases hab with h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    exact List.ofFn_injective (by decide +kernel)

theorem isRoot_deltaHT : IsRoot .E8 deltaHT := by
  rw [← wordProd_wordDeltaHT]
  exact IsRoot.smul (isRoot_single _ 4) _

theorem isRoot_deltaTS : IsRoot .E8 deltaTS := by
  rw [← wordProd_wordDeltaTS]
  exact IsRoot.smul (isRoot_single _ 6) _

theorem deltaHT_mem_orthRoots {N : E8Neighbour} (hN : N = .high ∨ N = .two) :
    deltaHT ∈ orthRoots N.root ∧ -deltaHT ∈ orthRoots N.root := by
  have h0 : iform N.root deltaHT = 0 := by rcases hN with rfl | rfl <;> decide +kernel
  exact ⟨⟨isRoot_deltaHT, h0⟩, ⟨IsRoot.neg isRoot_deltaHT, by rw [iform_neg_right_E8, h0, neg_zero]⟩⟩

theorem deltaTS_mem_orthRoots {N : E8Neighbour} (hN : N = .two ∨ N = .six) :
    deltaTS ∈ orthRoots N.root ∧ -deltaTS ∈ orthRoots N.root := by
  have h0 : iform N.root deltaTS = 0 := by rcases hN with rfl | rfl <;> decide +kernel
  exact ⟨⟨isRoot_deltaTS, h0⟩, ⟨IsRoot.neg isRoot_deltaTS, by rw [iform_neg_right_E8, h0, neg_zero]⟩⟩

end Data

section Membership

variable {k : Type} [Field k]

theorem wordElt_mem_rootSpan_of_nodes {N : E8Neighbour} {ω : List (Fin (Tag.rank .E8))}
    (h : ∀ i ∈ ω, i ∈ N.nodes) : wordElt k ω ∈ rootSpan .E8 k (orthRoots N.root) :=
  wordElt_mem_rootSpan fun i hi => ⟨single_mem_orthRoots (h i hi), neg_single_mem_orthRoots (h i hi)⟩

variable [CharP k 2]

theorem wordElt_wordHT_mem {N : E8Neighbour} (hN : N = .high ∨ N = .two) :
    wordElt k wordHT ∈ rootSpan .E8 k (orthRoots N.root) := by
  have hδ := deltaHT_mem_orthRoots hN
  have hA : wordElt k (wordDeltaHT ++ [4] ++ wordDeltaHT.reverse) ∈
      rootSpan .E8 k (orthRoots N.root) :=
    wordElt_reflWord_mem_rootSpan wordDeltaHT 4 (by rw [wordProd_wordDeltaHT]; exact hδ.1)
      (by rw [wordProd_wordDeltaHT]; exact hδ.2)
  have hB : wordElt k [5, 0] ∈ rootSpan .E8 k (orthRoots N.root) :=
    wordElt_mem_rootSpan_of_nodes fun i hi => by
      rcases hN with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
        rcases hi with rfl | rfl <;> decide
  rw [wordHT, wordElt_append, wordElt_append]
  exact mul_mem (mul_mem hA hB) hA

theorem wordElt_wordTS_mem {N : E8Neighbour} (hN : N = .two ∨ N = .six) :
    wordElt k wordTS ∈ rootSpan .E8 k (orthRoots N.root) := by
  have hδ := deltaTS_mem_orthRoots hN
  have hA : wordElt k (wordDeltaTS ++ [6] ++ wordDeltaTS.reverse) ∈
      rootSpan .E8 k (orthRoots N.root) :=
    wordElt_reflWord_mem_rootSpan wordDeltaTS 6 (by rw [wordProd_wordDeltaTS]; exact hδ.1)
      (by rw [wordProd_wordDeltaTS]; exact hδ.2)
  have hB : wordElt k [7, 0] ∈ rootSpan .E8 k (orthRoots N.root) :=
    wordElt_mem_rootSpan_of_nodes fun i hi => by
      rcases hN with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
        rcases hi with rfl | rfl <;> decide
  rw [wordTS, wordElt_append, wordElt_append]
  exact mul_mem (mul_mem hA hB) hA

end Membership

section Overlaps

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 (fixSubfield σ)}

@[expose] def FieldNeighbourIso.TwistOn {N N' : E8Neighbour} (h : FieldNeighbourIso σ e N)
    (h' : FieldNeighbourIso σ e N') (ρ : K ≃+* K) (S : Finset (Fin (Tag.rank .E8))) : Prop :=
  ∀ j ∈ S, h.TwistAt h' ρ (Pi.single j 1) ∧ h.TwistAt h' ρ (-Pi.single j 1)

variable [CharP K 2]

theorem FieldNeighbourIso.TwistAt.transfer_single {N N' : E8Neighbour}
    {h : FieldNeighbourIso σ e N} {h' : FieldNeighbourIso σ e N'} {ρ : K ≃+* K}
    {a b : Fin (Tag.rank .E8)} (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes)
    (hT : h.TwistAt h' ρ (Pi.single a 1) ∧ h.TwistAt h' ρ (-Pi.single a 1))
    (ω : List (Fin (Tag.rank .E8)))
    (hω : (coxeterSystem .E8).wordProd ω • (Pi.single a 1 : Fin (Tag.rank .E8) → ℤ) =
      Pi.single b 1)
    (hωN : wordElt (fixSubfield σ) ω ∈ rootSpan .E8 (fixSubfield σ) (orthRoots N.root))
    (hωN' : wordElt (fixSubfield σ) ω ∈ rootSpan .E8 (fixSubfield σ) (orthRoots N'.root)) :
    h.TwistAt h' ρ (Pi.single b 1) ∧ h.TwistAt h' ρ (-Pi.single b 1) := by
  refine ⟨?_, ?_⟩
  · have h1 := hT.1.conj_word (single_mem_orthRoots ha) (single_mem_orthRoots ha') ω hωN hωN'
    rwa [hω] at h1
  · have h1 := hT.2.conj_word (neg_single_mem_orthRoots ha) (neg_single_mem_orthRoots ha') ω hωN
      hωN'
    rwa [smul_neg, hω] at h1

theorem FieldNeighbourIso.TwistAt.transfer_pair {N N' : E8Neighbour}
    {h : FieldNeighbourIso σ e N} {h' : FieldNeighbourIso σ e N'} {ρ : K ≃+* K}
    {a b : Fin (Tag.rank .E8)} (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes) (hb : b ∈ N.nodes)
    (hb' : b ∈ N'.nodes)
    (hab : (a, b) = (0, 2) ∨ (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (5, 4) ∨
      (a, b) = (5, 6))
    (hT : h.TwistAt h' ρ (Pi.single a 1) ∧ h.TwistAt h' ρ (-Pi.single a 1)) :
    h.TwistAt h' ρ (Pi.single b 1) ∧ h.TwistAt h' ρ (-Pi.single b 1) := by
  have hmem : ∀ M : E8Neighbour, a ∈ M.nodes → b ∈ M.nodes →
      wordElt (fixSubfield σ) [a, b] ∈ rootSpan .E8 (fixSubfield σ) (orthRoots M.root) :=
    fun M haM hbM => wordElt_mem_rootSpan_of_nodes fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      exacts [haM, hbM]
  exact FieldNeighbourIso.TwistAt.transfer_single ha ha' hT [a, b] (wordProd_pair_single hab)
    (hmem N ha hb) (hmem N' ha' hb')

variable [Finite K] [Finite G]

theorem exists_twistOn_high_two (hX : FieldNeighbourIso σ e .high)
    (hY : FieldNeighbourIso σ e .two) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ hX.TwistOn hY ρ {0, 2, 4, 5, 6} := by
  obtain ⟨ρ, hρ, h0p, h0n⟩ := hX.exists_twistAt_single hY hq (j := 0) (by decide) (by decide)
  have h0 := And.intro h0p h0n
  have h2 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h5 := FieldNeighbourIso.TwistAt.transfer_single (by decide) (by decide) h0 wordHT
    wordProd_wordHT_single (wordElt_wordHT_mem (Or.inl rfl)) (wordElt_wordHT_mem (Or.inr rfl))
  have h4 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h5
  have h6 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h5
  refine ⟨ρ, hρ, fun j hj => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h2, h4, h5, h6]

theorem exists_twistOn_high_six (hX : FieldNeighbourIso σ e .high)
    (hZ : FieldNeighbourIso σ e .six) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ hX.TwistOn hZ ρ {0, 1, 2, 3} := by
  obtain ⟨ρ, hρ, h0p, h0n⟩ := hX.exists_twistAt_single hZ hq (j := 0) (by decide) (by decide)
  have h0 := And.intro h0p h0n
  have h2 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h3 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inl rfl)) h2
  have h1 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inl rfl))) h3
  refine ⟨ρ, hρ, fun j hj => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem exists_twistOn_two_six (hY : FieldNeighbourIso σ e .two)
    (hZ : FieldNeighbourIso σ e .six) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ hY.TwistOn hZ ρ {0, 2, 7} := by
  obtain ⟨ρ, hρ, h0p, h0n⟩ := hY.exists_twistAt_single hZ hq (j := 0) (by decide) (by decide)
  have h0 := And.intro h0p h0n
  have h2 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h7 := FieldNeighbourIso.TwistAt.transfer_single (by decide) (by decide) h0 wordTS
    wordProd_wordTS_single (wordElt_wordTS_mem (Or.inl rfl)) (wordElt_wordTS_mem (Or.inr rfl))
  refine ⟨ρ, hρ, fun j hj => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  exacts [h0, h2, h7]

omit [Finite G]
  [Finite K] [CharP K 2]
  in
theorem twist_cocycle (hX : FieldNeighbourIso σ e .high) (hY : FieldNeighbourIso σ e .two)
    (hZ : FieldNeighbourIso σ e .six) {ρht ρts ρhs : K ≃+* K}
    (hht : hX.TwistAt hY ρht (Pi.single 0 1)) (hts : hY.TwistAt hZ ρts (Pi.single 0 1))
    (hhs : hX.TwistAt hZ ρhs (Pi.single 0 1)) : ρhs = ρht.trans ρts := by
  have hγX : (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) ∈ orthRoots E8Neighbour.high.root :=
    single_mem_orthRoots (by decide)
  have hγY : (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) ∈ orthRoots E8Neighbour.two.root :=
    single_mem_orthRoots (by decide)
  have hγZ : (Pi.single 0 1 : Fin (Tag.rank .E8) → ℤ) ∈ orthRoots E8Neighbour.six.root :=
    single_mem_orthRoots (by decide)
  ext a
  have h4 : ((hZ.Φ (leviRootElt _ hγZ (ρhs a)) : neighbourCore e .six) : G) =
      hZ.Φ (leviRootElt _ hγZ (ρts (ρht a))) := by
    rw [← hhs hγX hγZ a, hht hγX hγY a, hts hγY hγZ (ρht a)]
  have h5 := hZ.Φ.injective (Subtype.ext h4)
  have h6 := congrArg (fun x : E8Neighbour.six.levi K =>
    ((x : adjointGroup .E8 K) : ModGL .E8 K)) h5
  simp only [coe_leviRootElt] at h6
  rw [RingEquiv.trans_apply]
  exact pinnedX_injective (τ := .E8) (R := K) _ h6

theorem exists_aligned_fieldNeighbourIso (hX : FieldNeighbourIso σ e .high)
    (hY : FieldNeighbourIso σ e .two) (hZ : FieldNeighbourIso σ e .six)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ (ρt ρs : K ≃+* K) (hρt : ∀ c : fixSubfield σ, ρt c = c)
      (hρs : ∀ c : fixSubfield σ, ρs c = c),
      hX.TwistOn (hY.twist ρt hρt) 1 {0, 2, 4, 5, 6} ∧
        hX.TwistOn (hZ.twist ρs hρs) 1 {0, 1, 2, 3} ∧
        (hY.twist ρt hρt).TwistOn (hZ.twist ρs hρs) 1 {0, 2, 7} := by
  obtain ⟨ρht, hρht, hTht⟩ := exists_twistOn_high_two hX hY hq
  obtain ⟨ρhs, hρhs, hThs⟩ := exists_twistOn_high_six hX hZ hq
  obtain ⟨ρts, -, hTts⟩ := exists_twistOn_two_six hY hZ hq
  have hcoc := twist_cocycle hX hY hZ (hTht 0 (by decide)).1 (hTts 0 (by decide)).1
    (hThs 0 (by decide)).1
  refine ⟨ρht, ρhs, hρht, hρhs, fun j hj => ⟨(hTht j hj).1.twist hρht, (hTht j hj).2.twist hρht⟩,
    fun j hj => ⟨(hThs j hj).1.twist hρhs, (hThs j hj).2.twist hρhs⟩, fun j hj => ?_⟩
  have key : ∀ {γ : Fin (Tag.rank .E8) → ℤ}, hY.TwistAt hZ ρts γ →
      (hY.twist ρht hρht).TwistAt (hZ.twist ρhs hρhs) 1 γ := by
    intro γ hT hγ hγ' a
    rw [FieldNeighbourIso.twist_apply, FieldNeighbourIso.twist_apply,
      leviEntrywiseEquiv_leviRootElt, leviEntrywiseEquiv_leviRootElt, RingAut.one_apply, hcoc,
      RingEquiv.trans_apply]
    exact hT hγ hγ' (ρht a)
  exact ⟨key (hTts j hj).1, key (hTts j hj).2⟩

omit [Finite G]
  [Finite K] [CharP K 2]
  in
theorem FieldNeighbourIso.eq_on_leviPiece {N N' : E8Neighbour} (h : FieldNeighbourIso σ e N)
    (h' : FieldNeighbourIso σ e N') {J : Finset (Fin (Tag.rank .E8))} (hJ : J ⊆ N.nodes)
    (hJ' : J ⊆ N'.nodes) (hT : h.TwistOn h' 1 J) {x : N.levi K} {x' : N'.levi K}
    (hxx' : (x : adjointGroup .E8 K) = x') (hx : x ∈ leviPiece K N J) :
    ((h.Φ x : neighbourCore e N) : G) = h'.Φ x' := by
  set I : Subgroup (adjointGroup .E8 K) := N.levi K ⊓ N'.levi K with hI
  set f : I →* G := (neighbourCore e N).subtype.comp
    (h.Φ.toMonoidHom.comp (Subgroup.inclusion inf_le_left)) with hf
  set f' : I →* G := (neighbourCore e N').subtype.comp
    (h'.Φ.toMonoidHom.comp (Subgroup.inclusion inf_le_right)) with hf'
  set H : Subgroup (ModGL .E8 K) :=
    ((MonoidHom.eqLocus f f').map I.subtype).map (adjointGroup .E8 K).subtype with hH
  have hgen : rootSpan .E8 K (amalgamRoots J) ≤ H := by
    refine iSup₂_le fun γ hγ => (closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    obtain ⟨j, hj, hγj⟩ := hγ
    have hγN : γ ∈ orthRoots N.root := by
      rcases hγj with rfl | rfl
      exacts [single_mem_orthRoots (hJ hj), neg_single_mem_orthRoots (hJ hj)]
    have hγN' : γ ∈ orthRoots N'.root := by
      rcases hγj with rfl | rfl
      exacts [single_mem_orthRoots (hJ' hj), neg_single_mem_orthRoots (hJ' hj)]
    have hTγ : h.TwistAt h' 1 γ := by
      rcases hγj with rfl | rfl
      exacts [(hT j hj).1, (hT j hj).2]
    refine ⟨⟨pinnedX .E8 K γ c, pinnedX_mem_adjointGroup γ c⟩,
      ⟨⟨_, ⟨(leviRootElt N hγN c).2, (leviRootElt N' hγN' c).2⟩⟩, ?_, rfl⟩, rfl⟩
    exact hTγ hγN hγN' c
  have hxH : ((x : adjointGroup .E8 K) : ModGL .E8 K) ∈ H := hgen (mem_leviPiece.1 hx)
  obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hxH
  have hyx' : ((y : adjointGroup .E8 K)) = x := Subtype.ext hyx
  have h1 : x = Subgroup.inclusion inf_le_left y := Subtype.ext hyx'.symm
  have h2 : x' = Subgroup.inclusion inf_le_right y := Subtype.ext (hxx'.symm.trans hyx'.symm)
  rw [h1, h2]
  exact hy

theorem exists_aligned_fieldNeighbourIso_eq_on_leviPiece (hX : FieldNeighbourIso σ e .high)
    (hY : FieldNeighbourIso σ e .two) (hZ : FieldNeighbourIso σ e .six)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ (hY' : FieldNeighbourIso σ e .two) (hZ' : FieldNeighbourIso σ e .six),
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 2, 4, 5, 6} →
        ∀ (x : E8Neighbour.high.levi K) (x' : E8Neighbour.two.levi K),
          (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .high J →
            ((hX.Φ x : neighbourCore e .high) : G) = hY'.Φ x') ∧
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 1, 2, 3} →
        ∀ (x : E8Neighbour.high.levi K) (x' : E8Neighbour.six.levi K),
          (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .high J →
            ((hX.Φ x : neighbourCore e .high) : G) = hZ'.Φ x') ∧
      (∀ {J : Finset (Fin (Tag.rank .E8))}, J ⊆ {0, 2, 7} →
        ∀ (x : E8Neighbour.two.levi K) (x' : E8Neighbour.six.levi K),
          (x : adjointGroup .E8 K) = x' → x ∈ leviPiece K .two J →
            ((hY'.Φ x : neighbourCore e .two) : G) = hZ'.Φ x') := by
  obtain ⟨ρt, ρs, hρt, hρs, h1, h2, h3⟩ := exists_aligned_fieldNeighbourIso hX hY hZ hq
  refine ⟨hY.twist ρt hρt, hZ.twist ρs hρs, fun hJ x x' hxx' hx => ?_,
    fun hJ x x' hxx' hx => ?_, fun hJ x x' hxx' hx => ?_⟩
  · exact hX.eq_on_leviPiece _ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h1 j (hJ hj)) hxx' hx
  · exact hX.eq_on_leviPiece _ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h2 j (hJ hj)) hxx' hx
  · exact (hY.twist ρt hρt).eq_on_leviPiece _ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h3 j (hJ hj)) hxx' hx

end Overlaps

end CFSG.SeitzReduction.E8Pilot
