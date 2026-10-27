module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignFieldTwist
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore)

local instance e7PilotAlignFieldTriangleNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Data

@[expose] def beta1 : Fin (Tag.rank .E7) → ℤ := ![0, 0, 1, 1, 1, 0, 0]

@[expose] def deltaHF : Fin (Tag.rank .E7) → ℤ := ![0, 0, 1, 1, 1, 1, 0]

@[expose] def deltaSF : Fin (Tag.rank .E7) → ℤ := ![1, 0, 1, 1, 1, 0, 0]

@[expose] def wordDeltaHF : List (Fin (Tag.rank .E7)) := [2, 3, 4]

@[expose] def wordDeltaSF : List (Fin (Tag.rank .E7)) := [0, 2, 3]

@[expose] def wordHS : List (Fin (Tag.rank .E7)) := [4, 3]

@[expose] def wordHF : List (Fin (Tag.rank .E7)) := wordDeltaHF ++ [5] ++ wordDeltaHF.reverse

@[expose] def wordSF : List (Fin (Tag.rank .E7)) := wordDeltaSF ++ [4] ++ wordDeltaSF.reverse

theorem wordProd_wordDeltaHF :
    (coxeterSystem .E7).wordProd wordDeltaHF • (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) =
      deltaHF := by
  simp only [wordDeltaHF, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wordDeltaSF :
    (coxeterSystem .E7).wordProd wordDeltaSF • (Pi.single 4 1 : Fin (Tag.rank .E7) → ℤ) =
      deltaSF := by
  simp only [wordDeltaSF, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wordHS_single :
    (coxeterSystem .E7).wordProd wordHS • (Pi.single 2 1 : Fin (Tag.rank .E7) → ℤ) = beta1 := by
  simp only [wordHS, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
    mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wordHF_neg_single :
    (coxeterSystem .E7).wordProd wordHF • (-Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) = beta1 := by
  simp only [wordHF, wordDeltaHF, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wordSF_neg_single :
    (coxeterSystem .E7).wordProd wordSF • (-Pi.single 0 1 : Fin (Tag.rank .E7) → ℤ) = beta1 := by
  simp only [wordSF, wordDeltaSF, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_pair_single {a b : Fin (Tag.rank .E7)}
    (hab : (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (3, 4) ∨ (a, b) = (5, 6)) :
    (coxeterSystem .E7).wordProd [a, b] • (Pi.single a 1 : Fin (Tag.rank .E7) → ℤ) =
      Pi.single b 1 := by
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
    simple_smul]
  rcases hab with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    exact List.ofFn_injective (by decide +kernel)

theorem isRoot_deltaHF :
    IsRoot .E7 deltaHF := by
  rw [← wordProd_wordDeltaHF]
  exact IsRoot.smul (isRoot_single _ 5) _

theorem isRoot_deltaSF :
    IsRoot .E7 deltaSF := by
  rw [← wordProd_wordDeltaSF]
  exact IsRoot.smul (isRoot_single _ 4) _

theorem isRoot_beta1 :
    IsRoot .E7 beta1 := by
  rw [← wordProd_wordHS_single]
  exact IsRoot.smul (isRoot_single _ 2) _

theorem deltaHF_mem_orthRoots
    {N : E7Neighbour} (hN : N = .high ∨ N = .four) :
    deltaHF ∈ orthRoots N.root ∧ -deltaHF ∈ orthRoots N.root := by
  have h0 : iform N.root deltaHF = 0 := by rcases hN with rfl | rfl <;> decide +kernel
  exact ⟨⟨isRoot_deltaHF, h0⟩,
    ⟨IsRoot.neg isRoot_deltaHF, by rw [iform_neg_right_E7, h0, neg_zero]⟩⟩

theorem deltaSF_mem_orthRoots
    {N : E7Neighbour} (hN : N = .seven ∨ N = .four) :
    deltaSF ∈ orthRoots N.root ∧ -deltaSF ∈ orthRoots N.root := by
  have h0 : iform N.root deltaSF = 0 := by rcases hN with rfl | rfl <;> decide +kernel
  exact ⟨⟨isRoot_deltaSF, h0⟩,
    ⟨IsRoot.neg isRoot_deltaSF, by rw [iform_neg_right_E7, h0, neg_zero]⟩⟩

theorem beta1_mem_orthRoots
    (N : E7Neighbour) : beta1 ∈ orthRoots N.root := by
  refine ⟨isRoot_beta1, ?_⟩
  cases N <;> decide +kernel

end Data

section Membership

variable {k : Type} [Field k]

theorem wordElt_mem_rootSpan_of_nodes {N : E7Neighbour} {ω : List (Fin (Tag.rank .E7))}
    (h : ∀ i ∈ ω, i ∈ N.nodes) : wordElt k ω ∈ rootSpan .E7 k (orthRoots N.root) :=
  wordElt_mem_rootSpan fun i hi =>
    ⟨single_mem_orthRoots (h i hi), neg_single_mem_orthRoots (h i hi)⟩

theorem wordElt_wordHS_mem {N : E7Neighbour} (hN : N = .high ∨ N = .seven) :
    wordElt k wordHS ∈ rootSpan .E7 k (orthRoots N.root) :=
  wordElt_mem_rootSpan_of_nodes fun i hi => by
    rcases hN with rfl | rfl <;> simp only [wordHS, List.mem_cons, List.not_mem_nil, or_false]
      at hi <;> rcases hi with rfl | rfl <;> decide

variable [CharP k 2]

theorem wordElt_wordHF_mem {N : E7Neighbour} (hN : N = .high ∨ N = .four) :
    wordElt k wordHF ∈ rootSpan .E7 k (orthRoots N.root) := by
  have hδ := deltaHF_mem_orthRoots hN
  exact wordElt_reflWord_mem_rootSpan wordDeltaHF 5 (by rw [wordProd_wordDeltaHF]; exact hδ.1)
    (by rw [wordProd_wordDeltaHF]; exact hδ.2)

theorem wordElt_wordSF_mem {N : E7Neighbour} (hN : N = .seven ∨ N = .four) :
    wordElt k wordSF ∈ rootSpan .E7 k (orthRoots N.root) := by
  have hδ := deltaSF_mem_orthRoots hN
  exact wordElt_reflWord_mem_rootSpan wordDeltaSF 4 (by rw [wordProd_wordDeltaSF]; exact hδ.1)
    (by rw [wordProd_wordDeltaSF]; exact hδ.2)

end Membership

section Overlaps

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

@[expose] def FieldNeighbourIso.TwistOn {N N' : E7Neighbour} (h : FieldNeighbourIso σ e N)
    (h' : FieldNeighbourIso σ e N') (ρ : K ≃+* K) (S : Finset (Fin (Tag.rank .E7))) : Prop :=
  ∀ j ∈ S, h.TwistAt h' ρ (Pi.single j 1) ∧ h.TwistAt h' ρ (-Pi.single j 1)

variable [CharP K 2]

theorem FieldNeighbourIso.TwistAt.transfer_single {N N' : E7Neighbour}
    {h : FieldNeighbourIso σ e N} {h' : FieldNeighbourIso σ e N'} {ρ : K ≃+* K}
    {a b : Fin (Tag.rank .E7)} (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes)
    (hT : h.TwistAt h' ρ (Pi.single a 1) ∧ h.TwistAt h' ρ (-Pi.single a 1))
    (ω : List (Fin (Tag.rank .E7)))
    (hω : (coxeterSystem .E7).wordProd ω • (Pi.single a 1 : Fin (Tag.rank .E7) → ℤ) =
      Pi.single b 1)
    (hωN : wordElt (fixSubfield σ) ω ∈ rootSpan .E7 (fixSubfield σ) (orthRoots N.root))
    (hωN' : wordElt (fixSubfield σ) ω ∈ rootSpan .E7 (fixSubfield σ) (orthRoots N'.root)) :
    h.TwistAt h' ρ (Pi.single b 1) ∧ h.TwistAt h' ρ (-Pi.single b 1) := by
  refine ⟨?_, ?_⟩
  · have h1 := hT.1.conj_word (single_mem_orthRoots ha) (single_mem_orthRoots ha') ω hωN hωN'
    rwa [hω] at h1
  · have h1 := hT.2.conj_word (neg_single_mem_orthRoots ha) (neg_single_mem_orthRoots ha') ω hωN
      hωN'
    rwa [smul_neg, hω] at h1

theorem FieldNeighbourIso.TwistAt.transfer_pair {N N' : E7Neighbour}
    {h : FieldNeighbourIso σ e N} {h' : FieldNeighbourIso σ e N'} {ρ : K ≃+* K}
    {a b : Fin (Tag.rank .E7)} (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes) (hb : b ∈ N.nodes)
    (hb' : b ∈ N'.nodes)
    (hab : (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (3, 4) ∨ (a, b) = (5, 6))
    (hT : h.TwistAt h' ρ (Pi.single a 1) ∧ h.TwistAt h' ρ (-Pi.single a 1)) :
    h.TwistAt h' ρ (Pi.single b 1) ∧ h.TwistAt h' ρ (-Pi.single b 1) := by
  have hmem : ∀ M : E7Neighbour, a ∈ M.nodes → b ∈ M.nodes →
      wordElt (fixSubfield σ) [a, b] ∈ rootSpan .E7 (fixSubfield σ) (orthRoots M.root) :=
    fun M haM hbM => wordElt_mem_rootSpan_of_nodes fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      exacts [haM, hbM]
  exact FieldNeighbourIso.TwistAt.transfer_single ha ha' hT [a, b] (wordProd_pair_single hab)
    (hmem N ha hb) (hmem N' ha' hb')

variable [Finite K] [Finite G]

theorem exists_twistOn_high_seven (hX : FieldNeighbourIso σ e .high)
    (hY : FieldNeighbourIso σ e .seven) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ hX.TwistOn hY ρ {1, 2, 3, 4} ∧
      hX.TwistAt hY ρ beta1 := by
  obtain ⟨ρ, hρ, h2p, h2n⟩ := hX.exists_twistAt_single hY hq (j := 2) (by decide) (by decide)
  have h2 := And.intro h2p h2n
  have h3 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h2
  have h1 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inl rfl)) h3
  have h4 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inl rfl))) h3
  have hβ := h2p.conj_word (single_mem_orthRoots (by decide)) (single_mem_orthRoots (by decide))
    wordHS (wordElt_wordHS_mem (Or.inl rfl)) (wordElt_wordHS_mem (Or.inr rfl))
  rw [wordProd_wordHS_single] at hβ
  refine ⟨ρ, hρ, fun j hj => ?_, hβ⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

theorem exists_twistOn_high_four (hX : FieldNeighbourIso σ e .high)
    (hZ : FieldNeighbourIso σ e .four) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ hX.TwistOn hZ ρ {5, 6} ∧
      hX.TwistAt hZ ρ beta1 := by
  obtain ⟨ρ, hρ, h5p, h5n⟩ := hX.exists_twistAt_single hZ hq (j := 5) (by decide) (by decide)
  have h5 := And.intro h5p h5n
  have h6 := FieldNeighbourIso.TwistAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr rfl))) h5
  have hβ := h5n.conj_word (neg_single_mem_orthRoots (by decide))
    (neg_single_mem_orthRoots (by decide)) wordHF (wordElt_wordHF_mem (Or.inl rfl))
    (wordElt_wordHF_mem (Or.inr rfl))
  rw [wordProd_wordHF_neg_single] at hβ
  refine ⟨ρ, hρ, fun j hj => ?_, hβ⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  exacts [h5, h6]

theorem exists_twistOn_seven_four (hY : FieldNeighbourIso σ e .seven)
    (hZ : FieldNeighbourIso σ e .four) (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ρ : K ≃+* K, (∀ c : fixSubfield σ, ρ c = c) ∧ hY.TwistOn hZ ρ {0} ∧
      hY.TwistAt hZ ρ beta1 := by
  obtain ⟨ρ, hρ, h0p, h0n⟩ := hY.exists_twistAt_single hZ hq (j := 0) (by decide) (by decide)
  have hβ := h0n.conj_word (neg_single_mem_orthRoots (by decide))
    (neg_single_mem_orthRoots (by decide)) wordSF (wordElt_wordSF_mem (Or.inl rfl))
    (wordElt_wordSF_mem (Or.inr rfl))
  rw [wordProd_wordSF_neg_single] at hβ
  refine ⟨ρ, hρ, fun j hj => ?_, hβ⟩
  rw [Finset.mem_singleton] at hj
  subst hj
  exact ⟨h0p, h0n⟩

omit [Finite G]
  [Finite K] [CharP K 2]
  in
theorem twist_cocycle (hX : FieldNeighbourIso σ e .high) (hY : FieldNeighbourIso σ e .seven)
    (hZ : FieldNeighbourIso σ e .four) {ρhs ρsf ρhf : K ≃+* K}
    (hhs : hX.TwistAt hY ρhs beta1) (hsf : hY.TwistAt hZ ρsf beta1)
    (hhf : hX.TwistAt hZ ρhf beta1) : ρhf = ρhs.trans ρsf := by
  have hγX := beta1_mem_orthRoots .high
  have hγY := beta1_mem_orthRoots .seven
  have hγZ := beta1_mem_orthRoots .four
  ext a
  have h4 : ((hZ.Φ (leviRootElt _ hγZ (ρhf a)) : neighbourCore e .four) : G) =
      hZ.Φ (leviRootElt _ hγZ (ρsf (ρhs a))) := by
    rw [← hhf hγX hγZ a, hhs hγX hγY a, hsf hγY hγZ (ρhs a)]
  have h5 := hZ.Φ.injective (Subtype.ext h4)
  have h6 := congrArg (fun x : E7Neighbour.four.levi K =>
    ((x : adjointGroup .E7 K) : ModGL .E7 K)) h5
  simp only [coe_leviRootElt] at h6
  rw [RingEquiv.trans_apply]
  exact pinnedX_injective (τ := .E7) (R := K) _ h6

theorem exists_aligned_fieldNeighbourIso (hX : FieldNeighbourIso σ e .high)
    (hY : FieldNeighbourIso σ e .seven) (hZ : FieldNeighbourIso σ e .four)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ (ρs ρf : K ≃+* K) (hρs : ∀ c : fixSubfield σ, ρs c = c)
      (hρf : ∀ c : fixSubfield σ, ρf c = c),
      hX.TwistOn (hY.twist ρs hρs) 1 {1, 2, 3, 4} ∧
        hX.TwistOn (hZ.twist ρf hρf) 1 {5, 6} ∧
        (hY.twist ρs hρs).TwistOn (hZ.twist ρf hρf) 1 {0} := by
  obtain ⟨ρhs, hρhs, hThs, hβhs⟩ := exists_twistOn_high_seven hX hY hq
  obtain ⟨ρhf, hρhf, hThf, hβhf⟩ := exists_twistOn_high_four hX hZ hq
  obtain ⟨ρsf, -, hTsf, hβsf⟩ := exists_twistOn_seven_four hY hZ hq
  have hcoc := twist_cocycle hX hY hZ hβhs hβsf hβhf
  refine ⟨ρhs, ρhf, hρhs, hρhf, fun j hj => ⟨(hThs j hj).1.twist hρhs, (hThs j hj).2.twist hρhs⟩,
    fun j hj => ⟨(hThf j hj).1.twist hρhf, (hThf j hj).2.twist hρhf⟩, fun j hj => ?_⟩
  have key : ∀ {γ : Fin (Tag.rank .E7) → ℤ}, hY.TwistAt hZ ρsf γ →
      (hY.twist ρhs hρhs).TwistAt (hZ.twist ρhf hρhf) 1 γ := by
    intro γ hT hγ hγ' a
    rw [FieldNeighbourIso.twist_apply, FieldNeighbourIso.twist_apply,
      leviEntrywiseEquiv_leviRootElt, leviEntrywiseEquiv_leviRootElt, RingAut.one_apply, hcoc,
      RingEquiv.trans_apply]
    exact hT hγ hγ' (ρhs a)
  exact ⟨key (hTsf j hj).1, key (hTsf j hj).2⟩

omit [Finite G]
  [Finite K] [CharP K 2]
  in
theorem FieldNeighbourIso.eq_on_leviPiece {N N' : E7Neighbour} (h : FieldNeighbourIso σ e N)
    (h' : FieldNeighbourIso σ e N') {J : Finset (Fin (Tag.rank .E7))} (hJ : J ⊆ N.nodes)
    (hJ' : J ⊆ N'.nodes) (hT : h.TwistOn h' 1 J) {x : N.levi K} {x' : N'.levi K}
    (hxx' : (x : adjointGroup .E7 K) = x') (hx : x ∈ leviPiece K N J) :
    ((h.Φ x : neighbourCore e N) : G) = h'.Φ x' := by
  set I : Subgroup (adjointGroup .E7 K) := N.levi K ⊓ N'.levi K with hI
  set f : I →* G := (neighbourCore e N).subtype.comp
    (h.Φ.toMonoidHom.comp (Subgroup.inclusion inf_le_left)) with hf
  set f' : I →* G := (neighbourCore e N').subtype.comp
    (h'.Φ.toMonoidHom.comp (Subgroup.inclusion inf_le_right)) with hf'
  set H : Subgroup (ModGL .E7 K) :=
    ((MonoidHom.eqLocus f f').map I.subtype).map (adjointGroup .E7 K).subtype with hH
  have hgen : rootSpan .E7 K (amalgamRoots J) ≤ H := by
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
    refine ⟨⟨pinnedX .E7 K γ c, pinnedX_mem_adjointGroup γ c⟩,
      ⟨⟨_, ⟨(leviRootElt N hγN c).2, (leviRootElt N' hγN' c).2⟩⟩, ?_, rfl⟩, rfl⟩
    exact hTγ hγN hγN' c
  have hxH : ((x : adjointGroup .E7 K) : ModGL .E7 K) ∈ H := hgen (mem_leviPiece.1 hx)
  obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hxH
  have hyx' : ((y : adjointGroup .E7 K)) = x := Subtype.ext hyx
  have h1 : x = Subgroup.inclusion inf_le_left y := Subtype.ext hyx'.symm
  have h2 : x' = Subgroup.inclusion inf_le_right y := Subtype.ext (hxx'.symm.trans hyx'.symm)
  rw [h1, h2]
  exact hy

theorem exists_aligned_fieldNeighbourIso_eq_on_leviPiece (hX : FieldNeighbourIso σ e .high)
    (hY : FieldNeighbourIso σ e .seven) (hZ : FieldNeighbourIso σ e .four)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ (hY' : FieldNeighbourIso σ e .seven) (hZ' : FieldNeighbourIso σ e .four),
      (∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {1, 2, 3, 4} →
        ∀ (x : E7Neighbour.high.levi K) (x' : E7Neighbour.seven.levi K),
          (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .high J →
            ((hX.Φ x : neighbourCore e .high) : G) = hY'.Φ x') ∧
      (∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {5, 6} →
        ∀ (x : E7Neighbour.high.levi K) (x' : E7Neighbour.four.levi K),
          (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .high J →
            ((hX.Φ x : neighbourCore e .high) : G) = hZ'.Φ x') ∧
      (∀ {J : Finset (Fin (Tag.rank .E7))}, J ⊆ {0} →
        ∀ (x : E7Neighbour.seven.levi K) (x' : E7Neighbour.four.levi K),
          (x : adjointGroup .E7 K) = x' → x ∈ leviPiece K .seven J →
            ((hY'.Φ x : neighbourCore e .seven) : G) = hZ'.Φ x') := by
  obtain ⟨ρs, ρf, hρs, hρf, h1, h2, h3⟩ := exists_aligned_fieldNeighbourIso hX hY hZ hq
  refine ⟨hY.twist ρs hρs, hZ.twist ρf hρf, fun hJ x x' hxx' hx => ?_,
    fun hJ x x' hxx' hx => ?_, fun hJ x x' hxx' hx => ?_⟩
  · exact hX.eq_on_leviPiece _ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h1 j (hJ hj)) hxx' hx
  · exact hX.eq_on_leviPiece _ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h2 j (hJ hj)) hxx' hx
  · exact (hY.twist ρs hρs).eq_on_leviPiece _ (hJ.trans (by decide)) (hJ.trans (by decide))
      (fun j hj => h3 j (hJ hj)) hxx' hx

end Overlaps

end CFSG.SeitzReduction.E7Pilot
