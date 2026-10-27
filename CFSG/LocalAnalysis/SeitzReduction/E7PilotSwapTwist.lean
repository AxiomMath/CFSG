module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotSwapPieces
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignFieldTriangle
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapTwist

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e7PilotSwapTwistNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem wordProd_wordSF_beta1 :
    (coxeterSystem .E7).wordProd wordSF • beta1 = (-Pi.single 0 1 : Fin (Tag.rank .E7) → ℤ) := by
  simp only [wordSF, wordDeltaSF, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem wordProd_wordSF_neg_beta1 :
    (coxeterSystem .E7).wordProd wordSF • (-beta1) = (Pi.single 0 1 : Fin (Tag.rank .E7) → ℤ) := by
  rw [smul_neg, wordProd_wordSF_beta1, neg_neg]

theorem wordProd_wordHF_single :
    (coxeterSystem .E7).wordProd wordHF • (Pi.single 5 1 : Fin (Tag.rank .E7) → ℤ) = -beta1 := by
  rw [← wordProd_wordHF_neg_single, smul_neg, neg_neg]

section Agree

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 K} {t : G}

@[expose] def SwapNeighbourIso.AgreeAt {N N' : E7Neighbour} (h : SwapNeighbourIso e t N)
    (h' : SwapNeighbourIso e t N') (γ : Fin (Tag.rank .E7) → ℤ) : Prop :=
  ∀ (hγ : γ ∈ orthRoots N.root) (hγ' : γ ∈ orthRoots N'.root) (a : K),
    ((h.Φ (leviRootElt N hγ a, 1) : neighbourCore e N) : G) = h'.Φ (leviRootElt N' hγ' a, 1)

@[expose] def SwapNeighbourIso.AgreeOn {N N' : E7Neighbour} (h : SwapNeighbourIso e t N)
    (h' : SwapNeighbourIso e t N') (S : Finset (Fin (Tag.rank .E7))) : Prop :=
  ∀ j ∈ S, h.AgreeAt h' (Pi.single j 1) ∧ h.AgreeAt h' (-Pi.single j 1)

theorem SwapNeighbourIso.AgreeAt.symm {N N' : E7Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {γ : Fin (Tag.rank .E7) → ℤ} (hT : h.AgreeAt h' γ) :
    h'.AgreeAt h γ :=
  fun hγ' hγ a => (hT hγ hγ' a).symm

theorem SwapNeighbourIso.AgreeAt.trans {N N' N'' : E7Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {h'' : SwapNeighbourIso e t N''}
    {γ : Fin (Tag.rank .E7) → ℤ} (h₁ : h.AgreeAt h' γ) (h₂ : h'.AgreeAt h'' γ)
    (hγ' : γ ∈ orthRoots N'.root) : h.AgreeAt h'' γ :=
  fun hγ hγ'' a => (h₁ hγ hγ' a).trans (h₂ hγ' hγ'' a)

theorem SwapNeighbourIso.AgreeOn.symm {N N' : E7Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {S : Finset (Fin (Tag.rank .E7))} (hT : h.AgreeOn h' S) :
    h'.AgreeOn h S :=
  fun j hj => ⟨(hT j hj).1.symm, (hT j hj).2.symm⟩

theorem SwapNeighbourIso.AgreeOn.mono {N N' : E7Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {S S' : Finset (Fin (Tag.rank .E7))} (hT : h.AgreeOn h' S)
    (hS : S' ⊆ S) : h.AgreeOn h' S' :=
  fun j hj => hT j (hS hj)

end Agree

section Transfer

variable {K : Type} [Field K] [CharP K 2] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 K} {t : G}

theorem SwapNeighbourIso.AgreeAt.conj_word {N N' : E7Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {γ : Fin (Tag.rank .E7) → ℤ} (hT : h.AgreeAt h' γ)
    (hγN : γ ∈ orthRoots N.root) (hγN' : γ ∈ orthRoots N'.root) (ω : List (Fin (Tag.rank .E7)))
    (hωN : wordElt K ω ∈ rootSpan .E7 K (orthRoots N.root))
    (hωN' : wordElt K ω ∈ rootSpan .E7 K (orthRoots N'.root)) :
    h.AgreeAt h' ((coxeterSystem .E7).wordProd ω • γ) := by
  intro hδ hδ' a
  set n : adjointGroup .E7 K := ⟨wordElt K ω, wordElt_mem_adjointGroup ω⟩ with hn
  set y : N.levi K := ⟨n, mem_subgroupOf.2 hωN⟩ with hy
  set y' : N'.levi K := ⟨n, mem_subgroupOf.2 hωN'⟩ with hy'
  have hconj : ∀ (M : E7Neighbour) (z : M.levi K), (z : adjointGroup .E7 K) = n →
      ∀ (hγM : γ ∈ orthRoots M.root) (hδM : (coxeterSystem .E7).wordProd ω • γ ∈ orthRoots M.root)
        (b : K), leviRootElt M hδM b = z * leviRootElt M hγM b * z⁻¹ := by
    intro M z hz hγM hδM b
    refine Subtype.ext (Subtype.ext ?_)
    simp only [coe_leviRootElt, Subgroup.coe_mul, Subgroup.coe_inv, hz, hn]
    rw [wordElt_conj_pinnedX ω hγM.1]
  rw [hconj N y rfl hγN hδ a, h.map_conj_one_of_mem y, hT hγN hγN' a,
    hconj N' y' rfl hγN' hδ' a, h'.map_conj_one_of_mem y']

theorem SwapNeighbourIso.AgreeAt.transfer_single {N N' : E7Neighbour}
    {h : SwapNeighbourIso e t N} {h' : SwapNeighbourIso e t N'} {a b : Fin (Tag.rank .E7)}
    (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes)
    (hT : h.AgreeAt h' (Pi.single a 1) ∧ h.AgreeAt h' (-Pi.single a 1))
    (ω : List (Fin (Tag.rank .E7)))
    (hω : (coxeterSystem .E7).wordProd ω • (Pi.single a 1 : Fin (Tag.rank .E7) → ℤ) =
      Pi.single b 1)
    (hωN : wordElt K ω ∈ rootSpan .E7 K (orthRoots N.root))
    (hωN' : wordElt K ω ∈ rootSpan .E7 K (orthRoots N'.root)) :
    h.AgreeAt h' (Pi.single b 1) ∧ h.AgreeAt h' (-Pi.single b 1) := by
  refine ⟨?_, ?_⟩
  · have h1 := hT.1.conj_word (single_mem_orthRoots ha) (single_mem_orthRoots ha') ω hωN hωN'
    rwa [hω] at h1
  · have h1 := hT.2.conj_word (neg_single_mem_orthRoots ha) (neg_single_mem_orthRoots ha') ω hωN
      hωN'
    rwa [smul_neg, hω] at h1

theorem SwapNeighbourIso.AgreeAt.transfer_pair {N N' : E7Neighbour}
    {h : SwapNeighbourIso e t N} {h' : SwapNeighbourIso e t N'} {a b : Fin (Tag.rank .E7)}
    (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes) (hb : b ∈ N.nodes) (hb' : b ∈ N'.nodes)
    (hab : (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (3, 4) ∨ (a, b) = (5, 6))
    (hT : h.AgreeAt h' (Pi.single a 1) ∧ h.AgreeAt h' (-Pi.single a 1)) :
    h.AgreeAt h' (Pi.single b 1) ∧ h.AgreeAt h' (-Pi.single b 1) := by
  have hmem : ∀ M : E7Neighbour, a ∈ M.nodes → b ∈ M.nodes →
      wordElt K [a, b] ∈ rootSpan .E7 K (orthRoots M.root) :=
    fun M haM hbM => wordElt_mem_rootSpan_of_nodes fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      exacts [haM, hbM]
  exact SwapNeighbourIso.AgreeAt.transfer_single ha ha' hT [a, b] (wordProd_pair_single hab)
    (hmem N ha hb) (hmem N' ha' hb')

end Transfer

section RankOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E7 K} {t : G}

theorem SwapNeighbourIso.agreeAt_or_agreeAt_flip {N N' : E7Neighbour}
    (h : SwapNeighbourIso e t N) (h' : SwapNeighbourIso e t N') (hq : 4 ≤ Nat.card K)
    {j : Fin (Tag.rank .E7)} (hj : j ∈ N.nodes) (hj' : j ∈ N'.nodes) :
    (h.AgreeAt h' (Pi.single j 1) ∧ h.AgreeAt h' (-Pi.single j 1)) ∨
      (h.AgreeAt h'.flip (Pi.single j 1) ∧ h.AgreeAt h'.flip (-Pi.single j 1)) := by
  have hα : IsRoot .E7 (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) := isRoot_single _ j
  obtain ⟨hRinj, hrange, -, hgen, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E7 K hα
  set R := rootSL2 .E7 K (Pi.single j 1 : Fin (Tag.rank .E7) → ℤ) with hR
  have hRmem : ∀ M : E7Neighbour, j ∈ M.nodes → ∀ A,
      R A ∈ rootSpan .E7 K (orthRoots M.root) := by
    intro M hjM A
    have hA : R A ∈ R.range := ⟨A, rfl⟩
    rw [hrange] at hA
    have hle : rootSubgroup .E7 K (Pi.single j 1) ⊔ rootSubgroup .E7 K (-Pi.single j 1) ≤
        rootSpan .E7 K (orthRoots M.root) :=
      sup_le (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots M.root) => rootSubgroup .E7 K α)
          _ (single_mem_orthRoots hjM) le_rfl)
        (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots M.root) => rootSubgroup .E7 K α)
          _ (neg_single_mem_orthRoots hjM) le_rfl)
    exact hle hA
  let ψ : ∀ M : E7Neighbour, j ∈ M.nodes →
      Matrix.SpecialLinearGroup (Fin 2) K →* M.levi K := fun M hjM =>
    (R.codRestrict (adjointGroup .E7 K) fun A =>
      EPilot.rootSpan_le_adjointGroup' _ (hRmem M hjM A)).codRestrict (M.levi K) fun A =>
        mem_subgroupOf.2 (hRmem M hjM A)
  have hψ : ∀ M hjM A, (((ψ M hjM A : M.levi K) : adjointGroup .E7 K) : ModGL .E7 K) = R A :=
    fun _ _ _ => rfl
  have hψinj : ∀ M hjM, Function.Injective (ψ M hjM) := fun M hjM A B hAB =>
    hRinj (by rw [← hψ M hjM A, ← hψ M hjM B, hAB])
  have hψrange : ∀ M hjM, (ψ M hjM).range = leviPiece K M {j} := by
    intro M hjM
    ext x
    rw [mem_leviPiece, rootSpan_amalgamRoots_singleton, ← hrange]
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨A, rfl⟩
    · rintro ⟨A, hA⟩
      exact ⟨A, Subtype.ext (Subtype.ext hA)⟩
  have hψψ : ∀ A, ((ψ N hj A : N.levi K) : adjointGroup .E7 K) = (ψ N' hj' A : N'.levi K) :=
    fun A => Subtype.ext ((hψ N hj A).trans (hψ N' hj' A).symm)
  set P : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* G :=
    (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp ((ψ N hj).prodMap (ψ N hj))) with hP
  set Q : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* G :=
    (neighbourCore e N').subtype.comp (h'.Φ.toMonoidHom.comp ((ψ N' hj').prodMap (ψ N' hj')))
    with hQ
  have hPapp : ∀ A B, P (A, B) = h.Φ (ψ N hj A, ψ N hj B) := fun _ _ => rfl
  have hQapp : ∀ A B, Q (A, B) = h'.Φ (ψ N' hj' A, ψ N' hj' B) := fun _ _ => rfl
  have hPinj : Function.Injective P := by
    intro z z' hzz'
    rw [← Prod.mk.eta (p := z), ← Prod.mk.eta (p := z'), hPapp, hPapp] at hzz'
    have h1 := h.coe_injective hzz'
    exact Prod.ext (hψinj N hj (congrArg Prod.fst h1)) (hψinj N hj (congrArg Prod.snd h1))
  have hJ : ({j} : Finset (Fin (Tag.rank .E7))).card ≤ 2 := by simp
  have hQP : ∀ A, ∃ z, Q (A, 1) = P z := by
    intro A
    have h1 : Q (A, 1) ∈ pieceCore e {j} := by
      rw [← h'.map_leviPiece hq (Finset.singleton_subset_iff.2 hj') hJ]
      refine ⟨(ψ N' hj' A, ψ N' hj' 1), ⟨?_, ?_⟩, rfl⟩
      · rw [← hψrange N' hj']
        exact ⟨A, rfl⟩
      · rw [← hψrange N' hj']
        exact ⟨1, rfl⟩
    rw [← h.map_leviPiece hq (Finset.singleton_subset_iff.2 hj) hJ] at h1
    obtain ⟨⟨z₁, z₂⟩, ⟨hz₁, hz₂⟩, hz⟩ := h1
    rw [← hψrange N hj] at hz₁ hz₂
    obtain ⟨a, rfl⟩ := hz₁
    obtain ⟨b, rfl⟩ := hz₂
    exact ⟨(a, b), hz.symm⟩
  have hdiag : ∀ A, Q (A, A) = P (A, A) := by
    intro A
    rw [hQapp, hPapp, h'.diag, h.diag, hψψ]
  have hPt : ∀ A B, t * P (A, B) * t⁻¹ = P (B, A) := fun A B => by
    rw [hPapp, hPapp, h.swap]
  have hQt : ∀ A B, t * Q (A, B) * t⁻¹ = Q (B, A) := fun A B => by
    rw [hQapp, hQapp, h'.swap]
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup hq
  have hZ : center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    CFSG.RankThree.PartOne.KCRootAxis.sl2_center_eq_bot
  have hu : ∀ (M : E7Neighbour) (hjM : j ∈ M.nodes) (hγ : Pi.single j 1 ∈ orthRoots M.root)
      (a : K), leviRootElt M hγ a = ψ M hjM (uSL a) :=
    fun M hjM hγ a => Subtype.ext (Subtype.ext ((coe_leviRootElt M hγ a).trans (hgen a).1.symm))
  have hv : ∀ (M : E7Neighbour) (hjM : j ∈ M.nodes) (hγ : -Pi.single j 1 ∈ orthRoots M.root)
      (a : K), leviRootElt M hγ a = ψ M hjM (vSL a) :=
    fun M hjM hγ a => Subtype.ext (Subtype.ext ((coe_leviRootElt M hγ a).trans (hgen a).2.symm))
  have hP1 : ∀ A, P (A, 1) = h.Φ (ψ N hj A, 1) := fun A => by rw [hPapp, map_one]
  have hQ1 : ∀ A, Q (A, 1) = h'.Φ (ψ N' hj' A, 1) := fun A => by rw [hQapp, map_one]
  have hP1' : ∀ A, P (1, A) = h.Φ (1, ψ N hj A) := fun A => by rw [hPapp, map_one]
  rcases E8Pilot.forall_eq_or_forall_eq_of_swap hZ P Q hPinj hQP hdiag hPt hQt with h1 | h1
  · left
    refine ⟨fun hγ hγ' a => ?_, fun hγ hγ' a => ?_⟩
    · rw [hu N hj hγ, hu N' hj' hγ', ← hP1, ← hQ1, h1]
    · rw [hv N hj hγ, hv N' hj' hγ', ← hP1, ← hQ1, h1]
  · right
    have h2 : ∀ A, ((h.Φ (ψ N hj A, 1) : neighbourCore e N) : G) =
        h'.flip.Φ (ψ N' hj' A, 1) := by
      intro A
      have h3 : t * Q (A, 1) * t⁻¹ = t * P (1, A) * t⁻¹ := by rw [h1 A]
      rw [hQ1, hP1', h'.swap, h.swap] at h3
      rw [SwapNeighbourIso.flip_apply]
      exact h3.symm
    refine ⟨fun hγ hγ' a => ?_, fun hγ hγ' a => ?_⟩
    · rw [hu N hj hγ, hu N' hj' hγ', h2]
    · rw [hv N hj hγ, hv N' hj' hγ', h2]

end RankOne

section Triangle

variable {K : Type} [Field K] [CharP K 2] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 K} {t : G}

theorem neg_beta1_mem_orthRoots (N : E7Neighbour) : -beta1 ∈ orthRoots N.root :=
  ⟨IsRoot.neg isRoot_beta1, by rw [iform_neg_right_E7, (beta1_mem_orthRoots N).2, neg_zero]⟩

theorem SwapNeighbourIso.agreeOn_high_seven_of_two {hX : SwapNeighbourIso e t .high}
    {hY : SwapNeighbourIso e t .seven}
    (h2 : hX.AgreeAt hY (Pi.single 2 1) ∧ hX.AgreeAt hY (-Pi.single 2 1)) :
    hX.AgreeOn hY {1, 2, 3, 4} ∧ hX.AgreeAt hY beta1 ∧ hX.AgreeAt hY (-beta1) := by
  have h3 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h2
  have h1 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inl rfl)) h3
  have h4 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inl rfl))) h3
  have hβ := h2.1.conj_word (single_mem_orthRoots (by decide)) (single_mem_orthRoots (by decide))
    wordHS (wordElt_wordHS_mem (Or.inl rfl)) (wordElt_wordHS_mem (Or.inr rfl))
  rw [wordProd_wordHS_single] at hβ
  have hβ' := h2.2.conj_word (neg_single_mem_orthRoots (by decide))
    (neg_single_mem_orthRoots (by decide)) wordHS (wordElt_wordHS_mem (Or.inl rfl))
    (wordElt_wordHS_mem (Or.inr rfl))
  rw [smul_neg, wordProd_wordHS_single] at hβ'
  refine ⟨fun j hj => ?_, hβ, hβ'⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

theorem SwapNeighbourIso.agreeOn_high_four_of_five {hX : SwapNeighbourIso e t .high}
    {hZ : SwapNeighbourIso e t .four}
    (h5 : hX.AgreeAt hZ (Pi.single 5 1) ∧ hX.AgreeAt hZ (-Pi.single 5 1)) :
    hX.AgreeOn hZ {5, 6} ∧ hX.AgreeAt hZ beta1 ∧ hX.AgreeAt hZ (-beta1) := by
  have h6 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr rfl))) h5
  have hβ := h5.2.conj_word (neg_single_mem_orthRoots (by decide))
    (neg_single_mem_orthRoots (by decide)) wordHF (wordElt_wordHF_mem (Or.inl rfl))
    (wordElt_wordHF_mem (Or.inr rfl))
  rw [wordProd_wordHF_neg_single] at hβ
  have hβ' := h5.1.conj_word (single_mem_orthRoots (by decide)) (single_mem_orthRoots (by decide))
    wordHF (wordElt_wordHF_mem (Or.inl rfl)) (wordElt_wordHF_mem (Or.inr rfl))
  rw [wordProd_wordHF_single] at hβ'
  refine ⟨fun j hj => ?_, hβ, hβ'⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  exacts [h5, h6]

theorem SwapNeighbourIso.agreeOn_seven_four_of_beta1 {hY : SwapNeighbourIso e t .seven}
    {hZ : SwapNeighbourIso e t .four} (hβ : hY.AgreeAt hZ beta1) (hβ' : hY.AgreeAt hZ (-beta1)) :
    hY.AgreeOn hZ {0} := by
  have h0n := hβ.conj_word (beta1_mem_orthRoots _) (beta1_mem_orthRoots _) wordSF
    (wordElt_wordSF_mem (Or.inl rfl)) (wordElt_wordSF_mem (Or.inr rfl))
  rw [wordProd_wordSF_beta1] at h0n
  have h0p := hβ'.conj_word (neg_beta1_mem_orthRoots _) (neg_beta1_mem_orthRoots _) wordSF
    (wordElt_wordSF_mem (Or.inl rfl)) (wordElt_wordSF_mem (Or.inr rfl))
  rw [wordProd_wordSF_neg_beta1] at h0p
  intro j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  exact ⟨h0p, h0n⟩

variable [Finite K] [Finite G]

theorem exists_aligned_swapNeighbourIso (hX : SwapNeighbourIso e t .high)
    (hY : SwapNeighbourIso e t .seven) (hZ : SwapNeighbourIso e t .four) (hq : 4 ≤ Nat.card K) :
    ∃ (hY' : SwapNeighbourIso e t .seven) (hZ' : SwapNeighbourIso e t .four),
      hX.AgreeOn hY' {1, 2, 3, 4} ∧ hX.AgreeOn hZ' {5, 6} ∧ hY'.AgreeOn hZ' {0} := by
  obtain ⟨hY', hXY⟩ : ∃ hY' : SwapNeighbourIso e t .seven,
      hX.AgreeAt hY' (Pi.single 2 1) ∧ hX.AgreeAt hY' (-Pi.single 2 1) := by
    rcases hX.agreeAt_or_agreeAt_flip hY hq (j := 2) (by decide) (by decide) with h0 | h0
    exacts [⟨hY, h0⟩, ⟨hY.flip, h0⟩]
  obtain ⟨hZ', hXZ⟩ : ∃ hZ' : SwapNeighbourIso e t .four,
      hX.AgreeAt hZ' (Pi.single 5 1) ∧ hX.AgreeAt hZ' (-Pi.single 5 1) := by
    rcases hX.agreeAt_or_agreeAt_flip hZ hq (j := 5) (by decide) (by decide) with h0 | h0
    exacts [⟨hZ, h0⟩, ⟨hZ.flip, h0⟩]
  obtain ⟨hHS, hβs, hβs'⟩ := SwapNeighbourIso.agreeOn_high_seven_of_two hXY
  obtain ⟨hHF, hβf, hβf'⟩ := SwapNeighbourIso.agreeOn_high_four_of_five hXZ
  exact ⟨hY', hZ', hHS, hHF, SwapNeighbourIso.agreeOn_seven_four_of_beta1
    (hβs.symm.trans hβf (beta1_mem_orthRoots _)) (hβs'.symm.trans hβf' (neg_beta1_mem_orthRoots _))⟩

end Triangle

section LeviPiece

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E7 K} {t : G}

theorem SwapNeighbourIso.fst_eq_of_agreeOn {N N' : E7Neighbour} (h : SwapNeighbourIso e t N)
    (h' : SwapNeighbourIso e t N') {J : Finset (Fin (Tag.rank .E7))} (hJ : J ⊆ N.nodes)
    (hJ' : J ⊆ N'.nodes) (hT : h.AgreeOn h' J)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE7 K).rootGroup J) :
    h.fst hJ x = h'.fst hJ' x := by
  set I : Subgroup (adjointGroup .E7 K) := N.levi K ⊓ N'.levi K with hI
  set f : I →* G := (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp
    ((MonoidHom.inl (N.levi K) (N.levi K)).comp (Subgroup.inclusion inf_le_left))) with hf
  set f' : I →* G := (neighbourCore e N').subtype.comp (h'.Φ.toMonoidHom.comp
    ((MonoidHom.inl (N'.levi K) (N'.levi K)).comp (Subgroup.inclusion inf_le_right))) with hf'
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
    have hTγ : h.AgreeAt h' γ := by
      rcases hγj with rfl | rfl
      exacts [(hT j hj).1, (hT j hj).2]
    refine ⟨⟨pinnedX .E7 K γ c, pinnedX_mem_adjointGroup γ c⟩,
      ⟨⟨_, ⟨(leviRootElt N hγN c).2, (leviRootElt N' hγN' c).2⟩⟩, ?_, rfl⟩, rfl⟩
    exact hTγ hγN hγN' c
  have hxR : ((x : adjointGroup .E7 K) : ModGL .E7 K) ∈ rootSpan .E7 K (amalgamRoots J) :=
    mem_subgroupOf.1 ((levi_adjDatumE7_eq (K := K) J).le x.2)
  obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hgen hxR
  have hyx' : ((y : adjointGroup .E7 K)) = x := Subtype.ext hyx
  have h1 : (⟨x, levi_le_neighbourLevi hJ x.2⟩ : N.levi K) = Subgroup.inclusion inf_le_left y :=
    Subtype.ext hyx'.symm
  have h2 : (⟨x, levi_le_neighbourLevi hJ' x.2⟩ : N'.levi K) =
      Subgroup.inclusion inf_le_right y := Subtype.ext hyx'.symm
  rw [SwapNeighbourIso.fst_apply, SwapNeighbourIso.fst_apply, h1, h2]
  exact hy

end LeviPiece

end CFSG.SeitzReduction.E7Pilot
