module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapPieces
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldTriangle
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapTwist

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e8PilotSwapTwistNeZeroRank : NeZero Tag.E8.rank := ⟨by decide⟩

theorem forall_eq_or_forall_eq_of_swap {S M : Type*} [Group S] [Group M] [IsSimpleGroup S]
    (hZ : center S = ⊥) (P Q : S × S →* M) (hP : Function.Injective P)
    (hQP : ∀ x, ∃ z, Q (x, 1) = P z) (hdiag : ∀ x, Q (x, x) = P (x, x)) {t : M}
    (hPt : ∀ x y, t * P (x, y) * t⁻¹ = P (y, x)) (hQt : ∀ x y, t * Q (x, y) * t⁻¹ = Q (y, x)) :
    (∀ x, Q (x, 1) = P (x, 1)) ∨ (∀ x, Q (x, 1) = P (1, x)) := by
  have hmem : ∀ x, (Q.comp (MonoidHom.inl S S)) x ∈ P.range := fun x => by
    obtain ⟨z, hz⟩ := hQP x
    exact ⟨z, hz.symm⟩
  obtain ⟨F, hF⟩ : ∃ F : S →* S × S, ∀ x, P (F x) = Q (x, 1) :=
    ⟨(MonoidHom.ofInjective hP).symm.toMonoidHom.comp
      ((Q.comp (MonoidHom.inl S S)).codRestrict P.range hmem), fun x => by simp⟩
  set α : S →* S := (MonoidHom.fst S S).comp F with hα
  set β : S →* S := (MonoidHom.snd S S).comp F with hβ
  have hFαβ : ∀ x, F x = (α x, β x) := fun x => rfl
  have hQ1 : ∀ x, Q (x, 1) = P (α x, β x) := fun x => by rw [← hFαβ, hF]
  have hQ2 : ∀ x, Q (1, x) = P (β x, α x) := fun x => by
    rw [← hQt x 1, hQ1, hPt]
  have hmul : ∀ x, α x * β x = x := by
    intro x
    have h1 : Q (x, x) = Q (x, 1) * Q (1, x) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hQ1, hQ2, ← map_mul, Prod.mk_mul_mk, hdiag] at h1
    exact (congrArg Prod.fst (hP h1)).symm
  have hcomm : ∀ x y, Commute (α x) (β y) := by
    intro x y
    have hc : Commute ((x, 1) : S × S) (1, y) := by
      change ((x, 1) : S × S) * (1, y) = (1, y) * (x, 1)
      simp only [Prod.mk_mul_mk, mul_one, one_mul]
    have h1 := (hc.map Q).eq
    rw [hQ1, hQ2, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk] at h1
    exact congrArg Prod.fst (hP h1)
  rcases F4Pilot.forall_eq_one_or_forall_eq_one_of_mul_eq hZ α β hmul hcomm with h | h
  · right
    intro x
    have hb : β x = x := by
      have h1 := hmul x
      rwa [h x, one_mul] at h1
    rw [hQ1, h x, hb]
  · left
    intro x
    have ha : α x = x := by
      have h1 := hmul x
      rwa [h x, mul_one] at h1
    rw [hQ1, h x, ha]

section Agree

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 K} {t : G}

@[expose] def SwapNeighbourIso.AgreeAt {N N' : E8Neighbour} (h : SwapNeighbourIso e t N)
    (h' : SwapNeighbourIso e t N') (γ : Fin (Tag.rank .E8) → ℤ) : Prop :=
  ∀ (hγ : γ ∈ orthRoots N.root) (hγ' : γ ∈ orthRoots N'.root) (a : K),
    ((h.Φ (leviRootElt N hγ a, 1) : neighbourCore e N) : G) = h'.Φ (leviRootElt N' hγ' a, 1)

@[expose] def SwapNeighbourIso.AgreeOn {N N' : E8Neighbour} (h : SwapNeighbourIso e t N)
    (h' : SwapNeighbourIso e t N') (S : Finset (Fin (Tag.rank .E8))) : Prop :=
  ∀ j ∈ S, h.AgreeAt h' (Pi.single j 1) ∧ h.AgreeAt h' (-Pi.single j 1)

theorem SwapNeighbourIso.AgreeAt.symm {N N' : E8Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {γ : Fin (Tag.rank .E8) → ℤ} (hT : h.AgreeAt h' γ) :
    h'.AgreeAt h γ :=
  fun hγ' hγ a => (hT hγ hγ' a).symm

theorem SwapNeighbourIso.AgreeAt.trans {N N' N'' : E8Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {h'' : SwapNeighbourIso e t N''}
    {γ : Fin (Tag.rank .E8) → ℤ} (h₁ : h.AgreeAt h' γ) (h₂ : h'.AgreeAt h'' γ)
    (hγ' : γ ∈ orthRoots N'.root) : h.AgreeAt h'' γ :=
  fun hγ hγ'' a => (h₁ hγ hγ' a).trans (h₂ hγ' hγ'' a)

theorem SwapNeighbourIso.AgreeOn.symm {N N' : E8Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {S : Finset (Fin (Tag.rank .E8))} (hT : h.AgreeOn h' S) :
    h'.AgreeOn h S :=
  fun j hj => ⟨(hT j hj).1.symm, (hT j hj).2.symm⟩

theorem SwapNeighbourIso.AgreeOn.mono {N N' : E8Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {S S' : Finset (Fin (Tag.rank .E8))} (hT : h.AgreeOn h' S)
    (hS : S' ⊆ S) : h.AgreeOn h' S' :=
  fun j hj => hT j (hS hj)

end Agree

section Transfer

variable {K : Type} [Field K] [CharP K 2] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 K} {t : G}

theorem SwapNeighbourIso.map_conj_one_of_mem {N : E8Neighbour} (h : SwapNeighbourIso e t N)
    (y x : N.levi K) :
    ((h.Φ (y * x * y⁻¹, 1) : neighbourCore e N) : G) =
      ((e.symm (y : adjointGroup .E8 K) : L) : G) * (h.Φ (x, 1) : G) *
        ((e.symm (y : adjointGroup .E8 K) : L) : G)⁻¹ := by
  rw [← h.map_conj_of_mem y x 1, mul_one, mul_inv_cancel]

theorem SwapNeighbourIso.AgreeAt.conj_word {N N' : E8Neighbour} {h : SwapNeighbourIso e t N}
    {h' : SwapNeighbourIso e t N'} {γ : Fin (Tag.rank .E8) → ℤ} (hT : h.AgreeAt h' γ)
    (hγN : γ ∈ orthRoots N.root) (hγN' : γ ∈ orthRoots N'.root) (ω : List (Fin (Tag.rank .E8)))
    (hωN : wordElt K ω ∈ rootSpan .E8 K (orthRoots N.root))
    (hωN' : wordElt K ω ∈ rootSpan .E8 K (orthRoots N'.root)) :
    h.AgreeAt h' ((coxeterSystem .E8).wordProd ω • γ) := by
  intro hδ hδ' a
  set n : adjointGroup .E8 K := ⟨wordElt K ω, wordElt_mem_adjointGroup ω⟩ with hn
  set y : N.levi K := ⟨n, mem_subgroupOf.2 hωN⟩ with hy
  set y' : N'.levi K := ⟨n, mem_subgroupOf.2 hωN'⟩ with hy'
  have hconj : ∀ (M : E8Neighbour) (z : M.levi K), (z : adjointGroup .E8 K) = n →
      ∀ (hγM : γ ∈ orthRoots M.root) (hδM : (coxeterSystem .E8).wordProd ω • γ ∈ orthRoots M.root)
        (b : K), leviRootElt M hδM b = z * leviRootElt M hγM b * z⁻¹ := by
    intro M z hz hγM hδM b
    refine Subtype.ext (Subtype.ext ?_)
    simp only [coe_leviRootElt, Subgroup.coe_mul, Subgroup.coe_inv, hz, hn]
    rw [wordElt_conj_pinnedX ω hγM.1]
  rw [hconj N y rfl hγN hδ a, h.map_conj_one_of_mem y, hT hγN hγN' a,
    hconj N' y' rfl hγN' hδ' a, h'.map_conj_one_of_mem y']

theorem SwapNeighbourIso.AgreeAt.transfer_single {N N' : E8Neighbour}
    {h : SwapNeighbourIso e t N} {h' : SwapNeighbourIso e t N'} {a b : Fin (Tag.rank .E8)}
    (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes)
    (hT : h.AgreeAt h' (Pi.single a 1) ∧ h.AgreeAt h' (-Pi.single a 1))
    (ω : List (Fin (Tag.rank .E8)))
    (hω : (coxeterSystem .E8).wordProd ω • (Pi.single a 1 : Fin (Tag.rank .E8) → ℤ) =
      Pi.single b 1)
    (hωN : wordElt K ω ∈ rootSpan .E8 K (orthRoots N.root))
    (hωN' : wordElt K ω ∈ rootSpan .E8 K (orthRoots N'.root)) :
    h.AgreeAt h' (Pi.single b 1) ∧ h.AgreeAt h' (-Pi.single b 1) := by
  refine ⟨?_, ?_⟩
  · have h1 := hT.1.conj_word (single_mem_orthRoots ha) (single_mem_orthRoots ha') ω hωN hωN'
    rwa [hω] at h1
  · have h1 := hT.2.conj_word (neg_single_mem_orthRoots ha) (neg_single_mem_orthRoots ha') ω hωN
      hωN'
    rwa [smul_neg, hω] at h1

theorem SwapNeighbourIso.AgreeAt.transfer_pair {N N' : E8Neighbour}
    {h : SwapNeighbourIso e t N} {h' : SwapNeighbourIso e t N'} {a b : Fin (Tag.rank .E8)}
    (ha : a ∈ N.nodes) (ha' : a ∈ N'.nodes) (hb : b ∈ N.nodes) (hb' : b ∈ N'.nodes)
    (hab : (a, b) = (0, 2) ∨ (a, b) = (2, 3) ∨ (a, b) = (3, 1) ∨ (a, b) = (5, 4) ∨
      (a, b) = (5, 6))
    (hT : h.AgreeAt h' (Pi.single a 1) ∧ h.AgreeAt h' (-Pi.single a 1)) :
    h.AgreeAt h' (Pi.single b 1) ∧ h.AgreeAt h' (-Pi.single b 1) := by
  have hmem : ∀ M : E8Neighbour, a ∈ M.nodes → b ∈ M.nodes →
      wordElt K [a, b] ∈ rootSpan .E8 K (orthRoots M.root) :=
    fun M haM hbM => wordElt_mem_rootSpan_of_nodes fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      exacts [haM, hbM]
  exact SwapNeighbourIso.AgreeAt.transfer_single ha ha' hT [a, b] (wordProd_pair_single hab)
    (hmem N ha hb) (hmem N' ha' hb')

end Transfer

section RankOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E8 K} {t : G}

theorem SwapNeighbourIso.agreeAt_or_agreeAt_flip {N N' : E8Neighbour}
    (h : SwapNeighbourIso e t N) (h' : SwapNeighbourIso e t N') (hq : 4 ≤ Nat.card K)
    {j : Fin (Tag.rank .E8)} (hj : j ∈ N.nodes) (hj' : j ∈ N'.nodes) :
    (h.AgreeAt h' (Pi.single j 1) ∧ h.AgreeAt h' (-Pi.single j 1)) ∨
      (h.AgreeAt h'.flip (Pi.single j 1) ∧ h.AgreeAt h'.flip (-Pi.single j 1)) := by
  have hα : IsRoot .E8 (Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) := isRoot_single _ j
  obtain ⟨hRinj, hrange, -, hgen, -⟩ :=
    CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .E8 K hα
  set R := rootSL2 .E8 K (Pi.single j 1 : Fin (Tag.rank .E8) → ℤ) with hR
  have hRmem : ∀ M : E8Neighbour, j ∈ M.nodes → ∀ A,
      R A ∈ rootSpan .E8 K (orthRoots M.root) := by
    intro M hjM A
    have hA : R A ∈ R.range := ⟨A, rfl⟩
    rw [hrange] at hA
    have hle : rootSubgroup .E8 K (Pi.single j 1) ⊔ rootSubgroup .E8 K (-Pi.single j 1) ≤
        rootSpan .E8 K (orthRoots M.root) :=
      sup_le (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots M.root) => rootSubgroup .E8 K α)
          _ (single_mem_orthRoots hjM) le_rfl)
        (le_iSup₂_of_le (f := fun α (_ : α ∈ orthRoots M.root) => rootSubgroup .E8 K α)
          _ (neg_single_mem_orthRoots hjM) le_rfl)
    exact hle hA
  let ψ : ∀ M : E8Neighbour, j ∈ M.nodes →
      Matrix.SpecialLinearGroup (Fin 2) K →* M.levi K := fun M hjM =>
    (R.codRestrict (adjointGroup .E8 K) fun A =>
      rootSpan_le_adjointGroup_E8 _ (hRmem M hjM A)).codRestrict (M.levi K) fun A =>
        mem_subgroupOf.2 (hRmem M hjM A)
  have hψ : ∀ M hjM A, (((ψ M hjM A : M.levi K) : adjointGroup .E8 K) : ModGL .E8 K) = R A :=
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
  have hψψ : ∀ A, ((ψ N hj A : N.levi K) : adjointGroup .E8 K) = (ψ N' hj' A : N'.levi K) :=
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
  have hJ : ({j} : Finset (Fin (Tag.rank .E8))).card ≤ 2 := by simp
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
  have hu : ∀ (M : E8Neighbour) (hjM : j ∈ M.nodes) (hγ : Pi.single j 1 ∈ orthRoots M.root)
      (a : K), leviRootElt M hγ a = ψ M hjM (uSL a) :=
    fun M hjM hγ a => Subtype.ext (Subtype.ext ((coe_leviRootElt M hγ a).trans (hgen a).1.symm))
  have hv : ∀ (M : E8Neighbour) (hjM : j ∈ M.nodes) (hγ : -Pi.single j 1 ∈ orthRoots M.root)
      (a : K), leviRootElt M hγ a = ψ M hjM (vSL a) :=
    fun M hjM hγ a => Subtype.ext (Subtype.ext ((coe_leviRootElt M hγ a).trans (hgen a).2.symm))
  have hP1 : ∀ A, P (A, 1) = h.Φ (ψ N hj A, 1) := fun A => by rw [hPapp, map_one]
  have hQ1 : ∀ A, Q (A, 1) = h'.Φ (ψ N' hj' A, 1) := fun A => by rw [hQapp, map_one]
  have hP1' : ∀ A, P (1, A) = h.Φ (1, ψ N hj A) := fun A => by rw [hPapp, map_one]
  rcases forall_eq_or_forall_eq_of_swap hZ P Q hPinj hQP hdiag hPt hQt with h1 | h1
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

section Overlaps

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] [Finite G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E8 K} {t : G}

theorem SwapNeighbourIso.agreeOn_high_two_of_zero {hX : SwapNeighbourIso e t .high}
    {hY : SwapNeighbourIso e t .two}
    (h0 : hX.AgreeAt hY (Pi.single 0 1) ∧ hX.AgreeAt hY (-Pi.single 0 1)) :
    hX.AgreeOn hY {0, 2, 4, 5, 6} := by
  have h2 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h5 := SwapNeighbourIso.AgreeAt.transfer_single (by decide) (by decide) h0 wordHT
    wordProd_wordHT_single (wordElt_wordHT_mem (Or.inl rfl)) (wordElt_wordHT_mem (Or.inr rfl))
  have h4 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h5
  have h6 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h5
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  exacts [h0, h2, h4, h5, h6]

theorem SwapNeighbourIso.agreeOn_high_six_of_zero {hX : SwapNeighbourIso e t .high}
    {hZ : SwapNeighbourIso e t .six}
    (h0 : hX.AgreeAt hZ (Pi.single 0 1) ∧ hX.AgreeAt hZ (-Pi.single 0 1)) :
    hX.AgreeOn hZ {0, 1, 2, 3} := by
  have h2 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h3 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inl rfl)) h2
  have h1 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inr (Or.inr (Or.inl rfl))) h3
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem SwapNeighbourIso.agreeOn_two_six_of_zero {hY : SwapNeighbourIso e t .two}
    {hZ : SwapNeighbourIso e t .six}
    (h0 : hY.AgreeAt hZ (Pi.single 0 1) ∧ hY.AgreeAt hZ (-Pi.single 0 1)) :
    hY.AgreeOn hZ {0, 2, 7} := by
  have h2 := SwapNeighbourIso.AgreeAt.transfer_pair (by decide) (by decide) (by decide)
    (by decide) (Or.inl rfl) h0
  have h7 := SwapNeighbourIso.AgreeAt.transfer_single (by decide) (by decide) h0 wordTS
    wordProd_wordTS_single (wordElt_wordTS_mem (Or.inl rfl)) (wordElt_wordTS_mem (Or.inr rfl))
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  exacts [h0, h2, h7]

theorem exists_aligned_swapNeighbourIso (hX : SwapNeighbourIso e t .high)
    (hY : SwapNeighbourIso e t .two) (hZ : SwapNeighbourIso e t .six) (hq : 4 ≤ Nat.card K) :
    ∃ (hY' : SwapNeighbourIso e t .two) (hZ' : SwapNeighbourIso e t .six),
      hX.AgreeOn hY' {0, 2, 4, 5, 6} ∧ hX.AgreeOn hZ' {0, 1, 2, 3} ∧
        hY'.AgreeOn hZ' {0, 2, 7} := by
  obtain ⟨hY', hXY⟩ : ∃ hY' : SwapNeighbourIso e t .two,
      hX.AgreeAt hY' (Pi.single 0 1) ∧ hX.AgreeAt hY' (-Pi.single 0 1) := by
    rcases hX.agreeAt_or_agreeAt_flip hY hq (j := 0) (by decide) (by decide) with h0 | h0
    exacts [⟨hY, h0⟩, ⟨hY.flip, h0⟩]
  obtain ⟨hZ', hXZ⟩ : ∃ hZ' : SwapNeighbourIso e t .six,
      hX.AgreeAt hZ' (Pi.single 0 1) ∧ hX.AgreeAt hZ' (-Pi.single 0 1) := by
    rcases hX.agreeAt_or_agreeAt_flip hZ hq (j := 0) (by decide) (by decide) with h0 | h0
    exacts [⟨hZ, h0⟩, ⟨hZ.flip, h0⟩]
  have hYZ : hY'.AgreeAt hZ' (Pi.single 0 1) ∧ hY'.AgreeAt hZ' (-Pi.single 0 1) :=
    ⟨hXY.1.symm.trans hXZ.1 (single_mem_orthRoots (by decide)),
      hXY.2.symm.trans hXZ.2 (neg_single_mem_orthRoots (by decide))⟩
  exact ⟨hY', hZ', SwapNeighbourIso.agreeOn_high_two_of_zero hXY,
    SwapNeighbourIso.agreeOn_high_six_of_zero hXZ, SwapNeighbourIso.agreeOn_two_six_of_zero hYZ⟩

end Overlaps

section LeviPiece

variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E8 K} {t : G}

theorem SwapNeighbourIso.fst_eq_of_agreeOn {N N' : E8Neighbour} (h : SwapNeighbourIso e t N)
    (h' : SwapNeighbourIso e t N') {J : Finset (Fin (Tag.rank .E8))} (hJ : J ⊆ N.nodes)
    (hJ' : J ⊆ N'.nodes) (hT : h.AgreeOn h' J)
    (x : CFSG.LieType.CurtisTits.levi (adjDatumE8 K).rootGroup J) :
    h.fst hJ x = h'.fst hJ' x := by
  set I : Subgroup (adjointGroup .E8 K) := N.levi K ⊓ N'.levi K with hI
  set f : I →* G := (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp
    ((MonoidHom.inl (N.levi K) (N.levi K)).comp (Subgroup.inclusion inf_le_left))) with hf
  set f' : I →* G := (neighbourCore e N').subtype.comp (h'.Φ.toMonoidHom.comp
    ((MonoidHom.inl (N'.levi K) (N'.levi K)).comp (Subgroup.inclusion inf_le_right))) with hf'
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
    have hTγ : h.AgreeAt h' γ := by
      rcases hγj with rfl | rfl
      exacts [(hT j hj).1, (hT j hj).2]
    refine ⟨⟨pinnedX .E8 K γ c, pinnedX_mem_adjointGroup γ c⟩,
      ⟨⟨_, ⟨(leviRootElt N hγN c).2, (leviRootElt N' hγN' c).2⟩⟩, ?_, rfl⟩, rfl⟩
    exact hTγ hγN hγN' c
  have hxR : ((x : adjointGroup .E8 K) : ModGL .E8 K) ∈ rootSpan .E8 K (amalgamRoots J) :=
    mem_subgroupOf.1 ((levi_adjDatumE8_eq (K := K) J).le x.2)
  obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hgen hxR
  have hyx' : ((y : adjointGroup .E8 K)) = x := Subtype.ext hyx
  have h1 : (⟨x, levi_le_neighbourLevi hJ x.2⟩ : N.levi K) = Subgroup.inclusion inf_le_left y :=
    Subtype.ext hyx'.symm
  have h2 : (⟨x, levi_le_neighbourLevi hJ' x.2⟩ : N'.levi K) =
      Subgroup.inclusion inf_le_right y := Subtype.ext hyx'.symm
  rw [SwapNeighbourIso.fst_apply, SwapNeighbourIso.fst_apply, h1, h2]
  exact hy

end LeviPiece

end CFSG.SeitzReduction.E8Pilot
