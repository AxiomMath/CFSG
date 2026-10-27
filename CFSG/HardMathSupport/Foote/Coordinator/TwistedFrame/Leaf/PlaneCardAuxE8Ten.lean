module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxE6
public import CFSG.RankThree.PartOne.TCX.E.E8Five

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints adjEmb adjEmb_range
  adjEmb_frobenius wordProd_smul_eq_wordMat_mulVec commutator_eq_top_iff sigmaRootE8A4
  sigmaRootE8A4_eq_smul sigmaSetE8A4 sigmaSetE8A4_eq e8RootVec isRoot_e8RootVec
  isRoot_iff_exists_e8RootVec e8a4chain)

open CFSG.RankThree.PartOne.TCX.E CFSG.RankThree.Classical2
open CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem single_apply_eq_zero_of_mem {n : ℕ} {J : Finset ℕ} {k i : Fin n} (hk : k.val ∈ J)
    (hi : i.val ∉ J) : (Pi.single k (1 : ℤ) : Fin n → ℤ) i = 0 :=
  Pi.single_eq_of_ne (fun h => hi (by rw [h]; exact hk)) 1

theorem e8Ten_support_sub : ∀ m : Fin 240,
    (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → e8RootVec m i = 0) →
      e8RootVec m ∈ e8ListA := by
  decide +kernel

theorem e8Ten_listA_support : ∀ r ∈ e8ListA, ∀ i : Fin Tag.E8.rank,
    i.val ∉ TwClass.e8Ten.J₂ → r i = 0 := by
  decide +kernel

theorem e8Ten_orth_sub : ∀ m : Fin 240,
    (∀ k : Fin Tag.E8.rank, k.val ∈ TwClass.e8Ten.J₂ →
      iform (e8RootVec m) (Pi.single k 1) = 0) → e8RootVec m ∈ e8ListB := by
  decide +kernel

theorem e8Ten_listB_orth : ∀ β ∈ e8ListB, ∀ α ∈ e8ListA, iform β α = 0 := by
  decide +kernel

theorem e8Ten_piA : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain (Fin.rev j) (Fin.rev i) := by
  decide +kernel

theorem e8Ten_piB : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 TwClass.wordE8Ten *ᵥ (wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain (Fin.rev j) (Fin.rev i) := by
  decide +kernel

theorem e8Ten_S₂_eq : TwClass.e8Ten.S₂ = {r | r ∈ e8ListA} := by
  ext r
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    exact e8Ten_support_sub m hs
  · intro hr
    obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_left _ hr)
    exact ⟨isRoot_e8RootVec m, e8Ten_listA_support _ hr⟩

theorem e8Ten_S₁_eq : TwClass.e8Ten.S₁ = {r | r ∈ e8ListB} := by
  ext r
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e8RootVec.1 hr
    exact e8Ten_orth_sub m fun k hk =>
      hs (Pi.single k 1) ⟨isRoot_single _ k, fun i hi => single_apply_eq_zero_of_mem hk hi⟩
  · intro hr
    obtain ⟨m, rfl⟩ := e8_list_roots r (List.mem_append_right _ hr)
    refine ⟨isRoot_e8RootVec m, fun α hα => ?_⟩
    have hα' : α ∈ e8ListA := by
      have := e8Ten_S₂_eq ▸ hα
      exact this
    exact e8Ten_listB_orth _ hr α hα'

theorem e8VA_set : sigmaSetE8A4 e8VA = {r | r ∈ e8ListA} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_ofPred_eq, sigmaRootE8A4_eq_smul, e8VA_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact e8A_img i j hij
  · intro hr
    exact e8A_cover r hr

theorem e8VB_set : sigmaSetE8A4 e8VB = {r | r ∈ e8ListB} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_ofPred_eq, sigmaRootE8A4_eq_smul, e8VB_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact e8B_img i j hij
  · intro hr
    exact e8B_cover r hr

theorem e8Ten_S₂_emb_eq : sigmaSetE8A4 e8VA = TwClass.e8Ten.S₂ := by
  rw [e8VA_set, e8Ten_S₂_eq]

theorem e8Ten_S₁_emb_eq : sigmaSetE8A4 e8VB = TwClass.e8Ten.S₁ := by
  rw [e8VB_set, e8Ten_S₁_eq]

theorem e8Ten_frames (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) :
    Nat.card ↥(TwClass.e8Ten.X₁ D) = Nat.card K ^ 10 * ((Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 3 + 1) * ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 5 + 1))) ∧
      Nat.card ↥(TwClass.e8Ten.X₂ D) = Nat.card K ^ 10 * ((Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 3 + 1) * ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 5 + 1))) ∧
      Nat.card ↥(Subgroup.center ↥(TwClass.e8Ten.X₁ D)) = Nat.gcd 5 (Nat.card K + 1) := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hk⟩ := exists_prime_pow_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  haveI : CharP D.L ℓ := charP_langLevi D hℓ hk
  have hne : ((5 : ℕ), ℓ ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  let E₂ : UFrame TwClass.e8Ten.tag D.L 5 TwClass.e8Ten.S₂ :=
    (UFrame.ofAn (e8A4Embedding e8VA) D.L).cast e8Ten_S₂_emb_eq
  have hπ₂' : ∀ i j : Fin 5, i ≠ j →
      TwClass.e8Ten.w • E₂.r i j = E₂.r (Fin.revPerm j) (Fin.revPerm i) := by
    intro i j hij
    show (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • sigmaRootE8A4 e8VA i j =
      sigmaRootE8A4 e8VA (Fin.rev j) (Fin.rev i)
    rw [sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul, e8VA_smul, e8VA_smul,
      wordProd_smul_eq_wordMat_mulVec]
    exact e8Ten_piA i j hij
  obtain ⟨hfin₂, hcard₂, hq₂⟩ := UFrame.fixedRoot_unitary D (by norm_num) E₂ Fin.revPerm hπ₂' hℓ hf hk
  let E₁ : UFrame TwClass.e8Ten.tag D.L 5 TwClass.e8Ten.S₁ :=
    (UFrame.ofAn (e8A4Embedding e8VB) D.L).cast e8Ten_S₁_emb_eq
  have hπ₁' : ∀ i j : Fin 5, i ≠ j →
      TwClass.e8Ten.w • E₁.r i j = E₁.r (Fin.revPerm j) (Fin.revPerm i) := by
    intro i j hij
    show (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten • sigmaRootE8A4 e8VB i j =
      sigmaRootE8A4 e8VB (Fin.rev j) (Fin.rev i)
    rw [sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul, e8VB_smul, e8VB_smul,
      wordProd_smul_eq_wordMat_mulVec]
    exact e8Ten_piB i j hij
  obtain ⟨hfin₁, hcard₁, hq₁⟩ := UFrame.fixedRoot_unitary D (by norm_num) E₁ Fin.revPerm hπ₁' hℓ hf hk
  have hq₂' := hq₂ hne
  have hq₁' := hq₁ hne
  obtain ⟨e₁⟩ := frame_equiv_fixed D TwClass.e8Ten.S₁
    (hrat_perfect (Or.inr (Or.inr ⟨rfl, rfl⟩)) D) hfin₁ (fixedRootGroup_perfect D _ hq₁'.1)
  obtain ⟨e₂⟩ := frame_equiv_fixed D TwClass.e8Ten.S₂
    (hrat_perfect (Or.inr (Or.inr ⟨rfl, rfl⟩)) D) hfin₂ (fixedRootGroup_perfect D _ hq₂'.1)
  have h5 := card_unitarySet_five (Ω := D.L) (ℓ := ℓ) hf
  refine ⟨?_, ?_, ?_⟩
  · rw [show TwClass.e8Ten.X₁ D = D.frame TwClass.e8Ten.S₁ from rfl, Nat.card_congr e₁.toEquiv,
      hcard₁, h5, hk]
  · rw [show TwClass.e8Ten.X₂ D = D.frame TwClass.e8Ten.S₂ from rfl, Nat.card_congr e₂.toEquiv,
      hcard₂, h5, hk]
  · rw [show TwClass.e8Ten.X₁ D = D.frame TwClass.e8Ten.S₁ from rfl,
      natCard_center_eq_of_mulEquiv e₁, hq₁'.2, hk]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux
