module

public import CFSG.ClassicalInvolution.Asc77.AscBSE6

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSE

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.BSC.BSD
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => CFSG.ClassicalInvolution.Generic.CoreAssembly.conjClass

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


theorem false_of_five_fund_plus (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ} (ht : t = .POmegaPlus) (hn : n = 4)
    (hadm : StatedLieAdmissible t n p e) {X : Type*} [Group X]
    (φ : (modelUniv t n p e Fact.out).K →* X)
    (hφ : φ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K)
    (R : Fin 5 → Subgroup (modelUniv t n p e Fact.out).K)
    (hR : ∀ i, R i ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hRinj : Function.Injective R) (r : Fin 5 → (modelUniv t n p e Fact.out).K)
    (hr : ∀ i, IsInvIn (R i) (r i)) (hφr : ∀ i, φ (r i) = φ (r 0)) : False := by
  subst ht hn
  have hn3 : 3 ≤ 4 := by omega
  have hsf := spinFund_plus_four hp2 hq hadm
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p e)),
      plusDatum 4 (GaloisField p e) hn3⟩ → ∀ (φ : M.K →* X), φ.ker ≤ Subgroup.center M.K →
      ∀ (R : Fin 5 → Subgroup M.K), (∀ i, R i ∈ fundamentalSubgroups .POmegaPlus M.D) →
      Function.Injective R → ∀ (r : Fin 5 → M.K), (∀ i, IsInvIn (R i) (r i)) →
      (∀ i, φ (r i) = φ (r 0)) → False := by
    intro M hM φ hφ R hR hRinj r hr hφr
    subst hM
    exact hsf.false_of_five φ hφ R r hR hRinj (fun i => (hr i).1) (fun i => (hr i).2.1)
      (fun i => (hr i).2.2) hφr
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) φ hφ R hR hRinj r hr hφr

theorem false_of_d4_many {C : XCtx p f (𝒞 K) z}
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) {b : Fin C.D.card}
    (hD4 : C.D.tag b = .POmegaPlus) (hrank : C.D.rank b = 4) (hcard : 6 ≤ C.D.card) : False := by
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := fun h => by
    rw [hD4] at h
    exact absurd h.1 (by decide)
  have hexp : C.D.exp b = f := C.exp_eq b (by rw [hD4]; decide)
  have hq : 5 ≤ p ^ C.D.exp b := by rw [hexp]; exact C.hq
  obtain ⟨N, m, hinj, hN⟩ := exists_conj_twins hno hb
  obtain ⟨idx, hidx⟩ : ∃ idx : Fin 5 → {j : Fin C.D.card // j ≠ b}, Function.Injective idx := by
    have hle : Fintype.card (Fin 5) ≤ Fintype.card {j : Fin C.D.card // j ≠ b} := by
      rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
    exact ⟨e, e.injective⟩
  obtain ⟨-, h0cl, -⟩ := hN (idx 0)
  have hmsq : m * m = 1 := (isCentralInvolution_of_isClassicalMember h0cl).sq
  have hm1 : m ≠ 1 := (isCentralInvolution_of_isClassicalMember h0cl).ne_one
  obtain ⟨-, -, -, -, -, -, -, hm0, -⟩ := hN (idx 0)
  have hex : ∀ i, ∃ R ∈ fundamentalSubgroups (C.D.tag b) (compModel C.D b).D,
      modOdd z (exactCore z (N (idx i))) = R.map (C.psi b) ∧
        ∃ r ∈ R, C.psi b r = oddQuotMk z ⟨m, hm0⟩ := fun i => by
    obtain ⟨-, -, R, hR, himg, r, hrR, hm, hr⟩ := hN (idx i)
    exact ⟨R, hR, himg, r, hrR, hr⟩
  choose R hRfund himg r hrR hrψ using hex
  have hRinj : Function.Injective R := fun i j hij =>
    hidx (hinj ((hN (idx i)).eq_of_fund_eq (hN (idx j)) (himg i) (himg j) hij))
  have hinv : ∀ i, IsInvIn (R i) (r i) := fun i =>
    isInvIn_of_psi_eq hb (hRfund i) (hrR i) hm0 hmsq hm1 (hrψ i)
  exact false_of_five_fund_plus (p := p) C.hp hq hD4 hrank (C.D.admissible b) (C.psi b)
    (C.psi_ker b) R hRfund hRinj r hinv (fun i => (hrψ i).trans (hrψ 0).symm)

end CFSG.ClassicalInvolution.Asc77.BSC.BSE
