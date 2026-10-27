module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxDescent
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Classical2
open CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false


def UFrame.ofA2 {τ : Tag} {L : Type} [Field L] {ρ : SL(3, L) →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (h : IsA2Frame ρ σ) {S : Set (Fin τ.rank → ℤ)}
    (hS : {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} = S) : UFrame τ L 3 S where
  ρ := ρ
  r := σ
  ε := fun i j => if hij : i ≠ j then (h.transv i j hij).choose else 1
  inj := h.injective
  isRoot := h.isRoot
  gen := fun i j hij t => by
    simp only [dif_pos hij]
    exact (h.transv i j hij).choose_spec t
  range := by rw [h.range, hS]

theorem f4_short_support : ∀ r ∈ f4ShortList, ∀ i : Fin Tag.F4.rank,
    i.val ∉ TwClass.f4Six.J₂ → r i = 0 := by
  decide +kernel

theorem f4_support_sub : ∀ m : Fin 48,
    (∀ i : Fin Tag.F4.rank, i.val ∉ TwClass.f4Six.J₂ → f4RootVec m i = 0) →
      f4RootVec m ∈ f4ShortList := by
  decide +kernel

theorem f4_long_of_orth : ∀ m : Fin 48,
    (∀ α ∈ f4ShortList, CFSG.LieType.Steinberg.Adjoint.iform (f4RootVec m) α = 0) →
      f4RootVec m ∈ f4LongList := by
  decide +kernel

theorem f4_S₂_eq : TwClass.f4Six.S₂ = {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} := by
  have hSB : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} = {r | r ∈ f4ShortList} := by
    ext r
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact short_img i j hij
    · intro hr
      exact short_cover r hr
  rw [hSB]
  ext r
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hr
    exact f4_support_sub m hs
  · intro hr
    obtain ⟨m, rfl⟩ := list_roots r (List.mem_append_right _ hr)
    exact ⟨isRoot_f4RootVec m, f4_short_support _ hr⟩

theorem f4_S₁_eq : TwClass.f4Six.S₁ =
    {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j} := by
  have hSA : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j} =
      {r | r ∈ f4LongList} := by
    ext r
    simp only [Set.mem_ofPred_eq, f4LongV_smul]
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      exact long_img i j hij
    · intro hr
      obtain ⟨i, j, hij, h⟩ := long_cover r hr
      exact ⟨i, j, hij, h⟩
  rw [hSA]
  ext r
  constructor
  · rintro ⟨hr, hs⟩
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_f4RootVec.1 hr
    refine f4_long_of_orth m fun α hα => hs α ?_
    rw [f4_S₂_eq]
    exact (short_cover α hα)
  · intro hr
    obtain ⟨m, rfl⟩ := list_roots r (List.mem_append_left _ hr)
    refine ⟨isRoot_f4RootVec m, fun α hα => ?_⟩
    rw [f4_S₂_eq] at hα
    obtain ⟨i, j, hij, rfl⟩ := hα
    exact (orth_list _ hr _ (short_img i j hij)).1

theorem f4_pi_short : ∃ k : Fin 6, ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 TwClass.wordF4 *ᵥ f4ShortSigma i j = f4ShortSigma (perm3 k j) (perm3 k i) := by
  decide +kernel

theorem f4_pi_long : ∃ k : Fin 6, ∀ i j : Fin 3, i ≠ j →
    wordMat Tag.F4 TwClass.wordF4 *ᵥ (wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong i j) =
      wordMat Tag.F4 f4LongWord *ᵥ chainRoot f4chainLong (perm3 k j) (perm3 k i) := by
  decide +kernel

theorem f4_hrat {K : Type} [Field K] [Finite K] {w : WeylGroup Tag.F4}
    (D : LangLevi Tag.F4 K w) :
    ∀ P : Subgroup (ModGL Tag.F4 D.L), Finite P → P ≤ adjointGroup Tag.F4 D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb Tag.F4 K D.L).range := by
  intro P _ hPC hPF _
  rw [adjEmb_range, ← (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices
    Tag.F4 (Or.inr rfl) K D.L D.Fr D.hFr).1]
  intro x hx
  exact Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩

theorem f4Six_frames (K : Type) [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    Nat.card ↥(TwClass.f4Six.X₁ D) =
        Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1)) ∧
      Nat.card ↥(TwClass.f4Six.X₂ D) =
        Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 + 1)) ∧
      Nat.card ↥(Subgroup.center ↥(TwClass.f4Six.X₁ D)) = Nat.gcd 3 (Nat.card K + 1) := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hk⟩ := exists_prime_pow_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  haveI : CharP D.L ℓ := by
    have : Fintype K := Fintype.ofFinite K
    haveI : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
    exact (RingHom.charP_iff (algebraMap K D.L) (algebraMap K D.L).injective ℓ).1 inferInstance
  have hne : ((3 : ℕ), ℓ ^ f) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).2
    omega
  let E₂ : UFrame TwClass.f4Six.tag D.L 3 TwClass.f4Six.S₂ :=
    UFrame.ofA2 f4Short_frame f4_S₂_eq.symm
  obtain ⟨k₂, hπ₂⟩ := f4_pi_short
  set π₂ := perm3 k₂ with hπ₂def
  have hπ₂' : ∀ i j : Fin 3, i ≠ j → TwClass.f4Six.w • E₂.r i j = E₂.r (π₂ j) (π₂ i) := by
    intro i j hij
    show (coxeterSystem Tag.F4).wordProd TwClass.wordF4 • f4ShortSigma i j = _
    rw [wordProd_smul_eq_wordMat_mulVec]
    exact hπ₂ i j hij
  obtain ⟨hfin₂, hcard₂, hq₂⟩ := UFrame.fixedRoot_unitary D (by norm_num) E₂ π₂ hπ₂' hℓ hf hk
  let E₁ : UFrame TwClass.f4Six.tag D.L 3 TwClass.f4Six.S₁ :=
    UFrame.ofA2 ((f4Long_frame (L := D.L)).transport f4LongV) f4_S₁_eq.symm
  obtain ⟨k₁, hπ₁⟩ := f4_pi_long
  set π₁ := perm3 k₁ with hπ₁def
  have hπ₁' : ∀ i j : Fin 3, i ≠ j → TwClass.f4Six.w • E₁.r i j = E₁.r (π₁ j) (π₁ i) := by
    intro i j hij
    show (coxeterSystem Tag.F4).wordProd TwClass.wordF4 •
      (f4LongV • chainRoot f4chainLong i j) = f4LongV • chainRoot f4chainLong (π₁ j) (π₁ i)
    rw [f4LongV_smul, f4LongV_smul, wordProd_smul_eq_wordMat_mulVec]
    exact hπ₁ i j hij
  obtain ⟨hfin₁, hcard₁, hq₁⟩ := UFrame.fixedRoot_unitary D (by norm_num) E₁ π₁ hπ₁' hℓ hf hk
  have hq₂' := hq₂ hne
  have hq₁' := hq₁ hne
  have hperf : ∀ S : Set (Fin Tag.F4.rank → ℤ), CFSG.IsQuasisimple ↥(fixedRootGroup D S) →
      ⁅fixedRootGroup D S, fixedRootGroup D S⁆ = fixedRootGroup D S := fun S hS =>
    (commutator_eq_top_iff _).1 (Group.isPerfect_def.1 hS.1)
  obtain ⟨e₁⟩ := frame_equiv_fixed D TwClass.f4Six.S₁ (f4_hrat D) hfin₁ (hperf _ hq₁'.1)
  obtain ⟨e₂⟩ := frame_equiv_fixed D TwClass.f4Six.S₂ (f4_hrat D) hfin₂ (hperf _ hq₂'.1)
  have h3 := card_unitarySet_three (Ω := D.L) (ℓ := ℓ) hf
  refine ⟨?_, ?_, ?_⟩
  · rw [show TwClass.f4Six.X₁ D = D.frame TwClass.f4Six.S₁ from rfl, Nat.card_congr e₁.toEquiv,
      hcard₁, h3, hk]
  · rw [show TwClass.f4Six.X₂ D = D.frame TwClass.f4Six.S₂ from rfl, Nat.card_congr e₂.toEquiv,
      hcard₂, h3, hk]
  · rw [show TwClass.f4Six.X₁ D = D.frame TwClass.f4Six.S₁ from rfl,
      natCard_center_eq_of_mulEquiv e₁, hq₁'.2, hk]

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux
