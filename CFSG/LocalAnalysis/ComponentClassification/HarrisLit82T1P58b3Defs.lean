module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Config
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3L57
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Frame
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bOZ
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Residual

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def Harris82Lemma58bThreeRow (τ : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z₁ z₂ : G), orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ →
    z₁ * z₂ = z₂ * z₁ → ∀ L₁ L₂ K : Subgroup G,
    IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) →
    (IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∨
      IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) →
    z₁ ∈ L₁ → z₂ ∈ L₂ → Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) →
    IsTwoComponentIn K (centralizer {z₁}) → GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K →
    GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K →
    centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) →
    ∀ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K) →
    ∀ f : ℕ, Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) τ n 3 f →
      (∃ m : ℕ, IsCoverOf .POmegaOdd m 3 1 2 (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      ((IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∧
          ∃ (τ' : StatedLieTag) (n' : ℕ),
            Blueprint.LieModel (↥L₂ ⧸ Open.fusionZStar ↥L₂) τ' n' 3 1) →
        ∃ m : ℕ, Odd m ∧ 5 ≤ m ∧ IsCoverOf .POmegaOdd m 3 1 2 (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      (Nonempty (↥L₂ ⧸ pPrimeCore 2 ↥L₂ ≃* SL(2, ZMod 3)) →
        IsCoverOf .POmegaOdd 3 3 1 2 (↥K ⧸ pPrimeCore 2 ↥K))

namespace P58b3

theorem one_le_of_isCoverOf {Y : Type} [Group Y] {m p r : ℕ}
    (h : IsCoverOf .POmegaOdd m p r 2 Y) : 1 ≤ r := by
  obtain ⟨-, -, hm⟩ := h
  rcases hm with ⟨-, ⟨-, hr, -⟩, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact hr
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem ne_zero_of_isCoverOf {Y : Type} [Group Y] {m p r : ℕ}
    (h : IsCoverOf .POmegaOdd m p r 2 Y) : m ≠ 0 := by
  obtain ⟨-, -, hm⟩ := h
  rcases hm with ⟨-, ⟨-, -, hn, -⟩, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · omega
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem ordProj_card_multiplier_POmegaOdd (hGA : TBLit.GriessMultipliersAllModels)
    {S : Type} [Group S] {m : ℕ} (hm : Blueprint.LieModel S .POmegaOdd m 3 1) (hm0 : m ≠ 0) :
    ordProj[2] (Nat.card (Open.griessHopfMultiplier S)) = 2 := by
  rw [card_griessHopfMultiplier_eq hGA (models_lieModel_of_lieModel_of_ne_zero hm0 hm)]
  have hg : Blueprint.Multiplier.genericOrders .POmegaOdd m 3 1 = (2, 1) := rfl
  rw [hg, factorization_two_mul_odd (by norm_num) (P58b.odd_exceptionalOrders_POmegaOdd m 3 1)]
  norm_num

theorem isMTypeSchur_of_cover (hGA : TBLit.GriessMultipliersAllModels) {K : Type} [Group K]
    [Finite K] (hK : IsTwoQuasisimple K) (hch : IsSimpleChevalleyOver 3 (K ⧸ Open.fusionZStar K))
    {c : K} (hc2 : orderOf c = 2) (hcZ : c ∈ center K) {m : ℕ}
    (hcov : IsCoverOf .POmegaOdd m 3 1 2 (K ⧸ pPrimeCore 2 K)) : IsMTypeSchur 3 K := by
  refine .inl ⟨hK, hch, ?_, fun n r _ _ _ => ?_⟩
  · have hcZ' : c ∈ Open.fusionZStar K := F3.mem_fusionZStar_of_mem_center hcZ
    have h1 := orderOf_dvd_natCard (⟨c, hcZ'⟩ : Open.fusionZStar K)
    rw [Subgroup.orderOf_mk, hc2] at h1
    exact even_iff_two_dvd.mpr h1
  · rw [Frame.ordProj_card_fusionZStar, hcov.2.1]
    obtain ⟨e⟩ := L35.nonempty_fusionZStar_quotient_equiv K
    exact (ordProj_card_multiplier_POmegaOdd hGA
      (GSThmB.OddQuot.lieModel_of_equiv e.symm hcov.2.2) (ne_zero_of_isCoverOf hcov)).symm

theorem not_isQuasisimple_of_isSolvableTwoComponentIn {G : Type} [Group G] {L A : Subgroup G}
    (hL : IsSolvableTwoComponentIn L A) : ¬ IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) := by
  intro hq
  have h3 : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hSL : Group.IsSolvable SL(2, ZMod 3) :=
    LieType.HighestRoot.isSolvable_of_mulEquiv h3 (MulEquiv.refl _)
  have hsol : Group.IsSolvable (↥L ⧸ pPrimeCore 2 ↥L) := by
    rcases hL.2.2.2 with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have : Group.IsSolvable PSL(2, ZMod 3) :=
        Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
      exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    · exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have := hq.1
  exact Group.IsPerfect.not_isSolvable _ hsol

theorem not_isCoverOf_seven (h51e : Harris82Lemma51eOdd) {G : Type} [Group G] [Finite G]
    {z₁ z₂ : G} (hz₂ : orderOf z₂ = 2) {L₂ K : Subgroup G}
    (hL₂ : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∨
      IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}))
    (hz₂L : z₂ ∈ L₂) (hKc : IsTwoComponentIn K (centralizer {z₁}))
    (hO₂ : GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K) (hz₂K : z₂ ∈ K)
    (hz₂Z : (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K))
    (hch : IsSimpleChevalleyOver 3 (↥K ⧸ Open.fusionZStar ↥K)) (r : ℕ) :
    ¬ IsCoverOf .POmegaOdd 3 3 r 2 (↥L₂ ⧸ pPrimeCore 2 ↥L₂) := by
  intro hcov
  rcases hL₂ with hL₂ | hL₂
  · have : Group.IsPerfect ↥L₂ := hL₂.2.2.1
    have hL₂K : L₂ ≤ K :=
      (Sol78.le_oPrimeResidualOf le_rfl primeResidual_eq_top_of_isPerfect).trans hO₂
    have hle : K ⊓ centralizer {z₂} ≤ centralizer {z₁} ⊓ centralizer {z₂} :=
      inf_le_inf_right _ hKc.1
    have hJ : IsTwoComponentIn L₂ (K ⊓ centralizer {z₂}) :=
      ⟨le_inf hL₂K (hL₂.1.trans inf_le_right), F3L57.isSubnormal_subgroupOf_of_le hle hL₂.2.1,
        hL₂.2.2⟩
    let eJ : ↥(L₂.subgroupOf K) ≃* ↥L₂ := subgroupOfEquivOfLe hL₂K
    exact F3S7.false_of_lemma51eOdd h51e hKc.2.2 Nat.prime_three (by norm_num) hch
      (by rw [Subgroup.orderOf_mk]; exact hz₂) hz₂Z (isTwoComponentIn_subgroupOf_inf hz₂K hJ)
      (mem_subgroupOf.mpr hz₂L) (one_le_of_isCoverOf hcov)
      (isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eJ.symm (pPrimeCore_map_iso 2 eJ.symm))
        hcov)
  · exact not_isQuasisimple_of_isSolvableTwoComponentIn hL₂ hcov.1

end P58b3

theorem harris82Lemma58bThree_of_rows (h51e : Harris82Lemma51eOdd)
    (hGA : TBLit.GriessMultipliersAllModels) (hrow : ∀ τ n, Harris82Lemma58bThreeRow τ n) :
    Harris82Lemma58bThree := by
  intro G _ _ z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ K hL₁ hL₂ hz₁L hz₂L he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z hch
  obtain ⟨τ, n, f, hm⟩ := hch
  obtain ⟨⟨m, hcov⟩, hB, hC⟩ := hrow τ n G z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ K hL₁ hL₂ hz₁L hz₂L he₁
    hKc hO₁ hO₂ hN hz₂K hz₂Z f hm
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  have hz₁Z := mem_center_of_le_centralizer hKc.1 hz₁K
  have hz₁2 : orderOf (⟨z₁, hz₁K⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hz₁
  exact ⟨P58b3.isMTypeSchur_of_cover hGA hKc.2.2 ⟨τ, n, f, hm⟩ hz₁2 hz₁Z hcov, hB, hC,
    P58b3.not_isCoverOf_seven h51e hz₂ hL₂ hz₂L hKc hO₂ hz₂K hz₂Z ⟨τ, n, f, hm⟩⟩

end CFSG.ComponentClassification.HarrisLit.T1
