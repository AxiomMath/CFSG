module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank
open scoped commutatorElement

theorem pRank_two_eq_twoRank (G : Type) [Group G] [Finite G] :
    pRank 2 G = CFSG.Open.twoRank G :=
  CFSG.SectionRank.pRank_eq_open_pRank_top 2 G

theorem InB2.inT2 {K : Type} [Group K] (h : InB2 K) : InT2 K := h.1

@[expose] def C23List (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((5 ≤ p ^ f ∧ LieModel G .PSL 2 p f) ∨
      LieModel G .PSL 3 p f ∨ LieModel G .PSU 3 p f ∨
      (3 < p ^ f ∧ (LieModel G .PSp 2 p f ∨ LieModel G .G2 0 p f)) ∨
      LieModel G .trialityD4 0 p f ∨
      (3 < p ^ f ∧ ((p ^ f % 8 ≠ 1 ∧ LieModel G .PSL 4 p f) ∨
        (p ^ f % 8 ≠ 7 ∧ LieModel G .PSU 4 p f))))) ∨
    (∃ f : ℕ, LieModel G .twistedG2 0 3 f) ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨ Nonempty (G ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 10)) ∨ Nonempty (G ≃* alternatingGroup (Fin 11)) ∨
    NativeSporadic.IsSporadic G .M11 ∨ LieModel G .PSU 3 2 2 ∨
    NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .J1 ∨
    NativeSporadic.IsSporadic G .McL ∨ NativeSporadic.IsSporadic G .Ly ∨
    NativeSporadic.IsSporadic G .ONan

@[expose] def C2StarList (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((3 < p ^ f ∧ (LieModel G .PSL 2 p f ∨ LieModel G .PSp 2 p f ∨ LieModel G .G2 0 p f)) ∨
      LieModel G .PSL 3 p f ∨ LieModel G .PSU 3 p f ∨
      LieModel G .trialityD4 0 p f ∨
      (3 < p ^ f ∧ ((p ^ f % 8 ≠ 1 ∧ LieModel G .PSL 4 p f) ∨
        (p ^ f % 8 ≠ 7 ∧ LieModel G .PSU 4 p f))))) ∨
    (∃ f : ℕ, LieModel G .twistedG2 0 3 f) ∨
    LieModel G .PSU 3 2 2 ∨ Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    NativeSporadic.IsSporadic G .M11 ∨
    NativeSporadic.IsSporadic G .M12 ∨ NativeSporadic.IsSporadic G .J1 ∨
    NativeSporadic.IsSporadic G .McL ∨ NativeSporadic.IsSporadic G .Ly ∨
    NativeSporadic.IsSporadic G .ONan

@[expose] def HasC2StarHypothesis (G : Type) [Group G] : Prop :=
  pRank 2 G = 2 ∨
    (pRank 2 G = 3 ∧ ∃ (x : G) (K : Subgroup G), IsIL2Pair x K ∧
      (Nonempty ((↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin 7)) ∨
        HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun q => Odd q ∧ 3 < q))) ∨
    HasTwoThinConfiguration G

@[expose] def S_C23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsSpecialOddType G → C23List G

@[expose] def S_C23Ge3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsSpecialOddType G → 3 ≤ pRank 2 G →
    C23List G

@[expose] def S_C2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLB2Type G →
    ¬ HasTwoUniquenessSubgroup G →
      C23List G ∧ ¬ LieModel G .PSU 3 2 2 ∧ ¬ NativeSporadic.IsSporadic G .J1 ∧
        ¬ Nonempty (G ≃* alternatingGroup (Fin 5)) ∧ ¬ Nonempty (G ≃* alternatingGroup (Fin 9)) ∧
        ¬ Nonempty (G ≃* alternatingGroup (Fin 10)) ∧ ¬ Nonempty (G ≃* alternatingGroup (Fin 11))

@[expose] def S_SUS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLB2Type G →
    HasTwoUniquenessSubgroup G →
      LieModel G .PSL 2 2 2 ∨ LieModel G .PSU 3 2 2 ∨ NativeSporadic.IsSporadic G .J1

@[expose] def S_prop27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLB2Type G → pRank 2 G = 3 →
    L2Sub G InC2 → L2Meets G (fun K _ => HasL2Model K IsFM9)

@[expose] def S_C2star : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → HasC2StarHypothesis G → C2StarList G

@[expose] def S_corTwoThin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 4 ≤ pRank 2 G → L2Meets G InG2 →
    ¬ HasTwoThinConfiguration G

@[expose] def S_C3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLT2oType G →
    ¬ IsRestrictedEvenType G →
      Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ Nonempty (G ≃* alternatingGroup (Fin 10)) ∨
        Nonempty (G ≃* alternatingGroup (Fin 11))

@[expose] def S_C3o : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLT2oType G →
    IsEvenType G ∨ Nonempty (G ≃* alternatingGroup (Fin 11))

@[expose] def sylowBar {G : Type*} [Group G] (z : G) (S : Sylow 2 ↥(centralizer ({z} : Set G))) :
    Subgroup (CentralizerBar z) :=
  (S : Subgroup ↥(centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G))))

@[expose] def S_stage1_thm1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → pRank 2 G ≤ 2 →
    ∃ (Gs : Type) (_ : Group Gs), IsTwoTerminalGStarType G Gs ∧
      (HasL2Model Gs Odd ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
          (LieModel Gs .PSL 3 p f ∨ LieModel Gs .PSU 3 p f)) ∨
        LieModel Gs .PSU 3 2 2)

@[expose] def S_stage1_thm2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G →
    (∃ (x : G) (K : Subgroup G), IsTwoTerminal x K ∧ pRank 2 ↥K = 1) →
      ∃ z : G, IsStronglyClassicalInvolution G z ∧
        ∃ t : G, t ∈ centralizer ({z} : Set G) ∧ IsConj z t ∧ t ∉ zStar (rigidProduct z)

@[expose] def S_stage1_thm5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → HasTwoThinConfiguration G →
    ∃ (Gs : Type) (_ : Group Gs), InTarget2 Gs ∧ IsTwoTerminalGStarType G Gs

@[expose] def S_stage1_thm6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → pRank 2 G = 3 →
    L2Meets G (fun K _ => Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
      HasL2Model K (fun q => Odd q ∧ 3 < q)) →
      ∃ (Gs : Type) (_ : Group Gs), IsTwoTerminalGStarType G Gs ∧
        (IsReeGroup Gs ∨ NativeSporadic.IsSporadic Gs .J1 ∨ NativeSporadic.IsSporadic Gs .M12)

@[expose] def InStage2List (K : Type) [Group K] : Prop :=
  HasL2Model K (fun q => Odd q ∧ 3 < q) ∨ HasSL2Model K (fun q => Odd q ∧ 3 < q) ∨
    Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
    (∃ n : ℕ, 8 ≤ n ∧ n ≤ 11 ∧ IsDoubleCoverOfAlt K n) ∨
    (IsQuasisimple K ∧ Nat.card (center K) = 4 ∧ IsCyclic ↥(center K) ∧ IsL34Quotient K)

@[expose] def S_stage2_thm11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLBStar2Type G →
    L2Sub G InStage2List ∧ ¬ L2Meets G InG2

@[expose] def S_stage4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → IsLBStar2Type G → pRank 2 G = 3 →
    ¬ HasTwoUniquenessSubgroup G →
      (∃ f : ℕ, LieModel G .twistedG2 0 3 f) ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 3 < p ^ f ∧ LieModel G .G2 0 p f) ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel G .trialityD4 0 p f) ∨
        IsApproxTo G (NativeSporadic.Carrier .M12) ∨ IsApproxTo G (NativeSporadic.Carrier .ONan)

@[expose] def S_stage5_SP : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G →
    ∀ (Gs : Type) [Group Gs], (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧ LieModel Gs .PSp 2 p f) →
      IsTwoCentralClassicalType G Gs → Nonempty (G ≃* Gs)

@[expose] def S_stage5_LU : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G →
    ∀ (Gs : Type) [Group Gs], (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
        ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f))) →
      IsTwoCentralClassicalType G Gs → Nonempty (G ≃* Gs)

@[expose] def S_sixteenOne (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    SameCentralizerOfInvolutionPattern G (NativeSporadic.Carrier s) →
    (s = .M11 → Nat.card G = Nat.card (NativeSporadic.Carrier s)) →
      NativeSporadic.IsSporadic G s

@[expose] def S_twoThinOfB2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → 3 ≤ pRank 2 G → ¬ L2Meets G InG2 →
    L2Meets G InB2 → HasTwoThinConfiguration G

end CFSG.GH74.GLS
