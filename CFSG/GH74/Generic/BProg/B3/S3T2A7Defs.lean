module

public import CFSG.GH74.GLS.Types
public import CFSG.Assembly.OddCoreSpan

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def IsA7A11Quot (X : Type) [Group X] : Prop :=
  Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 11))

@[expose] def SecGH (Y : Type) [Group Y] : Prop :=
  ∀ (H : Subgroup Y) (N : Subgroup ↥H) (_ : N.Normal), IsSimpleGroup (↥H ⧸ N) →
    (∃ u v : ↥H ⧸ N, u * v ≠ v * u) → GHList (↥H ⧸ N)

structure Setting125 (Y : Type) [Group Y] (L B X₀ : Subgroup Y) (z : Y) : Prop where
  core : pPrimeCore 2 Y = ⊥
  sec4 : SectionalTwoRankLE Y 4
  secGH : SecGH Y
  comp : CFSG.IsComponent L
  B_el : CFSG.IsElementaryAbelian 2 ↥B
  B_rank : pRank 2 ↥B = 4
  z_mem : z ∈ B
  z_ne : z ≠ 1
  z_cent : z ∈ center Y
  gamma : gammaK 2 B 3 ≤ X₀

@[expose] def Sig125 {Y : Type} [Group Y] (L X₀ : Subgroup Y) : Prop :=
  ∃ w ∈ pPrimeCoreOf 2 X₀, w ∈ normalizer (L : Set Y) ∧ w ∉ centralizer (L : Set Y)

@[expose] def Cut125 {Y : Type} [Group Y] (L B : Subgroup Y) : Prop :=
  ∃ f ∈ B, f ∈ normalizer (L : Set Y) ∧ f ∉ centralizer (L : Set Y) ∧
    ∃ n ∈ CFSG.Assembly.Dichotomy.involutionOddCore f, n ∈ normalizer (L : Set Y) ∧
      n ∉ centralizer (L : Set Y)

@[expose] def Lem125p2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L B X₀ : Subgroup Y) (z : Y), Setting125 Y L B X₀ z →
    Sig125 L X₀ → Cut125 L B → IsA7A11Quot ↥L

@[expose] def Cell125 (P : ∀ (T : Type) [Group T], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L B X₀ : Subgroup Y) (z : Y), Setting125 Y L B X₀ z →
    P (↥L ⧸ center ↥L) → Sig125 L X₀ → Cut125 L B → False

@[expose] def LocBal1Two (T : Type*) [Group T] : Prop :=
  ∀ H : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ H →
    ∀ t : ↥H, orderOf t = 2 → CFSG.Assembly.Dichotomy.involutionOddCore t = ⊥

@[expose] def LocBal1For (P : ∀ (T : Type) [Group T], Prop) : Prop :=
  ∀ (T : Type) [Group T] [Finite T], P T → LocBal1Two T

@[expose] def SporGH (T : Type) [Group T] : Prop :=
  NativeSporadic.IsSporadic T .M11 ∨ NativeSporadic.IsSporadic T .M12 ∨
    NativeSporadic.IsSporadic T .M22 ∨ NativeSporadic.IsSporadic T .M23 ∨
    NativeSporadic.IsSporadic T .J1 ∨ NativeSporadic.IsSporadic T .J2 ∨
    NativeSporadic.IsSporadic T .J3 ∨ NativeSporadic.IsSporadic T .McL ∨
    NativeSporadic.IsSporadic T .Ly

@[expose] def Even2GH (T : Type) [Group T] : Prop :=
  LieModel T .PSL 2 2 3 ∨ LieModel T .PSL 2 2 4 ∨ LieModel T .PSU 3 2 2 ∨
    LieModel T .twistedB2 0 2 3

@[expose] def L34 (T : Type) [Group T] : Prop :=
  LieModel T .PSL 3 2 2

@[expose] def Alt810 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* alternatingGroup (Fin 8)) ∨ Nonempty (T ≃* alternatingGroup (Fin 10))

@[expose] def Alt9 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* alternatingGroup (Fin 9))

@[expose] def OddL2 (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel T .PSL 2 p f

@[expose] def OddL3 (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ (LieModel T .PSL 3 p f ∨ LieModel T .PSU 3 p f)

@[expose] def OddSp4 (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel T .PSp 2 p f

@[expose] def OddG2 (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel T .G2 0 p f

@[expose] def Odd3D4 (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel T .trialityD4 0 p f

@[expose] def OddL4 (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
    ((p ^ f % 8 ≠ 1 ∧ LieModel T .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel T .PSU 4 p f))

@[expose] def OddL5 (T : Type) [Group T] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧
    ((p ^ f % 4 = 3 ∧ LieModel T .PSL 5 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel T .PSU 5 p f))

@[expose] def Ree2G2 (T : Type) [Group T] : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ LieModel T .twistedG2 0 3 f

end CFSG.GH74.Generic.BProg.B3.S3T2A7
