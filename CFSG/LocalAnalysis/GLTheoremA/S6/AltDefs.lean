module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def isAltN (n : ℕ) : TauCeti.CFSGIndex → Prop
  | .alternating m _ => m = n
  | _ => False

section Perm

variable {G : Type} [Group G] [Finite G]

@[expose] def IsAltPType (p : ℕ) (L : Subgroup G) (n : ℕ) : Prop :=
  Nonempty (PQuot p L ≃* ↥(alternatingGroup (Fin n)))

@[expose] def movedLettersOf {Q : Type} [Group Q] {N : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin N)))
    (H : Subgroup Q) : Set (Fin N) :=
  {i | ∃ h ∈ H, ((e h : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) i ≠ i}

@[expose] def MovesExactly {Q : Type} [Group Q] {N : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin N)))
    (H : Subgroup Q) (k : ℕ) : Prop :=
  (movedLettersOf e H).ncard = k

@[expose] def IsRootAlt {Q : Type} [Group Q] {N : ℕ} (e : Q ≃* ↥(alternatingGroup (Fin N)))
    (H : Subgroup Q) (m : ℕ) : Prop :=
  Nonempty (↥H ≃* ↥(alternatingGroup (Fin m))) ∧ MovesExactly e H m

open Classical in
@[expose] noncomputable def permOfMod (p : ℕ) (L : Subgroup G) (n : ℕ)
    (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) (y : G) : Equiv.Perm (Fin n) :=
  if hy : y ∈ L then
    ((e (QuotientGroup.mk (⟨y, hy⟩ : ↥L) : PQuot p L) : alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n))
  else 1

@[expose] def IsPCycleMod (p : ℕ) (L : Subgroup G) (n : ℕ)
    (e : PQuot p L ≃* ↥(alternatingGroup (Fin n))) (y : G) : Prop :=
  y ∈ L ∧ (permOfMod p L n e y).cycleType = {p}

@[expose] def altDxy (x y : G) : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers y

structure AltSetup (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (n : ℕ) (y : G)
    (J : Subgroup G) : Prop where
  alt : IsAltPType p L n
  three_mul_le : 3 * p ≤ n
  seven_lt : 7 < n
  y_mem : y ∈ L
  y_order : orderOf y = p
  isElemAbelian_D : IsElemAbelian p (altDxy x y)
  card_D : Nat.card ↥(altDxy x y) = p ^ 2
  cycle : ∃ e : PQuot p L ≃* ↥(alternatingGroup (Fin n)), IsPCycleMod p L n e y ∧
    (imageMod p L J).map e.toMonoidHom =
      fixingSubgroup (alternatingGroup (Fin n)) ((permOfMod p L n e y).support : Set (Fin n))
  J_comp : GLAPComponent p (L ⊓ Subgroup.centralizer (altDxy x y : Set G)) J
  J_layer : GLAPLayer p (L ⊓ Subgroup.centralizer (altDxy x y : Set G)) = J
  J_alt : IsAltPType p J (n - p)
  B_eq : IsDirectZpowersInf B x L
  rank_L : CFSG.Open.pRank p L = n / p
  rank_J : CFSG.Open.pRank p J = n / p - 1
  rank_B : CFSG.Open.pRank p B ≤ n / p + 1

@[expose] def AltSetupAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
    catalogIs (PSimple p L) isAltIndex → ∃ (n : ℕ) (y : G) (J : Subgroup G), AltSetup p B x L n y J

@[expose] def Lemma72At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G) (n : ℕ) (y : G) (J : Subgroup G),
    IsSStarMax p B x L → AltSetup p B x L n y J → p = 3 ∧ 9 ≤ n ∧ n ≤ 12

@[expose] def gfTwoPP : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

@[expose] def IsL62Type (p : ℕ) (K : Subgroup G) : Prop :=
  pSimpleIsLie p K (.A 5 gfTwoPP) ∧ Subgroup.center (PQuot p K) = ⊥

structure Lemma73Data (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) (y : G) (J : Subgroup G)
    (a : G) (K T I S : Subgroup G) : Prop where
  a_mem : a ∈ altDxy x y
  a_ne_one : a ≠ 1
  K_comp : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K
  K_eq : K = closureIn J (GLAPLayer p (Subgroup.centralizer ({a} : Set G)))
  K_type : IsL62Type p K
  B_eq_K : IsDirectZpowersInf B a K
  T_le : T ≤ L
  T_two : IsPGroup 2 T
  T_not_le : ¬ T ≤ GLAPPrimeCoreOf p L
  B_le_N : B ≤ Subgroup.normalizer (T : Set G)
  covers : CoversMod p (T ⊔ J) L
  I_eq : I = GLAPLayer p
    (Subgroup.normalizer (T : Set G) ⊓ Subgroup.centralizer (altDxy x y : Set G) ⊓ L)
  I_le_J : I ≤ J
  I_alt : IsAltPType p I 7
  comm_T : (⁅I, T⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L
  S_eq : S = ⁅I, Subgroup.centralizer ({a} : Set G) ⊓ pCoreOf 2 (Subgroup.normalizer (T : Set G))⁆
  S_ne : S ≠ ⊥
  S_le_K : S ≤ K
  S_not_le : ¬ S ≤ GLAPPrimeCoreOf p K
  J_alt8 : Nonempty (↥(imageMod p K J) ≃* ↥(alternatingGroup (Fin 8)))
  I_alt7 : Nonempty (↥(imageMod p K I) ≃* ↥(alternatingGroup (Fin 7)))

@[expose] def Lemma73At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G) (n : ℕ) (y : G) (J : Subgroup G),
    IsSStarMax p B x L → AltSetup p B x L n y J →
    (p = 3 ∧ Nat.card ↥B = 3 ^ 4 ∧ n = 11) ∧
    ∃ (y' : G) (J' : Subgroup G), y' ∈ B ∧ AltSetup p B x L n y' J' ∧
      ∃ (a : G) (K T I S : Subgroup G), Lemma73Data p B x L y' J' a K T I S

end Perm

end CFSG.LocalAnalysis.GLTheoremA
