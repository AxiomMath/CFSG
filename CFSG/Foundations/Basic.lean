module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
public import CFSG.GroupTheory.Fitting.WholeGroupConstruction
public import Mathlib.Tactic.Eqns
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Foundations.MaxOrderThompsonDefs
public import CFSG.Foundations.FullStandardCore

public section

namespace CFSG

open Subgroup

universe u

variable {G : Type*} [Group G]

@[expose] def inSubgroup {G : Type u} [Group G] (F : ∀ (K : Type u) [Group K], Subgroup K)
    (H : Subgroup G) : Subgroup G :=
  (F H).map H.subtype

@[expose] def conjugate (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g⁻¹).toMonoidHom

variable (G) in
@[expose] def IsQuasisimple (Q : Type*) [Group Q] : Prop :=
  Group.IsPerfect Q ∧ IsSimpleGroup (Q ⧸ center Q) ∧
    ∃ a b : Q ⧸ center Q, a * b ≠ b * a

@[expose] def IsComponent (K : Subgroup G) : Prop :=
  IsQuasisimple K ∧ K.IsSubnormal

variable (G) in
@[expose] def layer : Subgroup G :=
  WholeGroup.layerOf (IsComponent (G := G))

variable (G) in
theorem layer.eq_sSup : layer G = sSup {K : Subgroup G | IsComponent K} :=
  rfl

attribute [eqns layer.eq_sSup] layer

variable (G) in
@[expose] def generalizedFitting : Subgroup G :=
  WholeGroup.fstarOf (layer G)

variable (G) in
theorem generalizedFitting.eq_sup : generalizedFitting G = fittingSubgroup G ⊔ layer G :=
  rfl

attribute [eqns generalizedFitting.eq_sup] generalizedFitting

@[expose] def IsCComponent (L : Subgroup G) : Prop :=
  L ≠ ⊥ ∧ ⁅L, L⁆ = L ∧ L.IsSubnormal ∧
    ∀ K : Subgroup G, K < L → K ≠ ⊥ → ⁅K, K⁆ = K → ¬ K.IsSubnormal

@[expose] def IsPComponent {X : Type*} [Group X] (p : ℕ) (L : Subgroup X) : Prop :=
  ∃ K : Subgroup (X ⧸ pPrimeCore p X), IsComponent K ∧ L.IsSubnormal ∧
    L.map (QuotientGroup.mk' (pPrimeCore p X)) = K ∧
    ∀ J : Subgroup X, J < L → J.IsSubnormal → J.map (QuotientGroup.mk' (pPrimeCore p X)) ≠ K

variable (G) in
@[expose] def pLayer (p : ℕ) : Subgroup G :=
  sSup {L : Subgroup G | IsPComponent p L}

variable (G) in
@[expose] def solvableRadical : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ Group.IsSolvable N}

variable (G) in
@[expose] def perfectResidual : Subgroup G :=
  ⨅ n : ℕ, derivedSeries G n

@[expose] noncomputable def pRank (p : ℕ) (H : Type*) [Group H] : ℕ :=
  sSup {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian p A ∧ Nat.card A = p ^ r}

@[expose] def IsPLocal (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ P : Subgroup G, P ≠ ⊥ ∧ IsPGroup p P ∧ H = normalizer (P : Set G)

@[expose] def IsMaximalTwoLocal (M : Subgroup G) : Prop :=
  IsPLocal 2 M ∧ ∀ H : Subgroup G, M < H → ¬ IsPLocal 2 H

@[expose] def maximalTwoLocalsContaining (X : Set G) : Set (Subgroup G) :=
  {M | IsMaximalTwoLocal M ∧ X ⊆ M}

variable (G) in
@[expose] noncomputable def twoLocalOddRank : ℕ :=
  sSup {r : ℕ | ∃ H : Subgroup G, IsPLocal 2 H ∧
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ r = pRank p H}

@[expose] def IsCharacteristicP (p : ℕ) (H : Type*) [Group H] : Prop :=
  centralizer (pCore p H : Set H) ≤ pCore p H

variable (G) in
@[expose] def IsCharacteristicPType (p : ℕ) : Prop :=
  ∀ H : Subgroup G, IsPLocal p H → IsCharacteristicP p H

variable (G) in
@[expose] def IsEvenCharacteristic : Prop :=
  ∀ H : Subgroup G, IsPLocal 2 H → (∃ S : Sylow 2 G, (S : Subgroup G) ≤ H) →
    IsCharacteristicP 2 H

@[expose] def IsStronglyQuasithin (H : Type*) [Group H] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → pRank p H ≤ 2

@[expose] def IsStronglyEmbedded (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ Even (Nat.card M) ∧ ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ conjugate M g))

@[expose] def IsStronglyClosedIn (S : Subgroup G) (A : Set G) : Prop :=
  A ⊆ S ∧ ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A

@[expose] def IsTISubset (D : Set G) (L : Subgroup G) : Prop :=
  D.Nonempty ∧ (1 : G) ∉ D ∧ normalizer D = L ∧
    ∀ g : G, g ∉ L → D ∩ (fun x => g⁻¹ * x * g) '' D = ∅

@[expose] def IsStandardSubgroup (L : Subgroup G) : Prop :=
  full_standard% FullStandardCore (IsQuasisimple L) conjugate L

theorem isStandardSubgroup_eq_fullStandardCore (L : Subgroup G) :
    IsStandardSubgroup L = FullStandardCore (IsQuasisimple L) conjugate L :=
  rfl

@[expose] def IsExtraspecialPGroup (p : ℕ) (P : Type*) [Group P] : Prop :=
  IsPGroup p P ∧ commutator P = center P ∧ frattini P = center P ∧ Nat.card (center P) = p

variable (G) in
@[expose] def elemThompsonFamily (p : ℕ) : Set (Subgroup G) :=
  {A | IsElementaryAbelian p A ∧ Nat.card A = p ^ pRank p G}

variable (G) in
@[expose] def elemThompson (p : ℕ) : Subgroup G :=
  sSup (elemThompsonFamily G p)

variable (G) in
@[expose] def elemThompsonCenterTorsion (p : ℕ) : Subgroup G where
  carrier := {z | z ∈ (center (elemThompson G p)).map (elemThompson G p).subtype ∧ z ^ p = 1}
  one_mem' := ⟨one_mem _, one_pow p⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, ha, rfl⟩, hap⟩ ⟨⟨b, hb, rfl⟩, hbp⟩
    refine ⟨mul_mem (mem_map_of_mem _ ha) (mem_map_of_mem _ hb), ?_⟩
    have hab : Commute (a : G) b :=
      (show Commute b a from mem_center_iff.mp ha b).symm.map (elemThompson G p).subtype
    change (a : G) ^ p = 1 at hap
    change (b : G) ^ p = 1 at hbp
    change ((a : G) * b) ^ p = 1
    rw [hab.mul_pow, hap, hbp, one_mul]
  inv_mem' := by
    rintro _ ⟨hz, hzp⟩
    exact ⟨inv_mem hz, by rw [inv_pow, hzp, inv_one]⟩

section Cores

variable (G)

theorem pCore_eq_piCore [Finite G] (p : ℕ) [Fact p.Prime] :
    pCore p G = piCore {q : Nat.Primes | q.val = p} G := by
  unfold pCore piCore IsPiSubgroup
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, and_congr_right_iff]
  intro _
  rw [IsPGroup.iff_card]
  constructor
  · rintro ⟨n, hn⟩ q hqN
    rw [hn] at hqN
    exact (Nat.prime_dvd_prime_iff_eq q.2 Fact.out).mp (q.2.dvd_of_dvd_pow hqN)
  · intro h
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      fun {d} hd hdN => h ⟨d, hd⟩ hdN⟩

theorem pPrimeCore_eq_piCore (p : ℕ) [Fact p.Prime] :
    pPrimeCore p G = piCore {q : Nat.Primes | q.val ≠ p} G := by
  unfold pPrimeCore piCore IsPiSubgroup
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, and_congr_right_iff]
  intro _
  rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
  constructor
  · rintro h q hqN rfl
    exact h hqN
  · intro h hp
    exact h ⟨p, Fact.out⟩ hp rfl

theorem oddCore_eq_piCore : oddCore G = piCore {q : Nat.Primes | q.val ≠ 2} G := by
  rw [← pPrimeCore_eq_piCore]
  unfold oddCore pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

end Cores

end CFSG
