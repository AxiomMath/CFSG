module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.LocalAnalysis.GLTheoremA

@[expose] def isSporadicIdx : TauCeti.CFSGIndex → Prop
  | .sporadic _ => True
  | _ => False

@[expose] def KD264KAlt (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal → CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K →
    catalogIs (↥K ⧸ Subgroup.center ↥K) isAltIndex →
    GLAPPrimeCore p ↥K = ⊥ → fullCoverLevel p ↥K = 4 →
    IsElemAbelian p B → K ⊔ B = ⊤ → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    (∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) ∨
      (p = 3 ∧ Nat.card B = 3 ^ 4 ∧ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3 ∧
        catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie isTrialityD4Big) ∧
        ∃ b ∈ B, ¬ InducesInnerMod 3 K b)

@[expose] def KD264KSpor (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal → CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K →
    catalogIs (↥K ⧸ Subgroup.center ↥K) isSporadicIdx →
    GLAPPrimeCore p ↥K = ⊥ → fullCoverLevel p ↥K = 4 →
    IsElemAbelian p B → K ⊔ B = ⊤ → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    (∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) ∨
      (p = 3 ∧ Nat.card B = 3 ^ 4 ∧ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3 ∧
        catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie isTrialityD4Big) ∧
        ∃ b ∈ B, ¬ InducesInnerMod 3 K b)

@[expose] def KD264KLie (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal → CFSG.Open.IsQuasisimple ↥K →
    CFSG.Open.IsKGroup ↥K →
    catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie fun _ => True) →
    GLAPPrimeCore p ↥K = ⊥ → fullCoverLevel p ↥K = 4 →
    IsElemAbelian p B → K ⊔ B = ⊤ → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    (∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) ∨
      (p = 3 ∧ Nat.card B = 3 ^ 4 ∧ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3 ∧
        catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie isTrialityD4Big) ∧
        ∃ b ∈ B, ¬ InducesInnerMod 3 K b)

@[expose] def KD264SporS (p : ℕ) : Prop :=
  ∀ (s : TauCeti.SporadicName) (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal →
    Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    GLAPPrimeCore p ↥K = ⊥ → fullCoverLevel p ↥K = 4 →
    IsElemAbelian p B → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    ∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥

theorem false_of_quasisimple_comm_quotient {K : Type} [Group K] (hq : CFSG.Open.IsQuasisimple K)
    {G : Type} [CommGroup G] (e : K ⧸ Subgroup.center K ≃* G) : False := by
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  set f : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K) with hf
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hKtop : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := hq.1
  have hS_top : ⁅(⊤ : Subgroup (K ⧸ Subgroup.center K)), (⊤ : Subgroup (K ⧸ Subgroup.center K))⁆ = ⊤ := by
    have h1 := Subgroup.map_commutator (⊤ : Subgroup K) (⊤ : Subgroup K) f
    rw [hKtop, Subgroup.map_top_of_surjective _ hfsurj] at h1
    exact h1.symm
  have hScomm : ∀ a b : K ⧸ Subgroup.center K, a * b = b * a := fun a b => by
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  have hbot : ⁅(⊤ : Subgroup (K ⧸ Subgroup.center K)), (⊤ : Subgroup (K ⧸ Subgroup.center K))⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hScomm y x
  have htb : (⊤ : Subgroup (K ⧸ Subgroup.center K)) = ⊥ := hS_top.symm.trans hbot
  have hsub : Subsingleton (K ⧸ Subgroup.center K) := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Subgroup (K ⧸ Subgroup.center K)) := htb ▸ Subgroup.mem_top (G := K ⧸ Subgroup.center K) a
    have hb : b ∈ (⊥ : Subgroup (K ⧸ Subgroup.center K)) := htb ▸ Subgroup.mem_top (G := K ⧸ Subgroup.center K) b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  exact not_subsingleton (K ⧸ Subgroup.center K) hsub

theorem kd264K_of_parts {p : ℕ} (hA : KD264KAlt p) (hS : KD264KSpor p) (hL : KD264KLie p) :
    KD264K p := by
  intro Y _ _ K B hKn hq hKG hc hcore hlev hB hKB hcard hmax hC
  obtain ⟨i, ⟨eK⟩⟩ := hc
  cases i with
  | cyclic q hq' =>
    exact (false_of_quasisimple_comm_quotient (G := Multiplicative (ZMod q)) hq eK).elim
  | alternating n h =>
    exact hA Y K B hKn hq hKG ⟨.alternating n h, trivial, ⟨eK⟩⟩ hcore hlev hB hKB hcard hmax hC
  | lie d =>
    exact hL Y K B hKn hq hKG ⟨.lie d, trivial, ⟨eK⟩⟩ hcore hlev hB hKB hcard hmax hC
  | sporadic s =>
    exact hS Y K B hKn hq hKG ⟨.sporadic s, trivial, ⟨eK⟩⟩ hcore hlev hB hKB hcard hmax hC

end CFSG.LocalAnalysis.GLTheoremA

end
