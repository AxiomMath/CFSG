module

public import CFSG.LocalAnalysis.GLTheoremB.BlockDefs
public import CFSG.LocalAnalysis.GLTheoremB.UniqStatements

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

variable {G : Type*} [Group G]

structure Prop95Hyp (p : ℕ) (M D : Subgroup G) : Prop where
  twoLocal : IsTwoLocal M
  le : D ≤ M
  plane : IsPPlane p D
  clause_a : ∀ d ∈ D, d ≠ 1 → pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) ≤ M
  clause_b : ∀ d ∈ D, d ≠ 1 →
    pCoreOf 2 (alphaOf p M ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      pCoreOf 2 (Subgroup.centralizer ({d} : Set G))
  clause_c : pCoreOf 2 M ≤ gammaD D

@[expose] def Prop95Alpha (p : ℕ) (M D L : Subgroup G) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ (hLM : L ≤ M)
    (e : ↥(barX p M L) ≃* ↥(alternatingGroup (Fin (k * p + 2))))
    (τ : Equiv.Perm (Fin (k * p + 2))), τ.IsSwap ∧
      Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 2 ∧
      ActsLike (barX p M (gammaD D)) (barX p M L) e
        (Subgroup.zpowers (MulAut.conjNormal (H := alternatingGroup (Fin (k * p + 2))) τ)) ∧
      ∀ V U : Subgroup G, IsNoncentralChiefFactor L (pCoreOf 2 L) V U →
        ChiefFactorIso L U V (e.toMonoidHom.comp (barMap p hLM))
          (fun σ x => altHeartAct (k * p + 2) (σ : Equiv.Perm (Fin (k * p + 2))) x)

@[expose] def Prop95BetaWith {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (p : ℕ) (M D L : Subgroup G) : Prop :=
  ∃ (hLM : L ≤ M) (e : ↥(barX p M L) ≃* ↥(StatedOmega Q)),
    Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 2 ∧
    ActsLikeTransvection Q (barX p M (gammaD D)) (barX p M L) e ∧
    ∀ V U : Subgroup G, IsNoncentralChiefFactor L (pCoreOf 2 L) V U →
      ChiefFactorIso L U V (e.toMonoidHom.comp (barMap p hLM))
        (fun g v => Matrix.mulVec ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) v)

@[expose] def Prop95Beta (p : ℕ) (M D L : Subgroup G) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    ((HasFixedPointFreeOrder true n p ∧
        Prop95BetaWith (StatedQuadPlus (n + 1) (ZMod 2)) p M D L) ∨
      (HasFixedPointFreeOrder false n p ∧
        Prop95BetaWith (StatedQuadMinus (n + 1) (ZMod 2) 1 1) p M D L))

@[expose] def Prop95Gamma (p : ℕ) (M D L : Subgroup G) : Prop :=
  p = 3 ∧ ∃ e : ↥(barX p M L) ≃* ↥(alternatingGroup (Fin 7)),
    Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 4 ∧
    ActsLikeRootFourGroup (barX p M (gammaD D)) (barX p M L) e ∧
    ∀ V U : Subgroup G, IsNoncentralChiefFactor L (pCoreOf 2 L) V U → Nat.card U = 16 * Nat.card V

@[expose] def Prop95Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      gammaD D ⊓ GLAPPrimeCoreOf p M = pCoreOf 2 M ∧
        barX p M (gammaD D) ≤
          Subgroup.centralizer
            ((CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
              Set (↥M ⧸ GLAPPrimeCore p ↥M)) ∧
        ∀ L : Subgroup G, GLAPComponent p M L →
          barX p M (gammaD D) ≤
            Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
              Set (↥M ⧸ GLAPPrimeCore p ↥M))

@[expose] def Prop95 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ M D : Subgroup G, Prop95Hyp p M D →
      gammaD D ⊓ GLAPPrimeCoreOf p M = pCoreOf 2 M ∧
        barX p M (gammaD D) ≤
          Subgroup.centralizer
            ((CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
              Set (↥M ⧸ GLAPPrimeCore p ↥M)) ∧
        ∀ L : Subgroup G, GLAPComponent p M L →
          barX p M (gammaD D) ≤
              Subgroup.normalizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
                Set (↥M ⧸ GLAPPrimeCore p ↥M)) ∧
            (barX p M (gammaD D) ≤
                Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
                  Set (↥M ⧸ GLAPPrimeCore p ↥M)) ∨
              (IsGLBlock M L ∧
                (Prop95Alpha p M D L ∨ Prop95Beta p M D L ∨ Prop95Gamma p M D L)))

theorem prop95Core_of_prop95 (h : Prop95) : Prop95Core := by
  intro G _ _ m p hS M D hD
  obtain ⟨h1, h2, h3⟩ := h G m p hS M D hD
  exact ⟨h1, h2, fun L hL => (h3 L hL).1⟩

end CFSG.LocalAnalysis.GLTheoremB
