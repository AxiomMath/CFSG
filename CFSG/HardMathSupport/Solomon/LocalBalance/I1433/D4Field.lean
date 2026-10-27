module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SL3Param

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def D4BlockType : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F))) → ∀ x : S, orderOf x = 3 →
    ∀ J : Subgroup S, GLAPComponent 3 (Subgroup.centralizer ({x} : Set S)) J → x ∈ J →
      ∀ q : ℕ, IsSL3EpsOver (↥J ⧸ GLAPPrimeCore 3 ↥J) q →
        IsSL3EpsOver (↥J ⧸ GLAPPrimeCore 3 ↥J) (Nat.card F)

theorem d4FieldSharp_of_blockType (h : D4BlockType) : D4FieldSharp := by
  intro X _ _ K Q₁ Q J t q c F _ _ ⟨e⟩
  obtain ⟨x, Q', J', c'⟩ := c.exists_sCfg
  have hq := c.setup.quasisimple
  have hKq : CFSG.Open.IsQuasisimple ↥K := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq
  have hF := h F (↥K ⧸ Subgroup.center ↥K) hq.2.1 ⟨a, b, hab⟩ ⟨e⟩ x c'.order J' c'.comp c'.mem q
    c'.sl3
  exact (IsSL3EpsOver.param_eq c'.sl3 hF).symm

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
