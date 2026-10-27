module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Lemma25Strong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ (B D : Subgroup G) (b : G) (L : Subgroup G), Lemma24Setup 3 B D b L →
      ∀ Lᵢ : Subgroup G, IsBConjugate B L Lᵢ → ∀ x : G,
        x ∈ Subgroup.centralizer ({b} : Set G) → orderOf x = 3 →
        ⁅Lᵢ, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) →
        let Jis : Subgroup G := ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
          GLBConj g (GLAPLayer 3 (Lᵢ ⊓ Subgroup.centralizer ({x} : Set G)))
        (x ∈ B → Lemma24Setup 3 B D x Jis ∧ Lemma24Conclusion B D x Jis) ∧
          ((barImageAt 3 b (Subgroup.closure {x, b}) ≤ barCenterAt 3 b (bClosure B L) ∨
              (D ≤ Subgroup.centralizer ({x} : Set G) ∧
                barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L))) →
            b ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G)))

theorem lemma25_of_strong (h : Lemma25Strong) : Lemma25 :=
  fun G _ _ m hS B D b L hs Lᵢ hLᵢ x hx hord hc =>
    ⟨fun hxB => (h G m hS B D b L hs Lᵢ hLᵢ x hx hord hc).1 hxB |>.2,
      (h G m hS B D b L hs Lᵢ hLᵢ x hx hord hc).2⟩

end CFSG.HardMathSupport.Solomon.LocalBalance
