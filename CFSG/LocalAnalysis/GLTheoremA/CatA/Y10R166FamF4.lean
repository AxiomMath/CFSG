module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcTorus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcOut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Defs
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Certs


@[expose]
def F4ModelAt : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n p : ℕ), Nat.card F = 2 ^ n → 2 ≤ n →
    p.Prime → p ≠ 2 → p ∣ 2 ^ n + 1 →
    ∃ (q : ℕ) (B' : Subgroup (adjointGroup .F4 F)) (x' : adjointGroup .F4 F)
      (J : Subgroup (adjointGroup .F4 F)), Concl166S (adjointGroup .F4 F) p q B' x' J

theorem exists_mulEquiv_adjointGroup_F4_of_label {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hK : HasLabel K (· = lab)) (ht : lab.tag = .F4) (hn : 2 ≤ lab.n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ lab.n ∧
      Nonempty (K ≃* adjointGroup .F4 F) := by
  have hK' : Rk2IsLabel K lab := hK
  obtain ⟨-, -, hM⟩ := rk2_model_of_isLabel hK'
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .F4 0 2 lab.n :=
    lieModel_of_markedModel_F4 ht hM
  obtain ⟨-, F, hF, hFin, hcard, ⟨e0⟩⟩ :=
    hM'.chevalleyExceptionalModel (by decide : StatedLieTag.F4 ∈ chevalleyExceptionalTags)
  refine ⟨F, hF, hFin, hcard, ?_⟩
  letI : Field F := hF
  letI : Finite F := hFin
  let χ : CFSG.Blueprint.AdjointQuotient .F4 F ≃* adjointGroup .F4 F :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := F))).trans
        QuotientGroup.quotientBot
  have hZ : Subgroup.center K = ⊥ :=
    rk2_center_eq_bot_of_large hK' (Or.inr (Or.inr (Or.inl ht))) hn
  let e1 : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨e1.symm.trans (e0.trans χ)⟩

theorem i166On_famF4_of_transport_of_model (hModel : F4ModelAt)
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J) :
    I166On i166FamF4 := by
  intro K _ _ lab p hK hfam hp hp2 _ _ _
  obtain ⟨ht, hn, hpd⟩ := hfam
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ :=
    exists_mulEquiv_adjointGroup_F4_of_label hK ht hn
  letI : Field F := hF
  letI : Finite F := hFin
  exact htr e (hModel F lab.n p hcard hn hp hp2 hpd)

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
