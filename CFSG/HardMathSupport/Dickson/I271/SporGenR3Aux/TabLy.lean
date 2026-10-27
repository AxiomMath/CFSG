module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyRk
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyB
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyThree

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
  CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Subgroup Equiv

section Main


theorem tabLy_coprime_outer (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    {G : Type} [Group G] [Finite G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
    {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))} (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.Coprime 3 (Nat.card (Outer (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G))))) := by
  obtain ⟨e⟩ := tabLy_centerQuot D S
  obtain ⟨b⟩ := hBr .McL
  have hq := tabLy_quasisimple D S
  have hs : IsSimpleGroup (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G))) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have h2 := hOut _ hs hnab .McL ⟨e.trans b⟩
  have hpos : 0 < Nat.card (Outer (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)))) := Nat.card_pos
  interval_cases h : Nat.card (Outer (↥(centralizer ({(x₁ : G)} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G)))) <;> norm_num

theorem tabLy_centShapeRk (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) :
    CentShapeRk 3 (GoodSpor 3 [.McL]) (RkSpor 3 [.McL]) (NativeSporadic.Carrier .Ly) := by
  haveI : Finite (NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  have hS : Nonempty (NativeSporadic.Carrier .Ly ≃* NativeSporadic.Carrier .Ly) :=
    ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hA : ShapeRkAt 3 (GoodSpor 3 [.McL]) (RkSpor 3 [.McL])
      (x₁ : NativeSporadic.Carrier .Ly) :=
    tabLy_threeA D St (hBr .McL) (tabLy_rkAut D St (tabLy_coprime_outer hOut hBr D St))
  have hB : ShapeRkAt 3 (GoodSpor 3 [.McL]) (RkSpor 3 [.McL])
      ((x₁ : NativeSporadic.Carrier .Ly) * (x₂ : NativeSporadic.Carrier .Ly)) :=
    Or.inl (tabLy_threeB D St (LyCore.lyThreeBOrder_thm _ hS t ρ D x₁ x₂ x₃ St)
      (oPrimeCoreTrivialAt_Ly_three _ hS _ (tabLy_orderOf_x₁x₂ D St)))
  have htr : ∀ {a b : NativeSporadic.Carrier .Ly}, IsConj a b →
      ShapeRkAt 3 (GoodSpor 3 [.McL]) (RkSpor 3 [.McL]) a →
        ShapeRkAt 3 (GoodSpor 3 [.McL]) (RkSpor 3 [.McL]) b := by
    intro a b hab ha
    obtain ⟨c, hc⟩ := isConj_iff.1 hab
    have := ShapeRkAt.of_equiv Nat.prime_three (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
      (fun _ _ _ _ e h => RkSpor.of_equiv e h) (MulAut.conj c) ha
    rwa [MulAut.conj_apply, hc] at this
  intro k hk1 hk3
  have hk : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  rcases (lemma45_classes_of_certificate D St).1 k hk with h | h
  · exact htr h.symm hA
  · exact htr h.symm hB

end Main

end CFSG.HardMathSupport.Dickson.I271
