module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.FourUGeneric

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux OuterFourInAux
open scoped commutatorElement

theorem pairSub_eq_sup {X : Type} [Group X] {x y : X} (hxy : Commute x y) :
    pairSub hxy = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  apply le_antisymm
  · rintro _ ⟨i, j, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) i))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) j))
  · refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_pairSub.2 ⟨1, 0, by simp⟩
    · exact mem_pairSub.2 ⟨0, 1, by simp⟩

@[expose] def FourUSelLoc (P : TauCeti.LieTypeIndex → Prop)
    (F : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B : Subgroup X) (x : X),
    IsComponentOf K ⊤ → IsSCp 3 ⊤ B → ∀ (hBN : B ≤ Subgroup.normalizer (K : Set X)),
      GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B → IsLieQuot ↥K P → ∀ (hx : x ∈ B), ¬ InnerAt K x →
      (∀ b ∈ B, ∃ i : ℕ, InnerAt K (x ^ i * b)) →
      (∀ (a : X) (ha : a ∈ B), ¬ InnerAt K a →
        F (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨a, hBN ha⟩)) →
      ∃ y ∈ B, InnerAt K y ∧ y ∉ Subgroup.centralizer (K : Set X) ∧ GoodAt K B y ∧
        IsCompLocallyBalanced 3 1 (Subgroup.zpowers x ⊔ Subgroup.zpowers y) K

theorem bal209FourUAt_of_inputs_loc {P : TauCeti.LieTypeIndex → Prop}
    {F : ∀ (S : Type) [Group S], MulAut S → Prop} {Q : TauCeti.LieTypeIndex → Prop}
    (hFd : FourUField P F) (hFix : FourUFixed P F Q)
    (hSel : FourUSelLoc P F) (hSLOB : FourUFixedSLOB Q) : Bal209FourUAt P F := by
  intro X _ _ hKG K B hK hBSC hBN hrank hLie hF
  obtain ⟨x, hxB, hxI, hdec, hFall⟩ := hFd X K B hK hBSC hBN hLie hF
  have hFx := hFall x hxB hxI
  obtain ⟨y, hyB, hyI, hyC, hyG, hlocSup⟩ :=
    hSel X hKG K B x hK hBSC hBN hrank hLie hxB hxI hdec hFall
  have hBel : IsElemAbelian 3 B := hBSC.2.1
  have hxN : x ∈ Subgroup.normalizer (K : Set X) := hBN hxB
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hx1 : x ≠ 1 := by
    intro h
    apply hxI
    rw [h]
    exact ⟨1, K.one_mem, by simp⟩
  have hy1 : y ≠ 1 := by
    intro h
    apply hyC
    rw [h]
    exact Subgroup.one_mem _
  have hxy : Commute x y := commute_of_elemAbelian hBel hxB hyB
  have hxI' : x ∉ innerSub K := fun h => hxI (mem_innerSub.1 h)
  have hyI' : y ∈ innerSub K := mem_innerSub.2 hyI
  have hAB : pairSub hxy ≤ B := pairSub_le hxy hxB hyB
  have hAel : IsElemAbelian 3 (pairSub hxy) := isElemAbelian_pairSub hxy hBel hxB hyB
  have hnc : ¬ IsCyclic ↥(pairSub hxy) := not_isCyclic_pairSub hxy hBel hxB hyB hx1 hy1 hxI' hyI'
  have hSC : IsSCp 3 (K ⊔ B) B :=
    ⟨le_sup_right, hBel, fun E _ hEel hBE => hBSC.2.2 E le_top hEel hBE⟩
  have hxA : x ∈ pairSub hxy := mem_pairSub.2 ⟨1, 0, by simp⟩
  obtain ⟨J₀, hJ₀, hJ₀u, hJ₀q, hJ₀L⟩ := hFix X K x hK hLie hxN hx3 hFx
  have hdvd : 3 ∣ Nat.card K :=
    (LieComp.three_dvd_card_of_glaPComponent hJ₀).trans
      (Subgroup.card_dvd_of_le (hJ₀.1.trans inf_le_left))
  have hloc : IsCompLocallyBalanced 3 1 (pairSub hxy) K := by
    rw [pairSub_eq_sup]
    exact hlocSup
  have hb : ∀ a ∈ pairSub hxy, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B a J := by
    intro a ha ha1 J hJ
    have haB : a ∈ B := hAB ha
    by_cases hinn : InnerAt K a
    · have hcen : Subgroup.centralizer ({a} : Set X) = Subgroup.centralizer ({y} : Set X) :=
        KSF4Pure.centralizer_eq_of_inner_mem_pairSub hxy hx3 hy3 hxI' hyI' hy1 ha
          (mem_innerSub.2 hinn) ha1
      have hJ' : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J := by
        rw [← hcen]; exact hJ
      obtain ⟨hBJ, hS⟩ := hyG J hJ'
      refine ⟨hBJ, ?_⟩
      unfold IsStronglyLocallyOneBalanced at hS ⊢
      rw [hcen]
      exact hS
    · have haN : a ∈ Subgroup.normalizer (K : Set X) := hBN haB
      have ha3 : a ^ 3 = 1 := hBel.2 a haB
      have hFa := hFall a haB hinn
      obtain ⟨J₁, hJ₁, hJ₁u, hJ₁q, hJ₁L⟩ := hFix X K a hK hLie haN ha3 hFa
      have hJeq : J = J₁ := hJ₁u J hJ
      subst hJeq
      have hBJ : B ≤ Subgroup.normalizer (J : Set X) := by
        intro b hb
        rw [mem_normalizer_iff_gLBConj_eq]
        have h1 := KSF4Kit.glaPComponent_gLBConj_centralizer (hBN hb)
          (commute_of_elemAbelian hBel hb haB).eq hJ
        exact hJ₁u _ h1
      exact ⟨hBJ, hSLOB X hKG K B a J hK hBSC hBN hrank haB hJ hJ₁q hJ₁L hBJ⟩
  have hc : ∃ a ∈ pairSub hxy, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X),
      Nat.Coprime 3 (orderOf w) → (∀ b ∈ B, ⁅w, b⁆ ∈ Subgroup.centralizer (K : Set X)) →
        ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          w ∈ Subgroup.normalizer (J : Set X) := by
    refine ⟨x, hxA, hx1, fun w hwN _ hwB J hJ => ?_⟩
    have hwx : ⁅w, x⁆ ∈ Subgroup.centralizer (K : Set X) := hwB x hxB
    have hwH := mem_normalizer_inf_centralizer hwN hxN hwx
    rw [mem_normalizer_iff_gLBConj_eq] at hwH ⊢
    have h1 := glaPComponent_gLBConj hJ w
    rw [hwH] at h1
    have hJ1 : J = J₀ := hJ₀u J hJ
    have hJ2 : GLBConj w J = J₀ := hJ₀u _ h1
    rw [hJ2, hJ1]
  exact i202Full_holds X 3 Nat.prime_three (by decide) K B (pairSub hxy) hK.2.2 hdvd hBN hBel hSC
    hAB hnc hloc hb hc

theorem sLOB_of_u3_component (h209U3 : Bal209FourUAt IsU3EightIndex (FieldAutU 3))
    {X : Type} [Group X] [Finite X] (hKG : CFSG.Open.IsKGroup X) {K B J : Subgroup X} {a : X}
    (hK : IsComponentOf K ⊤) (hBSC : IsSCp 3 ⊤ B)
    (hrank : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B) (haB : a ∈ B)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hJq : CFSG.Open.IsQuasisimple ↥J) (hJL : IsLieQuot ↥J IsU3EightIndex)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hF : ∃ φ ∈ autImage (B.subgroupOf (Subgroup.centralizer ({a} : Set X)))
        (J.subgroupOf (Subgroup.centralizer ({a} : Set X))),
        FieldAutU 3 (↥(J.subgroupOf (Subgroup.centralizer ({a} : Set X))) ⧸
          Subgroup.center ↥(J.subgroupOf (Subgroup.centralizer ({a} : Set X)))) φ) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  have hJcomp := KSF4Kit.isComponentOf_centralizer_of_glaPComponent hK hJ hJq
  have hBel : IsElemAbelian 3 B := hBSC.2.1
  have hBC : B ≤ Subgroup.centralizer ({a} : Set X) := le_centralizer_of_elemAbelian hBel haB
  set C := Subgroup.centralizer ({a} : Set X) with hCdef
  obtain ⟨hJC, hsubJ, hJq'⟩ := hJcomp
  have hsub' : CFSG.Open.IsSubnormal (J.subgroupOf C) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib ((CFSG.Open.IsSubnormal.iff_subgroupOf hJC).1 hsubJ)
  have hq' : CFSG.Open.IsQuasisimple ↥(J.subgroupOf C) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC) hJq'
  have hcomp : CFSG.Open.IsComponentOf (J.subgroupOf C) ⊤ := ⟨le_top, hsub', hq'⟩
  have hSC' : IsSCp 3 ⊤ (B.subgroupOf C) := isSCp_subgroupOf hBC hBSC
  have hBN' : B.subgroupOf C ≤
      Subgroup.normalizer (((J.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro b' hb'
    have hbB : (b' : X) ∈ B := Subgroup.mem_subgroupOf.1 hb'
    have hN := Subgroup.mem_normalizer_iff.1 (hBJ hbB)
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hLie : IsLieQuot ↥(J.subgroupOf C) IsU3EightIndex :=
    isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hJL
  have hrank' : GLATwoLocalRank 3 ↥C ≤ CFSG.Open.pRank 3 (B.subgroupOf C) := by
    have h1 := glaTwoLocalRank_subgroup_le Nat.prime_three C
    have h2 := pRank_map_eq_of_injective (by norm_num : 1 < 3) C.subtype C.subtype_injective
      (B.subgroupOf C)
    rw [Subgroup.map_subgroupOf_eq_of_le hBC] at h2
    exact h1.trans (hrank.trans h2.le)
  have hbal := h209U3 ↥C (hKG.subgroup C) (J.subgroupOf C) (B.subgroupOf C) hcomp hSC' hBN'
    hrank' hLie hF
  exact sLOB_of_balancedIn_centralizer hBC hJC hBJ hbal

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
