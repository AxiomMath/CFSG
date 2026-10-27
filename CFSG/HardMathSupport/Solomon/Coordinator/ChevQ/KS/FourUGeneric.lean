module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourIn
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4PureOut
public import CFSG.HardMathSupport.Dickson.Bal207.SmallBridge
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbL2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux
open scoped commutatorElement

section Generic

@[expose] def GoodAt {X : Type} [Group X] (K B : Subgroup X) (y : X) : Prop :=
  ∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J →
    B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced 3 B y J

@[expose] def FourUField (P : TauCeti.LieTypeIndex → Prop)
    (F : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K B : Subgroup X), IsComponentOf K ⊤ → IsSCp 3 ⊤ B →
    ∀ (hBN : B ≤ Subgroup.normalizer (K : Set X)), IsLieQuot ↥K P →
      (∃ φ ∈ autImage B K, F (↥K ⧸ Subgroup.center ↥K) φ) →
      ∃ x ∈ B, ¬ InnerAt K x ∧ (∀ b ∈ B, ∃ i : ℕ, InnerAt K (x ^ i * b)) ∧
        ∀ (a : X) (ha : a ∈ B), ¬ InnerAt K a →
          F (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨a, hBN ha⟩)

@[expose] def FourUFixed (P : TauCeti.LieTypeIndex → Prop)
    (F : ∀ (S : Type) [Group S], MulAut S → Prop) (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (a : X), IsComponentOf K ⊤ → IsLieQuot ↥K P →
    ∀ (ha : a ∈ Subgroup.normalizer (K : Set X)), a ^ 3 = 1 →
      F (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨a, ha⟩) →
      ∃ J₀ : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J₀ ∧
        (∀ J : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → J = J₀) ∧
        CFSG.Open.IsQuasisimple ↥J₀ ∧ IsLieQuot ↥J₀ Q

@[expose] def FourULocal (P : TauCeti.LieTypeIndex → Prop)
    (F : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K A : Subgroup X), IsComponentOf K ⊤ →
    IsLieQuot ↥K P → ∀ (hAN : A ≤ Subgroup.normalizer (K : Set X)), IsElemAbelian 3 A →
      (∀ (a : X) (ha : a ∈ A), ¬ InnerAt K a →
        F (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨a, hAN ha⟩)) →
        IsCompLocallyBalanced 3 1 A K

@[expose] def FourUSel (P : TauCeti.LieTypeIndex → Prop)
    (F : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B : Subgroup X) (x : X),
    IsComponentOf K ⊤ → IsSCp 3 ⊤ B → ∀ (hBN : B ≤ Subgroup.normalizer (K : Set X)),
      GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B → IsLieQuot ↥K P → ∀ (hx : x ∈ B), ¬ InnerAt K x →
      (∀ b ∈ B, ∃ i : ℕ, InnerAt K (x ^ i * b)) →
      F (↥K ⧸ Subgroup.center ↥K) (actHom K ⟨x, hBN hx⟩) →
      ∃ y ∈ B, InnerAt K y ∧ y ∉ Subgroup.centralizer (K : Set X) ∧ GoodAt K B y

@[expose] def FourUFixedSLOB (Q : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ (K B : Subgroup X) (a : X) (J : Subgroup X),
    IsComponentOf K ⊤ → IsSCp 3 ⊤ B → B ≤ Subgroup.normalizer (K : Set X) →
      GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B → a ∈ B →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J → CFSG.Open.IsQuasisimple ↥J →
      IsLieQuot ↥J Q → B ≤ Subgroup.normalizer (J : Set X) →
        IsStronglyLocallyOneBalanced 3 B a J

theorem bal209FourUAt_of_inputs {P : TauCeti.LieTypeIndex → Prop}
    {F : ∀ (S : Type) [Group S], MulAut S → Prop} {Q : TauCeti.LieTypeIndex → Prop}
    (hFd : FourUField P F) (hFix : FourUFixed P F Q) (hLoc : FourULocal P F)
    (hSel : FourUSel P F) (hSLOB : FourUFixedSLOB Q) : Bal209FourUAt P F := by
  intro X _ _ hKG K B hK hBSC hBN hrank hLie hF
  obtain ⟨x, hxB, hxI, hdec, hFall⟩ := hFd X K B hK hBSC hBN hLie hF
  have hFx := hFall x hxB hxI
  obtain ⟨y, hyB, hyI, hyC, hyG⟩ :=
    hSel X hKG K B x hK hBSC hBN hrank hLie hxB hxI hdec hFx
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
  have hloc := hLoc X K (pairSub hxy) hK hLie (hAB.trans hBN) hAel
    (fun a ha hna => hFall a (hAB ha) hna)
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

end Generic

section SLOB

open KSCompSLOB

@[expose] def IsU6TwoIndex (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, IsTwoPow q 1 ∧ d = .twistedA 5 q

theorem isU6Two_bal207 : ∀ d, IsU6TwoIndex d →
    Bal207Index 3 d ∧ ¬ CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex d := by
  rintro d ⟨q, hq, rfl⟩
  refine ⟨?_, ?_⟩
  · show 3 = 3 ∧ (((IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ ¬ 3 ∣ 5 + 1) ∨ (IsTwoPow q 1 ∧ 5 = 5))
    exact ⟨rfl, Or.inr ⟨hq, rfl⟩⟩
  · simp [CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex]

theorem fourUFixedSLOB_u6 (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) :
    FourUFixedSLOB IsU6TwoIndex := by
  intro X _ _ hKG K B a J hK hBSC hBN hrank haB hJ hJq hJL hBJ
  exact sLOB_of_bal207_component h207 hKG hBSC haB
    (KSF4Kit.isComponentOf_centralizer_of_glaPComponent hK hJ hJq) hBJ isU6Two_bal207 hJL

end SLOB

theorem sLOB_of_balancedIn_centralizer {X : Type} [Group X] {B J : Subgroup X} {a : X}
    (hBC : B ≤ Subgroup.centralizer ({a} : Set X)) (hJC : J ≤ Subgroup.centralizer ({a} : Set X))
    (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hbal : IsStronglyBalancedIn 3 (B.subgroupOf (Subgroup.centralizer ({a} : Set X)))
      (J.subgroupOf (Subgroup.centralizer ({a} : Set X)))) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  set C := Subgroup.centralizer ({a} : Set X) with hCdef
  intro S hS hcop hBS
  have hSC : S ≤ C := fun s hs => (Subgroup.mem_inf.1 (hS hs)).2
  have hS'N : S.subgroupOf C ≤
      Subgroup.normalizer (((J.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro s' hs'
    have hsS : (s' : X) ∈ S := Subgroup.mem_subgroupOf.1 hs'
    have hsN : (s' : X) ∈ Subgroup.normalizer (J : Set X) := (Subgroup.mem_inf.1 (hS hsS)).1
    have hN := Subgroup.mem_normalizer_iff.1 hsN
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hcard : Nat.Coprime 3 (Nat.card (S.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
    exact hcop
  have hB'N' : B.subgroupOf C ⊓
      Subgroup.normalizer (((J.subgroupOf C : Subgroup ↥C)) : Set ↥C) ≤
      Subgroup.normalizer (((S.subgroupOf C : Subgroup ↥C)) : Set ↥C) := by
    intro b' hb'
    have hb'B : b' ∈ B.subgroupOf C := (Subgroup.mem_inf.1 hb').1
    have hbB : (b' : X) ∈ B := Subgroup.mem_subgroupOf.1 hb'B
    have hbS : (b' : X) ∈ Subgroup.normalizer (S : Set X) :=
      hBS (Subgroup.mem_inf.2 ⟨hbB, hBJ hbB⟩)
    have hN := Subgroup.mem_normalizer_iff.1 hbS
    rw [Subgroup.mem_normalizer_iff]
    intro k
    simpa [Subgroup.mem_subgroupOf] using hN (k : X)
  have hcent := hbal (S.subgroupOf C) hS'N hcard hB'N'
  refine Subgroup.commutator_le.2 (fun h hh s hs => ?_)
  have hcomm : h * s = s * h := by
    have hsC : (⟨s, hSC hs⟩ : ↥C) ∈ S.subgroupOf C := Subgroup.mem_subgroupOf.2 hs
    have hhC : (⟨h, hJC hh⟩ : ↥C) ∈ J.subgroupOf C := Subgroup.mem_subgroupOf.2 hh
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hcent hsC) _ hhC)
  rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
  exact Subgroup.one_mem _

theorem fourUFixedSLOB_e6 (h : Bal209Two) : FourUFixedSLOB Bal209TwoIndex := by
  intro X _ _ hKG K B a J hK hBSC hBN hrank haB hJ hJq hJL hBJ
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
  have hLie : IsLieQuot ↥(J.subgroupOf C) Bal209TwoIndex :=
    isLieQuot_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hJL
  have hrank' : GLATwoLocalRank 3 ↥C ≤ CFSG.Open.pRank 3 (B.subgroupOf C) := by
    have h1 := glaTwoLocalRank_subgroup_le Nat.prime_three C
    have h2 := pRank_map_eq_of_injective (by norm_num : 1 < 3) C.subtype C.subtype_injective
      (B.subgroupOf C)
    rw [Subgroup.map_subgroupOf_eq_of_le hBC] at h2
    exact h1.trans (hrank.trans h2.le)
  have hbal := h ↥C (hKG.subgroup C) (J.subgroupOf C) (B.subgroupOf C) hcomp hSC' hBN' hrank' hLie
  exact sLOB_of_balancedIn_centralizer hBC hJC hBJ hbal

section L2Eight

open CFSG.HardMathSupport.Dickson.Bal207 CFSG.HardMathSupport.Dickson.Bal207.Small

theorem sLOB_of_l2Eight_component
    {X : Type} [Group X] [Finite X]
    {K B J : Subgroup X} {a : X} (hK : IsSubnormal K ⊤) (hBSC : IsSCp 3 ⊤ B) (haB : a ∈ B)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set X)) (hL : IsLieQuot ↥J IsL2EightIndex) :
    IsStronglyLocallyOneBalanced 3 B a J := by
  have hJC : GLAPComponent 3 (Subgroup.centralizer ({a} : Set X)) J :=
    glaPComponent_centralizer Nat.prime_three hK hJ
  have hsn := Glue.isSubnormal_centralizer_of_glaPComponent a hK hJ
  have hH := compHyp_bar Nat.prime_three (by decide) hJC (le_centralizer_of_mem hBSC haB) hBJ hBSC
  obtain ⟨⟨d, hv⟩, hd, ⟨eJ⟩⟩ := hL
  obtain ⟨q, rfl, hq⟩ := hd.exists
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF8 : Nat.card (GaloisField q.p q.exponent) = 8 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq.1, hq.2]
    norm_num
  let eJ' := eJ.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  haveI : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q.p q.exponent)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF8]; norm_num)
  obtain ⟨⟨e₃⟩, -⟩ := barX_centralQuotient hJC eJ'.isSimpleGroup
  refine stronglyLocallyOneBalanced_of_bar Nat.prime_three hsn hBJ ?_
  exact Amb.l2EightCase hH.core hH.comp hH.scp hH.norm hF8 (e₃.symm.trans eJ')

end L2Eight

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
