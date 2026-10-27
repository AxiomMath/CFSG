module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeC
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeMoore
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeE

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native
  CFSG.Sporadic.Co1Block CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Dickson.I271

section Conj

theorem shapeRkAt_conj {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T') {x : Q}
    (h : ShapeRkAt p Good Rk x) (c : Q) : ShapeRkAt p Good Rk (c * x * c⁻¹) :=
  ShapeRkAt.of_equiv hp hGood hRk (MulAut.conj c) h

theorem three_ne_one_of_orderOf {G : Type} [Group G] {t : G} (h : orderOf t = 3) : t ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  exact absurd h (by norm_num)

end Conj

section Census


theorem tabCo1_census_three (s : ↥GA) (hs : orderOf s = 3) :
    ∃ g x : ↥GA, s = g * x * g⁻¹ ∧
      (MRep (rootRows 0) (x : GL24) ∨ MRep (rootRows 1) (x : GL24) ∨
        MRep (rootRows 2) (x : GL24) ∨
        MRep (mul (mul (aRows 1) (aRows 4)) (aRows 5)) (x : GL24)) := by
  have := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨g, -, hg⟩ := @CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full
    ↥GA (Subgroup.toGroup GA) 3 ⟨Nat.prime_three⟩ ⊤ Qg inferInstance le_top
    (by rw [card_Qg, factorization_card_GA]) s (Subgroup.mem_top s) hs
  set t := g⁻¹ * s * g with htdef
  have hto : orderOf t = 3 := by
    have := orderOf_conj_GA g⁻¹ s
    rw [inv_inv] at this
    rw [htdef, this, hs]
  have hst : s = g * t * g⁻¹ := by rw [htdef]; group
  rcases fusion_root hg hto with hE | ⟨j, hj, c, ht'⟩
  · obtain ⟨g', x, hx, hcases⟩ := tabCo1_threeE_census t hE
      (@three_ne_one_of_orderOf ↥GA (Subgroup.toGroup GA) t hto)
    refine ⟨g * g', x, ?_, ?_⟩
    · rw [hst, hx]
      group
    · rcases hcases with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  · refine ⟨g * c, root j, ?_, ?_⟩
    · rw [hst, ht']
      group
    · have hr : MRep (rootRows j) (root j : GL24) := wordL_rep _
      rcases hj with rfl | rfl | rfl
      · exact Or.inl hr
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr (Or.inl hr))

end Census

@[expose] def Co1ThreeAShape : Prop :=
  ∀ x : ↥GA, MRep (mul (mul (aRows 1) (aRows 4)) (aRows 5)) (x : GL24) →
    ShapeRkAt 3 (GoodSpor 3 [.Suz]) (RkSpor 3 [.Suz]) x

section Final


theorem tabCo1_centShapeRk_three
    (hb : Nonempty (CFSG.Blueprint.NativeSporadic.Suz ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group))
    (h3A : ∀ x : ↥GA, MRep (mul (mul (aRows 1) (aRows 4)) (aRows 5)) (x : GL24) →
      ShapeRkAt 3 (GoodSpor 3 [.Suz]) (RkSpor 3 [.Suz]) x) :
    CentShapeRk 3 (GoodSpor 3 [.Suz]) (RkSpor 3 [.Suz]) ↥GA := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro k hk1 hk3
  obtain ⟨g, x, hx, hcases⟩ := tabCo1_census_three k (orderOf_eq_prime hk3 hk1)
  have hshape : ShapeRkAt 3 (GoodSpor 3 [.Suz]) (RkSpor 3 [.Suz]) x := by
    rcases hcases with h | h | h | h
    · exact Or.inl (tabCo1_threeC x h)
    · exact tabCo1_threeB hb x h
    · exact tabCo1_threeD hb x h
    · exact h3A x h
  rw [hx]
  exact @shapeRkAt_conj ↥GA (Subgroup.toGroup GA) inferInstance 3 Nat.prime_three _ _
    (fun _ _ _ _ e h => GoodSpor.of_equiv e h) (fun _ _ _ _ e h => RkSpor.of_equiv e h) x hshape g

theorem centShapeRk_Co1_three
    (hBr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (h3A : ∀ x : ↥GA, MRep (mul (mul (aRows 1) (aRows 4)) (aRows 5)) (x : GL24) →
      ShapeRkAt 3 (GoodSpor 3 [.Suz]) (RkSpor 3 [.Suz]) x) :
    CentShapeRk 3 (GoodSpor 3 [.Suz]) (RkSpor 3 [.Suz]) (NativeSporadic.Carrier .Co1) := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  haveI : Finite (NativeSporadic.Carrier .Co1) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .Co1 (by decide)
  have h := tabCo1_centShapeRk_three (hBr .Suz) h3A
  have e : ↥GA ≃* NativeSporadic.Carrier .Co1 := co1MatEquiv.symm
  exact CentShapeRk.of_equiv (Q := ↥GA) (Q' := NativeSporadic.Carrier .Co1) Nat.prime_three
    (fun _ _ _ _ e h => GoodSpor.of_equiv e h) (fun _ _ _ _ e h => RkSpor.of_equiv e h) e h

end Final

end CFSG.HardMathSupport.Dickson.I271.TabCo1
