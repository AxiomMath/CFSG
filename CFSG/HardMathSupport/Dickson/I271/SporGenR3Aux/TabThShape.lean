module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShapeSMain
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShapeZ
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThCentU
public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalBridge

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp

section Components


theorem th_orders : thS ^ 3 = 1 ∧ thZ ^ 3 = 1 ∧ thU ^ 3 = 1 := by
  obtain ⟨hs, hz, hu⟩ := th_orderOf
  exact ⟨by rw [← hs]; exact pow_orderOf_eq_one _, by rw [← hz]; exact pow_orderOf_eq_one _,
    by rw [← hu]; exact pow_orderOf_eq_one _⟩

end Components

section Assembly


theorem th_centShapeRk :
    CentShapeRk 3 (LeafType 3) (fun _ _ => True) ↥J := by
  haveI : Finite ↥J := finite_J
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨hS3, hZ3, hU3⟩ := th_orders
  intro k hk1 hkp
  have hk3 : orderOf k = 3 := orderOf_eq_prime hkp hk1
  obtain ⟨h, c, hc, e, he, hcon⟩ := th_census k hk3
  have hrep : c ^ 3 = 1 ∧ ShapeRkAt 3 (LeafType 3) (fun _ _ => True) c := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨hS3, th_shape_S⟩
    · exact ⟨hZ3, th_shape_Z⟩
    · exact ⟨hU3, th_shape_U⟩
  obtain ⟨hc3, hshape⟩ := hrep
  have hshape' : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (c ^ e) :=
    ShapeRkAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc3 he).symm hshape
  have hconj := ShapeRkAt.of_equiv Nat.prime_three hGood hRk (MulAut.conj h) hshape'
  have hk : (MulAut.conj h) (c ^ e) = k := by
    rw [MulAut.conj_apply]
    exact hcon
  rw [hk] at hconj
  exact hconj

theorem leafShape_Th : LeafShape .Th 3 := by
  haveI : Finite ↥J := finite_J
  have e : NativeSporadic.Th ≃* ↥J := thEquivJ
  haveI : Finite NativeSporadic.Th := Finite.of_equiv ↥J e.symm.toEquiv
  have h : CentShapeRk 3 (LeafType 3) (fun _ _ => True) NativeSporadic.Th :=
    CentShapeRk.of_equiv (Q := ↥J) (Q' := NativeSporadic.Th) Nat.prime_three
      (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h) e.symm th_centShapeRk
  have h2 : CentShape 3 (LeafType 3) NativeSporadic.Th := CentShape.of_centShapeRk h
  exact h2

end Assembly

end CFSG.HardMathSupport.Dickson.I271
