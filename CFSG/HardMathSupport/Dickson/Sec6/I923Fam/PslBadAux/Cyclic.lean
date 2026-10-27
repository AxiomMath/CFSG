module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover

theorem isCyclic_prod_of_subsingleton_right {A B : Type*} [Group A] [Group B] [IsCyclic A]
    [Subsingleton B] : IsCyclic (A × B) := by
  haveI : Unique B := ⟨⟨1⟩, fun b => Subsingleton.elim _ _⟩
  exact isCyclic_of_surjective (MulEquiv.prodUnique (M := A) (N := B)).symm.toMonoidHom
    (MulEquiv.prodUnique (M := A) (N := B)).symm.surjective

theorem exceptionalOrders_psl_eq {n p f : ℕ} (hn : 3 ≤ n) (h322 : ¬(n = 3 ∧ p = 2 ∧ f = 2))
    (hdvd : ¬ Nat.Coprime 3 (Nat.gcd n (p ^ f - 1))) :
    Multiplier.exceptionalOrders .PSL n p f = (1, 1) := by
  unfold Multiplier.exceptionalOrders
  split <;> simp_all

theorem isCyclic_hopfMultiplier_psl (hGA : GriessAllModelsStatement) {X : Type} [Group X]
    {n p f : ℕ} (hm : StatedClassicalModel X .PSL n p f) (hn : 3 ≤ n)
    (h322 : ¬(n = 3 ∧ p = 2 ∧ f = 2)) (hdvd : ¬ Nat.Coprime 3 (Nat.gcd n (p ^ f - 1))) :
    IsCyclic (hopfMultiplier X) := by
  obtain ⟨-, ⟨e⟩⟩ := hGA X .PSL n p f ⟨hm.1, Or.inl hm⟩
  have hex := exceptionalOrders_psl_eq hn h322 hdvd
  have hgb : (Multiplier.genericOrders .PSL n p f).2 = 1 := rfl
  have hE1 : (Multiplier.exceptionalOrders .PSL n p f).1 = 1 := by rw [hex]
  have hE2 : (Multiplier.exceptionalOrders .PSL n p f).2 = 1 := by rw [hex]
  haveI : Subsingleton (Multiplicative (ZMod (Multiplier.genericOrders .PSL n p f).2)) := by
    rw [hgb]; infer_instance
  haveI : Subsingleton (Multiplicative (ZMod (Multiplier.exceptionalOrders .PSL n p f).1)) := by
    rw [hE1]; infer_instance
  haveI : Subsingleton (Multiplicative (ZMod (Multiplier.exceptionalOrders .PSL n p f).2)) := by
    rw [hE2]; infer_instance
  haveI : IsCyclic (Multiplier.generic .PSL n p f × Multiplier.exceptional .PSL n p f) := by
    haveI : IsCyclic (Multiplier.generic .PSL n p f) := isCyclic_prod_of_subsingleton_right
    exact isCyclic_prod_of_subsingleton_right
  let e' : hopfMultiplier X ≃* Multiplier.generic .PSL n p f × Multiplier.exceptional .PSL n p f :=
    (hopfMultiplierEquivGriess X).symm.trans e
  exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

end CFSG.HardMathSupport.Dickson.Sec6.I923
