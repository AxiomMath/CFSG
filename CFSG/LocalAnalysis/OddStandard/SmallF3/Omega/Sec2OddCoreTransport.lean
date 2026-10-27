module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

@[expose] def centralizerMulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    ↥(Subgroup.centralizer ({g} : Set G)) ≃* ↥(Subgroup.centralizer ({e g} : Set H)) where
  toFun x := ⟨e x, Subgroup.mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp x.2])⟩
  invFun y := ⟨e.symm y, Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply,
      Subgroup.mem_centralizer_singleton_iff.mp y.2])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : G) (y : G))

theorem oddCore_centralizer_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {g : G} (h : oddCore ↥(Subgroup.centralizer ({e g} : Set H)) = ⊥) :
    oddCore ↥(Subgroup.centralizer ({g} : Set G)) = ⊥ :=
  oddCore_eq_bot_of_mulEquiv (centralizerMulEquiv e g).symm h

theorem oddCore_quotient_eq_bot_of_odd {G : Type*} [Group G] [Finite G] (hG : oddCore G = ⊥)
    (N : Subgroup G) [hn : N.Normal] (hN : Odd (Nat.card N)) : oddCore (G ⧸ N) = ⊥ := by
  have hNbot : N = ⊥ := le_bot_iff.mp (hG ▸ le_oddCore_of_normal hn hN)
  exact oddCore_eq_bot_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hNbot).trans QuotientGroup.quotientBot).symm hG

theorem isPGroup_two_centralizer_of_pow_eq_one {G : Type*} [Group G] {a : G} (k : ℕ)
    (h : ∀ g : G, g * a = a * g → g ^ (2 ^ k) = 1) :
    IsPGroup 2 ↥(Subgroup.centralizer ({a} : Set G)) := fun g =>
  ⟨k, Subtype.ext (h (g : G) (Subgroup.mem_centralizer_singleton_iff.mp g.2))⟩

end CFSG.OddStandard.SmallF3.Omega
