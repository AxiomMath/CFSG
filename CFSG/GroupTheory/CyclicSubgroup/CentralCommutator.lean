module


public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GroupTheory.CyclicSubgroup

theorem isCyclic_of_faithful_central_commutator {G : Type*} [Group G]
    (D X : Subgroup G) [IsCyclic X] (y : G)
    (hcent : D ≤ Subgroup.centralizer (X : Set G))
    (hcomm : ∀ d ∈ D, d * y * d⁻¹ * y⁻¹ ∈ X)
    (hfaith : ∀ d ∈ D, d * y = y * d → d = 1) :
    IsCyclic D := by
  let f : D →* X :=
    { toFun := fun d => ⟨d.1 * y * d.1⁻¹ * y⁻¹, hcomm d.1 d.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro a b
        have hb : (b.1 * y * b.1⁻¹ * y⁻¹) * a.1 = a.1 * (b.1 * y * b.1⁻¹ * y⁻¹) := by
          have := hcent a.2 (b.1 * y * b.1⁻¹ * y⁻¹) (hcomm b.1 b.2)
          simpa [mul_assoc] using this
        have hc : (a.1 * y * a.1⁻¹ * y⁻¹) * (b.1 * y * b.1⁻¹ * y⁻¹)
            = (b.1 * y * b.1⁻¹ * y⁻¹) * (a.1 * y * a.1⁻¹ * y⁻¹) := by
          letI := IsCyclic.commGroup (α := X)
          have := mul_comm (⟨a.1 * y * a.1⁻¹ * y⁻¹, hcomm a.1 a.2⟩ : X)
            ⟨b.1 * y * b.1⁻¹ * y⁻¹, hcomm b.1 b.2⟩
          exact congrArg Subtype.val this
        ext
        simp only [Subgroup.coe_mul]
        rw [hc]
        calc (a.1 * b.1) * y * (a.1 * b.1)⁻¹ * y⁻¹
            = (a.1 * (b.1 * y * b.1⁻¹ * y⁻¹) * a.1⁻¹) *
                (a.1 * y * a.1⁻¹ * y⁻¹) := by group
          _ = _ := by rw [← hb]; group }
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro d hd
    have h1 : d.1 * y * d.1⁻¹ * y⁻¹ = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hd)
      simpa [f] using this
    apply Subtype.ext
    apply hfaith d.1 d.2
    calc d.1 * y = (d.1 * y * d.1⁻¹ * y⁻¹) * (y * d.1) := by group
      _ = y * d.1 := by rw [h1, one_mul]
  exact isCyclic_of_injective f hinj

end CFSG.GroupTheory.CyclicSubgroup
