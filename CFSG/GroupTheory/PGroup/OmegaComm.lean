module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega

public section

namespace CFSG

variable {X : Type*}

theorem mem_omega₁_iff_of_comm {p : ℕ} [Group X]
    (hcomm : ∀ a b : X, a * b = b * a) {y : X} :
    y ∈ omega₁ X (p := p) ↔ y ^ p = 1 := by
  constructor
  · intro hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => simpa using hx
    | one => simp
    | mul x z _ _ hx hz =>
        have hc : Commute x z := hcomm x z
        rw [hc.mul_pow, hx, hz, one_mul]
    | inv x _ hx => rw [inv_pow, hx, inv_one]
  · intro hy
    exact Subgroup.subset_closure (by simpa using hy)

theorem card_omega₁_of_isCyclic {p : ℕ} [Group X] [Finite X] [IsCyclic X] :
    Nat.card (omega₁ X (p := p)) = (Nat.card X).gcd p := by
  letI : CommGroup X := IsCyclic.commGroup
  have hcomm : ∀ a b : X, a * b = b * a := fun a b => mul_comm a b
  have heq : omega₁ X (p := p) = MonoidHom.ker (powMonoidHom p : X →* X) := by
    ext y
    rw [mem_omega₁_iff_of_comm hcomm, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [heq, IsCyclic.card_powMonoidHom_ker]

end CFSG
