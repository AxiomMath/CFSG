module

public import CFSG.CGT.T75N.L29TwoGroup

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups
open CFSG.LieType.Steinberg.CentralExt

theorem ker_eq_bot_of_sylow_lift
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (π : Y →* SpecialLinearGroup (Fin n) F) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center Y) (R : Subgroup Y) (hRK : R ⊓ π.ker = ⊥)
    (hcard : Nat.card R = 2 ^ (Nat.card (SpecialLinearGroup (Fin n) F)).factorization 2) :
    π.ker = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SpecialLinearGroup (Fin n) F) := Finite.of_surjective _ hπ
  have hpK : IsPGroup 2 π.ker := isPGroup_two_ker hn π hπ hcen
  let f : R →* SpecialLinearGroup (Fin n) F := π.comp R.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxK : (x : Y) ∈ π.ker := hx
    have hx' : (x : Y) ∈ R ⊓ π.ker := ⟨x.2, hxK⟩
    rw [hRK] at hx'
    exact Subtype.ext (Subgroup.mem_bot.1 hx')
  let e : R ≃* f.range := MonoidHom.ofInjective hf
  have hcardE : Nat.card f.range = Nat.card R := (Nat.card_congr e.toEquiv).symm
  let P : Sylow 2 (SpecialLinearGroup (Fin n) F) :=
    Sylow.ofCard f.range (by rw [hcardE]; exact hcard)
  let s : P.toSubgroup →* Y := R.subtype.comp e.symm.toMonoidHom
  have hs : ∀ x : P.toSubgroup, π (s x) = (x : SpecialLinearGroup (Fin n) F) := by
    intro x
    have h1 : f (e.symm x) = (x : SpecialLinearGroup (Fin n) F) := by
      have := congrArg (fun y : f.range => (y : SpecialLinearGroup (Fin n) F))
        (e.apply_symm_apply x)
      exact this
    exact h1
  obtain ⟨s₀, hs₀⟩ := CFSG.Semidihedral.CentralTransferSplitting.exists_section_of_sylow 2
    Nat.prime_two π hπ hcen hpK P s hs
  exact SL2Closed.ker_eq_bot_of_section π hcen s₀ hs₀

end CFSG.CGT.T75N
