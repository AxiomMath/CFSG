module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Fix

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

variable {V : Type} [CommGroup V] [Finite V] {u : MulAut V} {H : Subgroup (MulAut V)}
  {Bv : Subgroup V}

theorem prime_dvd_255 (F : Ctx V u H Bv) {Q : Subgroup (MulAut V)} (hQ : Q ≠ ⊥)
    (hodd : Odd (Nat.card Q)) (hQn : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q)
    (p : ℕ) [Fact p.Prime] (hexp : ∀ g ∈ Q, g ^ p = 1) : p ∣ 255 := by
  classical
  have hP : IsPGroup p Q := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hexp g g.2)⟩
  have hmod := hP.card_modEq_card_fixedPoints V
  have hfp : Nat.card (MulAction.fixedPoints Q V) = 1 := by
    haveI : Unique (MulAction.fixedPoints Q V) :=
      { default := ⟨1, fun q => map_one (q : MulAut V)⟩
        uniq := fun x => Subtype.ext (fixed_eq_one F hQ hodd hQn x (fun q hq => x.2 ⟨q, hq⟩)) }
    exact Nat.card_unique
  rw [hfp, F.card] at hmod
  have := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2 ^ 8)).1 hmod.symm
  simpa using this

end C10

end CFSG.OddStandard.SmallF3.Omega
