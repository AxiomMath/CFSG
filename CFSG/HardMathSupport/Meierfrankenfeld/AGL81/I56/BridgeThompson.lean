module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_fixed_of_isPGroup (hV : ∀ v : V, v ^ 2 = 1) {P : Subgroup (MulAut V)}
    (hP : IsPGroup 2 ↥P) (D : Subgroup V) (hD : ∀ p ∈ P, ∀ d ∈ D, p d ∈ D) (hD1 : D ≠ ⊥) :
    ∃ d ∈ D, d ≠ 1 ∧ ∀ p ∈ P, p d = d := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _inst : MulAction ↥P ↥D :=
    { smul := fun p d => ⟨p.1 d.1, hD p.1 p.2 d.1 d.2⟩
      one_smul := fun d => Subtype.ext (by
        show ((1 : ↥P) : MulAut V) (d : V) = d
        rfl)
      mul_smul := fun p q d => Subtype.ext (by
        show ((p * q : ↥P) : MulAut V) (d : V) = (p : MulAut V) ((q : MulAut V) (d : V))
        rfl) }
  have hmod := hP.card_modEq_card_fixedPoints ↥D
  have hD2 : IsPGroup 2 ↥D := fun d => ⟨1, by
    apply Subtype.ext
    simpa [pow_one, pow_two] using hV d.1⟩
  obtain ⟨n, hn⟩ := hD2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
    have hsub : Subsingleton ↥D := Finite.card_le_one_iff_subsingleton.mp hn.le
    exact hd1 (Subsingleton.elim _ _)
  have heven : Nat.card D % 2 = 0 := by
    rw [hn]; exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  by_contra hcon
  have hfix : ∀ x : ↥D, x ∈ MulAction.fixedPoints ↥P ↥D → x = 1 := by
    intro x hx
    by_contra hx1
    exact hcon ⟨x.1, x.2, fun h => hx1 (Subtype.ext h), fun p hp => by
      have := hx ⟨p, hp⟩
      exact congrArg Subtype.val this⟩
  have hcard : Nat.card (MulAction.fixedPoints ↥P ↥D) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((hfix a.1 a.2).trans (hfix b.1 b.2).symm)⟩,
      ⟨⟨1, fun p => Subtype.ext (by
        show (p : MulAut V) (1 : V) = 1
        exact map_one _)⟩⟩⟩
  rw [hcard] at hmod
  unfold Nat.ModEq at hmod
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
