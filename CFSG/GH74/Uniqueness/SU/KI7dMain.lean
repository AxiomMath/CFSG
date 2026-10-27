module

public import CFSG.GH74.Uniqueness.SU.KI7dPerm
public import CFSG.GH74.Uniqueness.SU.KInputs2

public section

namespace CFSG.GH74.Uniqueness.SU.K

open Equiv Subgroup CFSG.GH74.Uniqueness.SU.KI7d

theorem ki7d : KI7d := by
  intro n hn X _ _ hX a ha2 p hp hp2 Y hY hinv
  obtain ⟨-, -, hcard, ⟨e⟩⟩ := hX
  have : Fact p.Prime := ⟨hp⟩
  let ρ : X →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  let π : X →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp ρ
  have hker : ∀ x : X, π x = 1 → x ∈ center X := by
    intro x hx
    have h1 : ρ x = 1 := Subtype.ext hx
    have h2 : (x : X ⧸ center X) = 1 := e.injective (by simpa [ρ] using h1)
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hsq : ∀ z ∈ center X, z * z = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := center X) (x := ⟨z, hz⟩)
    rw [hcard] at this
    have h := congrArg Subtype.val this
    simpa [pow_two] using h
  have hinj : Function.Injective (π.comp Y.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hz : (y : X) ∈ center X := hker _ hy
    obtain ⟨k, hk⟩ := hY y
    have hk' : (y : X) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd : Odd (p ^ k) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    obtain ⟨m, hm⟩ := hodd
    have h1 : (y : X) = 1 := by
      have : (y : X) ^ (2 * m + 1) = (y : X) := by
        rw [pow_succ, pow_mul, pow_two, hsq _ hz, one_pow, one_mul]
      rw [← this, ← hm]; exact hk'
    exact Subtype.ext h1
  set Yb : Subgroup (Perm (Fin n)) := (π.comp Y.subtype).range with hYb
  have hcardYb : Nat.card Yb = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have hpYb : IsPGroup p Yb := IsPGroup.of_card (n := k) (by rw [hcardYb, hk])
  have ha1 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, pow_two] at this
  have hbar2 : π a * π a = 1 := by rw [← map_mul, ha1, map_one]
  have hsign : Perm.sign (π a) = 1 := Perm.mem_alternatingGroup.mp (ρ a).2
  have hbinv : ∀ y ∈ Yb, π a * y * (π a)⁻¹ = y⁻¹ := by
    rintro _ ⟨y, rfl⟩
    show π a * π y * (π a)⁻¹ = (π y)⁻¹
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul, hinv y y.2]
  rw [← hcardYb]
  exact perm_bound hn hp hp2 Yb hpYb (π a) hbar2 hsign hbinv

end CFSG.GH74.Uniqueness.SU.K
