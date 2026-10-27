module

public import CFSG.Certificates.Kernel.K36K.Sound
public import CFSG.GH74.Generic.S1.Exo.Q3SingleM12

public section

namespace CFSG.KD.K36K

open CFSG.Blueprint CFSG.KS.K36K CFSG.KS.MaxD2 CFSG.KD.CoreD2K

theorem m12_eq_one_of_fix {t : Equiv.Perm (Fin 12)}
    (ht : t ∈ NativeSporadic.M12) {O : Finset (Fin 12)} (hO : 5 ≤ O.card)
    (hfix : ∀ x ∈ O, t x = x) : t = 1 := by
  let q : Fin 5 → Fin 12 := fun i => O.orderEmbOfFin rfl (Fin.castLE hO i)
  have hq : Function.Injective q := fun i j hij =>
    Fin.castLE_injective _ ((O.orderEmbOfFin rfl).injective hij)
  exact CFSG.GH74.Generic.S1.Exo.m12_fix_five t ht ⟨q, hq⟩ fun i =>
    hfix _ (Finset.orderEmbOfFin_mem O rfl _)

theorem m12_eq_one_of_fixWK {w kF k0 o0 : Nat} {F : Nat → Nat}
    {f : ℕ → Equiv.Perm (Fin 12)} {HW : List (List Nat)} {OL : List Nat} {OW : List (List Nat)}
    (hF : ∀ k < kF, PR 12 w (F k) (f k)) (h : fixWK 12 w kF F k0 o0 HW OL OW = true)
    (hO : 5 ≤ (Finset.univ.filter fun x : Fin 12 => (x : ℕ) ∈ OL).card)
    {t : Equiv.Perm (Fin 12)} (htM : t ∈ NativeSporadic.M12) (ht : ∀ k < kF, t * f k = f k * t) :
    t = 1 :=
  m12_eq_one_of_fix htM hO fun x hx =>
    fixWK_sound hF h t ht x (Finset.mem_filter.1 hx).2

end CFSG.KD.K36K

end
