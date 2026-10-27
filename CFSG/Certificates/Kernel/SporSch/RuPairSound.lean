module

public import Certificates.Data.Kernel.SporSch.RuPair
public import CFSG.Certificates.Kernel.Misc.RuBaseSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.Misc.RuPair

open CFSG.KC.Enum CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuBase CFSG.Sporadic.Th.Native

theorem tr_compT {n : Nat} {P Q : Table} {f g : Nat → Nat} (hP : TR n P f) (hQ : TR n Q g)
    (hg : ∀ x < n, g x < n) : TR n (compT n P Q) (fun x => f (g x)) := by
  refine ⟨by simp [compT], fun x hx => ?_⟩
  unfold ap compT
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
  have e : (Q[x]!).toNat = g x := hQ.2 x hx
  rw [e]
  exact hP.2 _ (hg x hx)

theorem commK_sound {G H GI HI T Z : Nat} {t z : Equiv.Perm (Fin 4060)}
    (hT : CFSG.KS.Raw.Orb.PRep 4060 12 T t) (hZ : CFSG.KS.Raw.Orb.PRep 4060 12 Z z)
    (h : commK G H GI HI T Z = true) (y : Fin 4060) :
    apP G (apP H (apP GI (apP HI y))) = ((t * z * t⁻¹) y : Fin 4060) := by
  have hb := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h _ (t⁻¹ y).2)
  have e1 : apP T (t⁻¹ y) = y := (hT (t⁻¹ y)).trans (congrArg Fin.val (t.apply_symm_apply y))
  have e2 : apP Z (t⁻¹ y) = z (t⁻¹ y) := hZ (t⁻¹ y)
  have e3 : apP T (z (t⁻¹ y)) = t (z (t⁻¹ y)) := hT (z (t⁻¹ y))
  rw [e1, e2, e3] at hb
  rw [hb, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

end CFSG.KC.Misc.RuPair

end
