module

public import CFSG.Sporadic.SuzOddCore.InvCentralizers
public import CFSG.Certificates.Kernel.Spor.BTupSound
import CFSG.Certificates.Kernel.Spor.BaseSep

public section

namespace CFSG.KS.BTup

open CFSG.Sporadic.SuzOddCore CFSG.Certificates CFSG.Certificates.Native

@[expose] def c1Base : Fin 3 → Fin 1782 := ![0, 2, 1]


theorem invE1_eq_one {h : Equiv.Perm (Fin 1782)} (hh : h ∈ invE 1)
    (hfix : ∀ t, h (c1Base t) = c1Base t) : h = 1 := by
  have hA := invInnerChain_arrays (i := 1) (by norm_num)
  have hV := (validSchreier_of_chainOK hA (by norm_num) invChain_check_1.2.2.1).1
  refine (invInnerChain 1).eq_one_of_fixes_base hV hh fun i => ?_
  have hi : (i : ℕ) < 3 := by
    have := hA.base_size
    have h3 : ((invInnerBases.getD 1 []).toArray).size = 3 := rfl
    omega
  have e : (invInnerChain 1).base.get i = c1Base ⟨i, hi⟩ := by
    apply Fin.ext
    rw [hA.base_val i]
    rcases i with ⟨i, hi'⟩
    interval_cases i <;> rfl
  rw [e]
  exact hfix _

theorem invE1_ext {g h : Equiv.Perm (Fin 1782)} (hg : g ∈ invE 1) (hh : h ∈ invE 1)
    (e : ∀ t, g (c1Base t) = h (c1Base t)) : g = h := by
  have h1 := invE1_eq_one (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg) fun t => by
    rw [Equiv.Perm.mul_apply, e t]
    exact Equiv.symm_apply_apply h _
  exact (inv_mul_eq_one.1 h1).symm

theorem card_eq_c1Orbit {H : Subgroup (Equiv.Perm (Fin 1782))} (hH : H ≤ invE 1) :
    Nat.card H = Nat.card {v : Fin 3 → Fin 1782 // ∃ h ∈ H, ∀ t, v t = h (c1Base t)} :=
  card_eq_orbit_card H c1Base fun h hh hfix => invE1_eq_one (hH hh) hfix

theorem card_genSub_of_btK {w kw km k cnt base : Nat} {G K R POS : Nat → Nat}
    {gp : Nat → Equiv.Perm (Fin 1782)} (hw : 0 < w) (hle : genSub 1782 k gp ≤ invE 1)
    (hg : ∀ j < k, ∀ x : Fin 1782, CFSG.KC.Enum.pg w (mask w) (G j) x = gp j x)
    (hb : ∀ t : Fin 3, CFSG.KC.Enum.pg w (mask w) base t = c1Base t) (hc : btHdK cnt = true)
    (hp : ∀ i < cnt, btPtK 1782 w (mask w) 3 kw km k cnt base G K R POS i = true) :
    Nat.card (genSub 1782 k gp) = cnt :=
  (card_eq_c1Orbit hle).trans (btOrbit_card hw hg hb hc hp)

end CFSG.KS.BTup

end
