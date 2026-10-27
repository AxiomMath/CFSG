module

public import Certificates.Data.Kernel.A45Cls.Pock
public import CFSG.Certificates.Kernel.Enum.ZCSound

public section

namespace CFSG.KC.A45Cls

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.EnumSound

variable {n w : Nat}

theorem exN_spec {N : Nat} {f : Nat → Bool} (h : exN N f = true) : ∃ i < N, f i = true := by
  unfold exN at h
  by_contra hc
  have h2 : allN N (fun i => !f i) = true := PK.allN_iff.2 fun i hi => by
    cases e : f i
    · rfl
    · exact absurd ⟨i, hi, e⟩ hc
  rw [h2] at h
  exact absurd h (by decide)

theorem eq3_of_eq {r p q s : Nat} {gr gp gq gs : Equiv.Perm (Fin n)} (hr : PRep n w r gr)
    (hp : PRep n w p gp) (hq : PRep n w q gq) (hs : PRep n w s gs) (e : gr = gp * gq * gs) :
    eq3 n w (mask w) r p q s = true := by
  refine eq3_iff.2 fun i hi => ?_
  rw [prep_at hs hi, hq (gs ⟨i, hi⟩), hp (gq (gs ⟨i, hi⟩)), prep_at hr hi, e]
  rfl

theorem eq22_sound {p q r s : Nat} {gp gq gr gs : Equiv.Perm (Fin n)}
    (h : eq22 n w (mask w) p q r s = true) (hp : PRep n w p gp) (hq : PRep n w q gq)
    (hr : PRep n w r gr) (hs : PRep n w s gs) : gp * gq = gr * gs := by
  unfold eq22 at h
  rw [PK.allN_iff] at h
  refine Equiv.ext fun x => Fin.ext ?_
  have e := Nat.eq_of_beq_eq_true (h x x.2)
  rw [hq x, hp (gq x), hs x, hr (gs x)] at e
  exact e

theorem cjAll_spec {N P : Nat} {X Y : Nat → Nat} {u : Equiv.Perm (Fin n)}
    {x y : Nat → Equiv.Perm (Fin n)} (h : cjAll n w N X Y P = true) (hu : PRep n w P u)
    (hx : ∀ j < N, PRep n w (X j) (x j)) (hy : ∀ m < N, PRep n w (Y m) (y m)) :
    ∀ j < N, ∃ m < N, y m = u * x j * u := by
  intro j hj
  obtain ⟨m, hm, e⟩ := exN_spec (PK.allN_iff.1 h j hj)
  exact ⟨m, hm, prep_unique (hy m hm) (eq3_prep e hu (hx j hj) hu)⟩

theorem cjBy_spec {N P Q : Nat} {X : Nat → Nat} {u v : Equiv.Perm (Fin n)}
    {x : Nat → Equiv.Perm (Fin n)} (h : cjBy n w N X P Q = true) (hu : PRep n w P u)
    (hv : PRep n w Q v) (hx : ∀ j < N, PRep n w (X j) (x j)) :
    ∃ k < N, x k * u = v * x k := by
  obtain ⟨k, hk, e⟩ := exN_spec h
  exact ⟨k, hk, eq22_sound e (hx k hk) hu hv (hx k hk)⟩

end CFSG.KC.A45Cls

end
