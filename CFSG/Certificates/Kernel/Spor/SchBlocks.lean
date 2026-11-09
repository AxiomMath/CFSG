module

public import CFSG.Certificates.Kernel.Spor.SchTriv

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem schK_of_blocks (n w m nw idn : Nat) (S SI LR TR TRI : Nat → Nat)
    (kS BP nb i T h₀ cnt u q : Nat) (hu : 0 < u) (hc : cnt ≤ q * u)
    (h : ∀ d < q, schK n w m nw idn S SI LR TR TRI kS BP nb i T (Nat.add h₀ (Nat.mul u d)) u = true) :
    schK n w m nw idn S SI LR TR TRI kS BP nb i T h₀ cnt = true := by
  unfold schK
  rw [strictB_eq, strictB_eq, strictB_eq]
  apply allN_of_forall
  intro dh hdh
  have hq : dh / u < q :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hdh (by rw [Nat.mul_comm]; exact hc))
  have h1 := h (dh / u) hq
  unfold schK at h1
  rw [strictB_eq, strictB_eq, strictB_eq] at h1
  have h2 := allN_spec h1 (dh % u) (Nat.mod_lt dh hu)
  have e : Nat.add (Nat.add h₀ (Nat.mul u (dh / u))) (dh % u) = Nat.add h₀ dh := by
    show h₀ + u * (dh / u) + dh % u = h₀ + dh
    have := Nat.div_add_mod dh u
    omega
  rw [← e]
  exact h2

end CFSG.KS.Raw

end
