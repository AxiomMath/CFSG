module

public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem schK_of_ge {n w m nw idn : Nat} {S SI LR TR TRI : Nat → Nat} {kS BP nb i T h₀ : Nat}
    (hc : rcnt (LR i) ≤ h₀) (cnt : Nat) :
    schK n w m nw idn S SI LR TR TRI kS BP nb i T h₀ cnt = true := by
  unfold schK
  rw [strictB_eq, strictB_eq, strictB_eq]
  apply allN_of_forall
  intro dh _
  rw [strictB_eq]
  have hb : Nat.blt (Nat.add h₀ dh) (rcnt (LR i)) = false := by
    cases h : Nat.blt (Nat.add h₀ dh) (rcnt (LR i))
    · rfl
    · have := Nat.blt_eq ▸ h
      simp only [Nat.add_eq] at this
      omega
  rw [hb]

theorem forall_lt_split {P : Nat → Prop} {a b : Nat} (h1 : ∀ s < a, P s) (h2 : ∀ s, a ≤ s → P s) :
    ∀ s < b, P s := fun s _ => (Nat.lt_or_ge s a).elim (h1 s) (h2 s)

theorem schK_slices {n w m nw idn : Nat} {S SI LR TR TRI : Nat → Nat} {kS BP nb i T NS NSi CH : Nat}
    (hc : rcnt (LR i) ≤ NSi * CH)
    (h : ∀ s < NSi, schK n w m nw idn S SI LR TR TRI kS BP nb i T (s * CH) CH = true) :
    ∀ s < NS, schK n w m nw idn S SI LR TR TRI kS BP nb i T (s * CH) CH = true :=
  forall_lt_split h fun _ hs => schK_of_ge (Nat.le_trans hc (Nat.mul_le_mul_right CH hs)) CH

end CFSG.KS.Raw

end
