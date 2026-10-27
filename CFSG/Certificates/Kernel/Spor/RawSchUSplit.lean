module

public import Certificates.Data.Kernel.Spor.RawSchU
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS

theorem allN_strict_split {K : Nat → Bool} {h₀ a b : Nat}
    (h1 : allN a (fun dh => strictB (Nat.add h₀ dh) K) = true)
    (h2 : allN b (fun dh => strictB (Nat.add (h₀ + a) dh) K) = true) :
    allN (a + b) (fun dh => strictB (Nat.add h₀ dh) K) = true := by
  apply allN_of_forall
  intro dh hdh
  rcases Nat.lt_or_ge dh a with hlt | hge
  · exact allN_spec h1 dh hlt
  · have h := allN_spec h2 (dh - a) (by omega)
    simp only [strictB_eq] at h ⊢
    have e : Nat.add (h₀ + a) (dh - a) = Nat.add h₀ dh := by
      simp only [Nat.add_eq]
      omega
    rwa [e] at h

theorem schK2U_split {n w m nw : Nat} {S SI LR TR TRI U : Nat → Nat}
    {kS BP D nb i T h₀ a b : Nat}
    (h1 : schK2U n w m nw S SI LR TR TRI U kS BP D nb i T h₀ a = true)
    (h2 : schK2U n w m nw S SI LR TR TRI U kS BP D nb i T (h₀ + a) b = true) :
    schK2U n w m nw S SI LR TR TRI U kS BP D nb i T h₀ (a + b) = true := by
  unfold schK2U at h1 h2 ⊢
  rw [strictB_eq, strictB_eq, strictB_eq, strictB_eq] at h1 h2 ⊢
  exact allN_strict_split h1 h2

end CFSG.KS.Raw

end
