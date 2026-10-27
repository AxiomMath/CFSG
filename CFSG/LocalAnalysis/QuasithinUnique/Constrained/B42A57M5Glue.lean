module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5Vec

public section

namespace CFSG.QuasithinUnique.B42A57

open Multiplicative

theorem Tc_injective_of (c : V4) (hc : ∀ u, Tc c u = 0 → u = 0) : Function.Injective (Tc c) := by
  intro a b hab
  have h1 : Tc c (a + b) = 0 := by
    rw [Tc_add, hab]
    funext i
    have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
    exact h2 _
  have h3 := hc _ h1
  funext i
  have h4 := congrFun h3 i
  simp only [Pi.add_apply, Pi.zero_apply] at h4
  have h5 : ∀ z z' : ZMod 2, z + z' = 0 → z = z' := by decide
  exact h5 _ _ h4

@[expose] def TcHom (c : V4) : Multiplicative V4 →* Multiplicative V4 where
  toFun u := ofAdd (Tc c (toAdd u))
  map_one' := by
    show ofAdd (Tc c 0) = 1
    rw [Tc_zero]
    rfl
  map_mul' u v := by
    show ofAdd (Tc c (toAdd u + toAdd v)) = ofAdd (Tc c (toAdd u)) * ofAdd (Tc c (toAdd v))
    rw [Tc_add]
    rfl

theorem TcHom_injective (c : V4) (hc : ∀ u, Tc c u = 0 → u = 0) : Function.Injective (TcHom c) :=
  fun a b h => by
    have : Tc c (toAdd a) = Tc c (toAdd b) := congrArg toAdd h
    exact toAdd.injective (Tc_injective_of c hc this)

@[expose] noncomputable def TcEquiv (c : V4) (hc : ∀ u, Tc c u = 0 → u = 0) :
    Multiplicative V4 ≃* Multiplicative V4 :=
  MulEquiv.ofBijective (TcHom c)
    ⟨TcHom_injective c hc, Finite.surjective_of_injective (TcHom_injective c hc)⟩

theorem TcEquiv_apply (c : V4) (hc : ∀ u, Tc c u = 0 → u = 0) (u : V4) :
    TcEquiv c hc (ofAdd u) = ofAdd (Tc c u) := rfl

end CFSG.QuasithinUnique.B42A57
