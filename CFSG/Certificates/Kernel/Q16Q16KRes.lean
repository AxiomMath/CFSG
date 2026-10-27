module

public import CFSG.Certificates.Kernel.Census.RestrictSound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic

public section

namespace CFSG.KC.Q16Q16K

open Subgroup CFSG.KC.Census CFSG.KC.Census.Restrict CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

theorem noQ16Q16_of_res {n m : ℕ} {X : Set (Equiv.Perm (Fin n))} {Y : Set (Equiv.Perm (Fin m))}
    (O : Fin m → Fin n) (hO : Function.Injective O) (hX : ∀ g ∈ X, ∀ i, ∃ j, g (O i) = O j)
    (hY : ∀ σ ∈ Y, ∃ g ∈ X, ∀ i, g (O i) = O (σ i))
    (hcard : Nat.card (closure X) ≤ Nat.card (closure Y)) (h : NoQ16Q16 (closure Y)) :
    NoQ16Q16 (closure X) := by
  have hS : closure X ≤ stab O :=
    (closure_le _).2 fun g hg => mem_stab_of_maps hO (hX g hg)
  let f : closure X →* Equiv.Perm (Fin m) := (resHom hO).comp (inclusion hS)
  have hle : closure Y ≤ f.range := by
    rw [closure_le]
    intro σ hσ
    obtain ⟨g, hg, hgσ⟩ := hY σ hσ
    exact ⟨⟨g, subset_closure hg⟩, resHom_eq hO hgσ⟩
  have hinj : Function.Injective f :=
    injective_of_card_le_range f (hcard.trans (card_le_of_le hle))
  have hR : Nat.card (closure X) = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have heq : closure Y = f.range := eq_of_le_of_card_ge hle (hR ▸ hcard)
  exact NoQ16Q16.of_injective (MonoidHom.ofInjective hinj).toMonoidHom
    (MonoidHom.ofInjective hinj).injective (heq ▸ h)

end CFSG.KC.Q16Q16K

end
