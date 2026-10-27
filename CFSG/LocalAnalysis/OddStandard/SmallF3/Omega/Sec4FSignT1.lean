module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSign
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSignInv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.sign_T1 (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) :
    ∃ ψ : ↥(P ⊔ zpowers x) →* ℤˣ, ∀ (g : G) (hg : g ∈ P ⊔ zpowers x),
      (∃ k : G, g = k⁻¹ * t * k) → ψ ⟨g, hg⟩ = -1 := by
  obtain ⟨ψ, hψ⟩ := sec4F_sign_hom (P ⊔ zpowers x) (sec4FX t φ x)
    ((Set.finite_range _).union (Set.finite_range _))
    (fun g hg e he => h.T1_invariant hT hg he)
  refine ⟨ψ, fun g hg hgconj => ?_⟩
  have hgX := h.T1_conj_X hT hgconj hg
  rw [sec4FX] at hgX
  rcases hgX with ⟨q, hq⟩ | ⟨c, hc⟩
  ·
    obtain rfl : g = sec4MPt t φ q := hq.symm
    obtain ⟨u, v, huv, hRq, hact⟩ := h.R_right hT q
    refine hψ (sec4MPt t φ q) hg (sec4FD t φ x u) (sec4FD t φ x v)
      (Or.inr ⟨u, rfl⟩) (Or.inr ⟨v, rfl⟩) (fun hd => huv (h.d_inj hd)) ?_ ?_ ?_
    · rw [hact u, Equiv.swap_apply_left]
    · rw [hact v, Equiv.swap_apply_right]
    · intro e he heu hev
      rw [sec4FX] at he
      rcases he with ⟨p, rfl⟩ | ⟨c', rfl⟩
      · have hcomm := h.A_comm (sec4MPt_mem_A h.data q) (sec4MPt_mem_A h.data p)
        rw [hcomm]; group
      · have hcu : c' ≠ u := fun hcu => heu (by rw [hcu])
        have hcv : c' ≠ v := fun hcv => hev (by rw [hcv])
        have hcomm : sec4MPt t φ q * sec4FD t φ x c'
            = sec4FD t φ x c' * sec4MPt t φ q := by
          by_contra hne
          rcases (hRq c').mp hne with h' | h'
          · exact hcu h'
          · exact hcv h'
        rw [hcomm]; group
  ·
    obtain rfl : g = sec4FD t φ x c := hc.symm
    obtain ⟨u, v, huv, hRl, hreal⟩ := h.R_left hT c
    refine hψ (sec4FD t φ x c) hg (sec4MPt t φ u) (sec4MPt t φ v)
      (Or.inl ⟨u, rfl⟩) (Or.inl ⟨v, rfl⟩) (fun hp => huv (h.pt_injective hp)) ?_ ?_ ?_
    · rw [hreal u, Equiv.swap_apply_left]
    · rw [hreal v, Equiv.swap_apply_right]
    · intro e he heu hev
      rw [sec4FX] at he
      rcases he with ⟨p, rfl⟩ | ⟨c', rfl⟩
      · have hpu : p ≠ u := fun hpu => heu (by rw [hpu])
        have hpv : p ≠ v := fun hpv => hev (by rw [hpv])
        rw [hreal p, Equiv.swap_apply_of_ne_of_ne hpu hpv]
      · have hcomm : sec4FD t φ x c * sec4FD t φ x c'
            = sec4FD t φ x c' * sec4FD t φ x c := h.d_comm c c'
        rw [hcomm]; group

end CFSG.OddStandard.SmallF3.Omega
