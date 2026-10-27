module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourEightThree

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.G6

theorem actsAsNaturalL2_of_symData_three {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1)
    {E : Subgroup (MulAut V)} (θ : ↥E ≃* Equiv.Perm (Fin 3)) (β : ↥(commV E) →* coreMod 3)
    (hinv : ∀ x ∈ E, ∀ p ∈ commV E, x p ∈ commV E) (hsurj : Function.Surjective β)
    (hker : β.ker = ⊥)
    (hequiv : ∀ (x : ↥E) (p : ↥(commV E)) (hp : (x : MulAut V) p ∈ commV E),
      β ⟨(x : MulAut V) p, hp⟩ = coreAct 3 (θ x) (β p)) :
    ActsAsNaturalL2 E (commV E) := by
  have hinj : Function.Injective β := (MonoidHom.ker_eq_bot_iff β).1 hker
  let βe : ↥(commV E) ≃* coreMod 3 := MulEquiv.ofBijective β ⟨hinj, hsurj⟩
  have hU : Nat.card (commV E) = 4 := by
    rw [Nat.card_congr βe.toEquiv, CFSG.CGT.PushingUpLit.BHS.card_coreMod_three']
  have hst : E ≤ stabSub (commV E) := by
    intro x hx
    rw [mem_stabSub]
    intro u
    constructor
    · intro hxu
      have h := hinv x⁻¹ (E.inv_mem hx) (x u) hxu
      have hu : (x⁻¹ : MulAut V) (x u) = u := by simp
      rwa [hu] at h
    · intro hu
      exact hinv x hx u hu
  have hfaith : E ⊓ centSub (commV E) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgE, hgC⟩ := hg
    rw [mem_centSub] at hgC
    have hfix : ∀ q : ↥(coreMod 3), coreAct 3 (θ ⟨g, hgE⟩) q = q := by
      intro q
      obtain ⟨p, rfl⟩ := hsurj q
      have hp : (g : MulAut V) (p : V) ∈ commV E := hinv g hgE (p : V) p.2
      have hgp : (g : MulAut V) (p : V) = (p : V) := hgC (p : V) p.2
      rw [← hequiv ⟨g, hgE⟩ p hp]
      exact congrArg β (Subtype.ext hgp)
    have hact : coreAct 3 (θ ⟨g, hgE⟩) = 1 := MulEquiv.ext fun q => hfix q
    have hinj3 := CFSG.CGT.PushingUpLit.BHS.coreAct_injective (n := 3) (le_refl 3)
    have hθ1 : θ ⟨g, hgE⟩ = 1 := hinj3 (hact.trans (map_one (coreAct 3)).symm)
    have hg1 : (⟨g, hgE⟩ : ↥E) = 1 := θ.injective (hθ1.trans (map_one θ).symm)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hg1
  have htop : autSub E (commV E) = ⊤ := by
    rw [eq_top_iff]
    intro φ _
    obtain ⟨π, hπ⟩ :=
      CFSG.CGT.PushingUpLit.CGT6.coreAct_three_surjective (βe.symm.trans (φ.trans βe))
    refine (mem_autSub).2 ⟨⟨((θ.symm π : ↥E) : MulAut V), hst (θ.symm π).2⟩, (θ.symm π).2, ?_⟩
    ext p
    rw [resHom_apply]
    have hp : (((θ.symm π : ↥E) : MulAut V) (p : V)) ∈ commV E :=
      hinv _ (θ.symm π).2 (p : V) p.2
    have hb : β ⟨((θ.symm π : ↥E) : MulAut V) (p : V), hp⟩ = β (φ p) := by
      rw [hequiv (θ.symm π) p hp, MulEquiv.apply_symm_apply, hπ]
      have hsy : βe.symm (β p) = p := βe.symm_apply_apply p
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hsy]
      rfl
    exact congrArg Subtype.val (hinj hb)
  exact actsAsNaturalL2_of_full hV hU hst hfaith htop

end CFSG.AGLEmbeddingD2.Tits.E23

end
