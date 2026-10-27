module

public import CFSG.CGT.PushingUpLit.CGT6.EmbQuot
public import CFSG.CGT.PushingUpLit.CGT6.EmbTransNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Iso

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {A : Subgroup V} (h : GInv G A)
  {K : Subgroup (MulAut V)}

@[expose] noncomputable def commBarQEquiv (hKG : K ≤ G) (hA : A ⊓ commV K = ⊥) :
    ↥(commV K) ≃* ↥(commV (barQ h K)) :=
  MulEquiv.ofBijective
    (((QuotientGroup.mk' A).comp (commV K).subtype).codRestrict (commV (barQ h K))
      (fun u => by
        rw [← commV_barQ h hKG]
        exact ⟨u, u.2, rfl⟩))
    ⟨fun a b hab => by
      have h1 : ((a : V) : V ⧸ A) = ((b : V) : V ⧸ A) := congrArg Subtype.val hab
      have h2 : (a : V)⁻¹ * (b : V) ∈ A := QuotientGroup.eq.mp h1
      have h3 : (a : V)⁻¹ * (b : V) ∈ A ⊓ commV K :=
        ⟨h2, (commV K).mul_mem ((commV K).inv_mem a.2) b.2⟩
      rw [hA, Subgroup.mem_bot, inv_mul_eq_one] at h3
      exact Subtype.ext h3,
     fun y => by
      have hy : (y : V ⧸ A) ∈ (commV K).map (QuotientGroup.mk' A) := by
        rw [commV_barQ h hKG]
        exact y.2
      obtain ⟨u, hu, hu'⟩ := hy
      exact ⟨⟨u, hu⟩, Subtype.ext hu'⟩⟩

theorem coe_commBarQEquiv_apply (hKG : K ≤ G) (hA : A ⊓ commV K = ⊥) (k : ↥K)
    (u : ↥(commV K)) (hu : (k : MulAut V) (u : V) ∈ commV K) :
    ((commBarQEquiv h hKG hA ⟨(k : MulAut V) (u : V), hu⟩ : ↥(commV (barQ h K))) : V ⧸ A) =
      resQ G A h ⟨k, hKG k.2⟩
        ((commBarQEquiv h hKG hA u : ↥(commV (barQ h K))) : V ⧸ A) := rfl

theorem isNatSectionBy_barQ_iff {S M : Type*} [Group S] [Group M] (act : S → M → M)
    (hKG : K ≤ G) (hA : A ⊓ commV K = ⊥) (hinj : Function.Injective (resQ G A h)) :
    IsNatSectionBy act K (commV K) ⊥ ↔
      IsNatSectionBy act (barQ h K) (commV (barQ h K)) ⊥ := by
  constructor
  · intro hK
    refine IsNatSectionBy.of_equiv (homImgEquiv hinj hKG).symm (commBarQEquiv h hKG hA).symm
      (fun x hx p hp => commV_invariant hx hp) ?_ hK
    intro x p hp
    obtain ⟨k, rfl⟩ := (homImgEquiv hinj hKG).surjective x
    rw [MulEquiv.symm_apply_apply]
    obtain ⟨u, rfl⟩ := (commBarQEquiv h hKG hA).surjective p
    rw [MulEquiv.symm_apply_apply]
    have hku : (k : MulAut V) (u : V) ∈ commV K := commV_invariant k.2 u.2
    have h2 : (commBarQEquiv h hKG hA).symm
        ⟨(homImgEquiv hinj hKG k : MulAut (V ⧸ A))
          ((commBarQEquiv h hKG hA u : ↥(commV (barQ h K))) : V ⧸ A), hp⟩ =
        ⟨(k : MulAut V) u, hku⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      exact (coe_commBarQEquiv_apply h hKG hA k u hku).symm
    rw [h2]
  · intro hK
    refine IsNatSectionBy.of_equiv (homImgEquiv hinj hKG) (commBarQEquiv h hKG hA)
      (fun x hx p hp => commV_invariant hx hp) ?_ hK
    intro x p hp
    exact coe_commBarQEquiv_apply h hKG hA x p hp

end Iso

end CFSG.CGT.PushingUpLit.CGT6
