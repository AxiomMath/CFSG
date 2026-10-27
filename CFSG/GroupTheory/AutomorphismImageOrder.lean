module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GroupTheory

theorem card_dvd_of_lifts_automorphisms {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f)
    (A : Subgroup (MulAut X)) (B : Subgroup (MulAut Y))
    (hlift : ∀ b ∈ B, ∃ a ∈ A, ∀ x : X, f (a x) = b (f x)) :
    Nat.card B ∣ Nat.card A := by
  let R : Subgroup (MulAut X × MulAut Y) :=
    { carrier := {q | q.1 ∈ A ∧ q.2 ∈ B ∧ ∀ x, f (q.1 x) = q.2 (f x)}
      one_mem' := ⟨A.one_mem, B.one_mem, fun _ => rfl⟩
      mul_mem' := by
        rintro a b ⟨ha, ha', hfa⟩ ⟨hb, hb', hfb⟩
        refine ⟨A.mul_mem ha hb, B.mul_mem ha' hb', fun x => ?_⟩
        change f ((a.1 * b.1) x) = (a.2 * b.2) (f x)
        rw [MulAut.mul_apply, MulAut.mul_apply, hfa, hfb]
      inv_mem' := by
        rintro a ⟨ha, ha', hfa⟩
        refine ⟨A.inv_mem ha, B.inv_mem ha', fun x => ?_⟩
        change f (a.1⁻¹ x) = a.2⁻¹ (f x)
        have h := hfa (a.1⁻¹ x)
        rw [MulAut.apply_inv_self] at h
        rw [h, MulAut.inv_apply_self] }
  let fst : R →* A :=
    ((MonoidHom.fst _ _).comp R.subtype).codRestrict A (fun q => q.property.1)
  let snd : R →* B :=
    ((MonoidHom.snd _ _).comp R.subtype).codRestrict B (fun q => q.property.2.1)
  have hsnd : Function.Surjective snd := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha, hfa⟩ := hlift b hb
    exact ⟨⟨(a, b), ha, hb, hfa⟩, rfl⟩
  have hfst : Function.Injective fst := by
    intro q q' h
    have hfirst : q.val.1 = q'.val.1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Prod.ext hfirst
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := hf y
    rw [← q.property.2.2 x, ← q'.property.2.2 x, hfirst]
  exact (Subgroup.card_dvd_of_surjective hsnd).trans
    (Subgroup.card_dvd_of_injective fst hfst)

end CFSG.GroupTheory

end
