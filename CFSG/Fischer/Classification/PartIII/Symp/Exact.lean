module

public import CFSG.Fischer.Classification.PartIII.Symp.Transvection

public section

namespace CFSG.Fischer.Classification.LocalSymp

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer Symplectic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (B : LinearMap.BilinForm (ZMod 2) V)

theorem tv_comp_ne {u v : V} (huu : B u u = 0) (huv : B u v = 1) (hvu : B v u = 1) :
    tv B u ∘ tv B v ≠ tv B v ∘ tv B u := by
  intro h
  have hu : u ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearMap.zero_apply] at huv
    exact zero_ne_one huv
  have := congrFun h u
  simp only [Function.comp_apply, tv_apply, huu, zero_smul, add_zero, huv, one_smul, map_add,
    LinearMap.add_apply, hvu, zero_add] at this
  apply hu
  have h' : u + v + u = u + (u + v) := by abel
  rw [h', zmod_two_add_add_self] at this
  have := congrArg (· + v) this
  simpa only [add_assoc, zmod_two_add_self, add_zero] using this.symm

variable {X : Type} [Group X] (act : X → V → V)

theorem not_commute_of_tv (hsymm : ∀ x y, B x y = B y x)
    (hmul : ∀ a b, act (a * b) = act a ∘ act b) {f g : X} {u v : V} (hf : act f = tv B u)
    (hg : act g = tv B v) (huu : B u u = 0) (huv : B u v = 1) : f * g ≠ g * f := by
  intro h
  apply tv_comp_ne B huu huv (by rw [hsymm]; exact huv)
  rw [← hf, ← hg, ← hmul, ← hmul, h]

theorem commute_iff_of_tv (hsymm : ∀ x y, B x y = B y x)
    (hmul : ∀ a b, act (a * b) = act a ∘ act b) (hinj : Function.Injective act) {f g : X}
    {u v : V} (hf : act f = tv B u) (hg : act g = tv B v) (huu : B u u = 0) :
    f * g = g * f ↔ B u v = 0 := by
  refine ⟨fun h => ?_, commute_of_tv B act hsymm hmul hinj hf hg⟩
  by_contra hne
  exact not_commute_of_tv B act hsymm hmul hf hg huu (zmod_two_eq_one_of_ne_zero hne) h

theorem ncard_eq_of_tv [Finite X] [Finite V] (hnd : ∀ x, (∀ y, B y x = 0) → x = 0)
    (hinj : Function.Injective act) {F : Set X} {P : V → Prop} (hP0 : ∀ v, P v → v ≠ 0)
    (hF : ∀ f ∈ F, ∃ v, P v ∧ act f = tv B v) (hsurj : ∀ w, P w → ∃ f ∈ F, act f = tv B w) :
    F.ncard = {v | P v}.ncard := by
  refine le_antisymm (ncard_le_of_tv B act hinj hF) ?_
  choose! g hgF hg using hsurj
  exact Set.ncard_le_ncard_of_injOn g (fun w hw => hgF w hw) fun w hw w' hw' h =>
    eq_of_tv_eq B hnd (v := w') (hP0 w hw) (by rw [← hg w hw, ← hg w' hw', h])

variable (hsymm : ∀ x y, B x y = B y x) (hnd : ∀ x, (∀ y, B y x = 0) → x = 0)
  (hmul : ∀ a b, act (a * b) = act a ∘ act b) (hinj : Function.Injective act) {F : Set X}
  {P : V → Prop} (hP0 : ∀ v, P v → v ≠ 0) (hPB : ∀ v, P v → B v v = 0)
  (hF : ∀ f ∈ F, ∃ v, P v ∧ act f = tv B v) (hsurj : ∀ w, P w → ∃ f ∈ F, act f = tv B w)
include hsymm hnd hmul hinj hP0 hPB hF hsurj

theorem ncard_localClass_eq_of_tv [Finite X] [Finite V] {f₀ : X} {s : V} (hf₀ : f₀ ∈ F)
    (h₀ : act f₀ = tv B s) : (LocalClass F f₀).ncard = {w | P w ∧ B w s = 0 ∧ w ≠ s}.ncard := by
  obtain ⟨s₁, hs₁, h₁⟩ := hF f₀ hf₀
  have hss₁ : s = s₁ := eq_of_tv_eq B hnd (v := s₁) (by
    rintro rfl
    exact hP0 s₁ hs₁ (eq_of_tv_eq B hnd (hP0 s₁ hs₁) (by rw [← h₁, h₀]))) (by rw [← h₀, h₁])
  subst hss₁
  choose! vec hvec using hF
  choose! g hgF hg using hsurj
  apply le_antisymm
  · refine Set.ncard_le_ncard_of_injOn vec (fun f hf => ?_) fun f hf f' hf' h => ?_
    · obtain ⟨hP, hact⟩ := hvec f hf.1
      exact ⟨hP, (commute_iff_of_tv B act hsymm hmul hinj hact h₀ (hPB _ hP)).1 hf.2.2,
        fun he => hf.2.1 (hinj (by rw [hact, he, h₀]))⟩
    · exact hinj (by rw [(hvec f hf.1).2, (hvec f' hf'.1).2, h])
  · refine Set.ncard_le_ncard_of_injOn g (fun w ⟨hw, hws, hne⟩ => ?_) fun w hw w' hw' h => ?_
    · refine ⟨hgF w hw, fun he => hne ?_, commute_of_tv B act hsymm hmul hinj (hg w hw) h₀ hws⟩
      exact eq_of_tv_eq B hnd (v := s) (hP0 w hw) (by rw [← hg w hw, he, h₀])
    · exact eq_of_tv_eq B hnd (v := w') (hP0 w hw.1) (by rw [← hg w hw.1, ← hg w' hw'.1, h])

theorem ncard_muSet_eq_of_tv [Finite X] [Finite V] {f₀ f₁ : X} {s s' : V} (h₀ : act f₀ = tv B s)
    (h₁ : act f₁ = tv B s') (hss' : B s s' = 1) :
    (muSet F f₀ f₁).ncard = {w | P w ∧ B w s = 0 ∧ B w s' = 0}.ncard := by
  refine le_antisymm ?_ (ncard_le_ncard_muSet_of_tv B act hsymm hnd hmul hinj hP0 hsurj h₀ h₁
    hss')
  choose! vec hvec using hF
  refine Set.ncard_le_ncard_of_injOn vec (fun f hf => ?_) fun f hf f' hf' h => ?_
  · obtain ⟨hP, hact⟩ := hvec f hf.1.1
    have h0 := (commute_iff_of_tv B act hsymm hmul hinj hact h₀ (hPB _ hP)).1 hf.1.2.2
    have h1 := (commute_iff_of_tv B act hsymm hmul hinj hact h₁ (hPB _ hP)).1 hf.2.2.2
    exact ⟨hP, h0, h1⟩
  · exact hinj (by rw [(hvec f hf.1.1).2, (hvec f' hf'.1.1).2, h])

end CFSG.Fischer.Classification.LocalSymp
