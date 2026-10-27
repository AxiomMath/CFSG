module

public import CFSG.Fischer.Classification.Defs
public import CFSG.Fischer.Uniq.MuSets
public import CFSG.Fischer.Classification.Symplectic.Basic
public import CFSG.Open.Defs

public section

namespace CFSG.Fischer.Classification.LocalSymp

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer Symplectic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (B : LinearMap.BilinForm (ZMod 2) V)

section Tv

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

@[expose] def tv (v x : V) : V := x + B x v • v

theorem tv_apply (v x : V) : tv B v x = x + B x v • v := rfl

theorem tv_comm {u v : V} (huv : B u v = 0) (hvu : B v u = 0) (x : V) :
    tv B u (tv B v x) = tv B v (tv B u x) := by
  simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    huv, hvu, mul_zero, add_zero]
  abel

theorem tv_tv_tv {u v : V} (huu : B u u = 0) (huv : B u v = 1) (hvu : B v u = 1) (x : V) :
    tv B u (tv B v (tv B u x)) = tv B (u + v) x := by
  simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    huu, huv, hvu, mul_zero, add_zero, mul_one]
  rcases zmod_two_cases (B x u) with h1 | h1 <;> rcases zmod_two_cases (B x v) with h2 | h2 <;>
    simp only [h1, h2, zero_add, add_zero, zero_smul, one_smul, zmod_two_one_add_one] <;>
    zmod_two_abel

theorem eq_of_tv_eq (hnd : ∀ x, (∀ y, B y x = 0) → x = 0) {u v : V} (hu : u ≠ 0)
    (h : tv B u = tv B v) : u = v := by
  obtain ⟨y, hy⟩ : ∃ y, B y u ≠ 0 := by
    by_contra! h'
    exact hu (hnd u h')
  have hyv := congrFun h y
  rw [tv_apply, tv_apply, zmod_two_eq_one_of_ne_zero hy, one_smul] at hyv
  have h2 : u = B y v • v := add_left_cancel hyv
  rcases zmod_two_cases (B y v) with h0 | h0
  · rw [h0, zero_smul] at h2
    exact absurd h2 hu
  · rwa [h0, one_smul] at h2

end Tv

section Group

variable {X : Type} [Group X] (act : X → V → V)

theorem commute_of_tv (hsymm : ∀ x y, B x y = B y x) (hmul : ∀ a b, act (a * b) = act a ∘ act b)
    (hinj : Function.Injective act) {f g : X} {u v : V} (hf : act f = tv B u)
    (hg : act g = tv B v) (huv : B u v = 0) : f * g = g * f :=
  hinj (by
    rw [hmul, hmul, hf, hg]
    funext x
    exact tv_comm B huv (by rw [hsymm]; exact huv) x)

theorem bilin_eq_one_of_not_commute (hsymm : ∀ x y, B x y = B y x)
    (hmul : ∀ a b, act (a * b) = act a ∘ act b) (hinj : Function.Injective act) {f g : X}
    {u v : V} (hf : act f = tv B u) (hg : act g = tv B v) (hfg : f * g ≠ g * f) : B u v = 1 :=
  zmod_two_eq_one_of_ne_zero fun h => hfg (commute_of_tv B act hsymm hmul hinj hf hg h)

theorem isSymplecticType_of_tv (hsymm : ∀ x y, B x y = B y x)
    (hmul : ∀ a b, act (a * b) = act a ∘ act b) (hinj : Function.Injective act) {F : Set X}
    (hF : ∀ f ∈ F, ∃ v, B v v = 0 ∧ act f = tv B v) : IsSymplecticType F := by
  intro d hd e he z hz hde
  obtain ⟨u, huu, hu⟩ := hF d hd
  obtain ⟨v, -, hv⟩ := hF e he
  obtain ⟨w, -, hw⟩ := hF z hz
  have huv := bilin_eq_one_of_not_commute B act hsymm hmul hinj hu hv hde
  by_cases hwu : B w u = 0
  · exact Or.inl (commute_of_tv B act hsymm hmul hinj hw hu hwu)
  by_cases hwv : B w v = 0
  · exact Or.inr (Or.inl (commute_of_tv B act hsymm hmul hinj hw hv hwv))
  refine Or.inr (Or.inr (commute_of_tv B act hsymm hmul hinj hw (v := u + v) ?_ ?_))
  · rw [hmul, hmul, hu, hv]
    funext x
    exact tv_tv_tv B huu huv (by rw [hsymm]; exact huv) x
  · rw [map_add, zmod_two_eq_one_of_ne_zero hwu, zmod_two_eq_one_of_ne_zero hwv]
    rfl

omit [Group X] in
theorem ncard_le_of_tv [Finite V] (hinj : Function.Injective act) {F : Set X} {P : V → Prop}
    (hF : ∀ f ∈ F, ∃ v, P v ∧ act f = tv B v) : F.ncard ≤ {v | P v}.ncard := by
  choose! vec hvec using hF
  refine Set.ncard_le_ncard_of_injOn vec (fun f hf => (hvec f hf).1) fun f hf g hg h => ?_
  exact hinj (by rw [(hvec f hf).2, (hvec g hg).2, h])

theorem ncard_le_ncard_muSet_of_tv [Finite X] (hsymm : ∀ x y, B x y = B y x)
    (hnd : ∀ x, (∀ y, B y x = 0) → x = 0) (hmul : ∀ a b, act (a * b) = act a ∘ act b)
    (hinj : Function.Injective act) {F : Set X} {P : V → Prop} (hP0 : ∀ v, P v → v ≠ 0)
    (hsurj : ∀ w, P w → ∃ f ∈ F, act f = tv B w) {f₀ f₁ : X} {s s' : V}
    (h₀ : act f₀ = tv B s) (h₁ : act f₁ = tv B s') (hss' : B s s' = 1) :
    {w | P w ∧ B w s = 0 ∧ B w s' = 0}.ncard ≤ (muSet F f₀ f₁).ncard := by
  choose! g hgF hg using hsurj
  refine Set.ncard_le_ncard_of_injOn g (fun w ⟨hw, hws, hws'⟩ => ?_) fun w hw w' hw' h => ?_
  · refine ⟨⟨hgF w hw, fun h => ?_, commute_of_tv B act hsymm hmul hinj (hg w hw) h₀ hws⟩,
      ⟨hgF w hw, fun h => ?_, commute_of_tv B act hsymm hmul hinj (hg w hw) h₁ hws'⟩⟩
    · have hws₀ := eq_of_tv_eq B hnd (v := s) (hP0 w hw) (by rw [← hg w hw, h, h₀])
      rw [hws₀, hss'] at hws'
      exact one_ne_zero hws'
    · have hws₁ := eq_of_tv_eq B hnd (v := s') (hP0 w hw) (by rw [← hg w hw, h, h₁])
      rw [hws₁, hsymm, hss'] at hws
      exact one_ne_zero hws
  · exact eq_of_tv_eq B hnd (v := w') (hP0 w hw.1) (by rw [← hg w hw.1, ← hg w' hw'.1, h])

end Group

section Cosets

theorem sum_zmod_two (f : ZMod 2 → ℕ) : ∑ a, f a = f 0 + f 1 :=
  Fin.sum_univ_two f

variable {s s' : V}

theorem ncard_eq_add_add_add [Finite V] (hss : B s s = 0) (hs's' : B s' s' = 0)
    (hss' : B s s' = 1) (hs's : B s' s = 1) (R : V → Prop) :
    {x | R x}.ncard = {w | R w ∧ B w s = 0 ∧ B w s' = 0}.ncard +
      {w | R (s + w) ∧ B w s = 0 ∧ B w s' = 0}.ncard +
      {w | R (s' + w) ∧ B w s = 0 ∧ B w s' = 0}.ncard +
      {w | R (s + s' + w) ∧ B w s = 0 ∧ B w s' = 0}.ncard := by
  classical
  have := Fintype.ofFinite V
  have key : ∀ a : ZMod 2 × ZMod 2,
      ((Finset.univ.filter R).filter fun x => (B x s', B x s) = a).card =
        (Finset.univ.filter fun w => R (a.1 • s + a.2 • s' + w) ∧ B w s = 0 ∧ B w s' = 0).card := by
    rintro ⟨α, γ⟩
    have hts : B (α • s + γ • s') s = γ := by
      simp [hss, hs's]
    have hts' : B (α • s + γ • s') s' = α := by
      simp [hss', hs's']
    refine Finset.card_nbij' (fun x => x + (α • s + γ • s')) (fun w => α • s + γ • s' + w)
      ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, Prod.mk.injEq] at hx ⊢
      obtain ⟨hR, h1, h2⟩ := hx
      refine ⟨by rwa [add_comm x, zmod_two_add_add_self], ?_, ?_⟩
      · rw [map_add, LinearMap.add_apply, hts, h2, zmod2_add_self]
      · rw [map_add, LinearMap.add_apply, hts', h1, zmod2_add_self]
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq, Prod.mk.injEq] at hw ⊢
      obtain ⟨hR, h1, h2⟩ := hw
      refine ⟨hR, ?_, ?_⟩
      · rw [map_add, LinearMap.add_apply, hts', h2, add_zero]
      · rw [map_add, LinearMap.add_apply, hts, h1, add_zero]
    · intro x _
      simp only
      rw [add_comm x, zmod_two_add_add_self]
    · intro w _
      simp only
      rw [add_comm, ← add_assoc, zmod_two_add_self, zero_add]
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred,
    Finset.card_eq_sum_card_fiberwise (f := fun x => (B x s', B x s)) (t := Finset.univ)
      fun _ _ => Finset.mem_univ _]
  simp only [key, Fintype.sum_prod_type, sum_zmod_two, zero_smul, one_smul, zero_add,
    add_zero]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  ring

theorem card_eq_four_mul [Finite V] (hss : B s s = 0) (hs's' : B s' s' = 0) (hss' : B s s' = 1)
    (hs's : B s' s = 1) : Nat.card V = 4 * {w | B w s = 0 ∧ B w s' = 0}.ncard := by
  have h := ncard_eq_add_add_add B hss hs's' hss' hs's fun _ => True
  simp only [true_and, Set.ofPred_true, Set.ncard_univ] at h
  rw [h]
  ring

theorem ncard_quadratic_add [Finite V] (Q : QuadraticForm (ZMod 2) V)
    (hpol : ∀ x y, QuadraticMap.polar Q x y = B x y) (hs : Q s = 1) (hs' : Q s' = 1)
    (hss' : B s s' = 1) :
    {x | Q x = 1}.ncard + 2 * {w | Q w = 1 ∧ B w s = 0 ∧ B w s' = 0}.ncard =
      3 * {w | B w s = 0 ∧ B w s' = 0}.ncard := by
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    rw [← hpol, ← hpol, QuadraticMap.polar_comm]
  have halt : ∀ x, B x x = 0 := fun x => by
    rw [← hpol, QuadraticMap.polar_self, two_nsmul, zmod_two_add_self]
  have hadd : ∀ x y, Q (x + y) = Q x + Q y + B x y := fun x y => by
    rw [← hpol, QuadraticMap.polar]
    abel
  have h := ncard_eq_add_add_add B (halt s) (halt s') hss' (by rw [hsymm]; exact hss')
    fun x => Q x = 1
  have hcoset : ∀ p : V, Q p = 1 → (∀ w, B w s = 0 → B w s' = 0 → B p w = 0) →
      {w | Q (p + w) = 1 ∧ B w s = 0 ∧ B w s' = 0} = {w | Q w = 0 ∧ B w s = 0 ∧ B w s' = 0} := by
    intro p hp hpw
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hQ, h1, h2⟩
      refine ⟨?_, h1, h2⟩
      rw [hadd, hp, hpw w h1 h2, add_zero] at hQ
      rcases zmod_two_cases (Q w) with h0 | h0
      · exact h0
      · rw [h0] at hQ
        exact absurd hQ (by decide)
    · rintro ⟨hQ, h1, h2⟩
      refine ⟨?_, h1, h2⟩
      rw [hadd, hp, hpw w h1 h2, hQ]
      rfl
  have hs0 : ∀ w, B w s = 0 → B w s' = 0 → B s w = 0 := fun w h1 _ => by rw [hsymm]; exact h1
  have hs'0 : ∀ w, B w s = 0 → B w s' = 0 → B s' w = 0 := fun w _ h2 => by rw [hsymm]; exact h2
  have hss'0 : ∀ w, B w s = 0 → B w s' = 0 → B (s + s') w = 0 := fun w h1 h2 => by
    rw [map_add, LinearMap.add_apply, hs0 w h1 h2, hs'0 w h1 h2, add_zero]
  have hQss' : Q (s + s') = 1 := by
    rw [hadd, hs, hs', hss']
    rfl
  rw [hcoset s hs hs0, hcoset s' hs' hs'0, hcoset (s + s') hQss' hss'0] at h
  have hW : {w | B w s = 0 ∧ B w s' = 0}.ncard = {w | Q w = 0 ∧ B w s = 0 ∧ B w s' = 0}.ncard +
      {w | Q w = 1 ∧ B w s = 0 ∧ B w s' = 0}.ncard := by
    rw [← Set.ncard_union_eq]
    · congr 1
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      rcases zmod_two_cases (Q w) with h0 | h0 <;> simp [h0]
    · rw [Set.disjoint_left]
      rintro w ⟨h0, -⟩ ⟨h1, -⟩
      rw [h0] at h1
      exact absurd h1 (by decide)
  omega

end Cosets

end CFSG.Fischer.Classification.LocalSymp
