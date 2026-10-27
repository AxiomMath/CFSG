module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open Subgroup

structure SimpleCentreless (S : Type*) [Group S] : Prop where
  simple : ∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤
  center : ∀ z : S, (∀ g, z * g = g * z) → z = 1
  nontriv : ∃ s : S, s ≠ 1

variable {S : Type*} [Group S]

theorem mk_mul_one (a b : S) : ((a * b, 1) : S × S) = (a, 1) * (b, 1) := by simp

theorem one_mul_mk (a b : S) : ((1, a * b) : S × S) = (1, a) * (1, b) := by simp

theorem mk_eq_mul (s t : S) : ((s, t) : S × S) = (s, 1) * (1, t) := by simp

theorem map_eq_mul (φ : MulAut (S × S)) (x : S × S) : φ x = φ (x.1, 1) * φ (1, x.2) := by
  rw [← map_mul, ← mk_eq_mul]

@[expose] def fstPart (φ : MulAut (S × S)) (k : S × S →* S) : Subgroup S where
  carrier := {s | k (φ (s, 1)) = 1}
  one_mem' := by
    show k (φ (1, 1)) = 1
    rw [show ((1, 1) : S × S) = 1 from rfl, map_one, map_one]
  mul_mem' := by
    intro a b ha hb
    show k (φ (a * b, 1)) = 1
    rw [mk_mul_one, map_mul, map_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    show k (φ (a⁻¹, 1)) = 1
    rw [show ((a⁻¹, 1) : S × S) = (a, 1)⁻¹ by simp, map_inv, map_inv, ha, inv_one]

theorem fstPart_normal (φ : MulAut (S × S)) (k : S × S →* S) : (fstPart φ k).Normal := by
  refine ⟨fun n hn g => ?_⟩
  show k (φ (g * n * g⁻¹, 1)) = 1
  have hn' : k (φ (n, 1)) = 1 := hn
  rw [show ((g * n * g⁻¹, 1) : S × S) = (g, 1) * (n, 1) * (g, 1)⁻¹ by simp, map_mul, map_mul,
    map_inv, map_mul, map_mul, map_inv, hn', mul_one, mul_inv_cancel]

theorem SimpleCentreless.fst_or (hS : SimpleCentreless S) (φ : MulAut (S × S)) :
    (∀ s, (φ (s, 1)).2 = 1) ∨ (∀ s, (φ (s, 1)).1 = 1) := by
  rcases hS.simple _ (fstPart_normal φ (MonoidHom.snd S S)) with h2 | h2
  · rcases hS.simple _ (fstPart_normal φ (MonoidHom.fst S S)) with h1 | h1
    · exfalso
      obtain ⟨s, hs⟩ := hS.nontriv
      apply hs
      have hconj : ∀ (u : S × S) (w : S), ∃ w' : S,
          u * φ (w, 1) * u⁻¹ = φ (w', 1) := by
        intro u w
        refine ⟨(φ.symm u * (w, 1) * (φ.symm u)⁻¹).1, ?_⟩
        have h2c : (φ.symm u * (w, 1) * (φ.symm u)⁻¹).2 = 1 := by simp
        have : φ.symm u * (w, 1) * (φ.symm u)⁻¹ =
            ((φ.symm u * (w, 1) * (φ.symm u)⁻¹).1, 1) := Prod.ext rfl h2c
        rw [← this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      have hcomm : ∀ g : S × S, φ (s, 1) * g = g * φ (s, 1) := by
        intro g
        have h1g : ∀ u : S, φ (s, 1) * (u, 1) = (u, 1) * φ (s, 1) := by
          intro u
          obtain ⟨w', hw'⟩ := hconj (u, 1) s⁻¹
          have hc : φ (s, 1) * (u, 1) * (φ (s, 1))⁻¹ * (u, 1)⁻¹ = φ (s * w', 1) := by
            rw [mk_mul_one, map_mul, ← hw', show ((s⁻¹, 1) : S × S) = (s, 1)⁻¹ by simp,
              map_inv]
            group
          have hmem : s * w' ∈ fstPart φ (MonoidHom.snd S S) := by
            show (φ (s * w', 1)).2 = 1
            rw [← hc]
            simp
          rw [h2, mem_bot] at hmem
          rw [hmem] at hc
          have : φ (1, 1) = 1 := by rw [show ((1, 1) : S × S) = 1 from rfl, map_one]
          rw [this] at hc
          have := mul_inv_eq_one.mp hc
          rw [mul_inv_eq_iff_eq_mul] at this
          exact this
        have h2g : ∀ u : S, φ (s, 1) * (1, u) = (1, u) * φ (s, 1) := by
          intro u
          obtain ⟨w', hw'⟩ := hconj (1, u) s⁻¹
          have hc : φ (s, 1) * (1, u) * (φ (s, 1))⁻¹ * (1, u)⁻¹ = φ (s * w', 1) := by
            rw [mk_mul_one, map_mul, ← hw', show ((s⁻¹, 1) : S × S) = (s, 1)⁻¹ by simp,
              map_inv]
            group
          have hmem : s * w' ∈ fstPart φ (MonoidHom.fst S S) := by
            show (φ (s * w', 1)).1 = 1
            rw [← hc]
            simp
          rw [h1, mem_bot] at hmem
          rw [hmem] at hc
          have : φ (1, 1) = 1 := by rw [show ((1, 1) : S × S) = 1 from rfl, map_one]
          rw [this] at hc
          have := mul_inv_eq_one.mp hc
          rw [mul_inv_eq_iff_eq_mul] at this
          exact this
        obtain ⟨a, b⟩ := g
        rw [mk_eq_mul a b, ← mul_assoc, h1g, mul_assoc, h2g, mul_assoc]
      apply hS.center
      intro g
      have h := hcomm (φ (g, 1))
      rw [← map_mul, ← map_mul] at h
      have := congrArg Prod.fst (φ.injective h)
      simpa using this
    · right
      intro s
      have : s ∈ fstPart φ (MonoidHom.fst S S) := by rw [h1]; trivial
      exact this
  · left
    intro s
    have : s ∈ fstPart φ (MonoidHom.snd S S) := by rw [h2]; trivial
    exact this

abbrev swapAut (S : Type*) [Group S] : MulAut (S × S) := MulEquiv.prodComm

theorem SimpleCentreless.snd_or (hS : SimpleCentreless S) (φ : MulAut (S × S)) :
    (∀ t, (φ (1, t)).1 = 1) ∨ (∀ t, (φ (1, t)).2 = 1) := by
  rcases hS.fst_or (φ * swapAut S) with h | h
  · right
    intro t
    have := h t
    simpa [swapAut] using this
  · left
    intro t
    have := h t
    simpa [swapAut] using this

theorem fst_mem_of_preserve {φ : MulAut (S × S)} (h : ∀ s, (φ (s, 1)).2 = 1) (s : S) :
    φ (s, 1) = ((φ (s, 1)).1, 1) := Prod.ext rfl (h s)

theorem snd_mem_of_preserve {φ : MulAut (S × S)} (h : ∀ t, (φ (1, t)).1 = 1) (t : S) :
    φ (1, t) = (1, (φ (1, t)).2) := Prod.ext (h t) rfl

theorem SimpleCentreless.snd_of_fst [Finite S] (hS : SimpleCentreless S) {φ : MulAut (S × S)}
    (h : ∀ s, (φ (s, 1)).2 = 1) : ∀ t, (φ (1, t)).1 = 1 := by
  rcases hS.snd_or φ with h' | h'
  · exact h'
  · exfalso
    obtain ⟨s, hs⟩ := hS.nontriv
    obtain ⟨x, hx⟩ := φ.surjective (1, s)
    have : (φ x).2 = 1 := by
      rw [map_eq_mul, Prod.snd_mul, h, h', one_mul]
    rw [hx] at this
    exact hs this

theorem SimpleCentreless.snd_of_swap (hS : SimpleCentreless S) {φ : MulAut (S × S)}
    (h : ∀ s, (φ (s, 1)).1 = 1) : ∀ t, (φ (1, t)).2 = 1 := by
  rcases hS.snd_or φ with h' | h'
  · exfalso
    obtain ⟨s, hs⟩ := hS.nontriv
    obtain ⟨x, hx⟩ := φ.surjective (s, 1)
    have : (φ x).1 = 1 := by
      rw [map_eq_mul, Prod.fst_mul, h, h', one_mul]
    rw [hx] at this
    exact hs this
  · exact h'

theorem SimpleCentreless.presFst_of_odd [Finite S] (hS : SimpleCentreless S)
    {φ : MulAut (S × S)} (hφ : Odd (orderOf φ)) : ∀ s, (φ (s, 1)).2 = 1 := by
  rcases hS.fst_or φ with h | h
  · exact h
  · exfalso
    have h' := hS.snd_of_swap h
    have hk : ∀ k : ℕ, (∀ s, ((φ ^ (2 * k + 1)) (s, 1)).1 = 1) ∧
        (∀ t, ((φ ^ (2 * k + 1)) (1, t)).2 = 1) := by
      intro k
      induction k with
      | zero => simpa using ⟨h, h'⟩
      | succ k ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have e : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
        refine ⟨fun s => ?_, fun t => ?_⟩
        · rw [e, pow_add, pow_two, MulAut.mul_apply, MulAut.mul_apply]
          have h1 : φ (s, 1) = (1, (φ (s, 1)).2) := Prod.ext (h s) rfl
          rw [h1]
          have h2 : φ (1, (φ (s, 1)).2) = ((φ (1, (φ (s, 1)).2)).1, 1) :=
            Prod.ext rfl (h' _)
          rw [h2]
          exact ih1 _
        · rw [e, pow_add, pow_two, MulAut.mul_apply, MulAut.mul_apply]
          have h1 : φ (1, t) = ((φ (1, t)).1, 1) := Prod.ext rfl (h' t)
          rw [h1]
          have h2 : φ ((φ (1, t)).1, 1) = (1, (φ ((φ (1, t)).1, 1)).2) :=
            Prod.ext (h _) rfl
          rw [h2]
          exact ih2 _
    obtain ⟨k, hk'⟩ := hφ
    obtain ⟨s, hs⟩ := hS.nontriv
    have := (hk k).1 s
    rw [← hk', pow_orderOf_eq_one] at this
    exact hs this

@[expose] def presSub (S : Type*) [Group S] [Finite S] : Subgroup (MulAut (S × S)) where
  carrier := {φ | (∀ s, (φ (s, 1)).2 = 1) ∧ ∀ t, (φ (1, t)).1 = 1}
  one_mem' := ⟨fun s => rfl, fun t => rfl⟩
  mul_mem' := by
    rintro φ ψ ⟨h1, h2⟩ ⟨k1, k2⟩
    refine ⟨fun s => ?_, fun t => ?_⟩
    · rw [MulAut.mul_apply, fst_mem_of_preserve k1 s]
      exact h1 _
    · rw [MulAut.mul_apply, snd_mem_of_preserve k2 t]
      exact h2 _
  inv_mem' := by
    rintro φ ⟨h1, h2⟩
    have hinj1 : Function.Injective fun s : S => (φ (s, 1)).1 := by
      intro a b hab
      have : φ (a, 1) = φ (b, 1) := by
        rw [fst_mem_of_preserve h1, fst_mem_of_preserve h1 b]
        simp at hab ⊢
        exact hab
      have := congrArg Prod.fst (φ.injective this)
      exact this
    have hinj2 : Function.Injective fun t : S => (φ (1, t)).2 := by
      intro a b hab
      have : φ (1, a) = φ (1, b) := by
        rw [snd_mem_of_preserve h2, snd_mem_of_preserve h2 b]
        simp at hab ⊢
        exact hab
      have := congrArg Prod.snd (φ.injective this)
      exact this
    have hs1 := Finite.injective_iff_surjective.mp hinj1
    have hs2 := Finite.injective_iff_surjective.mp hinj2
    refine ⟨fun s => ?_, fun t => ?_⟩
    · obtain ⟨s', hs'⟩ := hs1 s
      simp only at hs'
      have : φ (s', 1) = (s, 1) := by rw [fst_mem_of_preserve h1, hs']
      rw [← this]
      show ((φ.symm) (φ (s', 1))).2 = 1
      rw [MulEquiv.symm_apply_apply]
    · obtain ⟨t', ht'⟩ := hs2 t
      simp only at ht'
      have : φ (1, t') = (1, t) := by rw [snd_mem_of_preserve h2, ht']
      rw [← this]
      show ((φ.symm) (φ (1, t'))).1 = 1
      rw [MulEquiv.symm_apply_apply]

section Proj

variable [Finite S]

theorem presSub_fst {φ : MulAut (S × S)} (hφ : φ ∈ presSub S) (s : S) :
    φ (s, 1) = ((φ (s, 1)).1, 1) := fst_mem_of_preserve hφ.1 s

theorem presSub_snd {φ : MulAut (S × S)} (hφ : φ ∈ presSub S) (t : S) :
    φ (1, t) = (1, (φ (1, t)).2) := snd_mem_of_preserve hφ.2 t

theorem bijective_of_injective_hom (f : S →* S) (hf : Function.Injective f) :
    Function.Bijective f := ⟨hf, Finite.injective_iff_surjective.mp hf⟩

@[expose] def fstMap (φ : presSub S) : S →* S :=
  MonoidHom.mk' (fun s => ((φ : MulAut (S × S)) (s, 1)).1) (fun a b => by
    rw [mk_mul_one, map_mul, Prod.fst_mul])

@[expose] def sndMap (φ : presSub S) : S →* S :=
  MonoidHom.mk' (fun t => ((φ : MulAut (S × S)) (1, t)).2) (fun a b => by
    rw [one_mul_mk, map_mul, Prod.snd_mul])

theorem fstMap_injective (φ : presSub S) : Function.Injective (fstMap φ) := by
  intro a b hab
  have h : (φ : MulAut (S × S)) (a, 1) = (φ : MulAut (S × S)) (b, 1) := by
    rw [presSub_fst φ.2, presSub_fst φ.2 b]
    exact congrArg (fun x => (x, (1 : S))) hab
  exact congrArg Prod.fst ((φ : MulAut (S × S)).injective h)

theorem sndMap_injective (φ : presSub S) : Function.Injective (sndMap φ) := by
  intro a b hab
  have h : (φ : MulAut (S × S)) (1, a) = (φ : MulAut (S × S)) (1, b) := by
    rw [presSub_snd φ.2, presSub_snd φ.2 b]
    exact congrArg (fun x => ((1 : S), x)) hab
  exact congrArg Prod.snd ((φ : MulAut (S × S)).injective h)

@[expose] def fstHom : presSub S →* MulAut S where
  toFun φ := MulEquiv.ofBijective (fstMap φ) (bijective_of_injective_hom _ (fstMap_injective φ))
  map_one' := by
    ext s
    rfl
  map_mul' φ ψ := by
    ext s
    change ((φ : MulAut (S × S)) ((ψ : MulAut (S × S)) (s, 1))).1 =
      ((φ : MulAut (S × S)) (((ψ : MulAut (S × S)) (s, 1)).1, 1)).1
    rw [← presSub_fst ψ.2]

@[expose] def sndHom : presSub S →* MulAut S where
  toFun φ := MulEquiv.ofBijective (sndMap φ) (bijective_of_injective_hom _ (sndMap_injective φ))
  map_one' := by
    ext s
    rfl
  map_mul' φ ψ := by
    ext t
    change ((φ : MulAut (S × S)) ((ψ : MulAut (S × S)) (1, t))).2 =
      ((φ : MulAut (S × S)) (1, ((ψ : MulAut (S × S)) (1, t)).2)).2
    rw [← presSub_snd ψ.2]

theorem fstHom_apply (φ : presSub S) (s : S) :
    fstHom φ s = ((φ : MulAut (S × S)) (s, 1)).1 := rfl

theorem sndHom_apply (φ : presSub S) (t : S) :
    sndHom φ t = ((φ : MulAut (S × S)) (1, t)).2 := rfl

theorem presSub_apply (φ : presSub S) (s t : S) :
    (φ : MulAut (S × S)) (s, t) = (fstHom φ s, sndHom φ t) := by
  rw [mk_eq_mul s t, map_mul, presSub_fst φ.2, presSub_snd φ.2]
  simp [fstHom_apply, sndHom_apply]

theorem presSub_ext {φ ψ : presSub S} (h1 : fstHom φ = fstHom ψ) (h2 : sndHom φ = sndHom ψ) :
    φ = ψ := by
  apply Subtype.ext
  ext ⟨s, t⟩ <;> rw [presSub_apply, presSub_apply, h1, h2]

end Proj

end CFSG.ComponentClassification.AutL2Facts
