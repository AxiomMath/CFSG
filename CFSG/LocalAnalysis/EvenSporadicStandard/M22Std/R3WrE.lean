module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrAlg

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

structure WrSit (X : Type) [Group X] [Finite X] (zb : X) (f : X →* Wr) (E : Subgroup X) :
    Prop where
  inj : Function.Injective f
  zb2 : zb * zb = 1
  E_norm : E.Normal
  E_iso : Nonempty (E ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6))
  C_card : Nat.card (centralizer ({zb} : Set X)) = 1440

theorem alt6_prod_hom_trivial (ψ : alternatingGroup (Fin 6) × alternatingGroup (Fin 6) →* ℤˣ)
    (p : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) : ψ p = 1 := by
  have h5 : 5 ≤ Nat.card (Fin 6) := by simp
  have key : ∀ φ : alternatingGroup (Fin 6) →* ℤˣ, ∀ a, φ a = 1 := fun φ a => by
    have := Abelianization.commutator_subset_ker φ
    rw [commutator_alternatingGroup_eq_top h5] at this
    exact MonoidHom.mem_ker.1 (this (Subgroup.mem_top a))
  have h1 := key (ψ.comp (MonoidHom.inl _ _)) p.1
  have h2 := key (ψ.comp (MonoidHom.inr _ _)) p.2
  have : p = (p.1, 1) * (1, p.2) := by simp
  rw [this, map_mul]
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] at h1 h2
  rw [h1, h2, mul_one]

variable {X : Type} [Group X] [Finite X] {zb : X} {f : X →* Wr} {E : Subgroup X}

namespace WrSit

theorem E_hom_trivial (h : WrSit X zb f E) (ψ : E →* ℤˣ) (g : E) : ψ g = 1 := by
  obtain ⟨e⟩ := h.E_iso
  have := alt6_prod_hom_trivial (ψ.comp e.symm.toMonoidHom) (e g)
  simpa using this

theorem E_flag (h : WrSit X zb f E) {g : X} (hg : g ∈ E) : (f g).e = false := by
  have := h.E_hom_trivial (Wr.flag.comp (f.comp E.subtype)) ⟨g, hg⟩
  exact (Wr.flag_eq_one_iff _).1 this

@[expose] noncomputable def signA (h : WrSit X zb f E) : E →* ℤˣ where
  toFun g := Equiv.Perm.sign (f g).a
  map_one' := by simp [map_one]
  map_mul' g g' := by
    have := h.E_flag g.2
    simp only [map_mul, Wr.mul_def, this, Bool.false_eq_true, ↓reduceIte, Subgroup.coe_mul]

@[expose] noncomputable def signB (h : WrSit X zb f E) : E →* ℤˣ where
  toFun g := Equiv.Perm.sign (f g).b
  map_one' := by simp [map_one]
  map_mul' g g' := by
    have := h.E_flag g.2
    simp only [map_mul, Wr.mul_def, this, Bool.false_eq_true, ↓reduceIte, Subgroup.coe_mul]

theorem E_sign (h : WrSit X zb f E) {g : X} (hg : g ∈ E) :
    Equiv.Perm.sign (f g).a = 1 ∧ Equiv.Perm.sign (f g).b = 1 :=
  ⟨h.E_hom_trivial h.signA ⟨g, hg⟩, h.E_hom_trivial h.signB ⟨g, hg⟩⟩

@[expose] noncomputable def theta (h : WrSit X zb f E) :
    E →* alternatingGroup (Fin 6) × alternatingGroup (Fin 6) where
  toFun g := (⟨(f g).a, Equiv.Perm.mem_alternatingGroup.2 (h.E_sign g.2).1⟩,
    ⟨(f g).b, Equiv.Perm.mem_alternatingGroup.2 (h.E_sign g.2).2⟩)
  map_one' := by
    ext <;> simp [map_one]
  map_mul' g g' := by
    have := h.E_flag g.2
    ext <;> simp [map_mul, Wr.mul_def, this]

theorem theta_injective (h : WrSit X zb f E) : Function.Injective h.theta := by
  intro g g' hgg
  have h1 : (f g).a = (f g').a := congrArg (fun p => (p.1 : Equiv.Perm (Fin 6))) hgg
  have h2 : (f g).b = (f g').b := congrArg (fun p => (p.2 : Equiv.Perm (Fin 6))) hgg
  have h3 : f g = f g' := by
    rcases hfg : f g with ⟨a, b, e⟩
    rcases hfg' : f g' with ⟨a', b', e'⟩
    rw [hfg, hfg'] at h1 h2
    have he := h.E_flag g.2
    have he' := h.E_flag g'.2
    rw [hfg] at he
    rw [hfg'] at he'
    simp only at h1 h2 he he'
    subst h1 h2 he he'
    rfl
  exact Subtype.ext (h.inj h3)

theorem theta_bijective (h : WrSit X zb f E) : Function.Bijective h.theta := by
  obtain ⟨e⟩ := h.E_iso
  refine h.theta_injective.bijective_of_nat_card_le ?_
  rw [Nat.card_congr e.toEquiv]

theorem E_surj (h : WrSit X zb f E) {c d : Equiv.Perm (Fin 6)} (hc : Equiv.Perm.sign c = 1)
    (hd : Equiv.Perm.sign d = 1) : ∃ g ∈ E, f g = ⟨c, d, false⟩ := by
  obtain ⟨g, hg⟩ := h.theta_bijective.2
    (⟨c, Equiv.Perm.mem_alternatingGroup.2 hc⟩, ⟨d, Equiv.Perm.mem_alternatingGroup.2 hd⟩)
  have h1 : (f g).a = c := congrArg (fun p => (p.1 : Equiv.Perm (Fin 6))) hg
  have h2 : (f g).b = d := congrArg (fun p => (p.2 : Equiv.Perm (Fin 6))) hg
  refine ⟨g, g.2, ?_⟩
  have he := h.E_flag g.2
  rcases hfg : f g with ⟨a, b, e⟩
  rw [hfg] at h1 h2 he
  simp only at h1 h2 he
  subst h1 h2 he
  rfl

theorem mem_E_iff (h : WrSit X zb f E) (g : X) :
    g ∈ E ↔ (f g).e = false ∧ Equiv.Perm.sign (f g).a = 1 ∧ Equiv.Perm.sign (f g).b = 1 := by
  constructor
  · intro hg
    exact ⟨h.E_flag hg, (h.E_sign hg).1, (h.E_sign hg).2⟩
  · rintro ⟨he, ha, hb⟩
    obtain ⟨g', hg', hfg'⟩ := h.E_surj ha hb
    have : f g = f g' := by
      rw [hfg']
      rcases hfg : f g with ⟨a, b, e⟩
      rw [hfg] at he
      simp only at he
      subst he
      rfl
    rw [h.inj this]
    exact hg'

end WrSit

end CFSG.EvenSporadicStandard.M22Std
