module

public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup

section Range

variable {Q M : Type*} [Group Q] [Group M]

theorem exists_mulEquiv_comp_eq_of_range_eq {f g : Q →* M}
    (hf : Function.Injective f) (hg : Function.Injective g) (h : f.range = g.range) :
    ∃ α : Q ≃* Q, ∀ a, f (α a) = g a := by
  refine ⟨(MonoidHom.ofInjective hg).trans
    ((MulEquiv.subgroupCongr h.symm).trans (MonoidHom.ofInjective hf).symm), fun a => ?_⟩
  simp only [MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

theorem eq_of_range_eq_of_rigid {f g : Q →* M}
    (hf : Function.Injective f) (hg : Function.Injective g) (h : f.range = g.range)
    {S : Set Q} (hS : ∀ s ∈ S, f s = g s)
    (hrigid : ∀ β : Q ≃* Q, (∀ s ∈ S, β s = s) → β = MulEquiv.refl Q) : f = g := by
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq_of_range_eq hf hg h
  have hfix : ∀ s ∈ S, α s = s := fun s hs => hf (by rw [hα, hS s hs])
  have hαid : α = MulEquiv.refl Q := hrigid α hfix
  ext a
  calc f a = f (α a) := by simp [hαid]
    _ = g a := hα a

end Range

section Centralizer

variable {M : Type*} [Group M]

theorem map_conj_centralizer_inf_centralizer (n a b : M) :
    (centralizer ({a} : Set M) ⊓ centralizer ({b} : Set M)).map (MulAut.conj n).toMonoidHom =
      centralizer ({n * a * n⁻¹} : Set M) ⊓ centralizer ({n * b * n⁻¹} : Set M) := by
  ext y
  obtain ⟨z, rfl⟩ := (MulAut.conj n).surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  exact and_congr (Commute.conj_iff n).symm (Commute.conj_iff n).symm

theorem centralizer_inf_centralizer_mul (a b : M) :
    centralizer ({a} : Set M) ⊓ centralizer ({a * b} : Set M) =
      centralizer ({a} : Set M) ⊓ centralizer ({b} : Set M) := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun (ha : Commute y a) =>
    ⟨fun (hab : Commute y (a * b)) => ?_, ha.mul_right⟩
  have hb : Commute y b := by simpa using ha.inv_right.mul_right hab
  exact hb

theorem map_conj_centralizer_inf_centralizer_of_swap {n t t' : M}
    (h₁ : n * t * n⁻¹ = t * t') (h₂ : n * t' * n⁻¹ = t) :
    (centralizer ({t} : Set M) ⊓ centralizer ({t'} : Set M)).map (MulAut.conj n).toMonoidHom =
      centralizer ({t} : Set M) ⊓ centralizer ({t'} : Set M) := by
  rw [map_conj_centralizer_inf_centralizer, h₁, h₂]
  exact (inf_comm _ _).trans (centralizer_inf_centralizer_mul t t')

end Centralizer

section ConjPullback

variable {G G₀ : Type*} [Group G] [Group G₀] {K₀ K : Subgroup G₀}

@[expose] def conjPullback (f : ↥K₀ →* G) (a : G₀) (n : G)
    (hK : ∀ x, a⁻¹ * x * a ∈ K₀ ↔ x ∈ K) : ↥K →* G :=
  (MulAut.conj n).toMonoidHom.comp (f.comp
    (((MulAut.conj a).symm.toMonoidHom.comp K.subtype).codRestrict K₀ fun x => (hK x).2 x.2))

@[simp]
theorem conjPullback_apply (f : ↥K₀ →* G) (a : G₀) (n : G)
    (hK : ∀ x, a⁻¹ * x * a ∈ K₀ ↔ x ∈ K) (x : ↥K) :
    conjPullback f a n hK x = n * f ⟨a⁻¹ * x * a, (hK x).2 x.2⟩ * n⁻¹ :=
  rfl

theorem conjPullback_injective {f : ↥K₀ →* G} (hf : Function.Injective f) (a : G₀) (n : G)
    (hK : ∀ x, a⁻¹ * x * a ∈ K₀ ↔ x ∈ K) : Function.Injective (conjPullback f a n hK) := by
  intro x y h
  simp only [conjPullback_apply, mul_left_inj, mul_right_inj] at h
  simpa using congrArg Subtype.val (hf h)

theorem range_conjPullback_comp_inclusion (f : ↥K₀ →* G) (a : G₀) (n : G)
    (hK : ∀ x, a⁻¹ * x * a ∈ K₀ ↔ x ∈ K) {Q : Subgroup G₀} (hQK : Q ≤ K) (hQK₀ : Q ≤ K₀)
    (hQ : ∀ x, a⁻¹ * x * a ∈ Q ↔ x ∈ Q) :
    ((conjPullback f a n hK).comp (Subgroup.inclusion hQK)).range =
      ((f.comp (Subgroup.inclusion hQK₀)).range).map (MulAut.conj n).toMonoidHom := by
  ext y
  simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply, conjPullback_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨⟨a⁻¹ * x * a, (hQ x).2 x.2⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    have hq : a⁻¹ * (a * (q : G₀) * a⁻¹) * a = q := by group
    exact ⟨⟨a * q * a⁻¹, (hQ _).1 (by rw [hq]; exact q.2)⟩,
      congrArg (fun z => n * f z * n⁻¹) (Subtype.ext hq)⟩

end ConjPullback

section RangeCentralizer

variable {X Y : Type*} [Group X] [Group Y] {K : Subgroup X} {K₀ : Subgroup Y}

theorem mem_centralizer_singleton_symm_iff (ψ : ↥K ≃* ↥K₀) {s : Y} (hs : s ∈ K₀) (x : ↥K₀) :
    (x : Y) ∈ centralizer ({s} : Set Y) ↔
      ((ψ.symm x : ↥K) : X) ∈ centralizer ({((ψ.symm ⟨s, hs⟩ : ↥K) : X)} : Set X) := by
  have := commute_map_iff ψ.symm.injective (x := x) (y := ⟨s, hs⟩)
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Subtype.val (this.2 (Subtype.ext h)), fun h => by
    simpa using congrArg Subtype.val (this.1 (Subtype.ext h))⟩

theorem range_comp_inclusion_inf_centralizer (ψ : ↥K ≃* ↥K₀) {s : Y} (hs : s ∈ K₀) :
    ((K.subtype.comp ψ.symm.toMonoidHom).comp
        (Subgroup.inclusion (inf_le_left : K₀ ⊓ centralizer ({s} : Set Y) ≤ K₀))).range =
      K ⊓ centralizer ({((ψ.symm ⟨s, hs⟩ : ↥K) : X)} : Set X) := by
  ext y
  constructor
  · rintro ⟨⟨x, hxK₀, hxC⟩, rfl⟩
    exact ⟨(ψ.symm ⟨x, hxK₀⟩).2, (mem_centralizer_singleton_symm_iff ψ hs ⟨x, hxK₀⟩).1 hxC⟩
  · rintro ⟨hyK, hyC⟩
    refine ⟨⟨ψ ⟨y, hyK⟩, (ψ ⟨y, hyK⟩).2,
      (mem_centralizer_singleton_symm_iff ψ hs _).2 ?_⟩, ?_⟩
    · simpa using hyC
    · exact congrArg Subtype.val (ψ.symm_apply_apply ⟨y, hyK⟩)

end RangeCentralizer

theorem exists_hom_agree_of_conj {G G₀ : Type*} [Group G] [Group G₀]
    {N : Subgroup G} {t : G} {ZN ZH ZH'' Q D : Subgroup G₀} {g₀ t₀ t₁ : G₀}
    (ψN : ↥N ≃* ↥ZN) (ψH : ↥(centralizer ({t} : Set G)) ≃* ↥ZH)
    (hagree : ∀ (x : G₀) (hN : x ∈ ZN) (hH : x ∈ ZH),
      ((ψN.symm ⟨x, hN⟩ : ↥N) : G) =
        ((ψH.symm ⟨x, hH⟩ : ↥(centralizer ({t} : Set G))) : G))
    (htN : t ∈ N) (hψt : ((ψN ⟨t, htN⟩ : ↥ZN) : G₀) = t₀)
    (hg₀ : g₀ ∈ ZN) (ht₁N : t₁ ∈ ZN) (ht₁H : t₁ ∈ ZH)
    (hconj₀ : g₀ * t₀ * g₀⁻¹ = t₀ * t₁) (hconj₁ : g₀ * t₁ * g₀⁻¹ = t₀)
    (hZH'' : ∀ x, g₀⁻¹ * x * g₀ ∈ ZH ↔ x ∈ ZH'')
    (hQ : ∀ x, g₀⁻¹ * x * g₀ ∈ Q ↔ x ∈ Q)
    (hHH'' : ZH ⊓ ZH'' = Q) (hcent : ZH ⊓ centralizer ({t₁} : Set G₀) = Q)
    (hDN : D ≤ ZN)
    (hrigid : ∀ β : ↥Q ≃* ↥Q, (∀ d : ↥Q, (d : G₀) ∈ D → β d = d) → β = MulEquiv.refl _) :
    ∃ φ : ↥ZH'' →* G,
      (∀ (x : G₀) (hN : x ∈ ZN) (h'' : x ∈ ZH''),
        ((ψN.symm ⟨x, hN⟩ : ↥N) : G) = φ ⟨x, h''⟩) ∧
      ∀ (x : G₀) (hH : x ∈ ZH) (h'' : x ∈ ZH''),
        ((ψH.symm ⟨x, hH⟩ : ↥(centralizer ({t} : Set G))) : G) = φ ⟨x, h''⟩ := by
  subst hψt
  subst hcent
  have e₀ := congrArg (fun z : ↥ZN => ((ψN.symm z : ↥N) : G))
    (Subtype.ext hconj₀ : (⟨g₀, hg₀⟩ : ↥ZN) * ψN ⟨t, htN⟩ * (⟨g₀, hg₀⟩ : ↥ZN)⁻¹ =
      ψN ⟨t, htN⟩ * ⟨t₁, ht₁N⟩)
  have e₁ := congrArg (fun z : ↥ZN => ((ψN.symm z : ↥N) : G))
    (Subtype.ext hconj₁ : (⟨g₀, hg₀⟩ : ↥ZN) * ⟨t₁, ht₁N⟩ * (⟨g₀, hg₀⟩ : ↥ZN)⁻¹ =
      ψN ⟨t, htN⟩)
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    MulEquiv.symm_apply_apply] at e₀ e₁
  rw [hagree t₁ ht₁N ht₁H] at e₀ e₁
  set n : G := ((ψN.symm ⟨g₀, hg₀⟩ : ↥N) : G) with hn
  set t' : G := ((ψH.symm ⟨t₁, ht₁H⟩ : ↥(centralizer ({t} : Set G))) : G)
  set f : ↥ZH →* G := (centralizer ({t} : Set G)).subtype.comp ψH.symm.toMonoidHom
  have hfapp : ∀ y, f y = ((ψH.symm y : ↥(centralizer ({t} : Set G))) : G) := fun y => rfl
  have hfinj : Function.Injective f := Subtype.val_injective.comp ψH.symm.injective
  set φ : ↥ZH'' →* G := conjPullback f g₀ n hZH'' with hφ
  have hφN : ∀ (x : G₀) (hN : x ∈ ZN) (h'' : x ∈ ZH''),
      ((ψN.symm ⟨x, hN⟩ : ↥N) : G) = φ ⟨x, h''⟩ := by
    intro x hN h''
    have h1 : g₀⁻¹ * x * g₀ ∈ ZN := ZN.mul_mem (ZN.mul_mem (ZN.inv_mem hg₀) hN) hg₀
    have h2 : g₀⁻¹ * x * g₀ ∈ ZH := (hZH'' x).2 h''
    rw [hφ, conjPullback_apply, hfapp, ← hagree _ h1 h2]
    have h3 : (⟨g₀⁻¹ * x * g₀, h1⟩ : ↥ZN) = (⟨g₀, hg₀⟩ : ↥ZN)⁻¹ * ⟨x, hN⟩ * ⟨g₀, hg₀⟩ := rfl
    rw [h3]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hn]
    group
  have hQ₁ : ZH ⊓ centralizer ({t₁} : Set G₀) ≤ ZH := inf_le_left
  have hQ₂ : ZH ⊓ centralizer ({t₁} : Set G₀) ≤ ZH'' := by
    rw [← hHH'']; exact inf_le_right
  have hr₁ : (f.comp (Subgroup.inclusion hQ₁)).range = centralizer {t} ⊓ centralizer {t'} :=
    range_comp_inclusion_inf_centralizer ψH ht₁H
  have hr₂ : (φ.comp (Subgroup.inclusion hQ₂)).range = centralizer {t} ⊓ centralizer {t'} := by
    rw [hφ, range_conjPullback_comp_inclusion f g₀ n hZH'' hQ₂ hQ₁ hQ, hr₁,
      map_conj_centralizer_inf_centralizer_of_swap e₀ e₁]
  have hfi : Function.Injective (f.comp (Subgroup.inclusion hQ₁)) :=
    hfinj.comp (Subgroup.inclusion_injective _)
  have hφi : Function.Injective (φ.comp (Subgroup.inclusion hQ₂)) :=
    (conjPullback_injective hfinj g₀ n hZH'').comp (Subgroup.inclusion_injective _)
  have heq : f.comp (Subgroup.inclusion hQ₁) = φ.comp (Subgroup.inclusion hQ₂) := by
    refine eq_of_range_eq_of_rigid hfi hφi (hr₁.trans hr₂.symm)
      (S := {d | (d : G₀) ∈ D}) ?_ hrigid
    intro d hd
    have hdN : (d : G₀) ∈ ZN := hDN hd
    have hdH : (d : G₀) ∈ ZH := d.2.1
    have hdH'' : (d : G₀) ∈ ZH'' := hQ₂ d.2
    show f ⟨d, hdH⟩ = φ ⟨d, hdH''⟩
    rw [hfapp, ← hagree _ hdN hdH]
    exact hφN _ hdN hdH''
  refine ⟨φ, hφN, fun x hH h'' => ?_⟩
  have hxQ : x ∈ ZH ⊓ centralizer ({t₁} : Set G₀) := by
    rw [← hHH'']; exact ⟨hH, h''⟩
  exact DFunLike.congr_fun heq ⟨x, hxQ⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
