module

public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B4ModelsApi

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin

variable {S : Type} [CommGroup S] {D : FFModel} (hD : D.IsActionModel)

include hD

@[expose] def secAut (γ : D.Gam) : ↥D.sec ≃* ↥D.sec where
  toFun := hD.actSec γ
  invFun := hD.actSec γ⁻¹
  left_inv m := Subtype.ext (hD.act_inv_act γ m)
  right_inv m := Subtype.ext (hD.act_act_inv γ m)
  map_mul' := (hD.actSec γ).map_mul

@[expose] def conjAct (β : S ≃* ↥D.sec) (γ : D.Gam) : MulAut S :=
  (β.trans (secAut hD γ)).trans β.symm

theorem conjAct_apply (β : S ≃* ↥D.sec) (γ : D.Gam) (s : S) :
    β (conjAct hD β γ s) = ⟨D.act γ (β s : D.Amb), hD.sec_inv γ _ (β s).2⟩ := by
  show β (β.symm (hD.actSec γ (β s))) = _
  rw [β.apply_symm_apply]
  rfl

@[expose] def conjHom (β : S ≃* ↥D.sec) : D.Gam →* MulAut S where
  toFun := conjAct hD β
  map_one' := by
    apply MulEquiv.ext
    intro s
    apply β.injective
    rw [conjAct_apply]
    exact Subtype.ext (hD.act_one _)
  map_mul' γ δ := by
    apply MulEquiv.ext
    intro s
    apply β.injective
    rw [conjAct_apply, MulAut.mul_apply, conjAct_apply, conjAct_apply]
    exact Subtype.ext (hD.act_mul_act γ δ _)

omit hD in
theorem eq_top_of_card_le {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h : Nat.card G ≤ Nat.card H) : H = ⊤ := by
  apply (Subgroup.card_eq_iff_eq_top H).1
  exact le_antisymm (Subgroup.card_le_card_group H) h

theorem realizesMod_of_equivariant (hker : D.ker = ⊥) (L : Subgroup (MulAut S))
    (π : D.Gam →* ↥L) (hπ : Function.Surjective π) (β : S ≃* ↥D.sec)
    (hβ : ∀ (γ : D.Gam) (s : S), (β (((π γ : ↥L) : MulAut S) s) : D.Amb) = D.act γ (β s)) :
    D.RealizesMod L := by
  refine ⟨π, hπ, le_top, hD.ker_le, fun _ u _ => trivial,
    fun _ z hz => by simpa using hz, hD.sec_inv, hD.ker_inv, ?_⟩
  refine ⟨(QuotientGroup.mk' (D.ker.subgroupOf D.sec)).comp
    (β.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom), ?_, ?_, ?_⟩
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨β.symm m, trivial⟩, by simp⟩
  · intro u
    show (QuotientGroup.mk (β (u : S)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot,
      Subgroup.mem_bot]
    constructor
    · intro h
      have : β (u : S) = 1 := Subtype.ext h
      exact β.injective (by rw [this, map_one])
    · intro h
      rw [h, map_one]
      rfl
  · intro γ u m hu hm hum
    have hu' : (QuotientGroup.mk (β (u : S)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
        QuotientGroup.mk m := hum
    have hbm : β (u : S) = m := by
      have := QuotientGroup.eq.1 hu'
      rw [Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot] at this
      have h2 : ((β (u : S))⁻¹ * m : ↥D.sec) = 1 := Subtype.ext this
      exact inv_mul_eq_one.1 h2
    show (QuotientGroup.mk (β (((π γ : ↥L) : MulAut S) (u : S))) :
      ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩
    congr 1
    apply Subtype.ext
    rw [hβ γ (u : S), hbm]

theorem realizesMod_of_two_generators [Finite D.Gam] (hker : D.ker = ⊥) (hfaith : D.Faithful)
    (L : Subgroup (MulAut S)) (hcard : Nat.card D.Gam ≤ Nat.card ↥L)
    (β : S ≃* ↥D.sec) (x y : MulAut S) (g₁ g₂ : D.Gam)
    (hx : ∀ s, (β (x s) : D.Amb) = D.act g₁ (β s)) (hy : ∀ s, (β (y s) : D.Amb) = D.act g₂ (β s))
    (hL : L = Subgroup.closure ({x, y} : Set (MulAut S))) : D.RealizesMod L := by
  set π₀ : D.Gam →* MulAut S := conjHom hD β with hπ₀
  have hπx : π₀ g₁ = x := by
    apply MulEquiv.ext
    intro s
    apply β.injective
    show β (conjAct hD β g₁ s) = β (x s)
    rw [conjAct_apply]
    exact Subtype.ext (hx s).symm
  have hπy : π₀ g₂ = y := by
    apply MulEquiv.ext
    intro s
    apply β.injective
    show β (conjAct hD β g₂ s) = β (y s)
    rw [conjAct_apply]
    exact Subtype.ext (hy s).symm
  have hinj : Function.Injective π₀ := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply hfaith
    intro m hm
    have h1 : conjAct hD β γ (β.symm ⟨m, hm⟩) = β.symm ⟨m, hm⟩ := by
      have := congrArg (fun f : MulAut S => f (β.symm ⟨m, hm⟩)) hγ
      exact this
    have h2 := conjAct_apply hD β γ (β.symm ⟨m, hm⟩)
    rw [h1, β.apply_symm_apply] at h2
    have h3 : D.act γ m = m := (congrArg Subtype.val h2).symm
    rw [h3, mul_inv_cancel]
    exact (Subgroup.one_mem _)
  set H : Subgroup D.Gam := Subgroup.closure ({g₁, g₂} : Set D.Gam) with hH
  have hmap : H.map π₀ = L := by
    rw [hH, MonoidHom.map_closure, hL, Set.image_pair, hπx, hπy]
  have hHtop : H = ⊤ := by
    apply eq_top_of_card_le
    rw [← Subgroup.card_map_of_injective hinj (K := H), hmap]
    exact hcard
  have hrange : π₀.range = L := by
    rw [MonoidHom.range_eq_map, ← hHtop, hmap]
  have hmem : ∀ γ, π₀ γ ∈ L := fun γ => by rw [← hrange]; exact ⟨γ, rfl⟩
  have hπsurj : Function.Surjective (π₀.codRestrict L hmem) := by
    intro l
    have hl : (l : MulAut S) ∈ π₀.range := by rw [hrange]; exact l.2
    obtain ⟨γ, hγ⟩ := hl
    exact ⟨γ, Subtype.ext hγ⟩
  refine realizesMod_of_equivariant hD hker L (π₀.codRestrict L hmem) hπsurj β ?_
  intro γ s
  have := conjAct_apply hD β γ s
  exact congrArg Subtype.val this

end CFSG.QuasithinUnique.B42A57
