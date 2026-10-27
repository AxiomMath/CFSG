module

public import CFSG.ClassicalInvolution.Generic.Frame
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Generic CFSG.Open

section Corr

variable {Y Z X : Type*} [Group Y] [Group Z] [Group X]

@[expose] def Corr {V : Subgroup Y} {W : Subgroup Z} (ψ : ↥V ≃* ↥W) (J : Subgroup Y) (J' : Subgroup Z) :
    Prop :=
  ∀ g : ↥V, (g : Y) ∈ J ↔ ((ψ g : ↥W) : Z) ∈ J'

@[expose] def Carries {V : Subgroup Y} {W : Subgroup Z} (ψ : ↥V ≃* ↥W) (P : Set (Subgroup Y))
    (P' : Set (Subgroup Z)) : Prop :=
  (∀ J ∈ P, ∃ J' ∈ P', Corr ψ J J') ∧ ∀ J' ∈ P', ∃ J ∈ P, Corr ψ J J'

variable {V : Subgroup Y} {W : Subgroup Z} {U : Subgroup X}

theorem Corr.symm {ψ : ↥V ≃* ↥W} {J : Subgroup Y} {J' : Subgroup Z} (h : Corr ψ J J') :
    Corr ψ.symm J' J := by
  intro g
  have := h (ψ.symm g)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem Corr.trans {ψ : ↥V ≃* ↥W} {ψ₂ : ↥W ≃* ↥U} {J : Subgroup Y} {J' : Subgroup Z} {J'' : Subgroup X}
    (h : Corr ψ J J') (h₂ : Corr ψ₂ J' J'') : Corr (ψ.trans ψ₂) J J'' := by
  intro g
  exact (h g).trans (h₂ (ψ g))

theorem Corr.conj {ψ : ↥V ≃* ↥W} {J : Subgroup Y} {J' : Subgroup Z} (h : Corr ψ J J') (e : ↥V) :
    Corr ψ (conjSub (e : Y) J) (conjSub ((ψ e : ↥W) : Z) J') := by
  intro g
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have := h (e⁻¹ * g * e)
  simpa [map_mul, map_inv] using this

theorem Corr.unique {ψ : ↥V ≃* ↥W} {J : Subgroup Y} {J₁ J₂ : Subgroup Z} (h₁ : Corr ψ J J₁)
    (h₂ : Corr ψ J J₂) (hJ₁ : J₁ ≤ W) (hJ₂ : J₂ ≤ W) : J₁ = J₂ := by
  have key : ∀ {A B : Subgroup Z}, Corr ψ J A → Corr ψ J B → A ≤ W → A ≤ B := by
    intro A B hA hB hAW z hz
    obtain ⟨g, hg⟩ := ψ.surjective ⟨z, hAW hz⟩
    have hz' : z = ((ψ g : ↥W) : Z) := by rw [hg]
    rw [hz'] at hz ⊢
    exact (hB g).1 ((hA g).2 hz)
  exact le_antisymm (key h₁ h₂ hJ₁) (key h₂ h₁ hJ₂)

theorem Carries.symm {ψ : ↥V ≃* ↥W} {P : Set (Subgroup Y)} {P' : Set (Subgroup Z)}
    (h : Carries ψ P P') : Carries ψ.symm P' P :=
  ⟨fun J' hJ' => by
    obtain ⟨J, hJ, hc⟩ := h.2 J' hJ'
    exact ⟨J, hJ, hc.symm⟩,
   fun J hJ => by
    obtain ⟨J', hJ', hc⟩ := h.1 J hJ
    exact ⟨J', hJ', hc.symm⟩⟩

theorem Carries.trans {ψ : ↥V ≃* ↥W} {ψ₂ : ↥W ≃* ↥U} {P : Set (Subgroup Y)} {P' : Set (Subgroup Z)}
    {P'' : Set (Subgroup X)} (h : Carries ψ P P') (h₂ : Carries ψ₂ P' P'') :
    Carries (ψ.trans ψ₂) P P'' :=
  ⟨fun J hJ => by
    obtain ⟨J', hJ', hc⟩ := h.1 J hJ
    obtain ⟨J'', hJ'', hc₂⟩ := h₂.1 J' hJ'
    exact ⟨J'', hJ'', hc.trans hc₂⟩,
   fun J'' hJ'' => by
    obtain ⟨J', hJ', hc₂⟩ := h₂.2 J'' hJ''
    obtain ⟨J, hJ, hc⟩ := h.2 J' hJ'
    exact ⟨J, hJ, hc.trans hc₂⟩⟩

end Corr

section Restr

variable {Y Z : Type*} [Group Y] [Group Z]

@[expose] def restr {V : Subgroup Y} {W : Subgroup Z} (ψ : ↥V ≃* ↥W) {X : Subgroup Y} {X' : Subgroup Z}
    (hX : X ≤ V) (hX' : X' ≤ W) (h : ∀ g : ↥V, (g : Y) ∈ X ↔ ((ψ g : ↥W) : Z) ∈ X') : ↥X ≃* ↥X' where
  toFun x := ⟨((ψ ⟨x, hX x.2⟩ : ↥W) : Z), (h _).1 x.2⟩
  invFun x := ⟨((ψ.symm ⟨x, hX' x.2⟩ : ↥V) : Y),
    (h _).2 (by rw [MulEquiv.apply_symm_apply]; exact x.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    show ((ψ (⟨x, hX x.2⟩ * ⟨y, hX y.2⟩) : ↥W) : Z) = ((ψ ⟨x, hX x.2⟩ : ↥W) : Z) * ((ψ ⟨y, hX y.2⟩ : ↥W) : Z)
    rw [map_mul]
    rfl

@[expose] def edgeAut {V₁ V₂ : Subgroup Y} {W₁ W₂ : Subgroup Z} (ψ₁ : ↥V₁ ≃* ↥W₁) (ψ₂ : ↥V₂ ≃* ↥W₂)
    (h₁ : ∀ g : ↥V₁, (g : Y) ∈ V₂ ↔ ((ψ₁ g : ↥W₁) : Z) ∈ W₂)
    (h₂ : ∀ g : ↥V₂, (g : Y) ∈ V₁ ↔ ((ψ₂ g : ↥W₂) : Z) ∈ W₁) : MulAut ↥(W₁ ⊓ W₂) :=
  (restr ψ₁ (X := V₁ ⊓ V₂) (X' := W₁ ⊓ W₂) inf_le_left inf_le_left (fun g =>
      ⟨fun hg => ⟨(ψ₁ g).2, (h₁ g).1 hg.2⟩, fun hg => ⟨g.2, (h₁ g).2 hg.2⟩⟩)).symm.trans
    (restr ψ₂ (X := V₁ ⊓ V₂) (X' := W₁ ⊓ W₂) inf_le_right inf_le_right (fun g =>
      ⟨fun hg => ⟨(h₂ g).1 hg.1, (ψ₂ g).2⟩, fun hg => ⟨(h₂ g).2 hg.1, g.2⟩⟩))

theorem edgeAut_val {V₁ V₂ : Subgroup Y} {W₁ W₂ : Subgroup Z} (ψ₁ : ↥V₁ ≃* ↥W₁) (ψ₂ : ↥V₂ ≃* ↥W₂)
    (h₁ : ∀ g : ↥V₁, (g : Y) ∈ V₂ ↔ ((ψ₁ g : ↥W₁) : Z) ∈ W₂)
    (h₂ : ∀ g : ↥V₂, (g : Y) ∈ V₁ ↔ ((ψ₂ g : ↥W₂) : Z) ∈ W₁) (x : ↥V₁) (hx : (x : Y) ∈ V₂)
    (g : ↥(W₁ ⊓ W₂)) (hg : (g : Z) = ((ψ₁ x : ↥W₁) : Z)) :
    ((edgeAut ψ₁ ψ₂ h₁ h₂ g : ↥(W₁ ⊓ W₂)) : Z) = ((ψ₂ ⟨x, hx⟩ : ↥W₂) : Z) := by
  unfold edgeAut
  rw [MulEquiv.trans_apply]
  have : (restr ψ₁ (X := V₁ ⊓ V₂) (X' := W₁ ⊓ W₂) inf_le_left inf_le_left (fun g =>
      ⟨fun hg => ⟨(ψ₁ g).2, (h₁ g).1 hg.2⟩, fun hg => ⟨g.2, (h₁ g).2 hg.2⟩⟩)).symm g =
      ⟨x, ⟨x.2, hx⟩⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hg
  rw [this]
  rfl

end Restr

section Tr

variable {Y Z : Type*} [Group Y] [Group Z] {V : Subgroup Y} {W : Subgroup Z}

@[expose] def tr (ψ : ↥V ≃* ↥W) (X : Subgroup Y) : Subgroup Z :=
  ((X.subgroupOf V).map ψ.toMonoidHom).map W.subtype

theorem mem_tr (ψ : ↥V ≃* ↥W) {X : Subgroup Y} {z : Z} :
    z ∈ tr ψ X ↔ ∃ g : ↥V, (g : Y) ∈ X ∧ ((ψ g : ↥W) : Z) = z := by
  unfold tr
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, rfl⟩

theorem mem_tr_apply (ψ : ↥V ≃* ↥W) {X : Subgroup Y} (g : ↥V) :
    ((ψ g : ↥W) : Z) ∈ tr ψ X ↔ (g : Y) ∈ X := by
  rw [mem_tr]
  constructor
  · rintro ⟨g', hg', he⟩
    have : g' = g := ψ.injective (Subtype.ext he)
    subst this
    exact hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

theorem tr_le (ψ : ↥V ≃* ↥W) (X : Subgroup Y) : tr ψ X ≤ W := by
  intro z hz
  obtain ⟨g, -, rfl⟩ := (mem_tr ψ).1 hz
  exact (ψ g).2

theorem tr_inf (ψ : ↥V ≃* ↥W) (X X' : Subgroup Y) : tr ψ X ⊓ tr ψ X' = tr ψ (X ⊓ X') := by
  ext z
  rw [Subgroup.mem_inf, mem_tr, mem_tr, mem_tr]
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, ⟨g', hg', he⟩⟩
    have : g' = g := ψ.injective (Subtype.ext he)
    subst this
    exact ⟨g', ⟨hg, hg'⟩, rfl⟩
  · rintro ⟨g, ⟨hg, hg'⟩, rfl⟩
    exact ⟨⟨g, hg, rfl⟩, ⟨g, hg', rfl⟩⟩

theorem card_tr (ψ : ↥V ≃* ↥W) {X : Subgroup Y} (hX : X ≤ V) : Nat.card (tr ψ X) = Nat.card X := by
  unfold tr
  rw [Subgroup.card_map_of_injective W.subtype_injective, Subgroup.card_map_of_injective ψ.injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem mem_pCoreOf_iff (ψ : ↥V ≃* ↥W) (p : ℕ) (a : ↥V) :
    (a : Y) ∈ pCoreOf p V ↔ ((ψ a : ↥W) : Z) ∈ pCoreOf p W := by
  rw [pCoreOf, pCoreOf]
  change V.subtype a ∈ _ ↔ W.subtype (ψ a) ∈ _
  rw [Subgroup.mem_map_iff_mem V.subtype_injective, Subgroup.mem_map_iff_mem W.subtype_injective,
    ← CFSG.LieType.BorelTits.map_pCore_mulEquiv p ψ]
  exact (Subgroup.mem_map_iff_mem (f := ψ.toMonoidHom) ψ.injective).symm

theorem pCoreOf_le_tr (ψ : ↥V ≃* ↥W) {X : Subgroup Y} (h : pCoreOf 2 V ≤ X) : pCoreOf 2 W ≤ tr ψ X := by
  intro z hz
  obtain ⟨g, hg⟩ := ψ.surjective ⟨z, CFSG.LieType.BorelTits.pCoreOf_le 2 W hz⟩
  have hz' : z = ((ψ g : ↥W) : Z) := by rw [hg]
  rw [hz'] at hz ⊢
  rw [mem_tr_apply]
  exact h ((mem_pCoreOf_iff ψ 2 g).2 hz)

end Tr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2
