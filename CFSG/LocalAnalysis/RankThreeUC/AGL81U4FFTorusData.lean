module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Subgroup

structure IsTorusDataIn {G : Type} [Group G] (c : ℕ) (Θ : Subgroup G)
    (Θi : Fin c → Subgroup G) (w θ₀ : G) (π : Equiv.Perm (Fin c)) : Prop where
  odd : Odd (Nat.card Θ)
  comm : ∀ a ∈ Θ, ∀ b ∈ Θ, a * b = b * a
  ne_bot : Θ ≠ ⊥
  Θi_le : ∀ i, Θi i ≤ Θ
  Θi_sup : ∀ i j, i ≠ j → Θi i ⊔ Θi j = Θ
  w_Θ : ∀ θ ∈ Θ, w * θ * w⁻¹ ∈ Θ ∧ w⁻¹ * θ * w ∈ Θ
  w_Θi : ∀ i, (∀ g ∈ Θi i, w * g * w⁻¹ ∈ Θi (π i)) ∧ ∀ g ∈ Θi (π i), w⁻¹ * g * w ∈ Θi i
  π_trans : ∀ i j : Fin c, ∃ k : ℕ, (π ^ k) i = j
  θ₀_mem : θ₀ ∈ Θ

variable {V : Type} [CommGroup V]

@[expose] def pbSub {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (Θ : Subgroup G) : Subgroup (MulAut V) :=
  (Θ.comap e.toMonoidHom).map L.subtype

theorem mem_pbSub {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (Θ : Subgroup G) {g : MulAut V} :
    g ∈ pbSub e Θ ↔ ∃ hg : g ∈ L, e ⟨g, hg⟩ ∈ Θ := by
  unfold pbSub
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨x.2, hx⟩
  · rintro ⟨hgL, hΘ⟩
    exact Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, hΘ, rfl⟩

private theorem mem_pbSub_val {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (Θ : Subgroup G) (y : ↥L) : (y : MulAut V) ∈ pbSub e Θ ↔ e y ∈ Θ := by
  rw [mem_pbSub]
  exact ⟨fun ⟨_, hy⟩ => hy, fun hy => ⟨y.2, hy⟩⟩

theorem pbSub_le {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (Θ : Subgroup G) : pbSub e Θ ≤ L := by
  intro g hg
  exact ((mem_pbSub e Θ).mp hg).1

theorem pbSub_mono {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    {Θ Θ' : Subgroup G} (h : Θ ≤ Θ') : pbSub e Θ ≤ pbSub e Θ' := by
  intro g hg
  obtain ⟨hgL, hΘ⟩ := (mem_pbSub e Θ).mp hg
  exact (mem_pbSub e Θ').mpr ⟨hgL, h hΘ⟩

theorem pbSub_sup {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (Θ Θ' : Subgroup G) : pbSub e (Θ ⊔ Θ') = pbSub e Θ ⊔ pbSub e Θ' := by
  unfold pbSub
  rw [← Subgroup.comap_sup_eq e.toMonoidHom Θ Θ' e.surjective, Subgroup.map_sup]

theorem pbSub_card {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (Θ : Subgroup G) : Nat.card ↥(pbSub e Θ) = Nat.card ↥Θ := by
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  unfold pbSub
  rw [Subgroup.card_subtype, Subgroup.comap_equiv_eq_map_symm',
    Subgroup.card_map_of_injective hinj]

theorem pbSub_ne_bot {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    {Θ : Subgroup G} (h : Θ ≠ ⊥) : pbSub e Θ ≠ ⊥ := by
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  intro hbot
  have hmem : ((e.symm (a : G) : ↥L) : MulAut V) ∈ pbSub e Θ :=
    (mem_pbSub_val e Θ _).mpr (by rw [MulEquiv.apply_symm_apply]; exact a.2)
  rw [hbot, Subgroup.mem_bot] at hmem
  apply ha
  apply Subtype.ext
  have h1 : e.symm (a : G) = 1 := Subtype.ext hmem
  have h2 := e.apply_symm_apply (a : G)
  rw [h1, map_one] at h2
  exact h2.symm

@[expose] def pbElt {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G) (x : G) :
    MulAut V := ((e.symm x : ↥L) : MulAut V)

theorem pbElt_mem {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G) (x : G) :
    pbElt e x ∈ L := (e.symm x).2

theorem pbElt_mem_pbSub {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    {Θ : Subgroup G} {x : G} (hx : x ∈ Θ) : pbElt e x ∈ pbSub e Θ := by
  refine (mem_pbSub_val e Θ (e.symm x)).mpr ?_
  rw [MulEquiv.apply_symm_apply]
  exact hx

private theorem pbElt_conj_eq {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (w : G) {g : MulAut V} (hg : g ∈ L) :
    pbElt e w * g * (pbElt e w)⁻¹ =
      ((e.symm w * (⟨g, hg⟩ : ↥L) * (e.symm w)⁻¹ : ↥L) : MulAut V) := by
  simp [pbElt]

private theorem pbElt_conj_inv_eq {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (w : G) {g : MulAut V} (hg : g ∈ L) :
    (pbElt e w)⁻¹ * g * pbElt e w =
      (((e.symm w)⁻¹ * (⟨g, hg⟩ : ↥L) * e.symm w : ↥L) : MulAut V) := by
  simp [pbElt]

private theorem apply_conj_symm {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (w : G) (y : ↥L) : e (e.symm w * y * (e.symm w)⁻¹) = w * e y * w⁻¹ := by
  simp

private theorem apply_conj_inv_symm {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    (w : G) (y : ↥L) : e ((e.symm w)⁻¹ * y * e.symm w) = w⁻¹ * e y * w := by
  simp

theorem IsTorusDataIn.isTorusData {L : Subgroup (MulAut V)} {G : Type} [Group G] (e : ↥L ≃* G)
    {c : ℕ} {Θ : Subgroup G} {Θi : Fin c → Subgroup G} {w θ₀ : G} {π : Equiv.Perm (Fin c)}
    (h : IsTorusDataIn c Θ Θi w θ₀ π) :
    IsTorusData L c (pbSub e Θ) (fun i => pbSub e (Θi i)) (pbElt e w) (pbElt e θ₀) π := by
  refine ⟨pbSub_le e Θ, ?_, ?_, ?_, ?_, ?_, pbElt_mem e w, ?_, ?_, h.π_trans,
    pbElt_mem_pbSub e h.θ₀_mem⟩
  · rw [pbSub_card]
    exact h.odd
  · intro a ha b hb
    obtain ⟨haL, ha'⟩ := (mem_pbSub e Θ).mp ha
    obtain ⟨hbL, hb'⟩ := (mem_pbSub e Θ).mp hb
    have h2 : (⟨a, haL⟩ : ↥L) * ⟨b, hbL⟩ = ⟨b, hbL⟩ * ⟨a, haL⟩ :=
      e.injective (by rw [map_mul, map_mul]; exact h.comm _ ha' _ hb')
    exact congrArg Subtype.val h2
  · exact pbSub_ne_bot e h.ne_bot
  · intro i
    exact pbSub_mono e (h.Θi_le i)
  · intro i j hij
    rw [← pbSub_sup e (Θi i) (Θi j), h.Θi_sup i j hij]
  · intro g hg
    obtain ⟨hgL, hgΘ⟩ := (mem_pbSub e Θ).mp hg
    obtain ⟨c1, c2⟩ := h.w_Θ _ hgΘ
    refine ⟨?_, ?_⟩
    · rw [pbElt_conj_eq e w hgL, mem_pbSub_val, apply_conj_symm]
      exact c1
    · rw [pbElt_conj_inv_eq e w hgL, mem_pbSub_val, apply_conj_inv_symm]
      exact c2
  · intro i
    obtain ⟨c1, c2⟩ := h.w_Θi i
    refine ⟨?_, ?_⟩
    · intro g hg
      obtain ⟨hgL, hgΘ⟩ := (mem_pbSub e (Θi i)).mp hg
      rw [pbElt_conj_eq e w hgL, mem_pbSub_val, apply_conj_symm]
      exact c1 _ hgΘ
    · intro g hg
      obtain ⟨hgL, hgΘ⟩ := (mem_pbSub e (Θi (π i))).mp hg
      rw [pbElt_conj_inv_eq e w hgL, mem_pbSub_val, apply_conj_inv_symm]
      exact c2 _ hgΘ

end CFSG.LocalAnalysis.RankThreeUC
