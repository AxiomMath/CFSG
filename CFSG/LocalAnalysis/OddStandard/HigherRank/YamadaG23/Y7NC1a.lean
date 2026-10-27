module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NFa

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t g g0 : G} {P U S F M U0 P0 : Subgroup G}

private lemma mem_zpowers_eq_one_or_self {a x : G} (ha : a ^ 2 = 1) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ha2 : a ^ (2 : ℤ) = 1 := by simpa using ha
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ha2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ha2, one_zpow, one_mul, zpow_one]

private lemma isElemAbelian_map_iff {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] {f : Γ₁ →* Γ₂}
    (hf : Function.Injective f) (p : ℕ) (E : Subgroup Γ₁) :
    IsElemAbelian p (E.map f) ↔ IsElemAbelian p E := by
  constructor
  · intro h
    haveI : IsMulCommutative (E.map f) := h.1
    refine ⟨IsMulCommutative.of_setLike_mul_comm ?_, ?_⟩
    · intro a ha b hb
      apply hf
      rw [map_mul, map_mul]
      exact setLike_mul_comm (s := E.map f) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    · intro x hx
      apply hf
      simpa using h.2 (f x) (show f x ∈ E.map f from ⟨x, hx, rfl⟩)
  · intro h
    haveI : IsMulCommutative E := h.1
    refine ⟨inferInstance, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simpa using congrArg f (h.2 x hx)

private lemma transport_rank' {X Y : Subgroup G} (e : ↥X ≃* ↥Y) {E : Subgroup G} (hE : E ≤ X) :
    ∃ E' : Subgroup G, E' ≤ Y ∧ Nat.card E' = Nat.card E ∧
      (IsElemAbelian 2 E' ↔ IsElemAbelian 2 E) ∧
      (∀ x (hx : x ∈ X), x ∈ E → ((e ⟨x, hx⟩ : ↥Y) : G) ∈ E') ∧
      (∀ y ∈ E', ∃ (x : G) (hx : x ∈ X), x ∈ E ∧ ((e ⟨x, hx⟩ : ↥Y) : G) = y) := by
  refine ⟨((E.subgroupOf X).map e.toMonoidHom).map Y.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, -, hzy⟩ := Subgroup.mem_map.1 hy
    rw [← hzy]
    exact z.2
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective Y),
      Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  · calc IsElemAbelian 2 (((E.subgroupOf X).map e.toMonoidHom).map Y.subtype)
        ↔ IsElemAbelian 2 ((E.subgroupOf X).map (Y.subtype.comp e.toMonoidHom)) := by
          rw [Subgroup.map_map]
      _ ↔ IsElemAbelian 2 (E.subgroupOf X) :=
          isElemAbelian_map_iff
            (fun a b h => e.injective (Subgroup.subtype_injective Y h)) 2 _
      _ ↔ IsElemAbelian 2 E :=
          (isElemAbelian_map_iff (Subgroup.subtype_injective X) 2 (E.subgroupOf X)).symm.trans
            (by rw [Subgroup.map_subgroupOf_eq_of_le hE])
  · intro x hx hxE
    exact Subgroup.mem_map.2
      ⟨e ⟨x, hx⟩, Subgroup.mem_map.2 ⟨⟨x, hx⟩, hxE, rfl⟩, rfl⟩
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.1 hz
    refine ⟨(w : G), w.2, hw, ?_⟩
    rw [← hzy, ← hwz]
    rfl

theorem y7n_c1_wr (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0) : Wr7 t P0 U0 :=
  ⟨h.wr.t_sq, h1.direct⟩

theorem y7n_c1_U_le (h1 : NtOne t g U S U0 P0 g0) : U ≤ U0 := by
  rw [h1.U0_eq]
  exact le_sup_left

theorem y7n_c1_P_le (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0) : P ≤ P0 := by
  rw [← h.wr.direct.1, ← h1.direct.1]
  exact sup_le_sup (y7n_c1_U_le h1) (Subgroup.map_mono (y7n_c1_U_le h1))

theorem y7n_c1_conj_g (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0) :
    ∀ u ∈ U0, g * u * g⁻¹ = g0 * u * g0⁻¹ := by
  intro u hu
  have hg0U0 : g0 ∈ U0 := by
    rw [h1.U0_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g0)
  have hg0t : t * g0 * t⁻¹ ∈ conjSub t U0 :=
    (mem_conjSub_iff' t U0 _).mpr ⟨g0, hg0U0, rfl⟩
  have hcomm : u * (t * g0 * t⁻¹) = (t * g0 * t⁻¹) * u :=
    h1.direct.2.2 u hu _ hg0t
  rw [← h1.gg0]
  calc g0 * (t * g0 * t⁻¹) * u * (g0 * (t * g0 * t⁻¹))⁻¹
      = g0 * ((t * g0 * t⁻¹) * u * (t * g0 * t⁻¹)⁻¹) * g0⁻¹ := by group
    _ = g0 * u * g0⁻¹ := by rw [← hcomm]; group

theorem y7n_c1_J1 (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0) :
    centEl U g ⊔ zpowers g0 ≤ U0 ∧ IsElemAbelian 2 (centEl U g ⊔ zpowers g0) ∧
      Nat.card ↥(centEl U g ⊔ zpowers g0) = 16 := by
  have hFU := y7n_fuFacts h
  have hFU_le_U : centEl U g ≤ U := inf_le_left
  have hg0U0 : g0 ∈ U0 := by
    rw [h1.U0_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g0)
  have hg0t : t * g0 * t⁻¹ ∈ conjSub t U0 :=
    (mem_conjSub_iff' t U0 _).mpr ⟨g0, hg0U0, rfl⟩
  have hcommg0 : ∀ a ∈ centEl U g, a * g0 = g0 * a := by
    intro a ha
    have haU0 : a ∈ U0 := y7n_c1_U_le h1 (hFU_le_U ha)
    have hag : a * g = g * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    have hcomm_a : a * (t * g0 * t⁻¹) = (t * g0 * t⁻¹) * a :=
      h1.direct.2.2 a haU0 _ hg0t
    have key : a * g0 * (t * g0 * t⁻¹) = g0 * a * (t * g0 * t⁻¹) := by
      calc a * g0 * (t * g0 * t⁻¹) = a * (g0 * (t * g0 * t⁻¹)) := by group
        _ = a * g := by rw [h1.gg0]
        _ = g * a := hag
        _ = (g0 * (t * g0 * t⁻¹)) * a := by rw [h1.gg0]
        _ = g0 * ((t * g0 * t⁻¹) * a) := by group
        _ = g0 * (a * (t * g0 * t⁻¹)) := by rw [← hcomm_a]
        _ = g0 * a * (t * g0 * t⁻¹) := by group
    exact mul_right_cancel key
  have hsup_el : IsElemAbelian 2 (centEl U g ⊔ zpowers g0) := by
    refine hFU.elem.sup_of_commute (isElemAbelian_zpowers h1.g0_sq) ?_
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a g0 from hcommg0 a ha) n).eq
  have hleU0 : centEl U g ⊔ zpowers g0 ≤ U0 :=
    sup_le (hFU_le_U.trans (y7n_c1_U_le h1)) (by rw [h1.U0_eq]; exact le_sup_right)
  have hg0_ne_one : g0 ≠ 1 := fun hg => h1.g0_notin (hg.symm ▸ U.one_mem)
  have hcardg0 : Nat.card (zpowers g0) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h1.g0_sq hg0_ne_one]
  have hdisj : Disjoint (centEl U g) (zpowers g0) := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_eq_one_or_self h1.g0_sq hx.2 with hx1 | hxg0
    · exact hx1
    · exact absurd (show g0 ∈ U from hxg0 ▸ hFU_le_U hx.1) h1.g0_notin
  have hnorm : zpowers g0 ≤ Subgroup.normalizer (centEl U g : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.mem_centralizer_iff.mpr (fun a ha => hcommg0 a ha)
  have hcardJ1 : Nat.card ↥(centEl U g ⊔ zpowers g0) = 16 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (centEl U g)
      (zpowers g0) hnorm hdisj, hFU.card, hcardg0]
  exact ⟨hleU0, hsup_el, hcardJ1⟩

theorem y7n_c1_U0_rank (h : NtTwo t g P U S F M) (h1 : NtOne t g U S U0 P0 g0)
    {E : Subgroup G} (hE : E ≤ U0) (hel : IsElemAbelian 2 E) :
    Nat.card E ≤ 16 ∧ (Nat.card E = 16 → E = centEl U g ⊔ zpowers g0) := by
  obtain ⟨e⟩ := h1.iso
  have hJ1 := y7n_c1_J1 h h1
  obtain ⟨E', hE'_le, hE'_card, hE'_iff, hE'_fwd, _⟩ := transport_rank' e hE
  have hE'_el : IsElemAbelian 2 E' := hE'_iff.mpr hel
  have hcard : Nat.card E ≤ 16 := by
    rw [← hE'_card]
    exact h.more.ab16 E' hE'_le hE'_el.1
  refine ⟨hcard, fun h16 => ?_⟩
  have hJ1le : centEl U g ⊔ zpowers g0 ≤ U0 := hJ1.1
  have hJ1el : IsElemAbelian 2 (centEl U g ⊔ zpowers g0) := hJ1.2.1
  have hJ1card : Nat.card ↥(centEl U g ⊔ zpowers g0) = 16 := hJ1.2.2
  obtain ⟨J1', hJ1'_le, hJ1'_card, hJ1'_iff, _, hJ1'_bwd⟩ := transport_rank' e hJ1le
  have hJ1'_el : IsElemAbelian 2 J1' := hJ1'_iff.mpr hJ1el
  have hE'_eq : E' = F ⊔ zpowers g :=
    h.more.uniq16 E' hE'_le hE'_el (by rw [hE'_card, h16])
  have hJ1'_eq : J1' = F ⊔ zpowers g :=
    h.more.uniq16 J1' hJ1'_le hJ1'_el (by rw [hJ1'_card, hJ1card])
  have hle : E ≤ centEl U g ⊔ zpowers g0 := by
    intro x hx
    have hxE' : ((e ⟨x, hE hx⟩ : ↥(S ⊔ zpowers g)) : G) ∈ E' := hE'_fwd x (hE hx) hx
    rw [hE'_eq] at hxE'
    have hxJ1' : ((e ⟨x, hE hx⟩ : ↥(S ⊔ zpowers g)) : G) ∈ J1' := by
      rw [hJ1'_eq]
      exact hxE'
    obtain ⟨x', hx'U0, hx'J1, hx'eq⟩ := hJ1'_bwd _ hxJ1'
    have hsub : (⟨x', hx'U0⟩ : ↥U0) = ⟨x, hE hx⟩ := e.injective (Subtype.ext hx'eq)
    have hxx : x' = x := congrArg Subtype.val hsub
    rwa [hxx] at hx'J1
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hJ1card, h16])

end CFSG.OddStandard.HigherRank.YamadaG23
