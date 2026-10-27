module

public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionDefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement

section Commutator

variable {G : Type*} [Group G]

theorem orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf b = orderOf a := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a

theorem commutator_mul_right_of_commute {g₁ g₂ c : G} (h₁ : c * g₁ = g₁ * c) :
    ⁅g₁, g₂ * c⁆ = ⁅g₁, g₂⁆ := by
  have h : c * g₁⁻¹ = g₁⁻¹ * c := ((Commute.inv_right (a := c) (b := g₁) h₁)).eq
  simp only [commutatorElement_def, mul_inv_rev]
  calc g₁ * (g₂ * c) * g₁⁻¹ * (c⁻¹ * g₂⁻¹) = g₁ * g₂ * (c * g₁⁻¹) * c⁻¹ * g₂⁻¹ := by group
    _ = g₁ * g₂ * (g₁⁻¹ * c) * c⁻¹ * g₂⁻¹ := by rw [h]
    _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by group

theorem commutator_mul_left_of_commute {g₁ g₂ c : G} (h₂ : c * g₂ = g₂ * c) :
    ⁅g₁ * c, g₂⁆ = ⁅g₁, g₂⁆ := by
  have h : c * g₂ * c⁻¹ = g₂ := by rw [h₂, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g₁ * c * g₂ * (c⁻¹ * g₁⁻¹) * g₂⁻¹ = g₁ * (c * g₂ * c⁻¹) * g₁⁻¹ * g₂⁻¹ := by group
    _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by rw [h]

theorem conj_mem_commutator {W : Subgroup G} {n : G} (hn : ∀ y ∈ W, n * y * n⁻¹ ∈ W) {x : G}
    (hx : x ∈ ⁅W, W⁆) : n * x * n⁻¹ ∈ ⁅W, W⁆ := by
  have hle : W.map (MulAut.conj n).toMonoidHom ≤ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact hn y hy
  have h1 : (⁅W, W⁆).map (MulAut.conj n).toMonoidHom ≤ ⁅W, W⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact h1 (Subgroup.mem_map_of_mem _ hx)

end Commutator

namespace Datum

section Adj

variable {G : Type*} [Group G] {A : Subgroup G} (d : Datum A) {W V₁ V₂ : Subgroup G}

theorem adj_le_P (hW : W ≤ d.V) : W ⊔ zpowers d.t ≤ d.P :=
  sup_le (hW.trans inf_le_left) ((zpowers_le).mpr d.t_mem_P)

theorem mem_adj_iff (hW : W ≤ d.V) {x : G} :
    x ∈ W ⊔ zpowers d.t ↔ x ∈ W ∨ x * d.t ∈ W :=
  mem_sup_zpowers_iff (fun _ hv => d.V_comm_t (hW hv)) d.t_mul_self

theorem isElemAbelian_adj (hW : W ≤ d.V) (hE : IsElemAbelian 2 W) :
    IsElemAbelian 2 (W ⊔ zpowers d.t) :=
  isElemAbelian_sup_zpowers hE (fun _ he => d.V_comm_t (hW he)) d.t_mul_self

theorem mem_V_or_of_mem_W (hR : Radicals d.V V₁ V₂) {y : G}
    (hy : y ∈ (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t)) : y ∈ d.V ∨ y * d.t ∈ d.V := by
  have hle : (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t) ≤ d.V ⊔ zpowers d.t :=
    sup_le (sup_le_sup_right hR.le₁ _) (sup_le_sup_right hR.le₂ _)
  exact (d.mem_adj_iff le_rfl).mp (hle hy)

theorem W_le_P (hR : Radicals d.V V₁ V₂) :
    (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t) ≤ d.P :=
  sup_le (d.adj_le_P hR.le₁) (d.adj_le_P hR.le₂)

end Adj

section Commutator

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} (d : Datum A) {V₁ V₂ : Subgroup G}

theorem commutator_mem_V {g₁ g₂ : G} (hg₁ : g₁ ∈ d.P) (h₁ : g₁ ∈ d.V ∨ g₁ * d.t ∈ d.V)
    (h₂ : g₂ ∈ d.V ∨ g₂ * d.t ∈ d.V) : ⁅g₁, g₂⁆ ∈ d.V := by
  have hcomm : ∀ {x : G}, x ∈ d.P → d.t * x = x * d.t := fun hx => (d.P_comm_t hx).symm
  have hVc : ∀ {a b : G}, a ∈ d.V → b ∈ d.V → ⁅a, b⁆ ∈ d.V := fun ha hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have step2 : ∀ {a : G}, a ∈ d.P → g₂ ∈ d.V ∨ g₂ * d.t ∈ d.V → ∃ v ∈ d.V, ⁅a, g₂⁆ = ⁅a, v⁆ := by
    intro a ha h
    rcases h with h | h
    · exact ⟨g₂, h, rfl⟩
    · refine ⟨g₂ * d.t, h, ?_⟩
      rw [commutator_mul_right_of_commute (hcomm ha)]
  have step1 : ∀ {b : G}, b ∈ d.P → g₁ ∈ d.V ∨ g₁ * d.t ∈ d.V → ∃ v ∈ d.V, ⁅g₁, b⁆ = ⁅v, b⁆ := by
    intro b hb h
    rcases h with h | h
    · exact ⟨g₁, h, rfl⟩
    · refine ⟨g₁ * d.t, h, ?_⟩
      rw [commutator_mul_left_of_commute (hcomm hb)]
  obtain ⟨v₂, hv₂, e₂⟩ := step2 hg₁ h₂
  obtain ⟨v₁, hv₁, e₁⟩ := step1 hv₂.1 h₁
  rw [e₂, e₁]
  exact hVc hv₁ hv₂

theorem commutator_W_le_V (hR : Radicals d.V V₁ V₂) :
    ⁅(V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t), (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t)⁆ ≤ d.V := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  exact d.commutator_mem_V (d.W_le_P hR hg₁) (d.mem_V_or_of_mem_W hR hg₁)
    (d.mem_V_or_of_mem_W hR hg₂)

theorem commutator_W_ne_bot (hR : Radicals d.V V₁ V₂) :
    ⁅(V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t), (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t)⁆ ≠ ⊥ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hR.exists_noncomm
  have hVW : d.V ≤ (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t) := by
    rw [← hR.sup_eq]
    exact sup_le_sup le_sup_left le_sup_left
  intro hbot
  have h1 := Subgroup.commutator_mem_commutator (hVW hx) (hVW hy)
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact hxy h1

end Commutator

end Datum

namespace Facts

section Rad

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem card_adj (F : Facts A) (d : Datum A) {W : Subgroup G} (hW : W ≤ d.V) :
    Nat.card ↥(W ⊔ zpowers d.t) = 2 * Nat.card W := by
  have h := card_eq_two_mul_card_inf (F := W ⊔ zpowers d.t) (V := W) (t := d.t)
    (mem_sup_right (mem_zpowers _)) (fun h => F.t_not_mem_V d (hW h))
    fun x hx => (d.mem_adj_iff hW).mp hx
  rwa [inf_eq_right.mpr le_sup_left] at h

theorem elem_eq_adj (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {E : Subgroup G}
    (hEP : E ≤ d.P) (hE : IsElemAbelian 2 E) (hcard : 32 ≤ Nat.card E) :
    E = V₁ ⊔ zpowers d.t ∨ E = V₂ ⊔ zpowers d.t := by
  have hcomm : ∀ e ∈ E, e * d.t = d.t * e := fun e he => d.P_comm_t (hEP he)
  have hF : IsElemAbelian 2 (E ⊔ zpowers d.t) := isElemAbelian_sup_zpowers hE hcomm d.t_mul_self
  have hFP : E ⊔ zpowers d.t ≤ d.P := sup_le hEP ((zpowers_le).mpr d.t_mem_P)
  have hFcard : 32 ≤ Nat.card ↥(E ⊔ zpowers d.t) :=
    hcard.trans (Subgroup.card_le_of_le le_sup_left)
  have hFV : ∀ y ∈ E ⊔ zpowers d.t, y ∈ d.V ∨ y * d.t ∈ d.V := fun y hy =>
    F.elem_mem_V_or d hFP hF hFcard hy
  have h2 := card_eq_two_mul_card_inf (F := E ⊔ zpowers d.t) (V := d.V) (t := d.t)
    (mem_sup_right (mem_zpowers _)) (F.t_not_mem_V d) hFV
  have hel : IsElemAbelian 2 ((E ⊔ zpowers d.t) ⊓ d.V) := isElemAbelian_of_le hF inf_le_left
  have key : ∀ W : Subgroup G, W ≤ d.V → Nat.card W = 16 → (E ⊔ zpowers d.t) ⊓ d.V ≤ W →
      E = W ⊔ zpowers d.t := by
    intro W hWV hWc hle
    have hEq : (E ⊔ zpowers d.t) ⊓ d.V = W :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hWc]; omega)
    have hFW : E ⊔ zpowers d.t ≤ W ⊔ zpowers d.t := by
      intro y hy
      rw [d.mem_adj_iff hWV]
      rcases hFV y hy with h | h
      · exact Or.inl (by rw [← hEq]; exact ⟨hy, h⟩)
      · exact Or.inr (by rw [← hEq]; exact ⟨mul_mem hy (mem_sup_right (mem_zpowers _)), h⟩)
    have hWc2 : Nat.card ↥(W ⊔ zpowers d.t) = 32 := by rw [F.card_adj d hWV, hWc]
    exact Subgroup.eq_of_le_of_card_ge (le_sup_left.trans hFW) (by rw [hWc2]; exact hcard)
  rcases hR.le_of_elem _ inf_le_right hel with h | h
  · exact Or.inl (key V₁ hR.le₁ hR.card₁ h)
  · exact Or.inr (key V₂ hR.le₂ hR.card₂ h)

theorem adj_properties (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {W : Subgroup G}
    (hW : W = V₁ ∨ W = V₂) :
    W ⊔ zpowers d.t ≤ d.P ∧ IsElemAbelian 2 (W ⊔ zpowers d.t) ∧
      Nat.card ↥(W ⊔ zpowers d.t) = 32 := by
  obtain ⟨hWV, hWe, hWc⟩ := hR.property hW
  exact ⟨d.adj_le_P hWV, d.isElemAbelian_adj hWV hWe, by rw [F.card_adj d hWV, hWc]⟩

theorem card_elem_le (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {E : Subgroup G}
    (hEP : E ≤ d.P) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 32 := by
  by_contra hlt
  push Not at hlt
  rcases F.elem_eq_adj d hR hEP hE hlt.le with h | h
  · have := (F.adj_properties d hR (Or.inl rfl)).2.2
    rw [← h] at this
    omega
  · have := (F.adj_properties d hR (Or.inr rfl)).2.2
    rw [← h] at this
    omega

theorem card_elem_eq_iff (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    {E : Subgroup G} (hEP : E ≤ d.P) (hE : IsElemAbelian 2 E) :
    Nat.card E = 32 ↔ E = V₁ ⊔ zpowers d.t ∨ E = V₂ ⊔ zpowers d.t := by
  refine ⟨fun h => F.elem_eq_adj d hR hEP hE h.ge, ?_⟩
  rintro (rfl | rfl)
  · exact (F.adj_properties d hR (Or.inl rfl)).2.2
  · exact (F.adj_properties d hR (Or.inr rfl)).2.2

end Rad

end Facts

namespace Facts

section Class

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem map_conj_adj (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {n : G}
    (hn : n ∈ normalizer (d.P : Set G)) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) :
    (W ⊔ zpowers d.t).map (MulAut.conj n).toMonoidHom = V₁ ⊔ zpowers d.t ∨
      (W ⊔ zpowers d.t).map (MulAut.conj n).toMonoidHom = V₂ ⊔ zpowers d.t := by
  obtain ⟨hWV, hWe, hWc⟩ := hR.property hW
  have hEP : W ⊔ zpowers d.t ≤ d.P := d.adj_le_P hWV
  have hE : IsElemAbelian 2 (W ⊔ zpowers d.t) := d.isElemAbelian_adj hWV hWe
  have hcard : Nat.card ↥(W ⊔ zpowers d.t) = 32 := by rw [F.card_adj d hWV, hWc]
  refine F.elem_eq_adj d hR ?_ (L34.isElemAbelian_map _ hE) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hn x).mp (hEP hx)
  · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hcard]

theorem central_mem_adj (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {z : G}
    (hz : z ∈ d.P ⊓ centralizer (d.P : Set G)) (hz2 : z * z = 1) {W : Subgroup G}
    (hW : W = V₁ ∨ W = V₂) : z ∈ W ⊔ zpowers d.t := by
  obtain ⟨hWV, hWe, hWc⟩ := hR.property hW
  have hEP : W ⊔ zpowers d.t ≤ d.P := d.adj_le_P hWV
  have hE : IsElemAbelian 2 (W ⊔ zpowers d.t) := d.isElemAbelian_adj hWV hWe
  have hcard : Nat.card ↥(W ⊔ zpowers d.t) = 32 := by rw [F.card_adj d hWV, hWc]
  have hF : IsElemAbelian 2 ((W ⊔ zpowers d.t) ⊔ zpowers z) :=
    isElemAbelian_sup_zpowers hE (fun e he => (mem_centralizer_iff.mp hz.2 e (hEP he))) hz2
  have hFP : (W ⊔ zpowers d.t) ⊔ zpowers z ≤ d.P := sup_le hEP ((zpowers_le).mpr hz.1)
  have hFcard : 32 ≤ Nat.card ↥((W ⊔ zpowers d.t) ⊔ zpowers z) := by
    rw [← hcard]
    exact Subgroup.card_le_of_le le_sup_left
  have hFcard' : Nat.card ↥((W ⊔ zpowers d.t) ⊔ zpowers z) ≤ 32 := by
    rcases F.elem_eq_adj d hR hFP hF hFcard with h | h
    · rw [h, F.card_adj d hR.le₁, hR.card₁]
    · rw [h, F.card_adj d hR.le₂, hR.card₂]
  have hFeq : (W ⊔ zpowers d.t) ⊔ zpowers z = W ⊔ zpowers d.t := by
    symm
    exact Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard]; exact hFcard')
  rw [← hFeq]
  exact mem_sup_right (mem_zpowers z)

theorem central_mem_U_or (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {z : G}
    (hz : z ∈ d.P ⊓ centralizer (d.P : Set G)) (hz2 : z * z = 1) :
    z ∈ d.V ⊓ centralizer (d.V : Set G) ∨ z * d.t ∈ d.V ⊓ centralizer (d.V : Set G) := by
  have h1 := (d.mem_adj_iff hR.le₁).mp (F.central_mem_adj d hR hz hz2 (Or.inl rfl))
  have h2 := (d.mem_adj_iff hR.le₂).mp (F.central_mem_adj d hR hz hz2 (Or.inr rfl))
  rw [← hR.inf_eq]
  have ht : ∀ a b : G, a ∈ d.V → b ∈ d.V → a⁻¹ * b = d.t → False := fun a b ha hb h =>
    F.t_not_mem_V d (h ▸ mul_mem (inv_mem ha) hb)
  rcases h1 with a1 | a1 <;> rcases h2 with a2 | a2
  · exact Or.inl ⟨a1, a2⟩
  · exact (ht z (z * d.t) (hR.le₁ a1) (hR.le₂ a2) (by group)).elim
  · exact (ht z (z * d.t) (hR.le₂ a2) (hR.le₁ a1) (by group)).elim
  · exact Or.inr ⟨a1, a2⟩

end Class

end Facts

namespace Facts

section Class2

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ : Subgroup G}

theorem conj_mem_W (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {n : G}
    (hn : n ∈ normalizer (d.P : Set G)) {y : G}
    (hy : y ∈ (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t)) :
    n * y * n⁻¹ ∈ (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t) := by
  have hmap : ((V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t)).map (MulAut.conj n).toMonoidHom ≤
      (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rcases F.map_conj_adj d hR hn (Or.inl rfl) with h | h <;> rw [h]
      exacts [le_sup_left, le_sup_right]
    · rcases F.map_conj_adj d hR hn (Or.inr rfl) with h | h <;> rw [h]
      exacts [le_sup_left, le_sup_right]
  have := hmap (Subgroup.mem_map_of_mem _ hy)
  simpa [MulAut.conj_apply] using this

theorem not_isConj_of_mem (F : Facts A) (d : Datum A) (hR : Radicals d.V V₁ V₂) {x : G}
    (hxA : x ∈ A) : ¬ IsConj d.t x := by
  intro hconj
  have hnorm : ∀ n ∈ normalizer (d.P : Set G), ∀ y ∈
      ⁅(V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t), (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t)⁆,
      n * y * n⁻¹ ∈
        ⁅(V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t), (V₁ ⊔ zpowers d.t) ⊔ (V₂ ⊔ zpowers d.t)⁆ :=
    fun n hn y hy => conj_mem_commutator (fun z hz => F.conj_mem_W d hR hn hz) hy
  obtain ⟨w, hwD, hw2, hwc⟩ := exists_involution_normal_center d.hP.isPGroup
    ((d.commutator_W_le_V hR).trans inf_le_left)
    (fun p hp y hy => hnorm p (le_normalizer hp) y hy) (d.commutator_W_ne_bot hR)
  have hwV : w ∈ d.V := d.commutator_W_le_V hR hwD
  have hxo : orderOf x = 2 := by rw [orderOf_eq_of_isConj hconj]; exact d.sector.t_order
  obtain ⟨a, haA, hax⟩ := F.invol_conj x hxA w hwV.2 hxo hw2
  have hwconj : IsConj d.t w := hconj.trans (isConj_iff.mpr ⟨a, hax⟩)
  have hwz : w ∈ d.P ⊓ centralizer (d.P : Set G) :=
    ⟨hwV.1, mem_centralizer_iff.mpr fun p hp => hwc p hp⟩
  obtain ⟨n, hn, hnt⟩ := exists_normalizer_conj_of_mem_center d.P_isSylow_centralizer hwz hwconj
  have htD := hnorm n hn w hwD
  have : n * w * n⁻¹ = d.t := by rw [← hnt]; group
  rw [this] at htD
  exact F.t_not_mem_A d (d.commutator_W_le_V hR htD).2

end Class2

end Facts

end CFSG.OddStandard.Seitz77
