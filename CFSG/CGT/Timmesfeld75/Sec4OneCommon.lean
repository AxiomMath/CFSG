module

public import CFSG.CGT.Timmesfeld75.Sec5One
public import CFSG.CGT.Timmesfeld75.Sec3GlobalConj
public import CFSG.CGT.Timmesfeld75.Sec3Six
public import CFSG.CGT.Timmesfeld75.Sec215Local
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Conjugates

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

omit [Finite G] in
theorem MaxPair.sec3 (hP : MaxPair T T₁) (hS : Sec3Global T) : Sec3 T T₁ := by
  have h := hP.sec3_conj hS (Subgroup.one_mem (Subgroup.normalizer (T : Set G)))
  rwa [conjSubgroup_one] at h

omit [Finite G] in
theorem MaxPair.card_normIn_le (hP : MaxPair T T₁) {U V : Subgroup G}
    (hU : ∃ u : G, U = conjSubgroup u T) (hV : ∃ v : G, V = conjSubgroup v T) (hne : V ≠ U) :
    Nat.card (normIn U V) ≤ Nat.card (normIn T T₁) := by
  obtain ⟨u, rfl⟩ := hU
  obtain ⟨v, rfl⟩ := hV
  have e : conjSubgroup v T = conjSubgroup u (conjSubgroup (u⁻¹ * v) T) := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  have hne' : conjSubgroup (u⁻¹ * v) T ≠ T := fun h => hne (by rw [e, h])
  rw [e, normIn_conj, card_conjSubgroup]
  exact hP.maximal _ hne'

theorem cfg_of_conj_conj (hT : IsWC T) {U V : Subgroup G} (hU : ∃ u : G, U = conjSubgroup u T)
    (hV : ∃ v : G, V = conjSubgroup v T) (hne : V ≠ U) (hL : normIn U V ≠ ⊥) : Cfg U V := by
  obtain ⟨u, rfl⟩ := hU
  obtain ⟨v, rfl⟩ := hV
  have e : conjSubgroup v T = conjSubgroup (v * u⁻¹) (conjSubgroup u T) := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [e] at hne hL ⊢
  exact Cfg.of_conj (hT.conj u) hne hL

omit [Finite G] in
theorem sec3_of_conj_conj (hS : Sec3Global T) {U V : Subgroup G}
    (hU : ∃ u : G, U = conjSubgroup u T) (hV : ∃ v : G, V = conjSubgroup v T) (hne : V ≠ U)
    (hL : normIn U V ≠ ⊥) : Sec3 U V := by
  obtain ⟨u, rfl⟩ := hU
  obtain ⟨v, rfl⟩ := hV
  have e : conjSubgroup v T = conjSubgroup (v * u⁻¹) (conjSubgroup u T) := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [e] at hne hL ⊢
  exact (hS.conj u) _ hne hL

omit [Finite G] in
theorem sec3Iso_of_conj_conj (hI : Sec3IsoGlobal T) {U V : Subgroup G}
    (hU : ∃ u : G, U = conjSubgroup u T) (hV : ∃ v : G, V = conjSubgroup v T) (hne : V ≠ U)
    (hL : normIn U V ≠ ⊥) : Sec3Iso U V := by
  obtain ⟨u, rfl⟩ := hU
  obtain ⟨v, rfl⟩ := hV
  have e : conjSubgroup v T = conjSubgroup (v * u⁻¹) (conjSubgroup u T) := by
    rw [conjSubgroup_conjSubgroup]
    congr 1
    group
  rw [e] at hne hL ⊢
  exact (hI.conj u) _ hne hL

omit [Finite G] in
theorem exists_conj_of_conj_conj {U V : Subgroup G} (hU : ∃ u : G, U = conjSubgroup u T)
    (hV : ∃ v : G, V = conjSubgroup v T) : ∃ x : G, V = conjSubgroup x U := by
  obtain ⟨u, rfl⟩ := hU
  obtain ⟨v, rfl⟩ := hV
  refine ⟨v * u⁻¹, ?_⟩
  rw [conjSubgroup_conjSubgroup]
  congr 1
  group

end Conjugates

section Generic

variable {G : Type} [Group G]

theorem le_normalizer_of_conjSubgroup_le {K N : Subgroup G}
    (h : ∀ g ∈ K, conjSubgroup g N ≤ N) : K ≤ Subgroup.normalizer (N : Set G) := fun g hg => by
  apply mem_normalizer_of_conjSubgroup_eq
  refine le_antisymm (h g hg) ?_
  have := h g⁻¹ (K.inv_mem hg)
  rwa [conjSubgroup_le_iff, inv_inv] at this

theorem conjSubgroup_le_of_forall_mem {g : G} {H N : Subgroup G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ N) : conjSubgroup g H ≤ N := by
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem isElemAbelian_of_le {p : ℕ} {A B : Subgroup G} (hB : IsElemAbelian p B) (hAB : A ≤ B) :
    IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB hAB

theorem isElemAbelian_sup_of_comm {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hc

end Generic


section Hyp

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G} {a : G}

structure Sec4Hyp (T T₁ : Subgroup G) (a : G) (T₂ : Subgroup G) : Prop where
  pair : MaxPair T T₁
  glob : Sec3Global T
  iso : Sec3IsoGlobal T
  ha : a ∈ normD T
  haL : a ∉ T ⊔ normIn T₁ T
  hcomm : ∀ l ∈ normIn T₁ T, ⁅a, l⁆ ∈ T
  conj : ∃ g : G, T₂ = conjSubgroup g T
  haT₂ : a ∈ T₂

theorem Sec4Hyp.mul_self_eq_one (h : Sec4Hyp T T₁ a T₂) : a * a = 1 := by
  obtain ⟨k, t, ht, -, hak⟩ := h.ha.1
  rw [hak]
  calc k⁻¹ * t * k * (k⁻¹ * t * k) = k⁻¹ * (t * t) * k := by group
    _ = 1 := by rw [elemAbelian_mul_self h.pair.wc.1 ht]; group

theorem Sec4Hyp.ne_one (h : Sec4Hyp T T₁ a T₂) : a ≠ 1 := by
  obtain ⟨k, t, ht, ht1, hak⟩ := h.ha.1
  intro h1
  apply ht1
  have : t = k * a * k⁻¹ := by rw [hak]; group
  rw [this, h1]
  group

theorem Sec4Hyp.mem_normalizer (h : Sec4Hyp T T₁ a T₂) : a ∈ Subgroup.normalizer (T : Set G) :=
  h.ha.2

theorem Sec4Hyp.not_mem_left (h : Sec4Hyp T T₁ a T₂) : a ∉ T := fun h' =>
  h.haL (Subgroup.mem_sup_left h')

theorem Sec4Hyp.not_mem_normIn (h : Sec4Hyp T T₁ a T₂) : a ∉ normIn T₁ T := fun h' =>
  h.haL (Subgroup.mem_sup_right h')

theorem Sec4Hyp.ne_left (h : Sec4Hyp T T₁ a T₂) : T₂ ≠ T := fun h' =>
  h.not_mem_left (h' ▸ h.haT₂)

theorem Sec4Hyp.isWC₁ (h : Sec4Hyp T T₁ a T₂) : IsWC T₁ := by
  obtain ⟨x, hx⟩ := h.pair.conj
  exact hx ▸ h.pair.wc.conj x

theorem Sec4Hyp.isWC₂ (h : Sec4Hyp T T₁ a T₂) : IsWC T₂ := by
  obtain ⟨x, hx⟩ := h.conj
  exact hx ▸ h.pair.wc.conj x

theorem Sec4Hyp.ne_right (h : Sec4Hyp T T₁ a T₂) : T₂ ≠ T₁ := fun h' =>
  h.not_mem_normIn (mem_normIn.2 ⟨h' ▸ h.haT₂, h.mem_normalizer⟩)

theorem Sec4Hyp.mem_normIn₂ (h : Sec4Hyp T T₁ a T₂) : a ∈ normIn T₂ T :=
  mem_normIn.2 ⟨h.haT₂, h.mem_normalizer⟩

theorem Sec4Hyp.normIn₂_ne_bot (h : Sec4Hyp T T₁ a T₂) : normIn T₂ T ≠ ⊥ :=
  Subgroup.ne_bot_iff_exists_ne_one.2
    ⟨⟨a, h.mem_normIn₂⟩, fun h' => h.ne_one (congrArg Subtype.val h')⟩

theorem Sec4Hyp.inf_left_eq_bot (h : Sec4Hyp T T₁ a T₂) : T ⊓ T₂ = ⊥ := by
  obtain ⟨g, hg⟩ := h.conj
  have := h.pair.wc.inf_conj_eq_bot (g := g) (hg ▸ h.ne_left)
  rwa [← hg] at this

theorem Sec4Hyp.inf_right_eq_bot (h : Sec4Hyp T T₁ a T₂) : T₁ ⊓ T₂ = ⊥ := by
  obtain ⟨x, hx⟩ := h.pair.conj
  obtain ⟨g, hg⟩ := h.conj
  have hwc : IsWC T₁ := hx ▸ h.pair.wc.conj x
  have e : T₂ = conjSubgroup (g * x⁻¹) T₁ := by
    rw [hx, conjSubgroup_conjSubgroup, hg]
    congr 1
    group
  have hne : conjSubgroup (g * x⁻¹) T₁ ≠ T₁ := e ▸ h.ne_right
  have := hwc.inf_conj_eq_bot hne
  rwa [← e] at this

end Hyp

section HypFinite

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem Sec4Hyp.sec3 (h : Sec4Hyp T T₁ a T₂) : Sec3 T T₁ := h.pair.sec3 h.glob

theorem Sec4Hyp.normIn_ne_bot (h : Sec4Hyp T T₁ a T₂) : normIn T T₂ ≠ ⊥ := by
  obtain ⟨g, hg⟩ := h.conj
  subst hg
  exact normIn_ne_bot_of_conj h.pair.wc h.ne_left h.normIn₂_ne_bot

theorem Sec4Hyp.cfg₂ (h : Sec4Hyp T T₁ a T₂) : Cfg T T₂ :=
  cfg_of_conj_conj h.pair.wc ⟨1, (conjSubgroup_one T).symm⟩ h.conj h.ne_left h.normIn_ne_bot

omit [Finite G] in
theorem Sec4Hyp.card_normIn_le (h : Sec4Hyp T T₁ a T₂) :
    Nat.card (normIn T T₂) ≤ Nat.card (normIn T T₁) :=
  h.pair.card_normIn_le ⟨1, (conjSubgroup_one T).symm⟩ h.conj h.ne_left

theorem Sec4Hyp.card_normIn₂ (h : Sec4Hyp T T₁ a T₂) :
    Nat.card (normIn T₂ T) = Nat.card (normIn T T₂) :=
  (h.cfg₂.card_normIn_eq h.conj).symm

theorem Sec4Hyp.card_normIn₁ (h : Sec4Hyp T T₁ a T₂) :
    Nat.card (normIn T₁ T) = Nat.card (normIn T T₁) :=
  h.sec3.card_normIn_swap

omit [Finite G] in
theorem Sec4Hyp.inf_centralizer_eq (h : Sec4Hyp T T₁ a T₂) :
    T ⊓ Subgroup.centralizer ({a} : Set G) = normIn T T₂ := by
  obtain ⟨g, hg⟩ := h.conj
  have hwc₂ : IsWC T₂ := hg ▸ h.pair.wc.conj g
  apply le_antisymm
  · rintro t ⟨htT, htC⟩
    exact mem_normIn.2 ⟨htT, hwc₂.centralizer_le_normalizer h.haT₂ h.ne_one htC⟩
  · intro t ht
    obtain ⟨htT, htN⟩ := mem_normIn.1 ht
    refine ⟨htT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact (mul_comm_of_mem_inf_normalizer h.inf_left_eq_bot h.haT₂ h.mem_normalizer htT htN).symm

end HypFinite

end CFSG.CGT.Timmesfeld75
