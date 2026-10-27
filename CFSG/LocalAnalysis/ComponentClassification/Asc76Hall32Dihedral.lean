module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Normal
public import CFSG.Goldschmidt75.TheoremBa

public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def dihedral (T : Subgroup G) (v : G) (hvN : v ∈ normalizer (T : Set G))
    (hv2 : v * v = 1) : Subgroup G where
  carrier := {x | x ∈ T ∨ x * v ∈ T}
  mul_mem' := by
    have hconj : ∀ y ∈ T, v⁻¹ * y * v ∈ T := fun y hy => by
      have h1 := (mem_normalizer_iff.mp (inv_mem hvN) y).mp hy
      rwa [inv_inv] at h1
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (mul_mem ha hb)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem ha hb)
    · refine Or.inr ?_
      have e : a * b * v = a * v * (v⁻¹ * b * v) := by group
      rw [e]
      exact mul_mem ha (hconj b hb)
    · refine Or.inl ?_
      have e : a * b = a * v * (v⁻¹ * (b * v) * v) * (v * v)⁻¹ := by group
      rw [e, hv2, inv_one, mul_one]
      exact mul_mem ha (hconj _ hb)
  one_mem' := Or.inl (one_mem T)
  inv_mem' := by
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
    rintro a (ha | ha)
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ?_
      have e : a⁻¹ * v = v * (a * v)⁻¹ * v⁻¹ := by
        calc a⁻¹ * v = a⁻¹ * v⁻¹ := by rw [hvi]
          _ = v * (a * v)⁻¹ * v⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.mp hvN _).mp (inv_mem ha)

theorem mem_dihedral {T : Subgroup G} {v : G} {hvN : v ∈ normalizer (T : Set G)}
    {hv2 : v * v = 1} {x : G} : x ∈ dihedral T v hvN hv2 ↔ x ∈ T ∨ x * v ∈ T :=
  Iff.rfl

variable [Finite G]

namespace Setup

variable {S T : Subgroup G} {z : G}

theorem exists_normalizer_conj (h : Setup S T z) {x g : G} (hx : x ∈ S)
    (hg : g ∈ centralizer ({z} : Set G)) (hxg : g⁻¹ * x * g ∈ S) :
    ∃ n : G, (∀ y ∈ T, n * y * n⁻¹ ∈ T) ∧ (∀ y ∈ T, n⁻¹ * y * n ∈ T) ∧
      ∃ τ ∈ T, n⁻¹ * x * n = τ * (g⁻¹ * x * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hCdef
  have hSC : S ≤ C := h.le_centralizer
  have hTC : T ≤ C := h.le.trans hSC
  have hSX : IsSylowOf 2 (S.subgroupOf C) ⊤ := by
    have h1 := (isSylowOf_iff_card.mp (isSylowOf_of_le hSC le_top h.sylow)).2
    refine isSylowOf_iff_card.mpr ⟨le_top, ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv, card_top, h1]
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_isSylowOf_top hSX
  have hmemP : ∀ y : C, (y : G) ∈ S → y ∈ (P : Subgroup C) := fun y hy => by
    rw [hP]; exact hy
  have hTP : T.subgroupOf C ≤ (P : Subgroup C) := fun y hy => hmemP y (h.le hy)
  have hsc : fusionStronglyClosed ((T.subgroupOf C : Subgroup C) : Set C) P := by
    intro a ha c hc
    rw [hP] at hc
    exact h.stronglyClosed a ha c c.2 hc
  set x' : C := ⟨x, hSC hx⟩ with hx'
  set u' : C := ⟨g⁻¹ * x * g, hSC hxg⟩ with hu'
  set g' : C := ⟨g, hg⟩ with hg'
  have himg : (fun y => g'⁻¹ * y * g') '' ({x'} : Set C) = ({u'} : Set C) := by
    rw [Set.image_singleton, Set.singleton_eq_singleton_iff]
    exact Subtype.ext rfl
  obtain ⟨n, hn, hnimg⟩ := CFSG.Goldschmidt75.theoremB_a P hTP hsc
    (Set.singleton_subset_iff.mpr (hmemP x' hx)) (Set.singleton_subset_iff.mpr (hmemP u' hxg))
    himg
  have hmem : n⁻¹ * x' * n ∈ ((T.subgroupOf C : Subgroup C) : Set C) * ({u'} : Set C) := by
    rw [← hnimg]
    exact Set.mem_image_of_mem _ (Set.mem_mul.mpr ⟨1, one_mem _, x', rfl, one_mul _⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hmem
  rw [Set.mem_singleton_iff] at hb
  subst hb
  have hnT : ∀ y ∈ T, (n : G) * y * (n : G)⁻¹ ∈ T := fun y hy =>
    (mem_normalizer_iff.mp hn ⟨y, hTC hy⟩).mp hy
  have hnT' : ∀ y ∈ T, (n : G)⁻¹ * y * n ∈ T := fun y hy => by
    have h1 := (mem_normalizer_iff.mp (inv_mem hn) ⟨y, hTC hy⟩).mp hy
    rw [inv_inv] at h1
    exact h1
  refine ⟨n, hnT, hnT', a, ha, ?_⟩
  have h1 := congrArg Subtype.val hab
  exact h1.symm

end Setup

namespace Split

variable {S T : Subgroup G} {z t v : G} {P₁ : Subgroup G}

omit [Finite G] in
theorem tzv_mul_tzv (h : Setup S T z) (hs : Split S T z t v P₁) :
    t * z * v * (t * z * v) = z := by
  have e1 : t * z * v = t * v * z := by
    calc t * z * v = t * (z * v) := mul_assoc _ _ _
      _ = t * (v * z) := by rw [hs.z_comm_v h]
      _ = t * v * z := (mul_assoc _ _ _).symm
  have hc' : z * (t * v) = t * v * z := by
    calc z * (t * v) = (z * t) * v := (mul_assoc _ _ _).symm
      _ = (t * z) * v := by rw [h.comm z h.mem t hs.t_mem]
      _ = t * z * v := rfl
      _ = t * v * z := e1
  have hc : Commute z (t * v) := hc'
  rw [e1, hc.mul_mul_mul_comm (t * v) z, hs.tv_mul_tv h, h.z_mul_z, mul_one]

theorem conj_tv_mem (h : Setup S T z) (hs : Split S T z t v P₁) {g : G}
    (hg : g⁻¹ * (t * v) * g ∈ S) : g⁻¹ * (t * v) * g * v ∈ T := by
  have hu2 : g⁻¹ * (t * v) * g * (g⁻¹ * (t * v) * g) = g⁻¹ * z * g := by
    calc g⁻¹ * (t * v) * g * (g⁻¹ * (t * v) * g) = g⁻¹ * (t * v * (t * v)) * g := by group
      _ = g⁻¹ * z * g := by rw [hs.tv_mul_tv h]
  have hwS : g⁻¹ * z * g ∈ S := hu2 ▸ mul_mem hg hg
  have hw1 : g⁻¹ * z * g ≠ 1 := fun e => h.ne_one (by
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [e]; group)
  have hwz : g⁻¹ * z * g = z := by
    obtain ⟨q, hq, hsq⟩ := hs.sq_mem h hg
    rw [hu2] at hsq
    have hr : q * q ∈ P₁ := mul_mem hq hq
    have hzz : q * q = z * (z * (q * q)) := by rw [← mul_assoc, h.z_mul_z, one_mul]
    rcases hs.conj_mem_of_mem h h.mem hwS with hw | hw | hw <;> rcases hsq with e | e
    · exact (hw1 (e.trans (hs.eq_one_of_mem h hr (e ▸ hw)))).elim
    · have hrT : q * q ∈ T := by
        rw [hzz, ← e]
        exact mul_mem h.mem hw
      rw [e, hs.eq_one_of_mem h hr hrT, mul_one]
    · exact (hs.v_not_mem' ((e.symm.trans hw) ▸ hr)).elim
    · have e2 : q * q = z * v := by rw [hzz, ← e, hw]
      exact (hs.zv_not_mem (e2 ▸ hr)).elim
    · exact (hs.zv_not_mem ((e.symm.trans hw) ▸ hr)).elim
    · have e2 : q * q = v := by rw [hzz, ← e, hw, ← mul_assoc, h.z_mul_z, one_mul]
      exact (hs.v_not_mem' (e2 ▸ hr)).elim
  have hgC : g ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc z * g = g * (g⁻¹ * z * g) := by group
      _ = g * z := by rw [hwz]
  obtain ⟨n, hnT, hnT', τ, hτ, hnx⟩ :=
    h.exists_normalizer_conj (mul_mem (h.le hs.t_mem) hs.v_mem) hgC hg
  have hnt : n⁻¹ * t * n ∈ T := hnT' t hs.t_mem
  have e1 : n⁻¹ * (t * v) * n = (n⁻¹ * t * n) * (n⁻¹ * v * n) := by group
  have haS : n⁻¹ * v * n ∈ S := by
    have e2 : n⁻¹ * v * n = (n⁻¹ * t * n)⁻¹ * (τ * (g⁻¹ * (t * v) * g)) := by
      rw [← hnx, e1]; group
    rw [e2]
    exact mul_mem (inv_mem (h.le hnt)) (mul_mem (h.le hτ) hg)
  obtain ⟨m, hm⟩ := hs.v_conj
  have hmn : (m * n)⁻¹ * z * (m * n) = n⁻¹ * v * n := by rw [← hm]; group
  have ha := hs.conj_mem_of_mem h h.mem (g := m * n) (by rw [hmn]; exact haS)
  rw [hmn] at ha
  have hu : g⁻¹ * (t * v) * g = τ⁻¹ * ((n⁻¹ * t * n) * (n⁻¹ * v * n)) := by
    rw [← e1, hnx]; group
  rcases ha with ha | ha | ha
  · exfalso
    have h1 := hnT _ ha
    rw [show n * (n⁻¹ * v * n) * n⁻¹ = v by group] at h1
    exact hs.v_not_mem (mem_centralizer_iff.mpr fun y hy => h.comm y hy v h1)
  · rw [hu, ha]
    have e3 : τ⁻¹ * (n⁻¹ * t * n * v) * v = τ⁻¹ * (n⁻¹ * t * n) * (v * v) := by group
    rw [e3, hs.v_mul_v, mul_one]
    exact mul_mem (inv_mem hτ) hnt
  · rw [hu, ha]
    have e3 : τ⁻¹ * (n⁻¹ * t * n * (z * v)) * v = τ⁻¹ * (n⁻¹ * t * n) * z * (v * v) := by
      group
    rw [e3, hs.v_mul_v, mul_one]
    exact mul_mem (mul_mem (inv_mem hτ) hnt) h.mem

theorem conj_mem_dihedral (h : Setup S T z) (hs : Split S T z t v P₁) {a g : G}
    (ha : a ∈ T ∨ a * v ∈ T) (hg : g⁻¹ * a * g ∈ S) :
    g⁻¹ * a * g ∈ T ∨ g⁻¹ * a * g * v ∈ T := by
  have hv2 := hs.v_mul_v
  have hD : ∀ y : G, (y ∈ T ∨ y = v ∨ y = z * v) → y ∈ T ∨ y * v ∈ T := by
    rintro y (hy | rfl | rfl)
    · exact Or.inl hy
    · exact Or.inr (by rw [hv2]; exact one_mem T)
    · exact Or.inr (by rw [mul_assoc, hv2, mul_one]; exact h.mem)
  rcases ha with ha | ha
  · exact hD _ (hs.conj_mem_of_mem h ha hg)
  · have hav : a = a * v * v := by rw [mul_assoc, hv2, mul_one]
    rcases eq_or_of_card_four h.card h.sq h.mem hs.t_mem h.ne_one hs.t_ne_one hs.t_ne_z ha with
      e | e | e | e
    ·
      have hav' : a = v := by rw [hav, e, one_mul]
      obtain ⟨m, hm⟩ := hs.v_conj
      have e2 : g⁻¹ * a * g = (m * g)⁻¹ * z * (m * g) := by rw [hav', ← hm]; group
      rw [e2] at hg ⊢
      exact hD _ (hs.conj_mem_of_mem h h.mem hg)
    ·
      have hav' : a = z * v := by rw [hav, e]
      obtain ⟨m, hm⟩ := hs.zv_conj
      have e2 : g⁻¹ * a * g = (m * g)⁻¹ * z * (m * g) := by rw [hav', ← hm]; group
      rw [e2] at hg ⊢
      exact hD _ (hs.conj_mem_of_mem h h.mem hg)
    ·
      have hav' : a = t * v := by rw [hav, e]
      rw [hav'] at hg ⊢
      exact Or.inr (hs.conj_tv_mem h hg)
    ·
      have hav' : a = v * (t * v) * v⁻¹ := by
        rw [hav, e]
        calc t * z * v = (v * t * v⁻¹) * v := by rw [hs.v_conj_t]
          _ = v * (t * v) * v⁻¹ := by group
      have e2 : g⁻¹ * a * g = (v⁻¹ * g)⁻¹ * (t * v) * (v⁻¹ * g) := by rw [hav']; group
      rw [e2] at hg ⊢
      exact Or.inr (hs.conj_tv_mem h hg)

omit [Finite G] in
theorem sq_comm_of_normalizes (h : Setup S T z) (hs : Split S T z t v P₁) {n : G}
    (hn : ∀ y : G, (y ∈ T ∨ y * v ∈ T) ↔ (n * y * n⁻¹ ∈ T ∨ n * y * n⁻¹ * v ∈ T)) :
    ∀ y : G, (y ∈ T ∨ y * v ∈ T) → y * (n * n) = n * n * y := by
  have hv2 := hs.v_mul_v
  have hDS : ∀ y : G, (y ∈ T ∨ y * v ∈ T) → y ∈ S := by
    rintro y (hy | hy)
    · exact h.le hy
    · have e : y = y * v * v := by rw [mul_assoc, hv2, mul_one]
      rw [e]
      exact mul_mem (h.le hy) hs.v_mem
  have hvD : v ∈ T ∨ v * v ∈ T := Or.inr (by rw [hv2]; exact one_mem T)
  have hwc := h.wc n⁻¹ (fun x hx => by
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h1 := (hn (n⁻¹ * x * n)).mp (Or.inl hx)
    rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at h1
    exact hDS x h1)
  have hnT' : ∀ y ∈ T, n⁻¹ * y * n ∈ T := fun y hy => by
    have h1 : y ∈ rightConjugate T n⁻¹ := by rw [hwc]; exact hy
    rw [mem_rightConjugate_iff, inv_inv] at h1
    exact h1
  have hnT : ∀ y ∈ T, n * y * n⁻¹ ∈ T := fun y hy => by
    have h1 : n * y * n⁻¹ ∈ rightConjugate T n⁻¹ := by
      rw [mem_rightConjugate_iff, inv_inv, show n⁻¹ * (n * y * n⁻¹) * n = y by group]
      exact hy
    rw [hwc] at h1
    exact h1
  have hnz : n * z * n⁻¹ = z := by
    have hv' : n⁻¹ * v * n ∈ S := by
      refine hDS _ ((hn _).mpr ?_)
      rw [show n * (n⁻¹ * v * n) * n⁻¹ = v by group]
      exact hvD
    have hcomm : n * z * n⁻¹ * v = v * (n * z * n⁻¹) := by
      have h1 := h.central _ hv'
      calc n * z * n⁻¹ * v = n * (z * (n⁻¹ * v * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * v * n) * z) * n⁻¹ := by rw [← h1]
        _ = v * (n * z * n⁻¹) := by group
    rcases h.eq_of_comm hs.v_mem hs.v_not_mem (hnT z h.mem) hcomm with e | e
    · refine (h.ne_one ?_).elim
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [e]; group
    · exact e
  have hnt : n * t * n⁻¹ = t ∨ n * t * n⁻¹ = t * z := by
    rcases eq_or_of_card_four h.card h.sq h.mem hs.t_mem h.ne_one hs.t_ne_one hs.t_ne_z
      (hnT t hs.t_mem) with e | e | e | e
    · refine (hs.t_ne_one ?_).elim
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [e]; group
    · refine (hs.t_ne_z ?_).elim
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = n⁻¹ * (n * z * n⁻¹) * n := by rw [e, hnz]
        _ = z := by group
    · exact Or.inl e
    · exact Or.inr e
  have hnv : n * v * n⁻¹ = v ∨ n * v * n⁻¹ = z * v := by
    rcases (hn v).mp hvD with h1 | h1
    · exfalso
      have h2 := hnT' _ h1
      rw [show n⁻¹ * (n * v * n⁻¹) * n = v by group] at h2
      exact hs.v_not_mem (mem_centralizer_iff.mpr fun y hy => h.comm y hy v h2)
    · have e : n * v * n⁻¹ = n * v * n⁻¹ * v * v := by rw [mul_assoc _ v v, hv2, mul_one]
      have hsq : n * v * n⁻¹ * (n * v * n⁻¹) = 1 := by
        calc n * v * n⁻¹ * (n * v * n⁻¹) = n * (v * v) * n⁻¹ := by group
          _ = 1 := by rw [hv2]; group
      rcases eq_or_of_card_four h.card h.sq h.mem hs.t_mem h.ne_one hs.t_ne_one hs.t_ne_z h1 with
        e' | e' | e' | e'
      · left; rw [e, e', one_mul]
      · right; rw [e, e']
      · exfalso
        rw [e, e', hs.tv_mul_tv h] at hsq
        exact h.ne_one hsq
      · exfalso
        rw [e, e', hs.tzv_mul_tzv h] at hsq
        exact h.ne_one hsq
  have hF_mul : ∀ a b : G, n * n * a * (n * n)⁻¹ = a → n * n * b * (n * n)⁻¹ = b →
      n * n * (a * b) * (n * n)⁻¹ = a * b := fun a b ha hb => by
    calc n * n * (a * b) * (n * n)⁻¹ =
        (n * n * a * (n * n)⁻¹) * (n * n * b * (n * n)⁻¹) := by group
      _ = a * b := by rw [ha, hb]
  have hFz : n * n * z * (n * n)⁻¹ = z := by
    calc n * n * z * (n * n)⁻¹ = n * (n * z * n⁻¹) * n⁻¹ := by group
      _ = z := by rw [hnz, hnz]
  have hFt : n * n * t * (n * n)⁻¹ = t := by
    have e0 : n * n * t * (n * n)⁻¹ = n * (n * t * n⁻¹) * n⁻¹ := by group
    rcases hnt with e | e
    · rw [e0, e, e]
    · rw [e0, e]
      calc n * (t * z) * n⁻¹ = (n * t * n⁻¹) * (n * z * n⁻¹) := by group
        _ = t := by rw [e, hnz, mul_assoc, h.z_mul_z, mul_one]
  have hFv : n * n * v * (n * n)⁻¹ = v := by
    have e0 : n * n * v * (n * n)⁻¹ = n * (n * v * n⁻¹) * n⁻¹ := by group
    rcases hnv with e | e
    · rw [e0, e, e]
    · rw [e0, e]
      calc n * (z * v) * n⁻¹ = (n * z * n⁻¹) * (n * v * n⁻¹) := by group
        _ = v := by rw [e, hnz, ← mul_assoc, h.z_mul_z, one_mul]
  have hFT : ∀ y ∈ T, n * n * y * (n * n)⁻¹ = y := fun y hy => by
    rcases eq_or_of_card_four h.card h.sq h.mem hs.t_mem h.ne_one hs.t_ne_one hs.t_ne_z hy with
      e | e | e | e
    · rw [e]; group
    · rw [e]; exact hFz
    · rw [e]; exact hFt
    · rw [e]; exact hF_mul t z hFt hFz
  have hFix : ∀ y : G, n * n * y * (n * n)⁻¹ = y → y * (n * n) = n * n * y :=
    fun y e => (mul_inv_eq_iff_eq_mul.mp e).symm
  rintro y (hy | hy)
  · exact hFix y (hFT y hy)
  · have e : y = y * v * v := by rw [mul_assoc, hv2, mul_one]
    refine hFix y ?_
    rw [e]
    exact hF_mul _ v (hFT _ hy) hFv

end Split

end CFSG.ComponentClassification.Asc76X.Hall32
