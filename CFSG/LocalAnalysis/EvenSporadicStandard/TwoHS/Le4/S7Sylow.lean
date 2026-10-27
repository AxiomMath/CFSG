module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Basic

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup


theorem inv_conj_mem_of_forall_mem {G : Type*} [Group G] [Finite G] (w : G) (A : Set G)
    (h : ∀ a ∈ A, w * a * w⁻¹ ∈ A) : ∀ a ∈ A, w⁻¹ * a * w ∈ A := by
  have hinj : Function.Injective (fun a : G => w * a * w⁻¹) := by
    intro a b hab; simpa using hab
  have hsub : (fun a : G => w * a * w⁻¹) '' A ⊆ A := by
    rintro _ ⟨a, ha, rfl⟩; exact h a ha
  have heq : (fun a : G => w * a * w⁻¹) '' A = A :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_image_of_injective _ hinj]) (Set.toFinite _)
  intro a ha
  rw [← heq] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have e : w⁻¹ * (w * b * w⁻¹) * w = b := by group
  show w⁻¹ * (w * b * w⁻¹) * w ∈ A
  rw [e]; exact hb

@[expose] def tConjClass {G : Type*} [Group G] (T : Subgroup G) (x : G) : Set G :=
  (fun z => z * x * z⁻¹) '' (T : Set G)

theorem tConjClass_conj {G : Type*} [Group G] {T : Subgroup G} {w : G}
    (hw : ∀ x, x ∈ T ↔ w * x * w⁻¹ ∈ T) (x : G) :
    tConjClass T (w * x * w⁻¹) = (fun a => w * a * w⁻¹) '' tConjClass T x := by
  have hw' : ∀ z ∈ T, w⁻¹ * z * w ∈ T := by
    intro z hz
    have e : w * (w⁻¹ * z * w) * w⁻¹ = z := by group
    exact (hw (w⁻¹ * z * w)).2 (by rw [e]; exact hz)
  ext a
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(w⁻¹ * z * w) * x * (w⁻¹ * z * w)⁻¹, ⟨_, hw' z hz, rfl⟩, ?_⟩
    group
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨w * z * w⁻¹, (hw z).1 hz, ?_⟩
    group

theorem ncard_tConjClass_conj {G : Type*} [Group G] {T : Subgroup G} {w : G}
    (hw : ∀ x, x ∈ T ↔ w * x * w⁻¹ ∈ T) (x : G) :
    (tConjClass T (w * x * w⁻¹)).ncard = (tConjClass T x).ncard := by
  rw [tConjClass_conj hw, Set.ncard_image_of_injective]
  intro a b hab; simpa using hab


structure Sect7SylowData {G : Type*} [Group G] (t : G) (T E F K : Subgroup G) : Prop where
  pgroup : IsPGroup 2 T
  E_le : E ≤ T
  F_le : F ≤ E
  K_le : K ≤ T
  E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  F_exp : ∀ x ∈ F, x * x = 1
  E_inv : ∀ x ∈ E, x * x = 1 → x ∈ F ∨ ∃ u ∈ F, x = t * u
  E_sq_onto : ∀ x ∈ E, x * x = 1 → ∃ e ∈ E, e * e = x
  star : ∀ x ∈ T, x * x = 1 → (tConjClass T x).ncard ≤ 4 → x ∈ E
  F_small : ∀ x ∈ F, (tConjClass T x).ncard ≤ 4
  tF_large : ∀ u ∈ F, ¬ (tConjClass T (t * u)).ncard ≤ 4
  CF_sq : ∀ x ∈ T, (∀ a ∈ F, x * a = a * x) → x * x ∈ E
  K_def : ∀ x ∈ T, (∀ a ∈ E, a * a = 1 → x * a = a * x) → x ∈ K
  K_cent_small : ∀ x ∈ K, x ∉ E →
    Nat.card ((centralizer ({x} : Set G)) ⊓ K : Subgroup G) < Nat.card E
  normalizer_M1 : ∀ w ∈ normalizer (T : Set G), w ∈ normalizer (E : Set G) → w ∈ T

theorem Sect7SylowData.normalizer_le {G : Type*} [Group G] [Finite G] {t : G}
    {T E F K : Subgroup G} (h : Sect7SylowData t T E F K) : normalizer (T : Set G) ≤ T := by
  intro w hwN
  have hw : ∀ x, x ∈ T ↔ w * x * w⁻¹ ∈ T := fun x => mem_normalizer_iff.1 hwN x
  have hinjw : Function.Injective (fun a : G => w * a * w⁻¹) := by
    intro a b hab; simpa using hab
  have hA : ∀ x ∈ (F : Set G), w * x * w⁻¹ ∈ (F : Set G) := by
    intro x hx
    have hxT : x ∈ T := h.E_le (h.F_le hx)
    have hxT' : w * x * w⁻¹ ∈ T := (hw x).1 hxT
    have hsq : (w * x * w⁻¹) * (w * x * w⁻¹) = 1 := by
      have : (w * x * w⁻¹) * (w * x * w⁻¹) = w * (x * x) * w⁻¹ := by group
      rw [this, h.F_exp x hx]; group
    have hcl : (tConjClass T (w * x * w⁻¹)).ncard ≤ 4 := by
      rw [ncard_tConjClass_conj hw]; exact h.F_small x hx
    have hE : w * x * w⁻¹ ∈ E := h.star _ hxT' hsq hcl
    rcases h.E_inv _ hE hsq with hF | ⟨u, hu, hu'⟩
    · exact hF
    · exfalso
      apply h.tF_large u hu
      rw [← hu']; exact hcl
  have hA' := inv_conj_mem_of_forall_mem w (F : Set G) hA
  have hEwT : ∀ e ∈ E, w * e * w⁻¹ ∈ T := fun e he => (hw e).1 (h.E_le he)
  have hEwF : ∀ e ∈ E, ∀ a ∈ F, (w * e * w⁻¹) * a = a * (w * e * w⁻¹) := by
    intro e he a ha
    have ha' : w⁻¹ * a * w ∈ F := hA' a ha
    have hc := h.E_comm e he _ (h.F_le ha')
    calc (w * e * w⁻¹) * a = w * (e * (w⁻¹ * a * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * a * w) * e) * w⁻¹ := by rw [hc]
      _ = a * (w * e * w⁻¹) := by group
  have hEwsq : ∀ e ∈ E, (w * e * w⁻¹) * (w * e * w⁻¹) ∈ E := fun e he =>
    h.CF_sq _ (hEwT e he) (hEwF e he)
  have hΩ : ∀ x ∈ {x : G | x ∈ E ∧ x * x = 1}, w * x * w⁻¹ ∈ {x : G | x ∈ E ∧ x * x = 1} := by
    rintro x ⟨hxE, hxx⟩
    obtain ⟨e, he, rfl⟩ := h.E_sq_onto x hxE hxx
    refine ⟨?_, ?_⟩
    · have : w * (e * e) * w⁻¹ = (w * e * w⁻¹) * (w * e * w⁻¹) := by group
      rw [this]; exact hEwsq e he
    · have : (w * (e * e) * w⁻¹) * (w * (e * e) * w⁻¹) = w * ((e * e) * (e * e)) * w⁻¹ := by
        group
      rw [this, hxx]; group
  have hΩ' := inv_conj_mem_of_forall_mem w _ hΩ
  have hEwK : ∀ e ∈ E, w * e * w⁻¹ ∈ K := by
    intro e he
    refine h.K_def _ (hEwT e he) fun a haE haa => ?_
    have ha' : w⁻¹ * a * w ∈ E := (hΩ' a ⟨haE, haa⟩).1
    have hc := h.E_comm e he _ ha'
    calc (w * e * w⁻¹) * a = w * (e * (w⁻¹ * a * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * a * w) * e) * w⁻¹ := by rw [hc]
      _ = a * (w * e * w⁻¹) := by group
  have hEw : ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    intro e he
    by_contra hne
    have hxK := hEwK e he
    have hsub : (fun a => w * a * w⁻¹) '' (E : Set G) ⊆
        (((centralizer ({w * e * w⁻¹} : Set G)) ⊓ K : Subgroup G) : Set G) := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨?_, hEwK a ha⟩
      show w * a * w⁻¹ ∈ centralizer ({w * e * w⁻¹} : Set G)
      rw [mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      calc w * e * w⁻¹ * (w * a * w⁻¹) = w * (e * a) * w⁻¹ := by group
        _ = w * (a * e) * w⁻¹ := by rw [h.E_comm e he a ha]
        _ = w * a * w⁻¹ * (w * e * w⁻¹) := by group
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ hinjw] at hle
    have hlt := h.K_cent_small _ hxK hne
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hle
    exact absurd hlt (not_lt.2 hle)
  have hwE : w ∈ normalizer (E : Set G) := by
    rw [mem_normalizer_iff]
    intro g
    constructor
    · exact fun hg => hEw g hg
    · intro hg
      have := inv_conj_mem_of_forall_mem w (E : Set G) hEw (w * g * w⁻¹) hg
      have e : w⁻¹ * (w * g * w⁻¹) * w = g := by group
      rwa [e] at this
  exact h.normalizer_M1 w hwN hwE

theorem Sect7SylowData.sylow {G : Type*} [Group G] [Finite G] {t : G} {T E F K : Subgroup G}
    (h : Sect7SylowData t T E F K) : ¬ 2 ∣ T.index :=
  not_two_dvd_index_of_normalizer_le h.pgroup h.normalizer_le

theorem core_of_K_def {G : Type*} [Group G] {T E F K : Subgroup G} {t : G} (htt : t * t = 1)
    (hE_inv : ∀ x ∈ E, x * x = 1 → x ∈ F ∨ ∃ u ∈ F, x = t * u)
    (tF_trans : ∀ u ∈ F, ∃ z ∈ T, z * t * z⁻¹ = t * u)
    (K_def : ∀ x ∈ T, (∀ a ∈ E, a * a = 1 → x * a = a * x) → x ∈ K) :
    ∀ x ∈ T, (∀ z ∈ T, (z * x * z⁻¹) * t = t * (z * x * z⁻¹)) → x ∈ K := by
  intro x hxT hx
  have hxt : x * t = t * x := by simpa using hx 1 T.one_mem
  have htu : ∀ u ∈ F, x * (t * u) = (t * u) * x := by
    intro u hu
    obtain ⟨z, hzT, hz⟩ := tF_trans u hu
    have h1 := hx z⁻¹ (T.inv_mem hzT)
    rw [← hz]
    calc x * (z * t * z⁻¹) = z * ((z⁻¹ * x * z⁻¹⁻¹) * t) * z⁻¹ := by group
      _ = z * (t * (z⁻¹ * x * z⁻¹⁻¹)) * z⁻¹ := by rw [h1]
      _ = (z * t * z⁻¹) * x := by group
  refine K_def x hxT fun a haE haa => ?_
  rcases hE_inv a haE haa with ha | ⟨u, hu, rfl⟩
  · have h1 := htu a ha
    have e : t * (t * a) = a := by rw [← mul_assoc, htt, one_mul]
    calc x * a = x * (t * (t * a)) := by rw [e]
      _ = (x * t) * (t * a) := by group
      _ = (t * x) * (t * a) := by rw [hxt]
      _ = t * (x * (t * a)) := by group
      _ = t * ((t * a) * x) := by rw [h1]
      _ = (t * (t * a)) * x := by group
      _ = a * x := by rw [e]
  · exact htu u hu

end CFSG.EvenSporadicStandard.TwoHS
