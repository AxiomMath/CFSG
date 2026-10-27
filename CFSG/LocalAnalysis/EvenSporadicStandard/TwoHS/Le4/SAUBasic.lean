module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

section Normalizes

variable {G : Type*} [Group G] [Finite G] {t : G} {T E F K : Subgroup G}

theorem Sect7SylowData.normalizes_F_E (h : Sect7SylowData t T E F K) {w : G}
    (hwN : w ∈ normalizer (T : Set G)) :
    (∀ x ∈ F, w * x * w⁻¹ ∈ F) ∧ w ∈ normalizer (E : Set G) := by
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
  refine ⟨fun x hx => hA x hx, ?_⟩
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
  rw [mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => hEw g hg
  · intro hg
    have := inv_conj_mem_of_forall_mem w (E : Set G) hEw (w * g * w⁻¹) hg
    have e : w⁻¹ * (w * g * w⁻¹) * w = g := by group
    rwa [e] at this

theorem Sect7SylowData.mem_normalizer_E (h : Sect7SylowData t T E F K) {z : G} (hz : z ∈ T) :
    z ∈ normalizer (E : Set G) :=
  (h.normalizes_F_E (le_normalizer hz)).2

theorem Sect7SylowData.conj_mem_E (h : Sect7SylowData t T E F K) {z : G} (hz : z ∈ T) {e : G}
    (he : e ∈ E) : z * e * z⁻¹ ∈ E :=
  (mem_normalizer_iff.1 (h.mem_normalizer_E hz) e).1 he

end Normalizes

section Classes

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem tConjClass_eq_orbit (T : Subgroup G) (x : G) :
    letI : MulAction T G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp T.subtype)
    tConjClass T x = MulAction.orbit T x := by
  let : MulAction T G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp T.subtype)
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, by
      show ConjAct.toConjAct (z : G) • x = z * x * z⁻¹
      rw [ConjAct.smul_def]; simp⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, z.2, by
      show z * x * z⁻¹ = ConjAct.toConjAct (z : G) • x
      rw [ConjAct.smul_def]; simp⟩

theorem ncard_tConjClass_pow_two {T : Subgroup G} (hT : IsPGroup 2 T) (x : G) :
    ∃ j : ℕ, (tConjClass T x).ncard = 2 ^ j := by
  let : MulAction T G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp T.subtype)
  obtain ⟨n, hn⟩ := hT.card_orbit x
  refine ⟨n, ?_⟩
  rw [tConjClass_eq_orbit T x, ← Nat.card_coe_set_eq]
  exact hn

omit [Finite G] in
theorem tConjClass_conj_mem {T : Subgroup G} {z : G} (hz : z ∈ T) (x : G) :
    tConjClass T (z * x * z⁻¹) = tConjClass T x := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a * z, T.mul_mem ha hz, by group⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b * z⁻¹, T.mul_mem hb (T.inv_mem hz), by group⟩

end Classes

section Trans

variable {G : Type*} [Group G] [Finite G] {t : G} {T E F K : Subgroup G}

theorem Sect7SylowData.tF_trans (h : Sect7SylowData t T E F K) (htt : t * t = 1) (ht : t ∈ E)
    (hF8 : (F : Set G).ncard = 8) : ∀ u ∈ F, ∃ z ∈ T, z * t * z⁻¹ = t * u := by
  set tF : Set G := (fun u => t * u) '' (F : Set G) with htF
  have hcard : tF.ncard = 8 := by
    rw [htF, Set.ncard_image_of_injective _ (mul_right_injective t), hF8]
  have hlarge : 4 < (tConjClass T t).ncard := by
    have := h.tF_large 1 F.one_mem
    rw [mul_one] at this
    omega
  have hsub : tConjClass T t ⊆ tF := by
    rintro _ ⟨z, hz, rfl⟩
    have hzE : z * t * z⁻¹ ∈ E := h.conj_mem_E hz ht
    have hsq : (z * t * z⁻¹) * (z * t * z⁻¹) = 1 := by
      have : (z * t * z⁻¹) * (z * t * z⁻¹) = z * (t * t) * z⁻¹ := by group
      rw [this, htt]; group
    rcases h.E_inv _ hzE hsq with hF | ⟨u, hu, hu'⟩
    · exfalso
      have h1 := h.F_small _ hF
      rw [tConjClass_conj_mem hz] at h1
      omega
    · exact ⟨u, hu, hu'.symm⟩
  obtain ⟨j, hj⟩ := ncard_tConjClass_pow_two h.pgroup t
  have hle : (tConjClass T t).ncard ≤ 8 := by
    rw [← hcard]; exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hj3 : j = 3 := by
    rw [hj] at hlarge hle
    have h1 : 2 ^ 2 < 2 ^ j := by simpa using hlarge
    have h2 : 2 ^ j ≤ 2 ^ 3 := by simpa using hle
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h1
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
    omega
  have hcl8 : (tConjClass T t).ncard = tF.ncard := by rw [hj, hj3, hcard]; norm_num
  have heq : tConjClass T t = tF :=
    Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  intro u hu
  have : t * u ∈ tConjClass T t := by rw [heq]; exact ⟨u, hu, rfl⟩
  obtain ⟨z, hz, hzu⟩ := this
  exact ⟨z, hz, hzu⟩

end Trans

end CFSG.EvenSporadicStandard.TwoHS
