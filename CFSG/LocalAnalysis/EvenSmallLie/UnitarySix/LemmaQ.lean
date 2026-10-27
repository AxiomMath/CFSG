module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSmallLie.UnitarySix.LemmaQ

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def centInvSup (D : Subgroup G) (t : G) : Subgroup G :=
  (D ⊓ centralizer {t}) ⊔ zpowers t

theorem exists_mem_normalizer_not_mem [Finite G] {p : ℕ} [Fact p.Prime] {Q R : Subgroup G}
    (hR : IsPGroup p R) (hQR : Q < R) :
    ∃ x ∈ R, x ∈ normalizer (Q : Set G) ∧ x ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hQR.not_ge
    intro r hr
    have : (⟨r, hr⟩ : R) ∈ Q.subgroupOf R := h ▸ mem_top _
    exact this
  obtain ⟨y, hyN, hyQ⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨y, y.2, ?_, hyQ⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact (mem_normalizer_iff.mp hyN ⟨h, hQR.le hh⟩).mp hh
  · intro hh
    have hyR : (y : G) ∈ R := y.2
    have hhR : h ∈ R := by
      have h1 : (y : G) * h * (y : G)⁻¹ ∈ R := hQR.le hh
      have h2 : (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) ∈ R :=
        R.mul_mem (R.mul_mem (R.inv_mem hyR) h1) hyR
      simpa [mul_assoc] using h2
    exact (mem_normalizer_iff.mp hyN ⟨h, hhR⟩).mpr hh

theorem isPGroup_subgroupOf {p : ℕ} {Q Y : Subgroup G} (hQ : IsPGroup p Q) :
    IsPGroup p (Q.subgroupOf Y) := by
  intro g
  obtain ⟨k, hk⟩ := hQ ⟨(g : Y), g.2⟩
  refine ⟨k, ?_⟩
  ext
  simpa using congrArg (fun z : Q => ((z : G))) hk

theorem exists_pGroup_gt [Finite G] {p : ℕ} [Fact p.Prime] {Y Q R : Subgroup G} (hQY : Q ≤ Y)
    (hQ : IsPGroup p Q) (hRY : R ≤ Y) (hR : IsPGroup p R) (hcard : Nat.card Q < Nat.card R) :
    ∃ P : Subgroup G, P ≤ Y ∧ IsPGroup p P ∧ Q < P := by
  obtain ⟨P', hP'⟩ := (isPGroup_subgroupOf (Y := Y) hQ).exists_le_sylow
  obtain ⟨P₂, hP₂⟩ := (isPGroup_subgroupOf (Y := Y) hR).exists_le_sylow
  have hcQ : Nat.card (Q.subgroupOf Y) = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQY).toEquiv
  have hcR : Nat.card (R.subgroupOf Y) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRY).toEquiv
  have hPP : Nat.card (P' : Subgroup Y) = Nat.card (P₂ : Subgroup Y) := by
    rw [P'.card_eq_multiplicity, P₂.card_eq_multiplicity]
  have hle : Nat.card (R.subgroupOf Y) ≤ Nat.card (P₂ : Subgroup Y) :=
    Subgroup.card_le_of_le hP₂
  refine ⟨(P' : Subgroup Y).map Y.subtype, map_subtype_le _, P'.isPGroup'.map _, ?_⟩
  have hQle : Q ≤ (P' : Subgroup Y).map Y.subtype := fun q hq => ⟨⟨q, hQY hq⟩, hP' hq, rfl⟩
  refine lt_of_le_of_ne hQle ?_
  intro hEq
  have hcm : Nat.card ((P' : Subgroup Y).map Y.subtype) = Nat.card (P' : Subgroup Y) :=
    Subgroup.card_map_of_injective Y.subtype_injective
  rw [← hEq] at hcm
  omega

theorem comm_of_mul_sq {t δ : G} (ht : t * t = 1) (hδ : δ * δ = 1)
    (h : (δ * t) * (δ * t) = 1) : δ * t = t * δ := by
  have h1 : t * δ * t = δ := by
    calc t * δ * t = δ * (δ * t * (δ * t)) := by group; simp [hδ]
      _ = δ := by rw [h, mul_one]
  calc δ * t = t * δ * t * t := by rw [h1]
    _ = t * δ := by rw [mul_assoc, ht, mul_one]

theorem conj_mem_centInvSup_of {D : Subgroup G} {t y δ : G} (ht : t * t = 1)
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDs : ∀ d ∈ D, d * d = 1)
    (hy : y ∈ normalizer (D : Set G)) (hδ : δ ∈ D) (hyt : y⁻¹ * t * y = δ * t) :
    ∀ h ∈ centInvSup D t, y⁻¹ * h * y ∈ centInvSup D t := by
  have hδt : δ * t = t * δ := by
    refine comm_of_mul_sq ht (hDs δ hδ) ?_
    rw [← hyt]
    calc (y⁻¹ * t * y) * (y⁻¹ * t * y) = y⁻¹ * (t * t) * y := by group
      _ = 1 := by rw [ht]; group
  let S : Subgroup G := (centInvSup D t).comap (MulAut.conj y⁻¹).toMonoidHom
  have hS : ∀ h, h ∈ S ↔ y⁻¹ * h * y ∈ centInvSup D t := by
    intro h; simp [S]
  suffices hle : centInvSup D t ≤ S from fun h hh => (hS h).mp (hle hh)
  refine sup_le ?_ ?_
  · intro a ha
    rw [hS]
    have haD : a ∈ D := ha.1
    have hat : a * t = t * a := ((mem_centralizer_iff.mp ha.2) t rfl).symm
    have ha'D : y⁻¹ * a * y ∈ D := (mem_normalizer_iff''.mp hy a).mp haD
    refine mem_sup_left (mem_inf.mpr ⟨ha'D, ?_⟩)
    rw [mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    have key : (y⁻¹ * a * y) * (δ * t) = (δ * t) * (y⁻¹ * a * y) := by
      rw [← hyt]
      calc (y⁻¹ * a * y) * (y⁻¹ * t * y) = y⁻¹ * (a * t) * y := by group
        _ = y⁻¹ * (t * a) * y := by rw [hat]
        _ = (y⁻¹ * t * y) * (y⁻¹ * a * y) := by group
    have hc := hDc _ ha'D δ hδ
    have : (y⁻¹ * a * y) * t = t * (y⁻¹ * a * y) := by
      have k2 : δ * ((y⁻¹ * a * y) * t) = δ * (t * (y⁻¹ * a * y)) := by
        calc δ * ((y⁻¹ * a * y) * t) = (y⁻¹ * a * y) * δ * t := by rw [← mul_assoc, ← hc]
          _ = (δ * t) * (y⁻¹ * a * y) := by rw [mul_assoc, key]
          _ = δ * (t * (y⁻¹ * a * y)) := by rw [mul_assoc]
      exact mul_left_cancel k2
    exact this.symm
  · rw [zpowers_le, hS, hyt]
    refine mul_mem (mem_sup_left (mem_inf.mpr ⟨hδ, ?_⟩)) (mem_sup_right (mem_zpowers t))
    rw [mem_centralizer_iff]; intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]
    exact hδt.symm

theorem mem_normalizer_centInvSup {D : Subgroup G} {t x δ : G} (ht : t * t = 1)
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hDs : ∀ d ∈ D, d * d = 1)
    (hx : x ∈ normalizer (D : Set G)) (hδ : δ ∈ D) (hxt : x⁻¹ * t * x = δ * t) :
    x ∈ normalizer (centInvSup D t : Set G) := by
  have hδ' : (x * δ * x⁻¹)⁻¹ ∈ D := inv_mem ((mem_normalizer_iff.mp hx δ).mp hδ)
  have hxt' : x⁻¹⁻¹ * t * x⁻¹ = (x * δ * x⁻¹)⁻¹ * t := by
    calc x⁻¹⁻¹ * t * x⁻¹ = (x * δ * x⁻¹)⁻¹ * (x * (δ * t) * x⁻¹) := by group
      _ = (x * δ * x⁻¹)⁻¹ * t := by rw [← hxt]; group
  rw [mem_normalizer_iff'']
  intro h
  refine ⟨conj_mem_centInvSup_of ht hDc hDs hx hδ hxt h, fun hh => ?_⟩
  have := conj_mem_centInvSup_of ht hDc hDs (inv_mem hx) hδ' hxt' _ hh
  simpa [mul_assoc] using this

theorem mem_normalizer_of_le_comm {D W : Subgroup G} (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hW : W ≤ D) {d : G} (hd : d ∈ D) : d ∈ normalizer (W : Set G) := by
  rw [mem_normalizer_iff]
  intro w
  by_cases hw : w ∈ W
  · have : d * w * d⁻¹ = w := by rw [hDc d hd w (hW hw)]; group
    rw [this]
  · have : d * w * d⁻¹ ∉ W := by
      intro h'
      apply hw
      have h2 : d⁻¹ * (d * w * d⁻¹) * d ∈ W := by
        have : d * w * d⁻¹ ∈ D := hW h'
        rw [hDc d⁻¹ (inv_mem hd) _ this]
        simpa [mul_assoc] using h'
      simpa [mul_assoc] using h2
    exact ⟨fun h => absurd h hw, fun h => absurd h this⟩

@[expose] def actTriv (D V : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ normalizer (D : Set G) ∧ y ∈ normalizer (V : Set G) ∧
    ∀ d ∈ D, y * d * y⁻¹ * d⁻¹ ∈ V}
  one_mem' := ⟨one_mem _, one_mem _, fun d _ => by simp⟩
  mul_mem' := by
    rintro y z ⟨hyD, hyV, hy⟩ ⟨hzD, hzV, hz⟩
    refine ⟨mul_mem hyD hzD, mul_mem hyV hzV, fun d hd => ?_⟩
    have h1 := hy d hd
    have h2 : y * (z * d * z⁻¹ * d⁻¹) * y⁻¹ ∈ V := (mem_normalizer_iff.mp hyV _).mp (hz d hd)
    have e : y * z * d * (y * z)⁻¹ * d⁻¹ =
        y * (z * d * z⁻¹ * d⁻¹) * y⁻¹ * (y * d * y⁻¹ * d⁻¹) := by group
    rw [e]
    exact mul_mem h2 h1
  inv_mem' := by
    rintro y ⟨hyD, hyV, hy⟩
    refine ⟨inv_mem hyD, inv_mem hyV, fun d hd => ?_⟩
    have hd' : y⁻¹ * d * y ∈ D := (mem_normalizer_iff''.mp hyD d).mp hd
    have e1 : y * (y⁻¹ * d * y) * y⁻¹ * (y⁻¹ * d * y)⁻¹ = d * (y⁻¹ * d * y)⁻¹ := by group
    have h1 : d * (y⁻¹ * d * y)⁻¹ ∈ V := e1 ▸ hy _ hd'
    have e2 : y⁻¹ * d * y⁻¹⁻¹ * d⁻¹ = (d * (y⁻¹ * d * y)⁻¹)⁻¹ := by group
    rw [e2]
    exact inv_mem h1

theorem conj_mem_actTriv {D V : Subgroup G} {u y : G} (huD : u ∈ normalizer (D : Set G))
    (huV : u ∈ normalizer (V : Set G)) (hy : y ∈ actTriv D V) : u * y * u⁻¹ ∈ actTriv D V := by
  obtain ⟨hyD, hyV, hy⟩ := hy
  refine ⟨mul_mem (mul_mem huD hyD) (inv_mem huD), mul_mem (mul_mem huV hyV) (inv_mem huV),
    fun d hd => ?_⟩
  have hd' : u⁻¹ * d * u ∈ D := (mem_normalizer_iff''.mp huD d).mp hd
  have h1 : u * (y * (u⁻¹ * d * u) * y⁻¹ * (u⁻¹ * d * u)⁻¹) * u⁻¹ ∈ V :=
    (mem_normalizer_iff.mp huV _).mp (hy _ hd')
  have e : u * y * u⁻¹ * d * (u * y * u⁻¹)⁻¹ * d⁻¹ =
      u * (y * (u⁻¹ * d * u) * y⁻¹ * (u⁻¹ * d * u)⁻¹) * u⁻¹ := by group
  rw [e]
  exact h1

theorem commutator_le_of_normalizer {D E J V : Subgroup G}
    (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hVD : V ≤ D)
    (hED : E ≤ normalizer (D : Set G)) (hEV : E ≤ normalizer (V : Set G))
    (hJD : J ≤ normalizer (D : Set G)) (hJV : J ≤ normalizer (V : Set G))
    (hJ : ∀ d ∈ D, ∀ j ∈ J, ⁅d, j⁆ ∈ V) (hE : E ≤ ⁅E, J⁆ ⊔ V) : ⁅D, E⁆ ≤ V := by
  have hJK : ∀ j ∈ J, j ∈ actTriv D V := fun j hj => ⟨hJD hj, hJV hj, fun d hd => by
    have := inv_mem (hJ d hd j hj)
    rw [commutatorElement_inv] at this
    exact this⟩
  have hVK : V ≤ actTriv D V := fun v hv => ⟨Subgroup.le_normalizer (hVD hv),
    Subgroup.le_normalizer hv, fun d hd => by
      rw [hDc v (hVD hv) d hd]; simp⟩
  have hEJK : ⁅E, J⁆ ≤ actTriv D V := by
    rw [commutator_le]
    intro u hu j hj
    rw [commutatorElement_def]
    exact mul_mem (conj_mem_actTriv (hED hu) (hEV hu) (hJK j hj)) (inv_mem (hJK j hj))
  have hEK : E ≤ actTriv D V := hE.trans (sup_le hEJK hVK)
  rw [commutator_le]
  intro d hd u hu
  have := inv_mem ((hEK hu).2.2 d hd)
  rwa [show (u * d * u⁻¹ * d⁻¹)⁻¹ = ⁅d, u⁆ by rw [commutatorElement_def]; group] at this

theorem le_normalizer_of_commutator_le {D E V : Subgroup G} (hc : ⁅D, E⁆ ≤ V) (hVE : V ≤ E) :
    D ≤ normalizer (E : Set G) := by
  intro d hd
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have h1 : ⁅d, g⁆ ∈ E := hVE (hc (commutator_mem_commutator hd hg))
    have e : d * g * d⁻¹ = ⁅d, g⁆ * g := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem h1 hg
  · intro hg
    have h1 : ⁅d⁻¹, d * g * d⁻¹⁆ ∈ E := hVE (hc (commutator_mem_commutator (inv_mem hd) hg))
    have e : g = ⁅d⁻¹, d * g * d⁻¹⁆ * (d * g * d⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem h1 hg

theorem Q_max_of_card_le [Finite G] {Y D Q : Subgroup G} {t : G}
    (h : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ Y →
      R ≤ normalizer (centInvSup D t : Set G) → Nat.card R ≤ Nat.card Q) :
    ∀ R : Subgroup G, IsPGroup 2 R → Q ≤ R → R ≤ Y →
      R ≤ normalizer (centInvSup D t : Set G) → R = Q := fun R hR hQR hRY hRN =>
  (Subgroup.eq_of_le_of_card_ge hQR (h R hR hRY hRN)).symm

end CFSG.EvenSmallLie.UnitarySix.LemmaQ
