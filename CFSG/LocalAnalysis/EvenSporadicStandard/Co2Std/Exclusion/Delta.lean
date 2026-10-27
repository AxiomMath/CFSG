module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.Hyp

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {G : Type} [Group G] {L A T : Subgroup G} {z t : G}

@[expose] def delta (z r : G) : G := z⁻¹ * (r * z * r⁻¹)

theorem mul_delta (z r : G) : z * delta z r = r * z * r⁻¹ := by
  simp [delta]

@[simp]
theorem delta_one : delta z (1 : G) = 1 := by
  simp [delta]

theorem delta_mem_of_conj_mem (hmem : ∀ m ∈ M A z, z⁻¹ * (m * z * m⁻¹) ∈ A) {r : G}
    (hr : r ∈ R₀ A z) : delta z r ∈ A := by
  simpa only [delta] using hmem r hr.1

theorem delta_mul_of_conj_mem (hmem : ∀ m ∈ M A z, z⁻¹ * (m * z * m⁻¹) ∈ A) {r s : G}
    (hr : r ∈ R₀ A z) (hs : s ∈ R₀ A z) :
    delta z (r * s) = delta z r * delta z s := by
  have hsA : delta z s ∈ A := delta_mem_of_conj_mem hmem hs
  have hcomm : delta z s * r = r * delta z s :=
    mem_centralizer_iff.1 hr.2 (delta z s) hsA
  have hrconj : r * delta z s * r⁻¹ = delta z s := by
    rw [← hcomm]
    group
  apply mul_left_cancel (a := z)
  calc z * delta z (r * s)
      = (r * s) * z * (r * s)⁻¹ := mul_delta z (r * s)
    _ = r * (s * z * s⁻¹) * r⁻¹ := by group
    _ = r * (z * delta z s) * r⁻¹ := by rw [← mul_delta z s]
    _ = (r * z * r⁻¹) * (r * delta z s * r⁻¹) := by group
    _ = (r * z * r⁻¹) * delta z s := by rw [hrconj]
    _ = (z * delta z r) * delta z s := by rw [mul_delta z r]
    _ = z * (delta z r * delta z s) := by group

@[expose]
def deltaHom (hmem : ∀ m ∈ M A z, z⁻¹ * (m * z * m⁻¹) ∈ A) : ↥(R₀ A z) →* ↥A where
  toFun r := ⟨delta z (r : G), delta_mem_of_conj_mem hmem r.2⟩
  map_one' := Subtype.ext delta_one
  map_mul' r s := Subtype.ext (delta_mul_of_conj_mem hmem r.2 s.2)

@[simp]
theorem coe_deltaHom_apply (hmem : ∀ m ∈ M A z, z⁻¹ * (m * z * m⁻¹) ∈ A)
    (r : ↥(R₀ A z)) : ((deltaHom hmem r : ↥A) : G) = delta z (r : G) := rfl

theorem delta_inv_of_conj_mem (hmem : ∀ m ∈ M A z, z⁻¹ * (m * z * m⁻¹) ∈ A) {r : G}
    (hr : r ∈ R₀ A z) : delta z r⁻¹ = (delta z r)⁻¹ := by
  have h := delta_mul_of_conj_mem hmem hr (inv_mem hr)
  rw [mul_inv_cancel, delta_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

variable [Finite G]

private theorem L_le_centralizer_z (h : Hyp G L A T z t) :
    L ≤ centralizer ({z} : Set G) := by
  rw [h.set.centralizer_z]
  exact le_sup_left

private theorem A_le_centralizer_z (h : Hyp G L A T z t) :
    A ≤ centralizer ({z} : Set G) :=
  h.jc.le.trans (L_le_centralizer_z h)

private theorem z_mem_centralizer_A (h : Hyp G L A T z t) :
    z ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff]
  intro a ha
  exact mem_centralizer_singleton_iff.1 (A_le_centralizer_z h ha)

private theorem B_le_centralizer_z (h : Hyp G L A T z t) :
    B A z ≤ centralizer ({z} : Set G) := by
  have hz : z ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
  exact sup_le (A_le_centralizer_z h) (zpowers_le.2 hz)

private theorem z_mem_R₀ (h : Hyp G L A T z t) : z ∈ R₀ A z := by
  refine ⟨?_, z_mem_centralizer_A h⟩
  change z ∈ normalizer (B A z : Set G)
  exact le_normalizer (mem_sup_right (mem_zpowers z))

theorem Hyp.commute_of_mem (h : Hyp G L A T z t) {l : G} (hl : l ∈ L) : l * z = z * l :=
  mem_centralizer_singleton_iff.1 (L_le_centralizer_z h hl)

theorem Hyp.z_inv (h : Hyp G L A T z t) : z⁻¹ = z := by
  have hzz := congrArg (· * z⁻¹) h.set.z_sq
  simpa [mul_assoc] using hzz.symm

theorem Hyp.B_le_R₀ (h : Hyp G L A T z t) : B A z ≤ R₀ A z := by
  have hAcent : A ≤ centralizer (A : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    letI : IsElementaryAbelian 2 ↥A := h.jc.module.elemAb
    exact congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : A) ⟨a, ha⟩)
  refine le_inf ?_ (sup_le hAcent (zpowers_le.2 (z_mem_centralizer_A h)))
  change B A z ≤ normalizer (B A z : Set G)
  exact le_normalizer

theorem Hyp.le_M (h : Hyp G L A T z t) : L ⊓ normalizer (A : Set G) ≤ M A z := by
  intro x hx
  have hxcent : x * z = z * x := h.commute_of_mem hx.1
  have hxnormz : x ∈ normalizer (zpowers z : Set G) := by
    have hmem : x ∈ normalizer ({z} : Set G) := by
      rw [normalizer_singleton]
      exact mem_centralizer_singleton_iff.2 hxcent
    simpa only [Subgroup.zpowers_eq_closure] using
      Subgroup.normalizer_le_normalizer_closure ({z} : Set G) hmem
  change x ∈ normalizer (B A z : Set G)
  exact Subgroup.inf_normalizer_le_normalizer_sup A (zpowers z) ⟨hx.2, hxnormz⟩

theorem E2Facts.delta_mem (h2 : E2Facts L A z) {r : G} (hr : r ∈ R₀ A z) : delta z r ∈ A :=
  delta_mem_of_conj_mem h2.conj_mem hr

theorem E2Facts.delta_mul (h2 : E2Facts L A z) {r s : G} (hr : r ∈ R₀ A z) (hs : s ∈ R₀ A z) :
    delta z (r * s) = delta z r * delta z s :=
  delta_mul_of_conj_mem h2.conj_mem hr hs

theorem Hyp.delta_eq_one_iff (h : Hyp G L A T z t) (h2 : E2Facts L A z) {r : G}
    (hr : r ∈ R₀ A z) : delta z r = 1 ↔ r ∈ B A z := by
  constructor
  · intro hδ
    have hconj : r * z * r⁻¹ = z := by
      rw [← mul_delta z r, hδ, mul_one]
    have hrz : r * z = z * r := by
      calc r * z = (r * z * r⁻¹) * r := by group
        _ = z * r := by rw [hconj]
    have hcentB : r ∈ centralizer (B A z : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      obtain ⟨a, ha, c, hc, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 (z_mem_centralizer_A h)) hb
      have hra : a * r = r * a := mem_centralizer_iff.1 hr.2 a ha
      have hrc : c * r = r * c := by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
        exact (Commute.zpow_left (show Commute z r from hrz.symm) k).eq
      calc a * c * r = a * (c * r) := by group
        _ = a * (r * c) := by rw [hrc]
        _ = (a * r) * c := by group
        _ = (r * a) * c := by rw [hra]
        _ = r * (a * c) := by group
    rwa [h2.centralizer_B] at hcentB
  · intro hrB
    have hrz : r * z = z * r := mem_centralizer_singleton_iff.1 (B_le_centralizer_z h hrB)
    rw [delta, hrz]
    group

theorem Hyp.deltaHom_eq_one_iff (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (r : ↥(R₀ A z)) : deltaHom h2.conj_mem r = 1 ↔ (r : G) ∈ B A z := by
  rw [← h.delta_eq_one_iff h2 r.2, ← coe_deltaHom_apply h2.conj_mem r]
  constructor
  · intro h1
    rw [h1, Subgroup.coe_one]
  · intro h1
    exact Subtype.ext (by simpa using h1)

theorem E2Facts.exists_delta_eq (h2 : E2Facts L A z) {a : G} (ha : a ∈ A) :
    ∃ r ∈ R₀ A z, delta z r = a := by
  obtain ⟨r, hr, hrz⟩ := h2.conj_surj a ha
  exact ⟨r, hr, by rw [delta, hrz]; group⟩

theorem Hyp.delta_conj (h : Hyp G L A T z t) {x r : G} (hx : x ∈ L) :
    delta z (x * r * x⁻¹) = x * delta z r * x⁻¹ := by
  have hxz : Commute x z := h.commute_of_mem hx
  have hxiz : x⁻¹ * z = z * x⁻¹ := hxz.inv_left.eq
  have hzix : z⁻¹ * x = x * z⁻¹ := hxz.inv_right.eq.symm
  calc delta z (x * r * x⁻¹)
      = z⁻¹ * (x * (r * z * r⁻¹) * x⁻¹) := by
          simp only [delta]
          congr 1
          calc x * r * x⁻¹ * z * (x * r * x⁻¹)⁻¹
              = x * r * (x⁻¹ * z * x) * r⁻¹ * x⁻¹ := by group
            _ = x * r * z * r⁻¹ * x⁻¹ := by
                rw [show x⁻¹ * z * x = z by rw [hxiz]; group]
            _ = x * (r * z * r⁻¹) * x⁻¹ := by group
    _ = x * (z⁻¹ * (r * z * r⁻¹)) * x⁻¹ := by
          calc z⁻¹ * (x * (r * z * r⁻¹) * x⁻¹)
              = (z⁻¹ * x) * (r * z * r⁻¹) * x⁻¹ := by group
            _ = (x * z⁻¹) * (r * z * r⁻¹) * x⁻¹ := by rw [hzix]
            _ = x * (z⁻¹ * (r * z * r⁻¹)) * x⁻¹ := by group
    _ = x * delta z r * x⁻¹ := rfl

theorem Hyp.exists_mul_of_mem_M (h : Hyp G L A T z t) (h2 : E2Facts L A z) {m : G}
    (hm : m ∈ M A z) : ∃ r ∈ R₀ A z, ∃ x ∈ L ⊓ normalizer (A : Set G), m = r * x := by
  have ha : z⁻¹ * (m * z * m⁻¹) ∈ A := h2.conj_mem m hm
  obtain ⟨r, hrR, hrz⟩ := h2.conj_surj (z⁻¹ * (m * z * m⁻¹)) ha
  have hrz' : r * z * r⁻¹ = m * z * m⁻¹ := by
    rw [hrz]
    group
  have hyM : r⁻¹ * m ∈ M A z := mul_mem (inv_mem hrR.1) hm
  have hyC : r⁻¹ * m ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc r⁻¹ * m * z = r⁻¹ * (m * z * m⁻¹) * m := by group
      _ = r⁻¹ * (r * z * r⁻¹) * m := by rw [← hrz']
      _ = z * (r⁻¹ * m) := by group
  have hy : r⁻¹ * m ∈ (L ⊓ normalizer (A : Set G)) ⊔ zpowers z := by
    rw [← h2.M_inf_centralizer]
    exact ⟨hyM, hyC⟩
  have hzcentN : zpowers z ≤ centralizer ((L ⊓ normalizer (A : Set G) : Subgroup G) : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro x hx
    exact h.commute_of_mem hx.1
  obtain ⟨x, hx, c, hc, hydec⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer hzcentN hy
  have hcx : x * c = c * x := mem_centralizer_iff.1 (hzcentN hc) x hx
  have hcR : c ∈ R₀ A z := zpowers_le.2 (z_mem_R₀ h) hc
  refine ⟨r * c, mul_mem hrR hcR, x, hx, ?_⟩
  calc m = r * (r⁻¹ * m) := by group
    _ = r * (x * c) := by rw [hydec]
    _ = r * (c * x) := by rw [hcx]
    _ = r * c * x := by group

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
