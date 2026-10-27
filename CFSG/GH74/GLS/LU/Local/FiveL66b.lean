module

public import CFSG.GH74.GLS.LU.Local.FiveL66a
public import CFSG.GH74.GLS.LU.Local.Torus4

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section L66b

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z u : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t : G}

abbrev PP (z u : G) : Subgroup G := centralizer ((UU z u : Subgroup G) : Set G)

omit [Finite G] in
theorem mem_PP {x : G} : x ∈ PP z u ↔ x * z = z * x ∧ x * u = u * x := by
  constructor
  · intro hx
    have h1 := Subgroup.mem_centralizer_iff.mp hx z (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
    have h2 := Subgroup.mem_centralizer_iff.mp hx u (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    have hle : UU z u ≤ centralizer ({x} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h1.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr h2.symm
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

omit [Finite G] in
theorem commute_zpowers_zu (hzu : z * u = u * z) : ∀ a ∈ zpowers z, ∀ b ∈ zpowers u, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  exact ((Commute.zpow_right (Commute.zpow_left (hzu : Commute z u) i) j)).eq

theorem mem_UU_iff (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {a : G} :
    a ∈ UU z u ↔ a = 1 ∨ a = z ∨ a = u ∨ a = z * u := by
  constructor
  · intro ha
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_of_commute (commute_zpowers_zu hzu)).mp ha
    rcases mem_zpowers_of_sq_eq_one hz2 hx with h | h <;>
      rcases mem_zpowers_of_sq_eq_one hu2 hy with h' | h' <;> simp [h, h']
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem mem_NN_of_conj {g : G} (hz : g * z * g⁻¹ ∈ UU z u) (hu : g * u * g⁻¹ ∈ UU z u) :
    g ∈ NN z u := by
  apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
  intro x hx
  have hle : UU z u ≤ (UU z u).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_comap]
      exact hz
    · rw [Subgroup.mem_comap]
      exact hu
  have := hle hx
  rw [Subgroup.mem_comap] at this
  exact this

omit [Finite G] in
theorem conj_mul' (g a b : G) : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group

theorem exists_perm_rep (hz2 : z * z = 1) (hu2 : u * u = 1) (hzu : z * u = u * z) {w x : G}
    (hwz : w * z * w⁻¹ = z) (hwu : w * u * w⁻¹ = u * z) (hxz : x * z * x⁻¹ = u)
    (hxu : x * u * x⁻¹ = z * u) {a b : G} (ha : a ∈ UU z u) (hb : b ∈ UU z u) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) :
    ∃ m : G, (m = 1 ∨ m = w ∨ m = x ∨ m = x * w ∨ m = x * x ∨ m = x * x * w) ∧
      m * z * m⁻¹ = a ∧ m * u * m⁻¹ = b := by
  have hzu' : u * z = z * u := hzu.symm
  have hxzu : x * (z * u) * x⁻¹ = z := by
    rw [conj_mul', hxz, hxu]
    calc u * (z * u) = (u * z) * u := by group
      _ = (z * u) * u := by rw [hzu']
      _ = z * (u * u) := by group
      _ = z := by rw [hu2, mul_one]
  have hxuz : x * (u * z) * x⁻¹ = z := by rw [hzu']; exact hxzu
  have hwzu : w * (z * u) * w⁻¹ = u := by
    rw [conj_mul', hwz, hwu]
    calc z * (u * z) = z * (z * u) := by rw [hzu']
      _ = (z * z) * u := by group
      _ = u := by rw [hz2, one_mul]
  rw [mem_UU_iff hz2 hu2 hzu] at ha hb
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb
  all_goals first
    | exact absurd ha ha1
    | exact absurd hb hb1
    | exact absurd (ha.trans hb.symm) hab
    | skip
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩ <;> simp [ha, hb]
  · refine ⟨w, Or.inr (Or.inl rfl), ?_, ?_⟩
    · rw [ha]; exact hwz
    · rw [hb, hwu, hzu']
  · refine ⟨x * w, Or.inr (Or.inr (Or.inr (Or.inl rfl))), ?_, ?_⟩
    · calc x * w * z * (x * w)⁻¹ = x * (w * z * w⁻¹) * x⁻¹ := by group
        _ = a := by rw [hwz, hxz, ha]
    · calc x * w * u * (x * w)⁻¹ = x * (w * u * w⁻¹) * x⁻¹ := by group
        _ = b := by rw [hwu, hxuz, hb]
  · exact ⟨x, Or.inr (Or.inr (Or.inl rfl)), by rw [ha]; exact hxz, by rw [hb]; exact hxu⟩
  · refine ⟨x * x, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), ?_, ?_⟩
    · calc x * x * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by group
        _ = a := by rw [hxz, hxu, ha]
    · calc x * x * u * (x * x)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by group
        _ = b := by rw [hxu, hxzu, hb]
  · refine ⟨x * x * w, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), ?_, ?_⟩
    · calc x * x * w * z * (x * x * w)⁻¹ = x * (x * (w * z * w⁻¹) * x⁻¹) * x⁻¹ := by group
        _ = a := by rw [hwz, hxz, hxu, ha]
    · calc x * x * w * u * (x * x * w)⁻¹ = x * (x * (w * u * w⁻¹) * x⁻¹) * x⁻¹ := by group
        _ = b := by rw [hwu, hxuz, hxz, hb]

theorem FiveCtx.exists_x (c : FiveCtx G p f z S K₁ K₂ t u) :
    ∃ x : G, x * z * x⁻¹ = u ∧ x * u * x⁻¹ = z * u := by
  have X := c.toLUCtx
  obtain ⟨h₀, hh₀⟩ := exists_h₀ c.hs
  obtain ⟨v, hv, w, hwK, hvz, huw⟩ := exists_v_w X hh₀
  obtain ⟨h1, -⟩ := h_conj c.hc c.hs hwK hvz huw
  refine ⟨(v * w)⁻¹, ?_, ?_⟩
  · rw [inv_inv]; exact h1
  · have hvC : v ∈ Cz u := (comps_u X hh₀).comp₁.1 hv
    have hvu : v * u = u * v := Subgroup.mem_centralizer_singleton_iff.mp hvC
    have e0 : u * w = w * z * u := by
      calc u * w = (u * w * u⁻¹) * u := by group
        _ = w * z * u := by rw [huw]
    have e2 : w⁻¹ * u * w = z * u := by
      calc w⁻¹ * u * w = w⁻¹ * (u * w) := by group
        _ = w⁻¹ * (w * z * u) := by rw [e0]
        _ = z * u := by group
    have hvinv : v⁻¹ * u * v = u := by
      calc v⁻¹ * u * v = v⁻¹ * (u * v) := by group
        _ = v⁻¹ * (v * u) := by rw [hvu]
        _ = u := by group
    rw [inv_inv]
    calc (v * w)⁻¹ * u * (v * w) = w⁻¹ * (v⁻¹ * u * v) * w := by group
      _ = w⁻¹ * u * w := by rw [hvinv]
      _ = z * u := e2

end L66b

end CFSG.GH74.GLS.LU.Local.Five
