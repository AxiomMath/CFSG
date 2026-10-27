module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.SetupS

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup ZTwoAux

namespace ZTwoAux

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_klein {V : Subgroup G} (hV : Nat.card V = 4) (hexp : ∀ v ∈ V, v ^ 2 = 1)
    {c₀ z₀ : G} (hc : c₀ ∈ normalizer (V : Set G)) (hc3 : c₀ ^ 3 = 1)
    (hfpf : ∀ v ∈ V, v ≠ 1 → c₀ * v * c₀⁻¹ ≠ v) (hz : z₀ ∈ V) (hz1 : z₀ ≠ 1) {w : G}
    (hw : w ∈ V) (hw1 : w ≠ 1) : ∃ g : G, g⁻¹ * z₀ * g = w := by
  have hcinv : c₀⁻¹ ∈ normalizer (V : Set G) := inv_mem hc
  have h1 : c₀ * c₀ = c₀⁻¹ := by
    have : c₀ * c₀ * c₀ = 1 := by simpa [pow_succ] using hc3
    exact eq_inv_of_mul_eq_one_left this
  have h2 : c₀⁻¹ * c₀⁻¹ = c₀ := by
    calc c₀⁻¹ * c₀⁻¹ = (c₀ * c₀)⁻¹ := by group
      _ = c₀⁻¹⁻¹ := by rw [h1]
      _ = c₀ := inv_inv _
  obtain ⟨a, ha⟩ : ∃ a, a = c₀ * z₀ * c₀⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = c₀⁻¹ * z₀ * c₀ := ⟨_, rfl⟩
  have haV : a ∈ V := ha ▸ (mem_normalizer_iff.mp hc z₀).mp hz
  have hbV : b ∈ V := by
    have := (mem_normalizer_iff.mp hcinv z₀).mp hz
    rw [hb]
    simpa using this
  have hca : c₀ * a * c₀⁻¹ = b := by
    calc c₀ * a * c₀⁻¹ = (c₀ * c₀) * z₀ * (c₀⁻¹ * c₀⁻¹) := by rw [ha]; group
      _ = b := by rw [h1, h2, hb]
  have hcb : c₀ * b * c₀⁻¹ = z₀ := by rw [hb]; group
  have ha1 : a ≠ 1 := by
    intro e
    apply hz1
    calc z₀ = c₀⁻¹ * (c₀ * z₀ * c₀⁻¹) * c₀ := by group
      _ = 1 := by rw [← ha, e]; group
  have hb1 : b ≠ 1 := by
    intro e
    apply hz1
    calc z₀ = c₀ * (c₀⁻¹ * z₀ * c₀) * c₀⁻¹ := by group
      _ = 1 := by rw [← hb, e]; group
  have haz : a ≠ z₀ := by
    rw [ha]
    exact hfpf z₀ hz hz1
  have hbz : b ≠ z₀ := by
    intro e
    apply hfpf z₀ hz hz1
    rw [e] at hcb
    exact hcb
  have hab : a ≠ b := by
    intro e
    apply hfpf a haV ha1
    rw [hca, e]
  have haz' : a ∉ zpowers z₀ := by
    intro hmem
    rcases (mem_zpowers_iff_of_sq_eq_one (hexp z₀ hz)).mp hmem with e | e
    · exact ha1 e
    · exact haz e
  have hb' : b = z₀ * a := by
    rcases (mem_klein_iff hV hexp hz haV hz1 haz' (g := b)).mp hbV with e | e | e | e
    · exact absurd e hb1
    · exact absurd e hbz
    · exact absurd e.symm hab
    · exact e
  rcases (mem_klein_iff hV hexp hz haV hz1 haz' (g := w)).mp hw with e | e | e | e
  · exact absurd e hw1
  · exact ⟨1, by rw [e]; group⟩
  · exact ⟨c₀⁻¹, by rw [e, ha]; group⟩
  · exact ⟨c₀, by rw [e, ← hb', hb]⟩

end ZTwoAux

namespace ZTwoConfig

variable {G : Type} [Group G] [Finite G] {T S U R : Subgroup G} {y x c : G}
  (h : ZTwoConfig T S U R y x c) {z : G} (hd : D8Data R U (conjSubgroup U x) z)

include h hd

omit hd in
theorem c_cube : c ^ 3 = 1 := h.c_order ▸ pow_orderOf_eq_one c

theorem conj_z_of_U {w : G} (hw : w ∈ U) (hw1 : w ≠ 1) : ∃ g : G, g⁻¹ * z * g = w :=
  exists_conj_of_klein h.card_U h.U_exp h.c_normalizes h.c_cube h.c_fpf hd.z_mem_U hd.z_ne_one
    hw hw1

theorem conj_z_of_U' {w : G} (hw : w ∈ conjSubgroup U x) (hw1 : w ≠ 1) :
    ∃ g : G, g⁻¹ * z * g = w := by
  have hc' : x⁻¹ * c * x ∈ normalizer ((conjSubgroup U x : Subgroup G) : Set G) := by
    rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_conjSubgroup,
      show x * (x⁻¹ * c * x) = c * x by group, ← conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.mpr h.c_normalizes]
  have hc3 : (x⁻¹ * c * x) ^ 3 = 1 := by
    have e : (x⁻¹ * c * x) ^ 3 = x⁻¹ * (c * c * c) * x := by
      rw [pow_succ, pow_two]; group
    rw [e]
    have : c * c * c = 1 := by simpa [pow_succ] using h.c_cube
    rw [this]; group
  have hfpf : ∀ v ∈ conjSubgroup U x, v ≠ 1 → (x⁻¹ * c * x) * v * (x⁻¹ * c * x)⁻¹ ≠ v := by
    intro v hv hv1 e
    rw [mem_conjSubgroup_iff] at hv
    refine h.c_fpf (x * v * x⁻¹) hv ?_ ?_
    · intro e1
      apply hv1
      calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
        _ = 1 := by rw [e1]; group
    · calc c * (x * v * x⁻¹) * c⁻¹
          = x * ((x⁻¹ * c * x) * v * (x⁻¹ * c * x)⁻¹) * x⁻¹ := by group
        _ = x * v * x⁻¹ := by rw [e]
  exact exists_conj_of_klein h.card_U' h.U'_exp hc' hc3 hfpf hd.z_mem_V hd.z_ne_one hw hw1

theorem conj_z_of_involution {r : G} (hr : r ∈ R) (hr2 : r ^ 2 = 1) (hr1 : r ≠ 1) :
    ∃ g : G, g⁻¹ * z * g = r := by
  rcases hd.mem_U_or_V_of_sq hr hr2 with hrU | hrV
  · exact h.conj_z_of_U hd hrU hr1
  · exact h.conj_z_of_U' hd hrV hr1

theorem y_not_conj_R {g r : G} (hr : r ∈ R) (hr2 : r ^ 2 = 1) (hr1 : r ≠ 1) :
    g⁻¹ * y * g ≠ r := by
  intro e
  obtain ⟨k, hk⟩ := h.conj_z_of_involution hd hr hr2 hr1
  apply h.y_not_conj_z hd (g * k⁻¹)
  calc (g * k⁻¹)⁻¹ * y * (g * k⁻¹) = k * (g⁻¹ * y * g) * k⁻¹ := by group
    _ = k * r * k⁻¹ := by rw [e]
    _ = k * (k⁻¹ * z * k) * k⁻¹ := by rw [hk]
    _ = z := by group

theorem fusion_S {a : G} (ha : a⁻¹ * y * a ∈ S) : y⁻¹ * (a⁻¹ * y * a) ∈ R := by
  have hw2 : (a⁻¹ * y * a) ^ 2 = 1 := by
    have e : (a⁻¹ * y * a) ^ 2 = a⁻¹ * (y * y) * a := by
      rw [pow_two]; group
    rw [e]
    have : y * y = 1 := by simpa [pow_two] using h.y_sq
    rw [this]; group
  obtain ⟨r, hr, hw | hw⟩ := (h.mem_S_iff).mp ha
  · exfalso
    have hr2 : r ^ 2 = 1 := by rw [← hw]; exact hw2
    have hr1 : r ≠ 1 := by
      intro e
      rw [e] at hw
      apply h.y_ne_one
      calc y = a * (a⁻¹ * y * a) * a⁻¹ := by group
        _ = 1 := by rw [hw]; group
    exact h.y_not_conj_R hd hr hr2 hr1 hw
  · rw [hw]
    have hc : y * r = r * y := (h.y_comm r (h.R_le hr)).symm
    have e : y⁻¹ * (r * y) = r := by
      calc y⁻¹ * (r * y) = y⁻¹ * (y * r) := by rw [hc]
        _ = r := by group
    rw [e]
    exact hr

end ZTwoConfig

end CFSG.QuasithinUnique
