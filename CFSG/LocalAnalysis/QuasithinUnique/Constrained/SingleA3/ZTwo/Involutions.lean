module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.SetupS

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup ZTwoAux

namespace ZTwoConfig

variable {G : Type} [Group G] [Finite G] {T S U R : Subgroup G} {y x c : G}
  (h : ZTwoConfig T S U R y x c) {z : G}

omit [Finite G] h in
theorem claimA {A B : Subgroup G} (hd : D8Data R A B z) {e r : G}
    (hA : ∀ u ∈ A, e⁻¹ * u * e ∈ B) (hr : r ∈ A) (hc : e⁻¹ * r * e = r) : r ∈ zpowers z := by
  have := hA r hr
  rw [hc] at this
  exact hd.inter r hr this

omit [Finite G] h in
theorem claimB {A B : Subgroup G} (hd : D8Data R A B z) {e r : G}
    (hA : ∀ u ∈ A, e⁻¹ * u * e ∈ B) (hz : e⁻¹ * z * e = z) (hy : e⁻¹ * y * e = z * y)
    (hr : r ∈ A) (hc : e⁻¹ * (r * y) * e = r * y) : False := by
  have h1 : e⁻¹ * r * e * (z * y) = r * y := by
    calc e⁻¹ * r * e * (z * y) = e⁻¹ * r * e * (e⁻¹ * y * e) := by rw [hy]
      _ = e⁻¹ * (r * y) * e := by group
      _ = r * y := hc
  have h2 : e⁻¹ * r * e = r * z := by
    calc e⁻¹ * r * e = (e⁻¹ * r * e * (z * y)) * (z * y)⁻¹ := by group
      _ = r * y * (z * y)⁻¹ := by rw [h1]
      _ = r * z⁻¹ := by group
      _ = r * z := by rw [inv_eq_self_of_sq_eq_one hd.z_sq]
  have h3 : r * z ∈ B := by
    have := hA r hr
    rwa [h2] at this
  have h4 : r * z ∈ A := A.mul_mem hr hd.z_mem_U
  have h5 : r * z ∈ zpowers z := hd.inter _ h4 h3
  have h6 : r ∈ zpowers z := by
    have := (zpowers z).mul_mem h5 ((zpowers z).inv_mem (mem_zpowers z))
    simpa using this
  rcases (mem_zpowers_iff_of_sq_eq_one hd.z_sq).mp h6 with rfl | rfl
  · rw [mul_one] at h2
    have : (1 : G) = z := by simpa using h2
    exact hd.z_ne_one this.symm
  · rw [hz] at h2
    have h7 : r * r = 1 := by simpa [pow_two] using hd.z_sq
    rw [h7] at h2
    exact hd.z_ne_one h2

variable (hd : D8Data R U (conjSubgroup U x) z)

include h hd

theorem comm_involution {s₀ s : G} (hs₀ : s₀ ∈ S) (hs : s ∈ S) (hs2 : s ^ 2 = 1)
    (hc : (x * s₀)⁻¹ * s * (x * s₀) = s) : s = 1 ∨ s = z := by
  obtain ⟨r, hr, hsr | hsr⟩ := (h.mem_S_iff).mp hs
  · rw [hsr] at hs2 hc ⊢
    rcases hd.mem_U_or_V_of_sq hr hs2 with hrU | hrV
    · have := claimA hd (fun u hu => h.U_conj_e hs₀ hu) hrU hc
      exact (mem_zpowers_iff_of_sq_eq_one hd.z_sq).mp this
    · have := claimA hd.symm (fun v hv => h.U'_conj_e hs₀ hv) hrV hc
      exact (mem_zpowers_iff_of_sq_eq_one hd.z_sq).mp this
  · rw [hsr] at hs2 hc ⊢
    have hr2 : r ^ 2 = 1 := by rw [← h.sq_of_mem_S hr]; exact hs2
    exfalso
    rcases hd.mem_U_or_V_of_sq hr hr2 with hrU | hrV
    · exact claimB hd (fun u hu => h.U_conj_e hs₀ hu) (h.conj_z_e hd hs₀) (h.conj_y_e hd hs₀)
        hrU hc
    · exact claimB hd.symm (fun v hv => h.U'_conj_e hs₀ hv) (h.conj_z_e hd hs₀)
        (h.conj_y_e hd hs₀) hrV hc

end ZTwoConfig

end CFSG.QuasithinUnique
