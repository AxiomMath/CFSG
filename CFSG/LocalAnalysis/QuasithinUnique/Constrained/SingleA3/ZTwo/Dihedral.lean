module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup

namespace ZTwoAux

variable {G : Type} [Group G]

structure D8Data (R U V : Subgroup G) (z : G) : Prop where
  R_eq : R = U ⊔ V
  card_U : Nat.card U = 4
  card_V : Nat.card V = 4
  U_exp : ∀ u ∈ U, u ^ 2 = 1
  V_exp : ∀ v ∈ V, v ^ 2 = 1
  U_norm_V : U ≤ normalizer (V : Set G)
  V_norm_U : V ≤ normalizer (U : Set G)
  R_nonab : ∃ r ∈ R, ∃ s ∈ R, r * s ≠ s * r
  z_mem_U : z ∈ U
  z_mem_V : z ∈ V
  z_ne_one : z ≠ 1
  inter : ∀ g ∈ U, g ∈ V → g ∈ zpowers z

namespace D8Data

variable {R U V : Subgroup G} {z : G} (hd : D8Data R U V z)

include hd

theorem z_sq : z ^ 2 = 1 := hd.U_exp z hd.z_mem_U

theorem mem_R_iff {r : G} : r ∈ R ↔ ∃ w ∈ U, ∃ w' ∈ V, w * w' = r := by
  rw [hd.R_eq]
  exact A3Dich.mem_sup_iff_of_le_normalizer hd.U_norm_V

theorem U_le_R : U ≤ R := hd.R_eq ▸ le_sup_left

theorem V_le_R : V ≤ R := hd.R_eq ▸ le_sup_right

theorem zpowers_le_U : zpowers z ≤ U := zpowers_le.mpr hd.z_mem_U

theorem zpowers_le_V : zpowers z ≤ V := zpowers_le.mpr hd.z_mem_V

theorem z_central {r : G} (hr : r ∈ R) : r * z = z * r := by
  have hU : U ≤ centralizer ({z} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (ZTwoAux.comm_of_exp_two hd.U_exp hu hd.z_mem_U)
  have hV : V ≤ centralizer ({z} : Set G) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (ZTwoAux.comm_of_exp_two hd.V_exp hv hd.z_mem_V)
  have : R ≤ centralizer ({z} : Set G) := hd.R_eq ▸ sup_le hU hV
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hr)

theorem U_comm {a b : G} (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a :=
  comm_of_exp_two hd.U_exp ha hb

theorem V_comm {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a :=
  comm_of_exp_two hd.V_exp ha hb

theorem card_zpowers_z : Nat.card (zpowers z) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hd.z_sq hd.z_ne_one

theorem symm : D8Data R V U z where
  R_eq := by rw [hd.R_eq, sup_comm]
  card_U := hd.card_V
  card_V := hd.card_U
  U_exp := hd.V_exp
  V_exp := hd.U_exp
  U_norm_V := hd.V_norm_U
  V_norm_U := hd.U_norm_V
  R_nonab := hd.R_nonab
  z_mem_U := hd.z_mem_V
  z_mem_V := hd.z_mem_U
  z_ne_one := hd.z_ne_one
  inter := fun g hgV hgU => hd.inter g hgU hgV

variable [Finite G]

theorem exists_U_not_Z : ∃ w ∈ U, w ∉ zpowers z := by
  by_contra h
  have : U ≤ zpowers z := fun w hw => by_contra fun hwz => h ⟨w, hw, hwz⟩
  have h1 := Subgroup.card_le_of_le this
  rw [hd.card_U, hd.card_zpowers_z] at h1
  omega

theorem exists_V_not_Z : ∃ w ∈ V, w ∉ zpowers z := by
  by_contra h
  have : V ≤ zpowers z := fun w hw => by_contra fun hwz => h ⟨w, hw, hwz⟩
  have h1 := Subgroup.card_le_of_le this
  rw [hd.card_V, hd.card_zpowers_z] at h1
  omega

theorem noncomm {w w' : G} (hw : w ∈ U) (hwz : w ∉ zpowers z) (hw' : w' ∈ V)
    (hw'z : w' ∉ zpowers z) : w * w' ≠ w' * w := by
  intro hcomm
  have hU := eq_zpowers_sup_zpowers hd.card_U hd.U_exp hd.z_mem_U hw hd.z_ne_one hwz
  have hV := eq_zpowers_sup_zpowers hd.card_V hd.V_exp hd.z_mem_V hw' hd.z_ne_one hw'z
  have h1 : U ≤ centralizer ({w'} : Set G) := by
    rw [hU]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr (comm_of_exp_two hd.V_exp hd.z_mem_V hw')
    · exact mem_centralizer_singleton_iff.mpr hcomm
  have hVU : V ≤ centralizer (U : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu1 : u * w' = w' * u := mem_centralizer_singleton_iff.mp (h1 hu)
    have hV' : V ≤ centralizer ({u} : Set G) := by
      rw [hV]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr (comm_of_exp_two hd.U_exp hd.z_mem_U hu)
      · exact mem_centralizer_singleton_iff.mpr hu1.symm
    exact (mem_centralizer_singleton_iff.mp (hV' hv)).symm
  have hRU : R ≤ centralizer (U : Set G) := by
    rw [hd.R_eq]
    refine sup_le ?_ hVU
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact comm_of_exp_two hd.U_exp ha hu
  have hUR : U ≤ centralizer (R : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hRU hr) u hu).symm
  have hRV : R ≤ centralizer (V : Set G) := by
    rw [hd.R_eq]
    refine sup_le ?_ ?_
    · intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (hVU hv) u hu).symm
    · intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact comm_of_exp_two hd.V_exp ha hv
  have hVR : V ≤ centralizer (R : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hRV hr) v hv).symm
  have hRR : R ≤ centralizer (R : Set G) := by
    rw [hd.R_eq]
    exact sup_le (hd.R_eq ▸ hUR) (hd.R_eq ▸ hVR)
  obtain ⟨r, hr, s, hs, hrs⟩ := hd.R_nonab
  exact hrs (Subgroup.mem_centralizer_iff.mp (hRR hr) s hs).symm

theorem mem_U_or_V_of_sq {r : G} (hr : r ∈ R) (hr2 : r ^ 2 = 1) : r ∈ U ∨ r ∈ V := by
  obtain ⟨w, hw, w', hw', rfl⟩ := hd.mem_R_iff.mp hr
  have hcomm : w * w' = w' * w := comm_of_sq_eq_one (hd.U_exp w hw) (hd.V_exp w' hw') hr2
  by_cases hwz : w ∈ zpowers z
  · right
    exact V.mul_mem (hd.zpowers_le_V hwz) hw'
  · by_cases hw'z : w' ∈ zpowers z
    · left
      exact U.mul_mem hw (hd.zpowers_le_U hw'z)
    · exact absurd hcomm (hd.noncomm hw hwz hw' hw'z)

theorem mem_zpowers_of_central {r : G} (hr : r ∈ R) (hc : ∀ s ∈ R, r * s = s * r) :
    r ∈ zpowers z := by
  obtain ⟨w, hw, w', hw', rfl⟩ := hd.mem_R_iff.mp hr
  by_cases hwz : w ∈ zpowers z
  · by_contra hn
    have hrV : w * w' ∈ V := V.mul_mem (hd.zpowers_le_V hwz) hw'
    obtain ⟨w₀, hw₀, hw₀z⟩ := hd.exists_U_not_Z
    exact hd.noncomm hw₀ hw₀z hrV hn (hc w₀ (hd.U_le_R hw₀)).symm
  · by_cases hw'z : w' ∈ zpowers z
    · by_contra hn
      have hrU : w * w' ∈ U := U.mul_mem hw (hd.zpowers_le_U hw'z)
      obtain ⟨w₀, hw₀, hw₀z⟩ := hd.exists_V_not_Z
      exact hd.noncomm hrU hn hw₀ hw₀z (hc w₀ (hd.V_le_R hw₀))
    · exfalso
      have h := hc w (hd.U_le_R hw)
      have h2 : w' * w = w * w' := by
        have : w * (w' * w) = w * (w * w') := by
          calc w * (w' * w) = w * w' * w := by rw [mul_assoc]
            _ = w * (w * w') := h
        exact mul_left_cancel this
      exact hd.noncomm hw hwz hw' hw'z h2.symm

omit [Finite G] in
theorem no_sq_one_of_mem_U (β : G ≃* G) (hU : ∀ u ∈ U, β u ∈ V) (hz : β z = z) {r : G}
    (hrU : r ∈ U) : r * β r * z ≠ 1 := by
  intro h1
  have hr2 : r ^ 2 = 1 := hd.U_exp r hrU
  have hβr : β r = r * z := by
    calc β r = r⁻¹ * (r * β r * z) * z⁻¹ := by group
      _ = r⁻¹ * 1 * z⁻¹ := by rw [h1]
      _ = r * z := by
        rw [inv_eq_self_of_sq_eq_one hr2, inv_eq_self_of_sq_eq_one hd.z_sq]
        simp
  have hmU : r * z ∈ U := U.mul_mem hrU hd.z_mem_U
  have hmV : r * z ∈ V := hβr ▸ hU r hrU
  have hZ : r * z ∈ zpowers z := hd.inter _ hmU hmV
  have hrZ : r ∈ zpowers z := by
    have := (zpowers z).mul_mem hZ ((zpowers z).inv_mem (mem_zpowers z))
    simpa using this
  rcases (mem_zpowers_iff_of_sq_eq_one hd.z_sq).mp hrZ with h | h
  · rw [h, map_one, one_mul] at hβr
    exact hd.z_ne_one hβr.symm
  · rw [h, hz] at hβr
    have h4 : z * z = 1 := by simpa [pow_two] using hd.z_sq
    rw [h4] at hβr
    exact hd.z_ne_one hβr

theorem no_sq_one (β : G ≃* G) (hβ2 : ∀ g, β (β g) = g) (hU : ∀ u ∈ U, β u ∈ V)
    (hV : ∀ v ∈ V, β v ∈ U) (hz : β z = z) {r : G} (hr : r ∈ R) : r * β r * z ≠ 1 := by
  obtain ⟨w, hw, w', hw', rfl⟩ := hd.mem_R_iff.mp hr
  by_cases hwz : w ∈ zpowers z
  · exact hd.symm.no_sq_one_of_mem_U β hV hz (V.mul_mem (hd.zpowers_le_V hwz) hw')
  by_cases hw'z : w' ∈ zpowers z
  · exact hd.no_sq_one_of_mem_U β hU hz (U.mul_mem hw (hd.zpowers_le_U hw'z))
  intro h1
  set w'' := β w with hw''
  have hw''V : w'' ∈ V := hU w hw
  have hw''Z : w'' ∉ zpowers z := by
    intro h
    apply hwz
    rcases (mem_zpowers_iff_of_sq_eq_one hd.z_sq).mp h with h | h
    · have : w = 1 := by rw [← hβ2 w, ← hw'', h, map_one]
      rw [this]; exact one_mem _
    · have : w = z := by rw [← hβ2 w, ← hw'', h, hz]
      rw [this]; exact mem_zpowers z
  have hβw'' : β w'' = w := hβ2 w
  have hw''2 : w'' * w'' = 1 := by simpa [pow_two] using hd.V_exp w'' hw''V
  have hw2 : w * w = 1 := by simpa [pow_two] using hd.U_exp w hw
  have hVgen := (mem_klein_iff hd.card_V hd.V_exp hd.z_mem_V hw''V hd.z_ne_one hw''Z
    (g := w')).mp hw'
  have hz1 := hd.z_ne_one
  rcases hVgen with h | h | h | h
  · exact hw'z (h ▸ one_mem _)
  · exact hw'z (h ▸ mem_zpowers z)
  ·
    subst h
    apply hz1
    have h2 : w * w'' * β (w * w'') = 1 := by
      rw [map_mul, ← hw'', hβw'']
      calc w * w'' * (w'' * w) = w * (w'' * w'') * w := by group
        _ = 1 := by rw [hw''2, mul_one, hw2]
    rw [h2, one_mul] at h1
    exact h1
  ·
    subst h
    apply hz1
    have h2 : w * (z * w'') * β (w * (z * w'')) = 1 := by
      rw [map_mul, map_mul, ← hw'', hβw'', hz]
      calc w * (z * w'') * (w'' * (z * w)) = w * z * (w'' * w'') * z * w := by group
        _ = 1 := by
          rw [hw''2, mul_one]
          calc w * z * z * w = w * (z * z) * w := by group
            _ = 1 := by rw [show z * z = 1 by simpa [pow_two] using hd.z_sq, mul_one, hw2]
    rw [h2, one_mul] at h1
    exact h1

end D8Data

end ZTwoAux

end CFSG.QuasithinUnique
