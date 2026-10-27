module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxInterfaces

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mul_z' {z : G} {Z A : Subgroup G} (hD : Width.Z4Data z 2 Z A)
    (hz : orderOf z = 2) {v : G} (hvF : v ∈ Fz z) (hv1 : v ≠ 1) (hvz : v ≠ z) (hv2 : v * v = 1) :
    ∃ a ∈ Fz z, a⁻¹ * v * a = v * z := by
  by_contra hno
  push Not at hno
  have hZ : v ∈ Z := by
    refine Width.mem_Z_of_comm hD hz hvF fun b hb => ?_
    by_contra hbv
    have hbF : b ∈ Fz z := hD.sup_eq ▸ Subgroup.mem_sup_right hb
    rcases Width.comm_F hD hz hbF hvF with h | h
    · exact hbv (commutatorElement_eq_one_iff_mul_comm.mp h).symm
    · have h' : b * v * b⁻¹ = z * v := by
        rw [commutatorElement_def] at h
        calc b * v * b⁻¹ = (b * v * b⁻¹ * v⁻¹) * v := by group
          _ = z * v := by rw [h]
      apply hno b⁻¹ ((Fz z).inv_mem hbF)
      rw [inv_inv, h']
      exact Width.Z_comm_F hD hD.mem_z hvF
  exact hvz (Width.involution_eq hD hz hZ (by rw [pow_two]; exact hv2) hv1)

theorem yBar_mul_z {z : G} {Z A : Subgroup G} (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 ↥(Fz z)) (hti : HSTI z) {u : G} (hu : u ∈ Dinv z) :
    u * z ∈ Dinv z ∧ yBar z (u * z) = yBar z u := by
  have huF : u ∈ Fz z := (hti.2 u hu).1
  obtain ⟨-, -, -, hu2, hu1⟩ := ZF_props hD hz hF2 hu.1
  have hFH : Fz z ≤ Hz z := Subgroup.map_subtype_le _
  obtain ⟨a, haF, ha⟩ := exists_conj_mul_z' hD hz huF hu1 hu.2.1 (by rw [← pow_two]; exact hu2)
  have hnH : a⁻¹ ∈ Hz z := hFH ((Fz z).inv_mem haF)
  have e : (a⁻¹ : G) * u * (a⁻¹)⁻¹ = u * z := by rw [inv_inv]; exact ha
  have h1 : u * z ∈ Dinv z := by
    have := Dinv_conj hu hnH
    rwa [e] at this
  refine ⟨h1, ?_⟩
  have h2 := yBar_conj hD hz hF2 hti hu ⟨a⁻¹, hnH⟩
  have h3 : qmk z ⟨a⁻¹, hnH⟩ = 1 := (qmk_eq_one_iff z _).mpr ((Fz z).inv_mem haF)
  simp only [h3, one_mul, inv_one, mul_one] at h2
  rw [← h2]
  exact congrArg (yBar z) e.symm

theorem transitive_of_odd {Q : Type*} [Group Q] (D : Set Q) (hinv : ∀ d ∈ D, d * d = 1)
    (hodd : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Odd (orderOf (d * e))) :
    ∀ d ∈ D, ∀ e ∈ D, ∃ m ∈ Subgroup.closure D, m * d * m⁻¹ = e := by
  intro d hd e he
  by_cases hde : d = e
  · exact ⟨1, one_mem _, by simp [hde]⟩
  · obtain ⟨j, hj⟩ := hodd d hd e he hde
    have hd2 := hinv d hd
    have he2 := hinv e he
    have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    set c := d * e with hc
    have hc1 : c ^ (2 * j + 1) = 1 := by
      rw [← hj]
      exact pow_orderOf_eq_one c
    have hdc : d * c * d⁻¹ = c⁻¹ := by
      rw [hc, mul_inv_rev, hei, hdi]
      calc d * (d * e) * d = (d * d) * e * d := by simp only [mul_assoc]
        _ = e * d := by rw [hd2, one_mul]
    set x := c ^ j with hx
    have hx2 : x * x = c⁻¹ := by
      rw [hx, ← pow_add, ← two_mul]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hc1)
    have hdx : d * x * d⁻¹ = x⁻¹ := by rw [hx, ← conj_pow, hdc, inv_pow]
    have h1 : d * x = x⁻¹ * d := by
      calc d * x = d * x * d⁻¹ * d := by group
        _ = x⁻¹ * d := by rw [hdx]
    have h2 : x * d = d * x⁻¹ := by
      calc x * d = x * (d * x) * x⁻¹ := by group
        _ = x * (x⁻¹ * d) * x⁻¹ := by rw [h1]
        _ = d * x⁻¹ := by group
    refine ⟨x, pow_mem (mul_mem (subset_closure hd) (subset_closure he)) j, ?_⟩
    calc x * d * x⁻¹ = d * x⁻¹ * x⁻¹ := by rw [h2]
      _ = d * (x * x)⁻¹ := by group
      _ = d * c := by rw [hx2, inv_inv]
      _ = e := by rw [hc, ← mul_assoc, hd2, one_mul]

theorem exists_dinv_le_T {z : G} {T : Sylow 2 G} (hbad : BadAt z T) :
    ∃ u ∈ Dinv z, ZF u ≤ (T : Subgroup G) := by
  obtain ⟨⟨⟨_, _, hz, _⟩, _⟩, _, hTH, hcard⟩ := hbad
  by_contra hno
  push Not at hno
  have hle : ET (T : Subgroup G) z ≤ Subgroup.zpowers z := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro v ⟨hv, hvT⟩
    by_cases hvz : v = z
    · rw [hvz]
      exact Subgroup.mem_zpowers z
    · exact absurd hvT (hno v ⟨hv, hvz, hvT.trans hTH⟩)
  have h2 : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have := Subgroup.card_le_of_le hle
  omega

theorem dtil_hyps {z : G} (hset : HSSetting G z) (hti : HSTI z) (hfib : FibreProp z) :
    (Dtil z).Nonempty ∧ (∀ d ∈ Dtil z, d * d = 1 ∧ d ≠ 1) ∧
      (∀ q : Qbar z, ∀ d ∈ Dtil z, q * d * q⁻¹ ∈ Dtil z) ∧
      (∀ d ∈ Dtil z, ∀ e ∈ Dtil z, d ≠ e →
        ¬ IsPGroup 2 ↥(Subgroup.closure ({d, e} : Set (Qbar z)))) := by
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hti.1
    exact ⟨yBar z u, u, hu, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨?_, yBar_ne_one hD hz hF2 hti hu⟩
    rw [← pow_two]
    exact yBar_sq hD hz hF2 hti hu
  · rintro q _ ⟨u, hu, rfl⟩
    obtain ⟨v, hv, h⟩ := exists_yBar_conj hD hz hF2 hti hu q
    exact ⟨v, hv, h.symm⟩
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩ hne hP
    rcases hfib u hu u' hu' hP with h | h
    · exact hne (by rw [h])
    · exact hne (by rw [h, (yBar_mul_z hD hz hF2 hti hu).2])

end CFSG.GF2Type.Aschbacher1976Full.HS
