module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [CharP K 2] [PerfectRing K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private theorem exists_hypPair_of_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate) {u y : V}
    (hu : Q u = 0) (hu0 : u ≠ 0) (huy : polar Q u y = 0) (hy : ∀ c : K, y ≠ c • u) :
    ∃ P : HypPair Q, P.e = u ∧ y ∈ P.perp := by
  classical
  have hy0 : y ≠ 0 := fun h => hy 0 (by rw [h, zero_smul])
  have hclaim : ∃ z : V, polar Q y z = 0 ∧ polar Q u z ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨z₁, hz₁⟩ := exists_polar_ne_zero hQ hy0
    set z₀ : V := (polar Q y z₁)⁻¹ • z₁ with hz₀def
    have hz₀ : polar Q y z₀ = 1 := by
      rw [hz₀def, polar_smul_right_eq, inv_mul_cancel₀ hz₁]
    have hzero : u - polar Q u z₀ • y = 0 := by
      apply eq_zero_of_polar_eq_zero hQ
      intro z
      have h1 : polar Q y (z - polar Q y z • z₀) = 0 := by
        rw [polar_sub_right, polar_smul_right_eq, hz₀, mul_one, sub_self]
      have h2 : polar Q u (z - polar Q y z • z₀) = 0 := h _ h1
      rw [polar_sub_right, polar_smul_right_eq] at h2
      rw [polar_sub_left, polar_smul_left_eq, mul_comm (polar Q u z₀) (polar Q y z)]
      exact h2
    have hu_eq : u = polar Q u z₀ • y := sub_eq_zero.mp hzero
    have hc0 : polar Q u z₀ ≠ 0 := by
      intro hc
      exact hu0 (by rw [hu_eq, hc, zero_smul])
    have h := congrArg (fun z => (polar Q u z₀)⁻¹ • z) hu_eq
    simp only [smul_smul, inv_mul_cancel₀ hc0, one_smul] at h
    exact hy (polar Q u z₀)⁻¹ h.symm
  obtain ⟨z, hyz, huz⟩ := hclaim
  set z' : V := (polar Q u z)⁻¹ • z with hz'def
  have hz'_u : polar Q u z' = 1 := by
    rw [hz'def, polar_smul_right_eq, inv_mul_cancel₀ huz]
  have hz'_y : polar Q y z' = 0 := by
    rw [hz'def, polar_smul_right_eq, hyz, mul_zero]
  refine ⟨HypPair.ofPolarEqOne hu hz'_u, rfl, ?_⟩
  rw [HypPair.mem_perp]
  refine ⟨huy, ?_⟩
  rw [polar_comm, HypPair.polar_ofPolarEqOne_f hu hz'_u (z := y) (by rwa [polar_comm])]
  exact hz'_y

private theorem exists_ne_zero_mem_perp (hdim : 4 ≤ Module.finrank K V) (P : HypPair Q) :
    ∃ z ∈ P.perp, z ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have htop : (⊤ : Submodule K V) ≤ Submodule.span K ({P.e, P.f} : Set V) := by
    intro x _
    have hx : P.proj x = 0 := h _ (P.proj_mem_perp x)
    rw [P.eq_add_proj x, hx, add_zero]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hfin : Module.finrank K V ≤ 2 := by
    have h1 : Module.finrank K (⊤ : Submodule K V) ≤
        Module.finrank K (Submodule.span K ({P.e, P.f} : Set V)) := Submodule.finrank_mono htop
    rw [finrank_top] at h1
    refine h1.trans ?_
    have h2 : Module.finrank K (Submodule.span K ({P.e, P.f} : Set V)) ≤
        ({P.e, P.f} : Set V).toFinset.card := finrank_span_le_card _
    refine h2.trans ?_
    simpa using (Finset.card_le_two (a := P.e) (b := P.f))
  omega

private theorem exists_anisotropic_mem_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {z : V} (hz : z ∈ P.perp) (hz0 : z ≠ 0) : ∃ x ∈ P.perp, Q x ≠ 0 := by
  by_cases hQz : Q z ≠ 0
  · exact ⟨z, hz, hQz⟩
  · push Not at hQz
    obtain ⟨w, hwP, hzw⟩ :=
      (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero hz hz0
    set w' : V := (polar Q z w)⁻¹ • w with hw'def
    have hw'P : w' ∈ P.perp := P.perp.smul_mem _ hwP
    have hzw' : polar Q z w' = 1 := by
      rw [hw'def, polar_smul_right_eq, inv_mul_cancel₀ hzw]
    by_cases hQw : Q w' ≠ 0
    · exact ⟨w', hw'P, hQw⟩
    · push Not at hQw
      refine ⟨z + w', P.perp.add_mem hz hw'P, ?_⟩
      rw [QuadraticMap.map_add Q, hQz, hQw, hzw']
      simp

private theorem exists_anisotropic_mem_perp_polar_ne_zero (hQ : (polarBilin Q).Nondegenerate)
    (P : HypPair Q) {e : V} (he : Q e = 0) (heP : e ∈ P.perp) (he0 : e ≠ 0) :
    ∃ x ∈ P.perp, Q x ≠ 0 ∧ polar Q e x ≠ 0 := by
  obtain ⟨w, hwP, hew⟩ := (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero heP he0
  set w' : V := (polar Q e w)⁻¹ • w with hw'def
  have hw'P : w' ∈ P.perp := P.perp.smul_mem _ hwP
  have hew' : polar Q e w' = 1 := by
    rw [hw'def, polar_smul_right_eq, inv_mul_cancel₀ hew]
  have hQe : Q ((1 - Q w') • e) = 0 := by
    rw [map_smul_eq_sq, he, mul_zero]
  have hB : polar Q w' ((1 - Q w') • e) = 1 - Q w' := by
    rw [polar_smul_right_eq, polar_comm Q w' e, hew', mul_one]
  have hQx : Q (w' + (1 - Q w') • e) = 1 := by
    rw [QuadraticMap.map_add Q, hQe, hB]
    ring
  have hex : polar Q e (w' + (1 - Q w') • e) = 1 := by
    rw [polar_add_right, hew', polar_smul_right_eq, polar_self_eq_zero he, mul_zero, add_zero]
  refine ⟨w' + (1 - Q w') • e, P.perp.add_mem hw'P (P.perp.smul_mem _ heP), ?_, ?_⟩
  · rw [hQx]
    exact one_ne_zero
  · rw [hex]
    exact one_ne_zero

private theorem exists_mem_commutator_fix_and_move_line_caseA1
    (hQ : (polarBilin Q).Nondegenerate) {e v : V} (he : Q e = 0) (he0 : e ≠ 0)
    (hv : ∀ c : K, v ≠ c • e) (hb : polar Q e v = 0) (hQv : Q v ≠ 0) :
    ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      g v = v ∧ ∀ c : K, g e ≠ c • e := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hvv : polar Q v v = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hve : polar Q v e = 0 := by rwa [polar_comm]
  obtain ⟨P, hPe, hvP⟩ := exists_hypPair_of_polar_eq_zero hQ he he0 hb hv
  have hPePf : polar Q e P.f = 1 := by rw [← hPe]; exact P.polar_ef
  have hvPf : polar Q v P.f = 0 := by
    rw [polar_comm]
    exact (HypPair.mem_perp.mp hvP).2
  have hmem : eichler Q P.f v ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    eichler_mem_commutator_of_anisotropic hQ P (u := P.f) (x := v)
      (fun y hy => (HypPair.mem_perp.mp hy).2) hvP hQv
  have hgv : eichler Q P.f v v = v := eichler_apply_of_polar_eq_zero hvPf hvv
  have hge : eichler Q P.f v e = e + v - Q v • P.f := by
    rw [eichler_apply P.Q_f (HypPair.mem_perp.mp hvP).2, hb, zero_add, hPePf]
    simp
  refine ⟨eichler Q P.f v, hmem, hgv, ?_⟩
  intro c hc
  have h0 : polar Q (eichler Q P.f v e) e = 0 := by
    rw [hc, polar_smul_left_eq, polar_self_eq_zero he, mul_zero]
  have h1 : polar Q (eichler Q P.f v e) e = -Q v := by
    rw [hge, polar_sub_left, polar_add_left, polar_smul_left_eq, polar_self_eq_zero he,
      hve, polar_comm Q P.f e, hPePf]
    ring
  rw [h1] at h0
  exact hQv (neg_eq_zero.mp h0)

private theorem exists_mem_commutator_fix_and_move_line_caseA2
    (hQ : (polarBilin Q).Nondegenerate) {e v : V} (he : Q e = 0) (he0 : e ≠ 0)
    (hv : ∀ c : K, v ≠ c • e) (hb : polar Q e v = 0) (hQv : Q v = 0) :
    ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      g v = v ∧ ∀ c : K, g e ≠ c • e := by
  classical
  have hv0 : v ≠ 0 := fun h => hv 0 (by rw [h, zero_smul])
  have hve : polar Q v e = 0 := by rwa [polar_comm]
  have hev : ∀ c : K, e ≠ c • v := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0, zero_smul] at hc
      exact he0 hc
    · exact hv c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  obtain ⟨P, hPe, heP⟩ := exists_hypPair_of_polar_eq_zero hQ hQv hv0 hve hev
  obtain ⟨x, hxP, hQx, hex⟩ :=
    exists_anisotropic_mem_perp_polar_ne_zero hQ P he heP he0
  have hvx : polar Q v x = 0 := by
    rw [← hPe]
    exact (HypPair.mem_perp.mp hxP).1
  have hmem : eichler Q v x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    eichler_mem_commutator_of_anisotropic hQ P (u := v) (x := x)
      (fun y hy => by rw [← hPe]; exact (HypPair.mem_perp.mp hy).1) hxP hQx
  have hgv : eichler Q v x v = v := eichler_apply_self (Q := Q) v x
  have hge : eichler Q v x e = e - polar Q e x • v := by
    rw [eichler_apply hQv hvx, hb, zero_smul, add_zero, mul_zero, add_zero]
  refine ⟨eichler Q v x, hmem, hgv, ?_⟩
  intro c hc
  have h4 : e = c • e + polar Q e x • v :=
    sub_eq_iff_eq_add.mp (hge.symm.trans hc)
  have hrel : polar Q e x • v = (1 - c) • e := by
    calc polar Q e x • v = (c • e + polar Q e x • v) - c • e := by abel
      _ = e - c • e := by rw [← h4]
      _ = (1 - c) • e := by rw [sub_smul, one_smul]
  have hv_eq : v = ((polar Q e x)⁻¹ * (1 - c)) • e := by
    rw [mul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hex, one_smul]
  exact hv _ hv_eq

private theorem exists_mem_commutator_fix_and_move_line_caseB1
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V) {e v : V}
    (he : Q e = 0) (hb : polar Q e v ≠ 0) (hQv : Q v = 0) :
    ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      g v = v ∧ ∀ c : K, g e ≠ c • e := by
  classical
  have hpolar : polar Q v ((polar Q e v)⁻¹ • e) = 1 := by
    rw [polar_smul_right_eq, polar_comm Q v e, inv_mul_cancel₀ hb]
  set P := HypPair.ofPolarEqOne hQv hpolar with hP
  have hPf : P.f = (polar Q e v)⁻¹ • e := by
    rw [hP, HypPair.ofPolarEqOne_f, map_smul_eq_sq, he, mul_zero, zero_smul, sub_zero]
  obtain ⟨z, hzP, hz0⟩ := exists_ne_zero_mem_perp hdim P
  obtain ⟨x, hxP, hQx⟩ := exists_anisotropic_mem_perp hQ P hzP hz0
  have hvx : polar Q v x = 0 := (HypPair.mem_perp.mp hxP).1
  have hx_e : polar Q e x = 0 := by
    have h1 : polar Q ((polar Q e v)⁻¹ • e) x = 0 := by
      simpa [hPf] using (HypPair.mem_perp.mp hxP).2
    rw [polar_smul_left_eq] at h1
    exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hb)
  have hmem : eichler Q v x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    eichler_mem_commutator_of_anisotropic hQ P (u := v) (x := x)
      (fun y hy => (HypPair.mem_perp.mp hy).1) hxP hQx
  have hgv : eichler Q v x v = v := eichler_apply_self (Q := Q) v x
  have hge : eichler Q v x e = e + polar Q e v • x - (Q x * polar Q e v) • v := by
    rw [eichler_apply hQv hvx, hx_e, zero_add]
  refine ⟨eichler Q v x, hmem, hgv, ?_⟩
  intro c hc
  have hx0 : x ≠ 0 := fun h => hQx (by rw [h, QuadraticMap.map_zero])
  obtain ⟨y, hyP, hxy⟩ :=
    (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero hxP hx0
  have hy_e : polar Q e y = 0 := by
    have h1 : polar Q ((polar Q e v)⁻¹ • e) y = 0 := by
      simpa [hPf] using (HypPair.mem_perp.mp hyP).2
    rw [polar_smul_left_eq] at h1
    exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hb)
  have hy_v : polar Q v y = 0 := (HypPair.mem_perp.mp hyP).1
  have h0 : polar Q (eichler Q v x e) y = 0 := by
    rw [hc, polar_smul_left_eq, hy_e, mul_zero]
  have h1 : polar Q (eichler Q v x e) y = polar Q e v * polar Q x y := by
    rw [hge, polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      hy_e, zero_add, hy_v, mul_zero, sub_zero]
  rw [h1] at h0
  exact (mul_ne_zero hb hxy) h0

private theorem exists_mem_commutator_fix_and_move_line_caseB2
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V) {e v : V}
    (he : Q e = 0) (hb : polar Q e v ≠ 0) (hQv : Q v ≠ 0) :
    ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      g v = v ∧ ∀ c : K, g e ≠ c • e := by
  classical
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hvv : polar Q v v = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hpolar : polar Q e ((polar Q e v)⁻¹ • v) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hb]
  set P := HypPair.ofPolarEqOne he hpolar with hP
  have hPf : P.f = (polar Q e v)⁻¹ • v - Q ((polar Q e v)⁻¹ • v) • e := by
    rw [hP, HypPair.ofPolarEqOne_f]
  obtain ⟨z, hzP, hz0⟩ := exists_ne_zero_mem_perp hdim P
  obtain ⟨x, hxP, hQx⟩ := exists_anisotropic_mem_perp hQ P hzP hz0
  have hex : polar Q e x = 0 := (HypPair.mem_perp.mp hxP).1
  have hvx : polar Q v x = 0 := by
    have h1 : polar Q ((polar Q e v)⁻¹ • v - Q ((polar Q e v)⁻¹ • v) • e) x = 0 := by
      simpa [hPf] using (HypPair.mem_perp.mp hxP).2
    rw [polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hex, mul_zero, sub_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hb)
  obtain ⟨t, ht⟩ : ∃ t : K, t ^ 2 = Q v / Q x := by
    obtain ⟨t, ht⟩ := surjective_frobenius K 2 (Q v / Q x)
    exact ⟨t, by rw [← ht, frobenius_def]⟩
  set y : V := t • x with hy
  clear_value y
  have hyP : y ∈ P.perp := by
    rw [hy]
    exact P.perp.smul_mem _ hxP
  have hQy : Q y = Q v := by
    rw [hy, map_smul_eq_sq, ht]
    exact div_mul_cancel₀ (Q v) hQx
  have hQy0 : Q y ≠ 0 := by rw [hQy]; exact hQv
  have he_y : polar Q e y = 0 := by
    rw [hy, polar_smul_right_eq, hex, mul_zero]
  have hv_y : polar Q v y = 0 := by
    rw [hy, polar_smul_right_eq, hvx, mul_zero]
  have huQ : Q (v + y) = 0 := by
    rw [QuadraticMap.map_add Q, hQy, hv_y, add_zero, ← two_mul, h2, zero_mul]
  have huy : polar Q (v + y) y = 0 := by
    rw [polar_add_left, hv_y, polar_self_eq_two_mul, h2, zero_mul, zero_add]
  have hu0 : v + y ≠ 0 := by
    intro h
    have h1 : polar Q e (v + y) = polar Q e v := by
      rw [polar_add_right, he_y, add_zero]
    rw [h, polar_zero_right] at h1
    exact hb h1.symm
  have hy_notin : ∀ c : K, y ≠ c • (v + y) := by
    intro c hc
    have h1 : polar Q e y = c * polar Q e (v + y) := by
      conv_lhs => rw [hc]
      rw [polar_smul_right_eq]
    have h2 : polar Q e (v + y) = polar Q e v := by
      rw [polar_add_right, he_y, add_zero]
    rw [he_y, h2] at h1
    have hc0 : c = 0 := (mul_eq_zero.mp h1.symm).resolve_right hb
    rw [hc0, zero_smul] at hc
    exact hQy0 (by rw [hc, QuadraticMap.map_zero])
  obtain ⟨P', hP'e, hyP'⟩ := exists_hypPair_of_polar_eq_zero hQ huQ hu0 huy hy_notin
  have hmem : eichler Q (v + y) y ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    eichler_mem_commutator_of_anisotropic hQ P' (u := v + y) (x := y)
      (fun z hz => by rw [← hP'e]; exact (HypPair.mem_perp.mp hz).1) hyP' hQy0
  have hvu : polar Q v (v + y) = 0 := by
    rw [polar_add_right, hvv, hv_y, add_zero]
  have hgv : eichler Q (v + y) y v = v := eichler_apply_of_polar_eq_zero hvu hv_y
  have hge : eichler Q (v + y) y e =
      e + polar Q e v • y - (Q y * polar Q e v) • (v + y) := by
    rw [eichler_apply huQ huy,
      show polar Q e (v + y) = polar Q e v by rw [polar_add_right, he_y, add_zero],
      he_y, zero_add]
  refine ⟨eichler Q (v + y) y, hmem, hgv, ?_⟩
  intro c hc
  have hye : polar Q y e = 0 := by rw [polar_comm]; exact he_y
  have hve : polar Q v e = polar Q e v := polar_comm ..
  have h0 : polar Q (eichler Q (v + y) y e) e = 0 := by
    rw [hc, polar_smul_left_eq, polar_self_eq_zero he, mul_zero]
  have h1 : polar Q (eichler Q (v + y) y e) e =
      -(Q v * polar Q e v * polar Q e v) := by
    rw [hge, polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq,
      polar_self_eq_zero he, hye, polar_add_left, hve, hye, add_zero, hQy]
    ring
  rw [h1] at h0
  exact (mul_ne_zero (mul_ne_zero hQv hb) hb) (neg_eq_zero.mp h0)

theorem exists_mem_commutator_fix_and_move_line (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 4 ≤ Module.finrank K V) {e v : V} (he : Q e = 0) (he0 : e ≠ 0)
    (hv : ∀ c : K, v ≠ c • e) :
    ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      g v = v ∧ ∀ c : K, g e ≠ c • e := by
  classical
  by_cases hb : polar Q e v = 0
  · by_cases hQv : Q v = 0
    · exact exists_mem_commutator_fix_and_move_line_caseA2 hQ he he0 hv hb hQv
    · exact exists_mem_commutator_fix_and_move_line_caseA1 hQ he he0 hv hb hQv
  · by_cases hQv : Q v = 0
    · exact exists_mem_commutator_fix_and_move_line_caseB1 hQ hdim he hb hQv
    · exact exists_mem_commutator_fix_and_move_line_caseB2 hQ hdim he hb hQv

end CFSG.ClassicalGroups.Orthogonal
