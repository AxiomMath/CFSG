module

public import CFSG.ClassicalInvolution.Q3.Q3T6XChain
public import CFSG.ClassicalInvolution.Q3.Q3T6XStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement


section Core

variable {F : Type} [Group F] [Finite F]

theorem bstar_of_min {S : Set F} (hD : DiagInputNormOn F S) {J K : Subgroup F} {t z : F}
    (hJ : Mem3 J t) (hK : Mem3 K z) (htS : t ∈ S) (hzS : z ∈ S) {a : F} (haJ : a ∈ J)
    (ha4 : orderOf a = 4) (haz : a * z = z * a) :
    t ∈ Subgroup.normalizer (K : Set F) := by
  classical
  by_contra hu
  have ha2 : a * a = t := mul_self_eq_of_orderOf_four hJ.isUniqueInvolution haJ ha4
  have hu2 : t * t = 1 := hJ.mul_self
  have hz2 : z * z = 1 := hK.mul_self
  have hur : t * z = z * t := by rw [← ha2, mul_assoc, haz, ← mul_assoc, haz, mul_assoc]
  have hne : K ≠ conjSub t K := fun h => hu (map_conj_eq_iff_mem_normalizer.mp h.symm)
  have hne' : K ≠ conjSub (a * a) K := by rwa [ha2]
  have hainv : a⁻¹ = a * (a * a) := inv_eq_mul_mul_of_orderOf_four ha4
  have hzJ : z ∈ Subgroup.normalizer (J : Set F) :=
    hJ.mem_normalizer_of_commute_of_mem_noncentral haJ (isPGroup_zpowers_of_orderOf_four ha4)
      (by rw [Nat.card_zpowers, ha4]; omega) haz.symm
  obtain ⟨R, hR2, haR, hRK, h1, h2, h3, hconjR⟩ := exists_quad_sylow hK ha4 haz hne'
  obtain ⟨q, hqV, g, hgV, hq2, hg2, hqg⟩ := hK.exists_two_sq_elements hRK
  have hzc : a * z * a⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr haz
  obtain ⟨q1, hq1d⟩ : ∃ q1 : F, q1 = a * q * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨q2, hq2d⟩ : ∃ q2 : F, q2 = a * q1 * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨q3, hq3d⟩ : ∃ q3 : F, q3 = a * q2 * a⁻¹ := ⟨_, rfl⟩
  have hq1 : q1 ∈ R ⊓ conjSub a K := hq1d ▸ hconjR q hqV
  have hq2m : q2 ∈ R ⊓ conjSub (a * a) K := by
    refine ⟨hq2d ▸ R.mul_mem (R.mul_mem haR hq1.1) (R.inv_mem haR), ?_⟩
    have := conj_mem_conjSub (n := a) hq1.2
    rw [← conjSub_mul, ← hq2d] at this
    exact this
  have hq3m : q3 ∈ R ⊓ conjSub a⁻¹ K := by
    refine ⟨hq3d ▸ R.mul_mem (R.mul_mem haR hq2m.1) (R.inv_mem haR), ?_⟩
    have := conj_mem_conjSub (n := a) hq2m.2
    rw [← conjSub_mul, ← hainv, ← hq3d] at this
    exact this
  have hs1 : q1 * q1 = z := by
    rw [hq1d]
    calc a * q * a⁻¹ * (a * q * a⁻¹) = a * (q * q) * a⁻¹ := by group
      _ = z := by rw [hq2, hzc]
  have hs2 : q2 * q2 = z := by
    rw [hq2d]
    calc a * q1 * a⁻¹ * (a * q1 * a⁻¹) = a * (q1 * q1) * a⁻¹ := by group
      _ = z := by rw [hs1, hzc]
  have hs3 : q3 * q3 = z := by
    rw [hq3d]
    calc a * q2 * a⁻¹ * (a * q2 * a⁻¹) = a * (q2 * q2) * a⁻¹ := by group
      _ = z := by rw [hs2, hzc]
  have c01 : q * q1 = q1 * q := h1 q hqV q1 hq1
  have c02 : q * q2 = q2 * q := h2 q hqV q2 hq2m
  have c03 : q * q3 = q3 * q := h3 q hqV q3 hq3m
  have c12 : q1 * q2 = q2 * q1 := by
    have := conj_comm_aux (a := a) c01
    rw [← hq1d, ← hq2d] at this
    exact this
  have c13 : q1 * q3 = q3 * q1 := by
    have := conj_comm_aux (a := a) c02
    rw [← hq1d, ← hq3d] at this
    exact this
  have c23 : q2 * q3 = q3 * q2 := by
    have := conj_comm_aux (a := a) c12
    rw [← hq2d, ← hq3d] at this
    exact this
  have hg1 : g * q1 = q1 * g := h1 g hgV q1 hq1
  have hg2' : g * q2 = q2 * g := h2 g hgV q2 hq2m
  have hg3 : g * q3 = q3 * g := h3 g hgV q3 hq3m
  have hq2eq : t * q * t⁻¹ = q2 := by
    rw [← ha2, hq2d, hq1d]
    group
  have hqpg : IsPGroup 2 (Subgroup.zpowers q) :=
    hR2.to_le (Subgroup.zpowers_le.mpr hqV.1)
  have heN : q * q2 ∈ Subgroup.normalizer (J : Set F) := by
    have := hD hK hzS htS hu2 hur hne hJ hzJ hqV.2 hqpg (by rw [hq2eq]; exact c02)
    rwa [hq2eq] at this
  have hyJ : q * q2 * q3⁻¹ * q1⁻¹ ∈ J := by
    have h1' : q * q2 * a * (q * q2)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp heN a).mp haJ
    have h2' := J.mul_mem h1' (J.inv_mem haJ)
    have e : q * q2 * a * (q * q2)⁻¹ * a⁻¹ = q * q2 * q3⁻¹ * q1⁻¹ := by
      rw [hq3d, hq1d]
      group
    rwa [e] at h2'
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hy2 : (q * q2 * q3⁻¹ * q1⁻¹) * (q * q2 * q3⁻¹ * q1⁻¹) = 1 := by
    have hPS : Commute (q * q2) (q3⁻¹ * q1⁻¹) :=
      Commute.mul_left (Commute.mul_right (Commute.inv_right (show Commute q q3 from c03))
          (Commute.inv_right (show Commute q q1 from c01)))
        (Commute.mul_right (Commute.inv_right (show Commute q2 q3 from c23))
          (Commute.inv_right (show Commute q2 q1 from (show Commute q1 q2 from c12).symm)))
    have hPP : (q * q2) * (q * q2) = 1 := by
      calc (q * q2) * (q * q2) = q * (q2 * q) * q2 := by group
        _ = q * (q * q2) * q2 := by rw [← c02]
        _ = (q * q) * (q2 * q2) := by group
        _ = 1 := by rw [hq2, hs2]; exact hz2
    have hSS : (q3⁻¹ * q1⁻¹) * (q3⁻¹ * q1⁻¹) = 1 := by
      have hc : q1⁻¹ * q3⁻¹ = q3⁻¹ * q1⁻¹ :=
        (Commute.inv_inv (show Commute q1 q3 from c13)).eq
      calc (q3⁻¹ * q1⁻¹) * (q3⁻¹ * q1⁻¹) = q3⁻¹ * (q1⁻¹ * q3⁻¹) * q1⁻¹ := by group
        _ = q3⁻¹ * (q3⁻¹ * q1⁻¹) * q1⁻¹ := by rw [hc]
        _ = (q3⁻¹ * q3⁻¹) * (q1⁻¹ * q1⁻¹) := by group
        _ = (q3 * q3)⁻¹ * (q1 * q1)⁻¹ := by rw [mul_inv_rev, mul_inv_rev]
        _ = 1 := by rw [hs3, hs1, hzi]; exact hz2
    calc (q * q2 * q3⁻¹ * q1⁻¹) * (q * q2 * q3⁻¹ * q1⁻¹)
        = ((q * q2) * (q3⁻¹ * q1⁻¹)) * ((q * q2) * (q3⁻¹ * q1⁻¹)) := by group
      _ = (q * q2) * ((q3⁻¹ * q1⁻¹) * (q * q2)) * (q3⁻¹ * q1⁻¹) := by group
      _ = (q * q2) * ((q * q2) * (q3⁻¹ * q1⁻¹)) * (q3⁻¹ * q1⁻¹) := by rw [← hPS.eq]
      _ = ((q * q2) * (q * q2)) * ((q3⁻¹ * q1⁻¹) * (q3⁻¹ * q1⁻¹)) := by group
      _ = 1 := by rw [hPP, hSS]; group
  have hK₁z : Mem3 (conjSub a K) z := hK.conj_of_commute haz
  have hK₂z : Mem3 (conjSub (a * a) K) z :=
    hK.conj_of_commute (by rw [mul_assoc, haz, ← mul_assoc, haz, mul_assoc])
  have hK₃z : Mem3 (conjSub a⁻¹ K) z := hK.conj_of_commute (inv_comm_of_comm haz)
  have hNK : ∀ x ∈ conjSub a K, x ∈ Subgroup.normalizer (K : Set F) := fun x hx =>
    hK₁z.le_normalizer_of_same hK hx
  have hNK₂ : ∀ x ∈ conjSub (a * a) K, x ∈ Subgroup.normalizer (K : Set F) := fun x hx =>
    hK₂z.le_normalizer_of_same hK hx
  have hNK₃ : ∀ x ∈ conjSub a⁻¹ K, x ∈ Subgroup.normalizer (K : Set F) := fun x hx =>
    hK₃z.le_normalizer_of_same hK hx
  rcases hJ.isUniqueInvolution.unique _ hyJ hy2 with hy | hy
  ·
    have hqq : q * q2 = q1 * q3 := by
      have := mul_inv_eq_one.mp hy
      exact mul_inv_eq_iff_eq_mul.mp this
    have hgq : g * q = q * g := by
      have e1 : g * (q * q2) = (q * q2) * g := by
        rw [hqq]
        calc g * (q1 * q3) = (g * q1) * q3 := by group
          _ = (q1 * g) * q3 := by rw [hg1]
          _ = q1 * (g * q3) := by group
          _ = q1 * (q3 * g) := by rw [hg3]
          _ = (q1 * q3) * g := by group
      have e2 : (g * q) * q2 = (q * g) * q2 := by
        calc (g * q) * q2 = g * (q * q2) := by group
          _ = (q * q2) * g := e1
          _ = q * (q2 * g) := by group
          _ = q * (g * q2) := by rw [hg2']
          _ = (q * g) * q2 := by group
      exact mul_right_cancel e2
    apply hqg
    calc (q * g) * (q * g) = q * (g * q) * g := by group
      _ = q * (q * g) * g := by rw [hgq]
      _ = (q * q) * (g * g) := by group
      _ = 1 := by rw [hq2, hg2]; exact hz2
  ·
    apply hu
    rw [← hy]
    have hq0N : q ∈ Subgroup.normalizer (K : Set F) := Subgroup.le_normalizer hqV.2
    exact (Subgroup.normalizer (K : Set F)).mul_mem
      ((Subgroup.normalizer (K : Set F)).mul_mem
        ((Subgroup.normalizer (K : Set F)).mul_mem hq0N (hNK₂ q2 hq2m.2))
        ((Subgroup.normalizer (K : Set F)).inv_mem (hNK₃ q3 hq3m.2)))
      ((Subgroup.normalizer (K : Set F)).inv_mem (hNK q1 hq1.2))

theorem bstarOn_of_diag {S : Set F} (hD : DiagInputNormOn F S) : BstarOn F S := by
  intro J K t z hJ hK htS hzS a haJ ha4 haz
  exact bstar_of_min hD hJ hK htS hzS haJ ha4 haz

theorem symOn_of_min {S : Set F} (h : Fusion3MinOn F S) : SymOn F S := by
  intro X Y x y hX hY hxS hyS hxY
  by_cases hc : ∃ a ∈ Y, orderOf a = 4 ∧ a * x = x * a
  · obtain ⟨a, haY, ha4, hax⟩ := hc
    exact bstar_of_min h.diagNorm hY hX hyS hxS haY ha4 hax
  · push Not at hc
    exact h.symOuter hX hY hxS hyS hxY hc

theorem core_min {S : Set F} (hS : ∀ x ∈ S, ∀ g : F, g * x * g⁻¹ ∈ S) (h : Fusion3MinOn F S)
    {K : Subgroup F} {z : F} (hK : Mem3 K z) (hzS : z ∈ S) {J : Subgroup F} {t : F}
    (hJ : Mem3 J t) (htS : t ∈ S) (hne : t ≠ z) (htK : t ∈ Subgroup.normalizer (K : Set F))
    {v : F} (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvz : v * z = z * v) :
    v ∈ Subgroup.normalizer (K : Set F) := by
  have hv4 : v ^ 4 = 1 := hJ.pow_four_of_isPGroup hvJ hv2
  have hdvd : orderOf v ∣ 4 := orderOf_dvd_of_pow_eq_one hv4
  have hcases : orderOf v = 1 ∨ orderOf v = 2 ∨ orderOf v = 4 := by
    obtain ⟨i, hi, hi'⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf v ∣ 2 ^ 2 by simpa using hdvd)
    interval_cases i
    · left; simpa using hi'
    · right; left; simpa using hi'
    · right; right; simpa using hi'
  rcases hcases with h1 | h2 | h4
  · rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  · have hsq : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [h2, pow_two] at this
    rcases hJ.isUniqueInvolution.unique v hvJ hsq with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact htK
  · have hvv : v * v = t := mul_self_eq_of_orderOf_four hJ.isUniqueInvolution hvJ h4
    exact core_four_min hS (bstarOn_of_diag h.diagNorm) (symOn_of_min h) hK hzS hJ htS hne hvJ h4
      hvz (hvv ▸ htK)

theorem mem_normalizer_of_core_min {S : Set F} (hS : ∀ x ∈ S, ∀ g : F, g * x * g⁻¹ ∈ S)
    (h : Fusion3MinOn F S) {J K : Subgroup F} {t z : F} (hJ : Mem3 J t) (hK : Mem3 K z)
    (htS : t ∈ S) (hzS : z ∈ S) (htK : t ∈ Subgroup.normalizer (K : Set F)) {y : F}
    (hyJ : y ∈ J) (hy2 : IsPGroup 2 (Subgroup.zpowers y)) (hyz : y * z = z * y) :
    y ∈ Subgroup.normalizer (K : Set F) := by
  by_cases htz : t = z
  · subst htz
    by_cases hJK : J = K
    · subst hJK
      exact Subgroup.le_normalizer hyJ
    · exact (hK.twin_facts hJ (Ne.symm hJK)).1 hyJ
  · exact core_min hS h hK hzS hJ htS htz htK hyJ hy2 hyz

theorem twoElementsNormalize_of_min {K : Subgroup F} {z : F} (hK : Mem3 K z)
    (h : Fusion3MinOn F (invClass z)) : Hat2A7R.TwoElementsNormalize K z := by
  have hS : ∀ x ∈ invClass z, ∀ g : F, g * x * g⁻¹ ∈ invClass z := by
    rintro x ⟨g, rfl⟩ g'
    exact ⟨g' * g, by group⟩
  have hzS : z ∈ invClass z := ⟨1, by group⟩
  intro k hkK hk2 hkz g hg
  have hJ : Mem3 (conjSub g K) (g * z * g⁻¹) := hK.conj g
  have hvJ : g * k * g⁻¹ ∈ conjSub g K := conj_mem_conjSub hkK
  have hv2 : IsPGroup 2 (Subgroup.zpowers (g * k * g⁻¹)) := by
    have := AscHypOmega.isPGroup_zpowers_conj hk2 g
    simpa using this
  have hvz : (g * k * g⁻¹) * z = z * (g * k * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hk4' : k ^ 4 = 1 := hK.pow_four_of_isPGroup hkK hk2
  have hk4 : orderOf k = 4 := by
    have hdvd : orderOf k ∣ 4 := orderOf_dvd_of_pow_eq_one hk4'
    have hcases : orderOf k = 1 ∨ orderOf k = 2 ∨ orderOf k = 4 := by
      obtain ⟨i, hi, hi'⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf k ∣ 2 ^ 2 by simpa using hdvd)
      interval_cases i
      · left; simpa using hi'
      · right; left; simpa using hi'
      · right; right; simpa using hi'
    rcases hcases with h1 | h2 | h4
    · exact absurd (by rw [orderOf_eq_one_iff.mp h1]; exact Subgroup.one_mem _) hkz
    · have hsq : k * k = 1 := by
        have := pow_orderOf_eq_one k
        rwa [h2, pow_two] at this
      rcases hK.isUniqueInvolution.unique k hkK hsq with h | h
      · exact absurd (by rw [h]; exact Subgroup.one_mem _) hkz
      · exact absurd (by rw [h]; exact Subgroup.mem_zpowers z) hkz
    · exact h4
  have hv4 : orderOf (g * k * g⁻¹) = 4 := by rw [orderOf_conj_eq]; exact hk4
  have htS : g * z * g⁻¹ ∈ invClass z := ⟨g, rfl⟩
  have htK : g * z * g⁻¹ ∈ Subgroup.normalizer (K : Set F) :=
    bstar_of_min h.diagNorm hJ hK htS hzS hvJ hv4 hvz
  exact mem_normalizer_of_core_min hS h hJ hK htS hzS htK hvJ hv2 hvz

end Core

end CFSG.ClassicalInvolution.Q3.Q3T6X
