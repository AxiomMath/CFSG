module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84_lemma35 {G : Type} [Group G] {t : G} {S1 S2 T0 T : Subgroup G}
    (ht : t * t = 1) (hT0 : T0 = S1 ⊔ S2) (hT : T = zpowers t ⊔ T0)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) (hinf : S1 ⊓ S2 = ⊥)
    (h12 : ∀ a ∈ S1, t * a * t⁻¹ ∈ S2) (h21 : ∀ a ∈ S2, t * a * t⁻¹ ∈ S1) :
    ∀ u ∈ T, u * u = 1 → u ∉ T0 → ∃ a ∈ S1, u = a * t * a⁻¹ := by
  intro u huT hu2 huT0
  have hnorm : ∀ x ∈ T0, t * x * t⁻¹ ∈ T0 := by
    have hle : S1 ⊔ S2 ≤ T0.comap (MulAut.conj t) := by
      refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_comap]
        change t * a * t⁻¹ ∈ T0
        rw [hT0]
        exact Subgroup.mem_sup_right (h12 a ha)
      · intro a ha
        rw [Subgroup.mem_comap]
        change t * a * t⁻¹ ∈ T0
        rw [hT0]
        exact Subgroup.mem_sup_left (h21 a ha)
    intro x hx
    have h := hle (hT0 ▸ hx)
    rw [Subgroup.mem_comap] at h
    change t * x * t⁻¹ ∈ T0 at h
    exact h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let K : Subgroup G :=
    { carrier := {x : G | x ∈ T0 ∨ x * t ∈ T0}
      one_mem' := Or.inl T0.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (T0.mul_mem hx hy)
        · exact Or.inr (by simpa [mul_assoc] using T0.mul_mem hx hy)
        · have hw : t * y * t ∈ T0 := by
            have h := hnorm y hy
            rwa [htinv] at h
          refine Or.inr ?_
          have h : (x * t) * (t * y * t) ∈ T0 := T0.mul_mem hx hw
          have heq : (x * y) * t = (x * t) * (t * y * t) := by
            calc
              (x * y) * t = x * (y * t) := by group
              _ = x * ((t * t) * (y * t)) := by rw [ht, one_mul]
              _ = (x * t) * (t * y * t) := by group
          rwa [← heq] at h
        · have hw : t * y ∈ T0 := by
            have h := hnorm (y * t) hy
            rwa [show t * (y * t) * t⁻¹ = t * y from by group] at h
          refine Or.inl ?_
          have h : (x * t) * (t * y) ∈ T0 := T0.mul_mem hx hw
          have heq : x * y = (x * t) * (t * y) := by
            calc
              x * y = x * ((t * t) * y) := by rw [ht, one_mul]
              _ = (x * t) * (t * y) := by group
          rwa [← heq] at h
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (T0.inv_mem hx)
        · refine Or.inr ?_
          have hw : t * (x * t)⁻¹ * t ∈ T0 := by
            have h := hnorm (x * t)⁻¹ (T0.inv_mem hx)
            rwa [htinv] at h
          have hx' : x = (x * t) * t := by rw [mul_assoc, ht, mul_one]
          have hxinv : x⁻¹ = t * (x * t)⁻¹ := by
            conv_lhs => rw [hx']
            rw [mul_inv_rev, htinv]
          rw [hxinv]
          exact hw }
  have hT0K : T0 ≤ K := fun x hx => (show x ∈ T0 ∨ x * t ∈ T0 from Or.inl hx)
  have hzpK : zpowers t ≤ K := by
    rw [Subgroup.zpowers_le]
    exact (show t ∈ T0 ∨ t * t ∈ T0 from Or.inr (by rw [ht]; exact T0.one_mem))
  have hTK : T ≤ K := by
    rw [hT]
    exact sup_le hzpK hT0K
  have huK : u ∈ K := hTK huT
  change u ∈ T0 ∨ u * t ∈ T0 at huK
  rcases huK with hu0 | hut
  · exact absurd hu0 huT0
  have hdec : ∃ s1 ∈ S1, ∃ s2 ∈ S2, s1 * s2 = u * t := by
    have hx : u * t ∈ S1 ⊔ S2 := hT0 ▸ hut
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun z _ => ∃ s1 ∈ S1, ∃ s2 ∈ S2, s1 * s2 = z)
      ?_ ?_ ?_ ?_ hx
    · rintro z (hz | hz)
      · exact ⟨z, hz, 1, S2.one_mem, by simp⟩
      · exact ⟨1, S1.one_mem, z, hz, by simp⟩
    · exact ⟨1, S1.one_mem, 1, S2.one_mem, by simp⟩
    · rintro a b _ _ ⟨s1, hs1, s2, hs2, rfl⟩ ⟨s1', hs1', s2', hs2', rfl⟩
      refine ⟨s1 * s1', S1.mul_mem hs1 hs1', s2 * s2', S2.mul_mem hs2 hs2', ?_⟩
      calc
        (s1 * s1') * (s2 * s2') = s1 * (s1' * (s2 * s2')) := by group
        _ = s1 * ((s1' * s2) * s2') := by group
        _ = s1 * ((s2 * s1') * s2') := by rw [hcomm s1' hs1' s2 hs2]
        _ = (s1 * s2) * (s1' * s2') := by group
    · rintro a _ ⟨s1, hs1, s2, hs2, rfl⟩
      refine ⟨s1⁻¹, S1.inv_mem hs1, s2⁻¹, S2.inv_mem hs2, ?_⟩
      rw [mul_inv_rev]
      exact hcomm s1⁻¹ (S1.inv_mem hs1) s2⁻¹ (S2.inv_mem hs2)
  obtain ⟨s1, hs1, s2, hs2, hprod⟩ := hdec
  set p : G := t * s1 * t⁻¹ with hp_def
  set q : G := t * s2 * t⁻¹ with hq_def
  have hp : p ∈ S2 := by rw [hp_def]; exact h12 s1 hs1
  have hq : q ∈ S1 := by rw [hq_def]; exact h21 s2 hs2
  have hu_eq : u = s1 * s2 * t := by
    have h1 : u = (u * t) * t := by rw [mul_assoc, ht, mul_one]
    rw [h1, ← hprod]
  have hpq_eq : p * q = t * s1 * s2 * t := by
    rw [hp_def, hq_def]
    calc
      (t * s1 * t⁻¹) * (t * s2 * t⁻¹) = t * s1 * (t⁻¹ * t) * s2 * t⁻¹ := by group
      _ = t * s1 * s2 * t⁻¹ := by rw [inv_mul_cancel, mul_one]
      _ = t * s1 * s2 * t := by rw [htinv]
  have h_rearr : s1 * s2 * (p * q) = (s1 * q) * (s2 * p) := by
    have hqs2 : q * s2 = s2 * q := hcomm q hq s2 hs2
    have hqp : q * p = p * q := hcomm q hq p hp
    calc
      s1 * s2 * (p * q) = s1 * s2 * (q * p) := by rw [hqp]
      _ = s1 * ((s2 * q) * p) := by group
      _ = s1 * ((q * s2) * p) := by rw [← hqs2]
      _ = (s1 * q) * (s2 * p) := by group
  have hLHS : u * u = (s1 * q) * (s2 * p) := by
    calc
      u * u = (s1 * s2 * t) * (s1 * s2 * t) := by rw [hu_eq]
      _ = s1 * s2 * (t * s1 * s2 * t) := by group
      _ = s1 * s2 * (p * q) := by rw [hpq_eq]
      _ = (s1 * q) * (s2 * p) := h_rearr
  have hpq : (s1 * q) * (s2 * p) = 1 := by
    rw [hLHS] at hu2
    exact hu2
  have hdis : Disjoint S1 S2 := disjoint_iff.mpr hinf
  have hsq : s1 * q = 1 :=
    (Subgroup.disjoint_iff_mul_eq_one.mp hdis (S1.mul_mem hs1 hq)
      (S2.mul_mem hs2 hp) hpq).1
  have hsp : s2 * p = 1 :=
    (Subgroup.disjoint_iff_mul_eq_one.mp hdis (S1.mul_mem hs1 hq)
      (S2.mul_mem hs2 hp) hpq).2
  have hq_eq : q = s1⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have hp_eq : p = s2⁻¹ := eq_inv_of_mul_eq_one_right hsp
  have hs2_eq : s2 = t * s1⁻¹ * t⁻¹ := by
    have h2 : s2 = p⁻¹ := by rw [hp_eq, inv_inv]
    rw [h2, hp_def]
    group
  refine ⟨s1, hs1, ?_⟩
  calc
    u = s1 * s2 * t := hu_eq
    _ = s1 * (t * s1⁻¹ * t⁻¹) * t := by rw [hs2_eq]
    _ = s1 * t * s1⁻¹ := by group

end CFSG.OddStandard.SmallF3.Omega
