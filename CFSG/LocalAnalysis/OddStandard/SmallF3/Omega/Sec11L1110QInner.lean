module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Q8

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {E : Type} [Group E] {z : E} {Q1 Q2 : Subgroup E}

private theorem conj_eqOn_of_closure_pair {Q : Subgroup E} {s u a b : E}
    (hQ : Q = Subgroup.closure ({a, b} : Set E))
    (ha : s * a * s⁻¹ = u * a * u⁻¹) (hb : s * b * s⁻¹ = u * b * u⁻¹) :
    ∀ x ∈ Q, s * x * s⁻¹ = u * x * u⁻¹ := by
  have hf : Set.EqOn ((MulAut.conj s).toMonoidHom) ((MulAut.conj u).toMonoidHom)
      ({a, b} : Set E) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using ha
    · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hb
  have h2 := MonoidHom.eqOn_closure hf
  intro x hx
  have hx' : x ∈ Subgroup.closure ({a, b} : Set E) := hQ ▸ hx
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2 hx'

private theorem inner1 (P : Sec11Q8Pair z Q1 Q2) {s : E} (h : ActsTrivModZ z s Q1) :
    ∃ u ∈ Q1, ∀ x ∈ Q1, s * x * s⁻¹ = u * x * u⁻¹ := by
  obtain ⟨a, ha, b, hb, hc, hQ1⟩ := P.exists_gen1
  have hab : a * b = z * b * a := by
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = z * (b * a) := by rw [hc]
      _ = z * b * a := by group
  have h1 : z * (a * b) = b * a := by
    calc z * (a * b) = z * (z * (b * a)) := by rw [hab]; group
      _ = (z * z) * (b * a) := by group
      _ = b * a := by rw [P.z_sq]; group
  have hba : b * a = z * a * b := by
    rw [← h1]; group
  have hab_a : a * b * a⁻¹ = z * b := by
    rw [hab]; group
  have hba_b : b * a * b⁻¹ = z * a := by
    rw [hba]; group
  have hsa : s * a * s⁻¹ = (s * a * s⁻¹ * a⁻¹) * a := by group
  have hsb : s * b * s⁻¹ = (s * b * s⁻¹ * b⁻¹) * b := by group
  have hca : s * a * s⁻¹ * a⁻¹ ∈ zpowers z := h a ha
  have hcb : s * b * s⁻¹ * b⁻¹ ∈ zpowers z := h b hb
  have hba_a : (b * a) * a * (b * a)⁻¹ = z * a := by
    calc (b * a) * a * (b * a)⁻¹ = b * a * b⁻¹ := by group
      _ = z * a := hba_b
  have hba_b' : (b * a) * b * (b * a)⁻¹ = z * b := by
    calc (b * a) * b * (b * a)⁻¹ = b * (a * b * a⁻¹) * b⁻¹ := by group
      _ = b * (z * b) * b⁻¹ := by rw [hab_a]
      _ = (b * z) * (b * b⁻¹) := by group
      _ = b * z := by group
      _ = z * b := P.z_central1 hb
  rcases P.mem_zpowers_iff.mp hca with hca1 | hcaz
  · rcases P.mem_zpowers_iff.mp hcb with hcb1 | hcbz
    · refine ⟨1, one_mem _, ?_⟩
      refine conj_eqOn_of_closure_pair (Q := Q1) hQ1 ?_ ?_
      · rw [hsa, hca1]; group
      · rw [hsb, hcb1]; group
    · refine ⟨a, ha, ?_⟩
      refine conj_eqOn_of_closure_pair (Q := Q1) hQ1 ?_ ?_
      · rw [hsa, hca1]; group
      · rw [hsb, hcbz, hab_a]
  · rcases P.mem_zpowers_iff.mp hcb with hcb1 | hcbz
    · refine ⟨b, hb, ?_⟩
      refine conj_eqOn_of_closure_pair (Q := Q1) hQ1 ?_ ?_
      · rw [hsa, hcaz, hba_b]
      · rw [hsb, hcb1]; group
    · refine ⟨b * a, mul_mem hb ha, ?_⟩
      refine conj_eqOn_of_closure_pair (Q := Q1) hQ1 ?_ ?_
      · rw [hsa, hcaz, hba_a]
      · rw [hsb, hcbz, hba_b']

theorem Sec11Q8Pair.triv_inner (P : Sec11Q8Pair z Q1 Q2) {s : E} (h1 : ActsTrivModZ z s Q1)
    (h2 : ActsTrivModZ z s Q2) :
    ∃ b ∈ Q1 ⊔ Q2, ∀ x ∈ Q1 ⊔ Q2, s * x * s⁻¹ = b * x * b⁻¹ := by
  obtain ⟨u, hu, hu_eq⟩ := inner1 P h1
  obtain ⟨u', hu', hu'_eq⟩ := inner1 P.symm h2
  refine ⟨u * u', ?_, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hu')
  · have hQ1conj : ∀ x ∈ Q1, (u * u') * x * (u * u')⁻¹ = u * x * u⁻¹ := by
      intro x hx
      have hc : u' * x = x * u' := (P.comm x hx u' hu').symm
      calc (u * u') * x * (u * u')⁻¹ = u * (u' * x * u'⁻¹) * u⁻¹ := by group
        _ = u * x * u⁻¹ := by
              rw [show u' * x * u'⁻¹ = x by rw [hc]; group]
    have hQ2conj : ∀ x ∈ Q2, (u * u') * x * (u * u')⁻¹ = u' * x * u'⁻¹ := by
      intro x hx
      have hq : u' * x * u'⁻¹ ∈ Q2 := mul_mem (mul_mem hu' hx) (inv_mem hu')
      have hc : u * (u' * x * u'⁻¹) = (u' * x * u'⁻¹) * u := P.comm u hu _ hq
      calc (u * u') * x * (u * u')⁻¹ = u * (u' * x * u'⁻¹) * u⁻¹ := by group
        _ = (u' * x * u'⁻¹) * u * u⁻¹ := by rw [hc]
        _ = u' * x * u'⁻¹ := by group
    intro x hx
    obtain ⟨x1, hx1, x2, hx2, rfl⟩ := P.exists_mul_of_mem_sup hx
    calc s * (x1 * x2) * s⁻¹
        = (s * x1 * s⁻¹) * (s * x2 * s⁻¹) := by group
      _ = (u * x1 * u⁻¹) * (u' * x2 * u'⁻¹) := by rw [hu_eq x1 hx1, hu'_eq x2 hx2]
      _ = (u * u') * (x1 * x2) * (u * u')⁻¹ := by
            rw [← hQ1conj x1 hx1, ← hQ2conj x2 hx2]; group

end CFSG.OddStandard.SmallF3.Omega
