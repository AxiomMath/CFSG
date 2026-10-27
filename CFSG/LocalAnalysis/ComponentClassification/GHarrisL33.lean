module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL32f
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL33Facts

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem SCert.SE.invRep_five : SE.invRep 5 = SE.gen 6 := by decide

namespace GHSylow

variable (D : GHSylow G)

abbrev a : G := D.toG (SE.invRep 7)

abbrev al : G := D.toG (SE.invRep 8)

omit [Finite G] in
theorem card_filter_le_of_conj {g : G} (p q : SE → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ c : SE, p c → ∃ c' : SE, D.toG c' = g⁻¹ * D.toG c * g ∧ q c') :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card := by
  choose f hf using h
  let F : {c : SE // p c} → {c : SE // q c} := fun c => ⟨f c.1 c.2, (hf c.1 c.2).2⟩
  have hF : Function.Injective F := by
    intro c₁ c₂ h12
    have h2 := congrArg D.toG (congrArg Subtype.val h12 : f c₁.1 c₁.2 = f c₂.1 c₂.2)
    rw [(hf _ _).1, (hf _ _).1] at h2
    have h3 : D.toG c₁.1 = D.toG c₂.1 := by
      have := congrArg (fun y => g * y * g⁻¹) h2
      simpa [mul_assoc] using this
    exact Subtype.ext (D.toG_injective h3)
  have := Fintype.card_le_of_injective F hF
  rwa [Fintype.card_subtype, Fintype.card_subtype] at this

omit [Finite G] in
theorem conj_conj (g h u : G) : (g * h)⁻¹ * u * (g * h) = h⁻¹ * (g⁻¹ * u * g) * h := by group

omit [Finite G] in
theorem not_conj_z_of_conj_x
    [Finite G] {g : G} (c : SE)
    (h : g⁻¹ * D.z * g = D.toG (c⁻¹ * SE.gen 6 * c)) : False := by
  apply D.not_conj_x_z
  refine ⟨D.toG c * g⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv] at h
  calc (D.toG c * g⁻¹)⁻¹ * D.x * (D.toG c * g⁻¹) =
      g * ((D.toG c)⁻¹ * D.x * D.toG c) * g⁻¹ := by group
    _ = g * (g⁻¹ * D.z * g) * g⁻¹ := by rw [h]
    _ = D.z := by group

theorem not_conj_x_a_and_al :
    ¬ ((∃ g : G, g⁻¹ * D.x * g = D.a) ∧ ∃ g : G, g⁻¹ * D.x * g = D.al) := by
  classical
  rintro ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩⟩
  obtain ⟨g, -, hC⟩ := exists_conj_extremal D.S.isPGroup' D.isSylowOf_X hh₁
  have hpre : ∀ s : SE, s * SE.invRep 7 = SE.invRep 7 * s →
      ∃ s' : SE, D.toG s' = g⁻¹ * D.toG s * g ∧ s' * SE.gen 6 = SE.gen 6 * s' := by
    intro s hs
    have hmem := hC (D.toG s) (mem_inf.mpr ⟨D.toG_mem s, mem_centralizer_singleton_iff.mpr (by
      rw [← map_mul, ← map_mul, hs])⟩)
    obtain ⟨hS, hx⟩ := mem_inf.mp hmem
    obtain ⟨s', hs'⟩ := D.exists_toG hS
    refine ⟨s', hs', D.toG_injective ?_⟩
    have := mem_centralizer_singleton_iff.mp hx
    rw [← hs'] at this
    rw [map_mul, map_mul]
    exact this
  obtain ⟨u, hu, hux⟩ := hpre _ SE.x_comm_a
  obtain ⟨v, hv, hvx⟩ := hpre _ SE.a3a4_comm_a
  have htg : g⁻¹ * D.t * g = D.toG (u⁻¹ * v⁻¹ * u * v) := by
    change g⁻¹ * D.toG (SE.invRep 1) * g = _
    rw [SE.comm_x_a3a4]
    simp only [map_mul, map_inv]
    rw [hu, hv]
    group
  have htz : g⁻¹ * D.t * g = D.z := by
    rw [htg, SE.comm_inv_X u v hux hvx ?_ ?_]
    · apply D.toG_injective
      rw [map_mul, ← htg, map_one]
      calc g⁻¹ * D.t * g * (g⁻¹ * D.t * g) = g⁻¹ * (D.t * D.t) * g := by group
        _ = 1 := by rw [D.t_mul_t]; group
    · intro h1
      apply D.t_ne_one
      have h' : g⁻¹ * D.t * g = 1 := by rw [htg, h1, map_one]
      calc D.t = g * (g⁻¹ * D.t * g) * g⁻¹ := by group
        _ = 1 := by rw [h']; group
  obtain ⟨w, hw, hwx⟩ := hpre (SE.gen 0) (SE.mul_gen0_comm _).symm
  have hw2 : w * w = 1 := D.toG_injective (by
    rw [map_mul, hw, map_one]
    calc g⁻¹ * D.z * g * (g⁻¹ * D.z * g) = g⁻¹ * (D.z * D.z) * g := by group
      _ = 1 := by rw [D.z_mul_z]; group)
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply D.z_ne_one
    have h' : g⁻¹ * D.z * g = 1 := by rw [← hw, map_one]
    calc D.z = g * (g⁻¹ * D.z * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hcard : 32 ≤ (Finset.univ.filter fun c : SE =>
      c * SE.gen 6 = SE.gen 6 * c ∧ c * w = w * c).card := by
    rw [← show (Finset.univ.filter fun c : SE => c * SE.invRep 7 = SE.invRep 7 * c).card = 32 from
      SE.card_filter_comm_invRep 7]
    refine D.card_filter_le_of_conj (g := g) _ _ fun c hc => ?_
    obtain ⟨c', hc', hc'x⟩ := hpre c hc
    refine ⟨c', hc', hc'x, D.toG_injective ?_⟩
    rw [map_mul, map_mul, hc', hw]
    have hcz : D.toG c * D.z = D.z * D.toG c := by
      rw [← map_mul, ← map_mul, SE.mul_gen0_comm]
    calc g⁻¹ * D.toG c * g * (g⁻¹ * D.toG (SE.gen 0) * g) = g⁻¹ * (D.toG c * D.z) * g := by
          group
      _ = g⁻¹ * (D.z * D.toG c) * g := by rw [hcz]
      _ = g⁻¹ * D.toG (SE.gen 0) * g * (g⁻¹ * D.toG c * g) := by group
  have hzg : g⁻¹ * D.z * g = D.t ∨ g⁻¹ * D.z * g = D.t * D.z := by
    rcases SE.large_cent_X w hw2 hw1 hwx hcard with h | h | h | h | h | h | h
    · exfalso
      apply D.z_ne_t
      have h' : g⁻¹ * D.z * g = g⁻¹ * D.t * g := by rw [← hw, h, htz]
      simpa using h'
    · exact Or.inl (by rw [← hw, h])
    · exact Or.inr (by rw [← hw, h, map_mul])
    · exact (D.not_conj_z_of_conj_x 1 (by rw [← hw, h]; simp)).elim
    · exact (D.not_conj_z_of_conj_x (SE.gen 2) (by rw [← hw, h, SE.conj_x_xz])).elim
    · exact (D.not_conj_z_of_conj_x (SE.invRep 3) (by rw [← hw, h, SE.conj_x_xt])).elim
    · exact (D.not_conj_z_of_conj_x (SE.gen 2 * SE.invRep 3) (by
        rw [← hw, h, SE.conj_x_xtz])).elim
  have hv2 : v * v = 1 := D.toG_injective (by
    rw [map_mul, hv, map_one]
    calc g⁻¹ * D.a3a4 * g * (g⁻¹ * D.a3a4 * g) = g⁻¹ * (D.a3a4 * D.a3a4) * g := by group
      _ = 1 := by rw [D.toG_invRep_mul_self 3]; group)
  have hvz : v * SE.gen 0 = SE.gen 0 * v := SE.mul_gen0_comm v
  have hvt : v * SE.invRep 1 = SE.invRep 1 * v := by
    have ha3t : D.a3a4 * D.z = D.z * D.a3a4 := by rw [← map_mul, ← map_mul, SE.mul_gen0_comm]
    have h1 : D.toG v * (g⁻¹ * D.z * g) = (g⁻¹ * D.z * g) * D.toG v := by
      rw [hv]
      calc g⁻¹ * D.a3a4 * g * (g⁻¹ * D.z * g) = g⁻¹ * (D.a3a4 * D.z) * g := by group
        _ = g⁻¹ * (D.z * D.a3a4) * g := by rw [ha3t]
        _ = g⁻¹ * D.z * g * (g⁻¹ * D.a3a4 * g) := by group
    rcases hzg with h | h <;> rw [h] at h1
    · exact D.toG_injective (by rw [map_mul, map_mul]; exact h1)
    · apply D.toG_injective
      rw [map_mul, map_mul]
      have hvz' : D.toG v * D.z = D.z * D.toG v := by rw [← map_mul, ← map_mul, hvz]
      calc D.toG v * D.t = D.toG v * (D.t * D.z) * D.z := by
            rw [mul_assoc (D.toG v), mul_assoc D.t, D.z_mul_z, mul_one]
        _ = D.t * D.z * D.toG v * D.z := by rw [h1]
        _ = D.t * (D.z * D.toG v * D.z) := by group
        _ = D.t * (D.toG v * D.z * D.z) := by rw [← hvz']
        _ = D.t * D.toG v := by rw [mul_assoc (D.toG v), D.z_mul_z, mul_one]
  have hsurj : ∀ y : G, (y = D.z ∨ y = D.t ∨ y = D.t * D.z) →
      ∃ c : G, (c = D.z ∨ c = D.t ∨ c = D.t * D.z) ∧ g⁻¹ * c * g = y := by
    have hmul : g⁻¹ * (D.t * D.z) * g = (g⁻¹ * D.t * g) * (g⁻¹ * D.z * g) := by group
    rintro y (rfl | rfl | rfl)
    · exact ⟨D.t, Or.inr (Or.inl rfl), htz⟩
    · rcases hzg with h | h
      · exact ⟨D.z, Or.inl rfl, h⟩
      · refine ⟨D.t * D.z, Or.inr (Or.inr rfl), ?_⟩
        rw [hmul, htz, h, ← mul_assoc, D.z_comm_t, mul_assoc, D.z_mul_z, mul_one]
    · rcases hzg with h | h
      · refine ⟨D.t * D.z, Or.inr (Or.inr rfl), ?_⟩
        rw [hmul, htz, h, D.z_comm_t]
      · exact ⟨D.z, Or.inl rfl, h⟩
  have hnot : ∀ c : G, (c = D.z ∨ c = D.t ∨ c = D.t * D.z) → D.toG v ≠ g⁻¹ * c * g := by
    rintro c hc hvc
    rw [hv] at hvc
    have ha : D.a3a4 = c := by simpa using hvc
    rcases hc with rfl | rfl | rfl
    · exact SE.a3a4_ne_gen0 (D.toG_injective ha)
    · exact SE.a3a4_ne_t (D.toG_injective ha)
    · exact SE.a3a4_ne_tz (D.toG_injective (by rw [map_mul]; exact ha))
  have hv1 : v ≠ 1 := by
    rintro rfl
    apply D.toG_invRep_ne_one 3
    have h' : g⁻¹ * D.a3a4 * g = 1 := by rw [← hv, map_one]
    calc D.a3a4 = g * (g⁻¹ * D.a3a4 * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hne : ∀ y : SE, (y = SE.gen 0 ∨ y = SE.invRep 1 ∨ y = SE.invRep 1 * SE.gen 0) → v ≠ y := by
    rintro y hy rfl
    obtain ⟨c, hc, hcy⟩ := hsurj (D.toG v) (by
      rcases hy with h | h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (map_mul _ _ _)))
    exact hnot c hc hcy.symm
  obtain ⟨s, hs⟩ := SE.classes_CXt v hv2 hvx hvt hv1 (hne _ (Or.inl rfl))
    (hne _ (Or.inr (Or.inl rfl))) (hne _ (Or.inr (Or.inr rfl)))
  have hconj : ∀ r : SE, s⁻¹ * v * s = r →
      (g * D.toG s)⁻¹ * D.a3a4 * (g * D.toG s) = D.toG r := by
    intro r hr
    rw [conj_conj, ← hv, ← map_inv, ← map_mul, ← map_mul, hr]
  rcases hs with h | h | h
  · rw [SE.invRep_five] at h
    have hc : (g * D.toG s)⁻¹ * D.a3a4 * (g * D.toG s) = D.x := hconj _ h
    apply D.not_conj_x_a3a4
    refine ⟨(g * D.toG s)⁻¹, ?_⟩
    rw [← hc]
    group
  · have hc : (g * D.toG s)⁻¹ * D.a3a4 * (g * D.toG s) = D.a := hconj _ h
    apply D.not_conj_x_a3a4
    refine ⟨h₁ * (g * D.toG s)⁻¹, ?_⟩
    rw [conj_conj, hh₁, ← hc]
    group
  · have hc : (g * D.toG s)⁻¹ * D.a3a4 * (g * D.toG s) = D.al := hconj _ h
    apply D.not_conj_x_a3a4
    refine ⟨h₂ * (g * D.toG s)⁻¹, ?_⟩
    rw [conj_conj, hh₂, ← hc]
    group

end GHSylow

end CFSG.ComponentClassification.GHarris
