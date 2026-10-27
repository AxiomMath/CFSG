module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalStruct

public section

namespace CFSG.QuasithinUnique

section Calc

variable {G : Type} [Group G]

theorem conj_mul_conj (g a b : G) : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by
  group

theorem forall_mem_closure_conj_eq {S : Set G} {h : G} (hS : ∀ a ∈ S, h * a * h⁻¹ = a) :
    ∀ a ∈ Subgroup.closure S, h * a * h⁻¹ = a := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => group
  | mul x y _ _ hx hy =>
    rw [conj_mul_conj, hx, hy]
  | inv x _ hx =>
    have : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
    rw [this, hx]

variable [Finite G]

theorem mem_normalizer_closure_of_gens {S : Set G} {g : G}
    (hS : ∀ a ∈ S, g * a * g⁻¹ ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y _ _ hx hy =>
    rw [conj_mul_conj]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem calc_P1 {zK e t f u v : G} {A : Subgroup G}
    (hA : A = Subgroup.closure ({zK, e, t, f} : Set G))
    (he : e * e = 1) (hf : f * f = 1) (hef : e * f = f * e)
    (hu1 : u * zK * u⁻¹ = zK * e) (hu2 : u * e * u⁻¹ = e) (hu3 : u * t * u⁻¹ = t)
    (hu4 : u * f * u⁻¹ = f * e)
    (hv1 : v * zK * v⁻¹ = zK) (hv2 : v * e * v⁻¹ = e) (hv3 : v * t * v⁻¹ = t * f)
    (hv4 : v * f * v⁻¹ = f) (hne : e ≠ 1) :
    u * v ∈ Subgroup.normalizer (A : Set G) ∧
      (∀ a ∈ A, (u * v) ^ 4 * a * ((u * v) ^ 4)⁻¹ = a) ∧
      ¬ ∀ a ∈ A, (u * v) * (u * v) * a * ((u * v) * (u * v))⁻¹ = a := by
  subst hA
  obtain ⟨g, hg⟩ : ∃ g : G, g = u * v := ⟨_, rfl⟩
  rw [← hg]
  have hzKA : zK ∈ Subgroup.closure ({zK, e, t, f} : Set G) := Subgroup.subset_closure (by simp)
  have heA : e ∈ Subgroup.closure ({zK, e, t, f} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({zK, e, t, f} : Set G) := Subgroup.subset_closure (by simp)
  have hfA : f ∈ Subgroup.closure ({zK, e, t, f} : Set G) := Subgroup.subset_closure (by simp)
  have c1 : g * zK * g⁻¹ = zK * e := by
    calc g * zK * g⁻¹ = u * (v * zK * v⁻¹) * u⁻¹ := by rw [hg]; group
      _ = zK * e := by rw [hv1, hu1]
  have c2 : g * e * g⁻¹ = e := by
    calc g * e * g⁻¹ = u * (v * e * v⁻¹) * u⁻¹ := by rw [hg]; group
      _ = e := by rw [hv2, hu2]
  have c3 : g * t * g⁻¹ = t * (f * e) := by
    calc g * t * g⁻¹ = u * (v * t * v⁻¹) * u⁻¹ := by rw [hg]; group
      _ = (u * t * u⁻¹) * (u * f * u⁻¹) := by rw [hv3, conj_mul_conj]
      _ = t * (f * e) := by rw [hu3, hu4]
  have c4 : g * f * g⁻¹ = f * e := by
    calc g * f * g⁻¹ = u * (v * f * v⁻¹) * u⁻¹ := by rw [hg]; group
      _ = f * e := by rw [hv4, hu4]
  obtain ⟨h, hh⟩ : ∃ h : G, h = g * g := ⟨_, rfl⟩
  have hh' : ∀ a : G, h * a * h⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := fun a => by rw [hh]; group
  have d1 : h * zK * h⁻¹ = zK := by
    rw [hh', c1, conj_mul_conj, c1, c2]
    calc zK * e * e = zK * (e * e) := by group
      _ = zK := by rw [he]; group
  have d2 : h * e * h⁻¹ = e := by rw [hh', c2, c2]
  have d3 : h * t * h⁻¹ = t * e := by
    rw [hh', c3, conj_mul_conj, c3, conj_mul_conj, c4, c2]
    calc t * (f * e) * (f * e * e) = t * ((f * e) * (f * e)) * e := by group
      _ = t * (f * (e * f) * e) * e := by group
      _ = t * (f * (f * e) * e) * e := by rw [hef]
      _ = t * ((f * f) * (e * e)) * e := by group
      _ = t * e := by rw [hf, he]; group
  have d4 : h * f * h⁻¹ = f := by
    rw [hh', c4, conj_mul_conj, c4, c2]
    calc f * e * e = f * (e * e) := by group
      _ = f := by rw [he]; group
  refine ⟨?_, ?_, ?_⟩
  · apply mem_normalizer_closure_of_gens
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha | ha | ha
    · rw [ha, c1]; exact Subgroup.mul_mem _ hzKA heA
    · rw [ha, c2]; exact heA
    · rw [ha, c3]; exact Subgroup.mul_mem _ htA (Subgroup.mul_mem _ hfA heA)
    · rw [ha, c4]; exact Subgroup.mul_mem _ hfA heA
  · have e4 : g ^ 4 = h * h := by rw [hh]; simp [pow_succ, mul_assoc]
    have hg4 : ∀ b : G, g ^ 4 * b * (g ^ 4)⁻¹ = h * (h * b * h⁻¹) * h⁻¹ := fun b => by
      rw [e4]; group
    have hS : ∀ a ∈ ({zK, e, t, f} : Set G), g ^ 4 * a * (g ^ 4)⁻¹ = a := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha | ha | ha
      · rw [ha, hg4, d1, d1]
      · rw [ha, hg4, d2, d2]
      · rw [ha, hg4, d3, conj_mul_conj, d3, d2]
        calc t * e * e = t * (e * e) := by group
          _ = t := by rw [he]; group
      · rw [ha, hg4, d4, d4]
    exact forall_mem_closure_conj_eq hS
  · intro hall
    have := hall t htA
    rw [← hh, d3] at this
    apply hne
    exact mul_left_cancel (this.trans (mul_one t).symm)

theorem calc_P2 {zK e t f u v : G} {A : Subgroup G}
    (hA : A = Subgroup.closure ({zK, e, t, f} : Set G))
    (he : e * e = 1) (hf : f * f = 1)
    (hu1 : u * zK * u⁻¹ = zK * e) (hu2 : u * e * u⁻¹ = e) (hu3 : u * t * u⁻¹ = t)
    (hu4 : u * f * u⁻¹ = f)
    (hv1 : v * zK * v⁻¹ = zK) (hv2 : v * e * v⁻¹ = e * f) (hv3 : v * t * v⁻¹ = t * f)
    (hv4 : v * f * v⁻¹ = f) (hne : f ≠ 1) :
    u * v ∈ Subgroup.normalizer (A : Set G) ∧
      (∀ a ∈ A, (u * v) ^ 4 * a * ((u * v) ^ 4)⁻¹ = a) ∧
      ¬ ∀ a ∈ A, (u * v) * (u * v) * a * ((u * v) * (u * v))⁻¹ = a := by
  subst hA
  obtain ⟨g, hg⟩ : ∃ g : G, g = u * v := ⟨_, rfl⟩
  rw [← hg]
  have hzKA : zK ∈ Subgroup.closure ({zK, e, t, f} : Set G) := Subgroup.subset_closure (by simp)
  have heA : e ∈ Subgroup.closure ({zK, e, t, f} : Set G) := Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({zK, e, t, f} : Set G) := Subgroup.subset_closure (by simp)
  have hfA : f ∈ Subgroup.closure ({zK, e, t, f} : Set G) := Subgroup.subset_closure (by simp)
  have c1 : g * zK * g⁻¹ = zK * e := by
    calc g * zK * g⁻¹ = u * (v * zK * v⁻¹) * u⁻¹ := by rw [hg]; group
      _ = zK * e := by rw [hv1, hu1]
  have c2 : g * e * g⁻¹ = e * f := by
    calc g * e * g⁻¹ = u * (v * e * v⁻¹) * u⁻¹ := by rw [hg]; group
      _ = (u * e * u⁻¹) * (u * f * u⁻¹) := by rw [hv2, conj_mul_conj]
      _ = e * f := by rw [hu2, hu4]
  have c3 : g * t * g⁻¹ = t * f := by
    calc g * t * g⁻¹ = u * (v * t * v⁻¹) * u⁻¹ := by rw [hg]; group
      _ = (u * t * u⁻¹) * (u * f * u⁻¹) := by rw [hv3, conj_mul_conj]
      _ = t * f := by rw [hu3, hu4]
  have c4 : g * f * g⁻¹ = f := by
    calc g * f * g⁻¹ = u * (v * f * v⁻¹) * u⁻¹ := by rw [hg]; group
      _ = f := by rw [hv4, hu4]
  obtain ⟨h, hh⟩ : ∃ h : G, h = g * g := ⟨_, rfl⟩
  have hh' : ∀ a : G, h * a * h⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := fun a => by rw [hh]; group
  have d1 : h * zK * h⁻¹ = zK * f := by
    rw [hh', c1, conj_mul_conj, c1, c2]
    calc zK * e * (e * f) = zK * (e * e) * f := by group
      _ = zK * f := by rw [he]; group
  have d2 : h * e * h⁻¹ = e := by
    rw [hh', c2, conj_mul_conj, c2, c4]
    calc e * f * f = e * (f * f) := by group
      _ = e := by rw [hf]; group
  have d3 : h * t * h⁻¹ = t := by
    rw [hh', c3, conj_mul_conj, c3, c4]
    calc t * f * f = t * (f * f) := by group
      _ = t := by rw [hf]; group
  have d4 : h * f * h⁻¹ = f := by rw [hh', c4, c4]
  refine ⟨?_, ?_, ?_⟩
  · apply mem_normalizer_closure_of_gens
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha | ha | ha
    · rw [ha, c1]; exact Subgroup.mul_mem _ hzKA heA
    · rw [ha, c2]; exact Subgroup.mul_mem _ heA hfA
    · rw [ha, c3]; exact Subgroup.mul_mem _ htA hfA
    · rw [ha, c4]; exact hfA
  · have e4 : g ^ 4 = h * h := by rw [hh]; simp [pow_succ, mul_assoc]
    have hg4 : ∀ b : G, g ^ 4 * b * (g ^ 4)⁻¹ = h * (h * b * h⁻¹) * h⁻¹ := fun b => by
      rw [e4]; group
    have hS : ∀ a ∈ ({zK, e, t, f} : Set G), g ^ 4 * a * (g ^ 4)⁻¹ = a := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha | ha | ha | ha
      · rw [ha, hg4, d1, conj_mul_conj, d1, d4]
        calc zK * f * f = zK * (f * f) := by group
          _ = zK := by rw [hf]; group
      · rw [ha, hg4, d2, d2]
      · rw [ha, hg4, d3, d3]
      · rw [ha, hg4, d4, d4]
    exact forall_mem_closure_conj_eq hS
  · intro hall
    have := hall zK hzKA
    rw [← hh, d1] at this
    apply hne
    exact mul_left_cancel (this.trans (mul_one zK).symm)

end Calc

end CFSG.QuasithinUnique
