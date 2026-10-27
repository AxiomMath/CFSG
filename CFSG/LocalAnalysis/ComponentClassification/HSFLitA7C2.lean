module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Omega

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

structure Case2 where
  yb : X
  ys : X
  f : X
  u : X
  hy : (yb = S.y ∧ ys = S.x * S.y) ∨ (yb = S.x * S.y ∧ ys = S.y)
  f_mem : f ∈ S.B
  f_not_mem : f ∉ (zpowers S.t ⊔ zpowers S.z : Subgroup X)
  u_mem : u ∈ S.E yb
  u_not_mem : u ∉ S.B
  fusion : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.t * f
  omega_big : ∀ e ∈ S.E yb, ConjTo S.t e ↔ e = S.t ∨ e = S.t * f ∨ e = u ∨ e = S.z * u
  omega_small : ∀ e ∈ S.E ys, ConjTo S.t e ↔ e = S.t ∨ e = S.t * f
  T₁ : Subgroup X
  T₁_p : IsPGroup 2 T₁
  T_le : S.data.T ≤ T₁
  T₁_le : T₁ ≤ normalizer (S.data.T : Set X)
  card_T₁ : Nat.card T₁ = 2 * Nat.card S.data.T

namespace Case2

variable {S} (C : S.Case2)

theorem yb_mem : C.yb ∈ S.data.R := by
  rcases C.hy with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]; exacts [S.y_mem, S.xy_mem]

theorem yb_sq : C.yb ^ 2 = 1 := by
  rcases C.hy with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]; exacts [S.y_sq, S.xy_sq]

theorem yb_not_mem_B : C.yb ∉ S.B := by
  rcases C.hy with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]; exacts [S.y_not_mem_B, S.xy_not_mem_B]

theorem yb_cases : C.yb = S.y ∨ C.yb = S.x * S.y := by
  rcases C.hy with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem card_E : Nat.card (S.E C.yb) = 16 := S.card_E C.yb_mem C.yb_sq C.yb_not_mem_B

theorem E_le_T : S.E C.yb ≤ S.data.T := S.E_le_T C.yb_mem

theorem t_mem_E : S.t ∈ S.E C.yb := subset_closure (by simp)

theorem z_mem_E : S.z ∈ S.E C.yb := subset_closure (by simp)

theorem B_le_E : S.B ≤ S.E C.yb := by
  rw [S.E_eq_B_sup]
  exact le_sup_left

theorem f_mem_E : C.f ∈ S.E C.yb := C.B_le_E C.f_mem

theorem f_ne_one : C.f ≠ 1 := fun h => C.f_not_mem (h ▸ one_mem _)

theorem f_sq : C.f ^ 2 = 1 := S.sq_of_mem_B C.f_mem

theorem u_sq : C.u ^ 2 = 1 := S.E_sq C.yb_mem C.yb_sq C.u_mem

theorem comm {a b : X} (ha : a ∈ S.E C.yb) (hb : b ∈ S.E C.yb) : a * b = b * a :=
  S.E_comm C.yb_mem ha hb

theorem zu_not_mem : S.z * C.u ∉ S.B := by
  intro h
  apply C.u_not_mem
  have : C.u = S.z⁻¹ * (S.z * C.u) := by group
  rw [this]
  exact mul_mem (inv_mem (subset_closure (by simp))) h

include C in
theorem not_subConj : ¬ SubConj (S.E S.y) (S.E (S.x * S.y)) := by
  rintro ⟨g, hg⟩
  obtain ⟨ν, hν⟩ : ∃ ν : X, ∀ e ∈ S.E C.yb, ν * e * ν⁻¹ ∈ S.E C.ys := by
    rcases C.hy with ⟨hb, hs⟩ | ⟨hb, hs⟩
    · refine ⟨g, fun e he => ?_⟩
      rw [hb] at he
      rw [hs, ← hg]
      exact ⟨e, he, rfl⟩
    · refine ⟨g⁻¹, fun e he => ?_⟩
      rw [hb, ← hg] at he
      rw [hs]
      obtain ⟨e', he', rfl⟩ := he
      simpa [MulAut.conj_apply, mul_assoc] using he'
  have hc : ∀ e ∈ S.E C.yb, ConjTo S.t e → ν * e * ν⁻¹ = S.t ∨ ν * e * ν⁻¹ = S.t * C.f := by
    intro e he hce
    exact (C.omega_small _ (hν e he)).mp ((conjTo_conj_iff S.t e ν).mpr hce)
  have h1 := hc S.t C.t_mem_E ((C.omega_big _ C.t_mem_E).mpr (Or.inl rfl))
  have h2 := hc C.u C.u_mem ((C.omega_big _ C.u_mem).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hzuE : S.z * C.u ∈ S.E C.yb := mul_mem C.z_mem_E C.u_mem
  have h3 := hc _ hzuE ((C.omega_big _ hzuE).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have hinj : ∀ a b : X, ν * a * ν⁻¹ = ν * b * ν⁻¹ → a = b := fun a b h => by
    simpa using h
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have htu : S.t ≠ C.u := fun h => C.u_not_mem (h ▸ htB)
  have htzu : S.t ≠ S.z * C.u := fun h => C.zu_not_mem (h ▸ htB)
  have huzu : C.u ≠ S.z * C.u := fun h => S.z_ne_one (by
    have := mul_right_cancel (h.symm.trans (one_mul C.u).symm)
    exact this)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · exact htu (hinj _ _ (h1.trans h2.symm))
  · exact htu (hinj _ _ (h1.trans h2.symm))
  · exact htzu (hinj _ _ (h1.trans h3.symm))
  · exact huzu (hinj _ _ (h2.trans h3.symm))
  · exact huzu (hinj _ _ (h2.trans h3.symm))
  · exact htzu (hinj _ _ (h1.trans h3.symm))
  · exact htu (hinj _ _ (h1.trans h2.symm))
  · exact htu (hinj _ _ (h1.trans h2.symm))

theorem T₁_le_normalizer : C.T₁ ≤ normalizer (S.E C.yb : Set X) := by
  intro n hn
  have hnN := C.T₁_le hn
  set E' : Subgroup X := (S.E C.yb).map (MulAut.conj n).toMonoidHom with hE'
  have hE'T : E' ≤ S.data.T := by
    rintro _ ⟨e, he, rfl⟩
    exact S.data.conj_mem_T hnN (C.E_le_T he)
  have hE'el : ElemAbelianTwo E' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, C.comm ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, S.E_sq C.yb_mem C.yb_sq ha, map_one]
  have hE'c : Nat.card E' = 16 := by
    rw [hE', card_map_of_injective (MulAut.conj n).injective, C.card_E]
  have hcases := S.eq_E_of_elem hE'T hE'el hE'c
  have hE'eq : E' = S.E C.yb := by
    rcases C.hy with ⟨hb, -⟩ | ⟨hb, -⟩ <;> rcases hcases with h | h
    · rw [h, hb]
    · exfalso
      refine not_subConj C ⟨n, ?_⟩
      simpa only [hE', hb] using h
    · exfalso
      refine not_subConj C ⟨n⁻¹, ?_⟩
      simp only [hE', hb] at h
      rw [← h, Subgroup.map_map]
      ext a
      simp [MulAut.conj_apply, mul_assoc]
    · rw [h, hb]
  refine mem_normalizer_of_conj_mem fun e he => ?_
  have : n * e * n⁻¹ ∈ E' := ⟨e, he, rfl⟩
  rwa [hE'eq] at this

theorem orbit_eq : {b | ∃ n ∈ normalizer (S.E C.yb : Set X), n * S.t * n⁻¹ = b} =
    ({S.t, S.t * C.f, C.u, S.z * C.u} : Set X) := by
  ext b
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hbE := (mem_normalizer_iff.mp hn _).mp C.t_mem_E
    rcases (C.omega_big _ hbE).mp ⟨n, rfl⟩ with h | h | h | h <;> simp [h]
  · intro hb
    have hbE : b ∈ S.E C.yb := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact C.t_mem_E
      · exact mul_mem C.t_mem_E C.f_mem_E
      · exact C.u_mem
      · exact mul_mem C.z_mem_E C.u_mem
    have hbc : ConjTo S.t b := by
      rw [C.omega_big _ hbE]
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hb
    obtain ⟨n, hn, hnb⟩ := S.exists_normalizer_conj_eq_t C.yb_cases (not_subConj C) hbE hbc
    exact ⟨n⁻¹, inv_mem hn, by rw [← hnb]; group⟩

theorem ncard_orbit : {b | ∃ n ∈ normalizer (S.E C.yb : Set X), n * S.t * n⁻¹ = b}.ncard = 4 := by
  rw [C.orbit_eq]
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have htfB : S.t * C.f ∈ S.B := mul_mem htB C.f_mem
  have htf : S.t ≠ S.t * C.f := fun h => C.f_ne_one (by
    have := mul_left_cancel (h.symm.trans (mul_one S.t).symm)
    exact this)
  have huzu : C.u ≠ S.z * C.u := fun h => S.z_ne_one (by
    have := mul_right_cancel (h.symm.trans (one_mul C.u).symm)
    exact this)
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair huzu]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => C.u_not_mem (h ▸ htfB), fun h => C.zu_not_mem (h ▸ htfB)⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨htf, fun h => C.u_not_mem (h ▸ htB), fun h => C.zu_not_mem (h ▸ htB)⟩

end Case2

end A7Base

end CFSG.ComponentClassification.HSFLit
