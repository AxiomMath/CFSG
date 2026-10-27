module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Omega

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup

theorem pow_fin_add {G : Type*} [Group G] {g : G} (hg : g ^ 2 = 1) (a b : Fin 2) :
    g ^ ((a + b : Fin 2) : ℕ) = g ^ (a : ℕ) * g ^ (b : ℕ) := by
  fin_cases a <;> fin_cases b <;> simp [← pow_two, hg]

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem mem_E_y_iff' {g : X} (hg : g ∈ S.data.T) : g ∈ S.E S.y ↔
    ∃ a b : Fin 2, (S.coords ⟨g, hg⟩).1 = (r 2) ^ (a : ℕ) * (sr 0) ^ (b : ℕ) :=
  S.mem_E_iff S.y_mem S.y_sq S.coords_y hg

theorem mem_E_xy_iff' {g : X} (hg : g ∈ S.data.T) : g ∈ S.E (S.x * S.y) ↔
    ∃ a b : Fin 2, (S.coords ⟨g, hg⟩).1 = (r 2) ^ (a : ℕ) * (sr 3) ^ (b : ℕ) :=
  S.mem_E_iff S.xy_mem S.xy_sq S.coords_xy hg

theorem mem_B_of_coords {g : X} (hg : g ∈ S.data.T)
    (h : (S.coords ⟨g, hg⟩).1 = 1 ∨ (S.coords ⟨g, hg⟩).1 = r 2) : g ∈ S.B := by
  rw [← S.mem_B_iff hg]
  intro h' hh'
  have key : ∀ p q : DihedralGroup 4 × DihedralGroup 2, (p.1 = 1 ∨ p.1 = r 2) →
      p * q = q * p := by decide
  have := key _ (S.coords ⟨h', hh'⟩) h
  rw [← map_mul, ← map_mul] at this
  exact congrArg Subtype.val (S.coords.injective this)

theorem coords_of_mem_B {g : X} (hg : g ∈ S.B) :
    (S.coords ⟨g, S.B_le_T hg⟩).1 = 1 ∨ (S.coords ⟨g, S.B_le_T hg⟩).1 = r 2 := by
  have hc : ∀ q : DihedralGroup 4 × DihedralGroup 2, S.coords ⟨g, S.B_le_T hg⟩ * q =
      q * S.coords ⟨g, S.B_le_T hg⟩ := by
    intro q
    obtain ⟨h, rfl⟩ := S.coords.surjective q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (S.central_of_mem_B hg h.2)
  have key : ∀ p : DihedralGroup 4 × DihedralGroup 2,
      (∀ q : DihedralGroup 4 × DihedralGroup 2, p * q = q * p) → p.1 = 1 ∨ p.1 = r 2 := by
    decide
  exact key _ hc

theorem mem_E_or_of_sq {g : X} (hg : g ∈ S.data.T) (hg2 : g ^ 2 = 1) :
    g ∈ S.E S.y ∨ g ∈ S.E (S.x * S.y) := by
  rw [S.mem_E_y_iff' hg, S.mem_E_xy_iff' hg]
  have : (⟨g, hg⟩ : S.data.T) ^ 2 = 1 := Subtype.ext hg2
  have h := congrArg Prod.fst (congrArg S.coords this)
  rw [map_pow, map_one, Prod.pow_fst] at h
  generalize (S.coords ⟨g, hg⟩).1 = p at h ⊢
  revert p
  decide

theorem conj_x_of_not_mem_B {g : X} (hg : g ∈ S.data.T) (hg2 : g ^ 2 = 1) (hgB : g ∉ S.B) :
    S.x * g * S.x⁻¹ = S.z * g := by
  have hgB' : ¬ ((S.coords ⟨g, hg⟩).1 = 1 ∨ (S.coords ⟨g, hg⟩).1 = r 2) :=
    fun h => hgB (S.mem_B_of_coords hg h)
  have h2 : (S.coords ⟨g, hg⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : S.data.T) ^ 2 = 1 := Subtype.ext hg2
    rw [this, map_one]
  have key : ∀ q : DihedralGroup 4 × DihedralGroup 2, q ^ 2 = 1 → ¬ (q.1 = 1 ∨ q.1 = r 2) →
      (r 1, 1) * q * (r 1, 1)⁻¹ = (r 2, 1) * q := by decide
  have hm : S.x * g * S.x⁻¹ ∈ S.data.T := mul_mem (mul_mem S.x_mem.1 hg) (inv_mem S.x_mem.1)
  have hm' : S.z * g ∈ S.data.T := mul_mem S.z_mem.1 hg
  have : (⟨S.x * g * S.x⁻¹, hm⟩ : S.data.T) = ⟨S.z * g, hm'⟩ := by
    apply S.coords.injective
    have e1 : (⟨S.x * g * S.x⁻¹, hm⟩ : S.data.T) =
        ⟨S.x, S.x_mem.1⟩ * ⟨g, hg⟩ * (⟨S.x, S.x_mem.1⟩ : S.data.T)⁻¹ := rfl
    have e2 : (⟨S.z * g, hm'⟩ : S.data.T) = ⟨S.z, S.z_mem.1⟩ * ⟨g, hg⟩ := rfl
    rw [e1, e2, map_mul, map_mul, map_inv, map_mul, S.coords_x, S.coords_z]
    exact key _ h2 hgB'
  exact congrArg Subtype.val this

theorem mem_E_of_commute {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y) {g : X} (hg : g ∈ S.data.T)
    (hc : ∀ e ∈ S.E yi, g * e = e * g) : g ∈ S.E yi := by
  have hyiE : yi ∈ S.E yi := subset_closure (by simp)
  rcases hyi with rfl | rfl
  · rw [S.mem_E_y_iff' hg]
    have h := hc _ hyiE
    have : (⟨g, hg⟩ : S.data.T) * ⟨S.y, S.y_mem.1⟩ = ⟨S.y, S.y_mem.1⟩ * ⟨g, hg⟩ := Subtype.ext h
    have h' := congrArg Prod.fst (congrArg S.coords this)
    rw [map_mul, map_mul, Prod.fst_mul, Prod.fst_mul, S.coords_y] at h'
    generalize (S.coords ⟨g, hg⟩).1 = p at h' ⊢
    revert p
    decide
  · rw [S.mem_E_xy_iff' hg]
    have h := hc _ hyiE
    have : (⟨g, hg⟩ : S.data.T) * ⟨S.x * S.y, S.xy_mem.1⟩ =
        ⟨S.x * S.y, S.xy_mem.1⟩ * ⟨g, hg⟩ := Subtype.ext h
    have h' := congrArg Prod.fst (congrArg S.coords this)
    rw [map_mul, map_mul, Prod.fst_mul, Prod.fst_mul, S.coords_xy] at h'
    generalize (S.coords ⟨g, hg⟩).1 = p at h' ⊢
    revert p
    decide

theorem eq_y_mul_of_mem_E_y {j : X} (hj : j ∈ S.E S.y) (hjB : j ∉ S.B) :
    ∃ f : X, (f = 1 ∨ f = S.t ∨ f = S.z * S.k ∨ f = S.t * (S.z * S.k)) ∧
      (j = S.y * f ∨ j = S.z * S.y * f) := by
  obtain ⟨a, b, c, d, rfl⟩ := S.eq_of_mem_E S.y_mem S.y_sq (S.z_comm_of_mem_T S.y_mem.1) hj
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hkB : S.k ∈ S.B := subset_closure (by simp)
  have hzy : S.z * S.y = S.y * S.z := S.z_comm_of_mem_T S.y_mem.1
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hz2 : S.z * S.z = 1 := by rw [← pow_two]; exact S.sq_of_mem_B hzB
  fin_cases b
  · exfalso
    apply hjB
    simp only [pow_zero, mul_one]
    exact mul_mem (mul_mem (pow_mem hzB _) (pow_mem htB _)) (pow_mem hkB _)
  fin_cases a <;> fin_cases c <;> fin_cases d <;> simp only [pow_zero, pow_one, one_mul, mul_one]
  · exact ⟨1, Or.inl rfl, Or.inl (mul_one _).symm⟩
  · refine ⟨S.z * S.k, Or.inr (Or.inr (Or.inl rfl)), Or.inr ?_⟩
    calc S.y * S.k = S.y * (S.z * S.z) * S.k := by rw [hz2, mul_one]
      _ = S.z * S.y * (S.z * S.k) := by rw [hzy]; group
  · exact ⟨S.t, Or.inr (Or.inl rfl), Or.inl rfl⟩
  · refine ⟨S.t * (S.z * S.k), Or.inr (Or.inr (Or.inr rfl)), Or.inr ?_⟩
    calc S.y * S.t * S.k = S.y * S.t * (S.z * S.z) * S.k := by rw [hz2, mul_one]
      _ = S.y * (S.t * S.z) * S.z * S.k := by group
      _ = S.y * (S.z * S.t) * S.z * S.k := by rw [hzt]
      _ = S.z * S.y * (S.t * (S.z * S.k)) := by rw [hzy]; group
  · exact ⟨1, Or.inl rfl, Or.inr (mul_one _).symm⟩
  · refine ⟨S.z * S.k, Or.inr (Or.inr (Or.inl rfl)), Or.inl ?_⟩
    rw [hzy]
    group
  · exact ⟨S.t, Or.inr (Or.inl rfl), Or.inr rfl⟩
  · refine ⟨S.t * (S.z * S.k), Or.inr (Or.inr (Or.inr rfl)), Or.inl ?_⟩
    calc S.z * S.y * S.t * S.k = S.y * (S.z * S.t) * S.k := by rw [hzy]; group
      _ = S.y * (S.t * (S.z * S.k)) := by rw [hzt]; group

theorem eq_xy_mul_of_mem_E_xy {j : X} (hj : j ∈ S.E (S.x * S.y)) (hjB : j ∉ S.B) :
    ∃ f ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X),
      j = S.x * S.y * f ∨ j = S.z * (S.x * S.y) * f := by
  obtain ⟨a, b, c, d, rfl⟩ :=
    S.eq_of_mem_E S.xy_mem S.xy_sq (S.z_comm_of_mem_T S.xy_mem.1) hj
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hkB : S.k ∈ S.B := subset_closure (by simp)
  have hf : S.t ^ (c : ℕ) * S.k ^ (d : ℕ) ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X) :=
    mul_mem (mem_sup_left (pow_mem (mem_zpowers _) _)) (mem_sup_right (pow_mem (mem_zpowers _) _))
  fin_cases b
  · exfalso
    apply hjB
    simp only [pow_zero, mul_one]
    exact mul_mem (mul_mem (pow_mem hzB _) (pow_mem htB _)) (pow_mem hkB _)
  refine ⟨_, hf, ?_⟩
  fin_cases a
  · left
    simp only [pow_zero, pow_one, one_mul]
    group
  · right
    simp only [pow_one]
    group

theorem exists_conj_mem_B {i : X} (hi : i ∈ centralizer ({S.t} : Set X)) (hi2 : i ^ 2 = 1) :
    ∃ g ∈ centralizer ({S.t} : Set X), g * i * g⁻¹ ∈ S.B := by
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have hp : IsPGroup 2 (zpowers i) := by
    intro h
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, ← hn, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hi2, one_zpow]
  obtain ⟨h, hh, hT⟩ := S.data.exists_conj_le_T hp (zpowers_le.mpr hi)
  have hjT : h * i * h⁻¹ ∈ S.data.T := hT ⟨i, mem_zpowers i, rfl⟩
  have hj2 : (h * i * h⁻¹) ^ 2 = 1 := by rw [conj_pow, hi2]; group
  suffices hj : ∃ g ∈ centralizer ({S.t} : Set X), g * (h * i * h⁻¹) * g⁻¹ ∈ S.B by
    obtain ⟨g, hg, hgB⟩ := hj
    refine ⟨g * h, mul_mem hg hh, ?_⟩
    have e : g * h * i * (g * h)⁻¹ = g * (h * i * h⁻¹) * g⁻¹ := by group
    rw [e]
    exact hgB
  set j := h * i * h⁻¹ with hjdef
  by_cases hjB : j ∈ S.B
  · exact ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]; exact hjB⟩
  rcases S.mem_E_or_of_sq hjT hj2 with hjE | hjE
  · obtain ⟨f, hf, hjf⟩ := S.eq_y_mul_of_mem_E_y hjE hjB
    have hfB : f ∈ S.B := by
      rcases hf with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact subset_closure (by simp)
      · exact mul_mem hzB (subset_closure (by simp))
      · exact mul_mem (subset_closure (by simp)) (mul_mem hzB (subset_closure (by simp)))
    obtain ⟨d, hdC, -, hdz, hdy, hdk⟩ := S.exists_d_y
    have hdf := S.conj_eq_of_mem_tzk hdC hdk hf
    rcases hjf with hjf | hjf <;> rw [hjf]
    · refine ⟨d, hdC, ?_⟩
      have e : d * (S.y * f) * d⁻¹ = (d * S.y * d⁻¹) * (d * f * d⁻¹) := by group
      rw [e, hdy, hdf]
      exact mul_mem hzB hfB
    · refine ⟨d⁻¹, inv_mem hdC, ?_⟩
      have h1 : d⁻¹ * (S.z * S.y) * d = S.z := by rw [← hdz]; group
      have h2 : d⁻¹ * f * d = f := by
        calc d⁻¹ * f * d = d⁻¹ * (d * f * d⁻¹) * d := by rw [hdf]
          _ = f := by group
      have e : d⁻¹ * (S.z * S.y * f) * d⁻¹⁻¹ = (d⁻¹ * (S.z * S.y) * d) * (d⁻¹ * f * d) := by
        group
      rw [e, h1, h2]
      exact mul_mem hzB hfB
  · obtain ⟨f, hf, hjf⟩ := S.eq_xy_mul_of_mem_E_xy hjE hjB
    have hfB : f ∈ S.B := by
      rcases S.eq_of_mem_tk hf with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    obtain ⟨d, hdC, -, hdz, hdxy, hdk⟩ := S.exists_d_xy
    have hdf := S.conj_eq_of_mem_tk hdC hdk hf
    rcases hjf with hjf | hjf <;> rw [hjf]
    · refine ⟨d⁻¹, inv_mem hdC, ?_⟩
      have h1 : d⁻¹ * (S.x * S.y) * d = S.z := by rw [← hdz]; group
      have h2 : d⁻¹ * f * d = f := by
        calc d⁻¹ * f * d = d⁻¹ * (d * f * d⁻¹) * d := by rw [hdf]
          _ = f := by group
      have e : d⁻¹ * (S.x * S.y * f) * d⁻¹⁻¹ = (d⁻¹ * (S.x * S.y) * d) * (d⁻¹ * f * d) := by
        group
      rw [e, h1, h2]
      exact mul_mem hzB hfB
    · refine ⟨d, hdC, ?_⟩
      have hxy2 : S.x * S.y * (S.z * (S.x * S.y)) = S.z := by
        calc S.x * S.y * (S.z * (S.x * S.y)) = S.z * ((S.x * S.y) * (S.x * S.y)) := by
              rw [← mul_assoc, ← S.z_comm_of_mem_T S.xy_mem.1]; group
          _ = S.z := by rw [← pow_two, S.xy_sq, mul_one]
      have e : d * (S.z * (S.x * S.y) * f) * d⁻¹ =
          (d * S.z * d⁻¹) * (d * (S.x * S.y) * d⁻¹) * (d * f * d⁻¹) := by group
      rw [e, hdz, hdxy, hdf, hxy2]
      exact mul_mem hzB hfB

end A7Base

end CFSG.ComponentClassification.HSFLit
