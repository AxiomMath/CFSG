module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NQ1N

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem conj_mem_closure {G : Type*} [Group G] {s : Set G} {K : Subgroup G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ K) {y : G} (hy : y ∈ closure s) : g * y * g⁻¹ ∈ K := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]; exact mul_mem ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]; exact inv_mem ha

theorem map_conj_eq_of_mem_normalizer {G : Type*} [Group G] {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    have := (mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr
    apply this
    simpa [mul_assoc] using hx

theorem eps_eq {P : Prop} {ε ε' : Fin 2} (h : ε = 0 ↔ P) (h' : ε' = 0 ↔ P) : ε = ε' := by
  rcases Fin.exists_fin_two.mp ⟨ε, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨ε', rfl⟩ with rfl | rfl
  · rfl
  · exact absurd (h'.mpr (h.mp rfl)) (by decide)
  · exact absurd (h.mpr (h'.mp rfl)) (by decide)
  · rfl

theorem xCols_M2C : ∀ ε, comp (comp xCols (M2C ε)) xCols = M3C ε := by decide

theorem xCols_cvw : ∀ ε α : Fin 2, lin xCols (α, 0, 0, ε * α) = (α, 0, 0, ε * α) := by decide

theorem xCols_cvw₂ : ∀ ε α : Fin 2, lin xCols (lin dCols (α, 0, 0, ε * α)) =
    addV (α, 0, 0, ε * α) (lin (M1C ε) (lin dCols (α, 0, 0, ε * α))) := by decide

theorem vC_t_part : ∀ φ : V4, addV (lin vC φ) φ = (0, 0, 0, φ.2.2.1) := by decide

theorem cvw_add : ∀ p : V4, ∀ φ : Fin 2, addV p (0, 0, 0, φ) = p → φ = 0 := by decide

theorem cvw_add₂ : ∀ p q : V4, ∀ φ : Fin 2, addV (addV p q) (0, 0, 0, φ) = addV p q → φ = 0 := by
  decide

theorem M3C_ki : ∀ ε φ : Fin 2, lin (M3C ε) (0, 0, 0, φ) = (0, 0, 0, φ) := by decide

theorem sig_decomp : ∀ σ₁ ∈ three, ∀ σ₂ ∈ three, σ₁ = σ₂ ∨
    ∃ i : Fin 3, ∃ j : Fin 2, comp (pw3 dCols i) (pw xCols j) = sigCols σ₁ σ₂ := by decide

theorem gC_transl : ∀ ε a b c : Fin 2, ∀ j,
    blk (lin (gC ε a b c) (pt j)) = j + blk (lin (gC ε a b c) (pt 0)) := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {T₁ : Subgroup X}

namespace Inst

variable {I : S.Inst} {H : S.Sec6Hyp T₁}

namespace Data6

variable (D : I.Data6 H) (R : D.Rel)

theorem mem_normalizer_Q0 {g : X} (hz : g * S.z * g⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂)
    (hy : g * I.yi * g⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂)
    (hk : g * I.ki * g⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂)
    (h1 : g * D.w₁ * g⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂)
    (h2 : g * D.w₂ * g⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂) :
    g ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) :=
  mem_normalizer_of_conj_mem fun q hq => conj_mem_closure (fun x hx => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact hy
    · exact hk
    · exact h1
    · exact h2) (I.Q0_le_closure _ _ hq)

theorem E0_gens {g : X} {c : Fin 4 → V4} (hg : I.Mat g c)
    (hc : ∀ a b d : Fin 2, (lin c (a, b, 0, d)).2.2.1 = 0) :
    g * S.z * g⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ ∧ g * I.yi * g⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ ∧
      g * I.ki * g⁻¹ ∈ S.Q0 I.yi I.ki D.w₁ D.w₂ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hg.conj_z]
    have := hc 1 0 0
    rw [show ((1, 0, 0, 0) : V4) = bas 0 from rfl, lin_bas] at this
    exact I.E0_le_Q0 _ _ (I.wV_mem_E0' this)
  · rw [hg.conj_yi]
    have := hc 0 1 0
    rw [show ((0, 1, 0, 0) : V4) = bas 1 from rfl, lin_bas] at this
    exact I.E0_le_Q0 _ _ (I.wV_mem_E0' this)
  · rw [hg.conj_ki]
    have := hc 0 0 1
    rw [show ((0, 0, 0, 1) : V4) = bas 3 from rfl, lin_bas] at this
    exact I.E0_le_Q0 _ _ (I.wV_mem_E0' this)

include R in
theorem E_normalizer {e : X} (he : e ∈ I.E) :
    e ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) := by
  obtain ⟨p, rfl⟩ := I.eq_wV he
  have hM := Mat.of_mem_centralizer (I.E_le_centralizer he)
  obtain ⟨hz, hy, hk⟩ := D.E0_gens hM (fun a b d => by rw [lin_bas_self])
  refine D.mem_normalizer_Q0 hz hy hk ?_ ?_
  · obtain ⟨f, hf, hf'⟩ := conj_E R.rel.m1 (fun e => (E_conj_E0 D.ε e).1) (M1C_sq D.ε) p
    rw [hf']; exact mul_mem (I.w₁_mem_Q0 _ _) (I.E0_le_Q0 _ _ hf)
  · obtain ⟨f, hf, hf'⟩ := conj_E R.rel.m2 (fun e => (E_conj_E0 D.ε e).2.1) (M2C_sq D.ε) p
    rw [hf']; exact mul_mem (I.w₂_mem_Q0 _ _) (I.E0_le_Q0 _ _ hf)

theorem v_normalizer : D.v ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) := by
  obtain ⟨hz, hy, hk⟩ := D.E0_gens D.v_mat vC_E0
  refine D.mem_normalizer_Q0 hz hy hk ?_ ?_
  · have e : D.v * D.w₁ * D.v⁻¹ = (D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹) * D.w₁ := by group
    rw [e, D.v_w₁]
    exact mul_mem (I.E0_le_Q0 _ _ (I.wV_mem_E0 _ _ _)) (I.w₁_mem_Q0 _ _)
  · have e : D.v * D.w₂ * D.v⁻¹ = (D.v * D.w₂ * D.v⁻¹ * D.w₂⁻¹) * D.w₂ := by group
    rw [e, D.v_w₂]
    exact mul_mem (I.E0_le_Q0 _ _ (I.wV_mem_E0' (dCols_E0 _ _))) (I.w₂_mem_Q0 _ _)

include R in
theorem Q₁_le_normalizer : D.Q₁ ≤ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) := by
  rw [D.Q₁_eq R]
  refine sup_le (sup_le (sup_le (fun e he => D.E_normalizer R he) ?_) ?_) ?_
  · exact zpowers_le.mpr D.v_normalizer
  · exact zpowers_le.mpr (le_normalizer (I.w₁_mem_Q0 _ _))
  · exact zpowers_le.mpr (le_normalizer (I.w₂_mem_Q0 _ _))

include R in
theorem d_normalizer : D.d ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) := by
  obtain ⟨hz, hy, hk⟩ := D.E0_gens D.d_mat dCols_E0'
  refine D.mem_normalizer_Q0 hz hy hk ?_ ?_
  · exact I.w₂_mem_Q0 _ _
  · rw [R.w₃]
    exact mul_mem (mul_mem (I.w₁_mem_Q0 _ _) (I.w₂_mem_Q0 _ _))
      (I.E0_le_Q0 _ _ (I.wV_mem_E0' R.e_E0))

theorem u_conj_w₁ : ∃ φ : V4, φ.2.2.1 = 0 ∧ D.u * D.w₁ * D.u⁻¹ = D.w₁ * I.wV φ := by
  have huM := D.u_mat
  have huiM : I.Mat D.u⁻¹ xCols := huM.inv xCols_xCols
  have hvu : D.v * D.u = D.u * D.v := D.u_v.symm
  have hM : I.Mat (D.u * D.w₁ * D.u⁻¹) (M1C D.ε) := by
    have := (huM.mul D.w₁_mat).mul huiM
    rwa [xCols_M1C] at this
  have hφ : D.w₁⁻¹ * (D.u * D.w₁ * D.u⁻¹) ∈ I.E :=
    D.mem_E_of_mem_Q₁ (mul_mem (inv_mem D.w₁_Q₁) (D.conj_mem_Q₁ D.u_S₁ D.w₁_Q₁))
      (D.w₁_mat.inv_mul_mem_centralizer hM)
  obtain ⟨φ, hφ'⟩ := I.eq_wV hφ
  have hw : D.u * D.w₁ * D.u⁻¹ = D.w₁ * I.wV φ := by rw [← hφ']; group
  have h1 : D.v * (D.u * D.w₁ * D.u⁻¹) * D.v⁻¹ * (D.u * D.w₁ * D.u⁻¹)⁻¹ =
      I.wV (D.α, 0, 0, D.ε * D.α) := by
    rw [comm_conj_of_commute hvu, D.v_w₁, huM.conj, xCols_cvw]
  have hve : D.v * I.wV φ * D.v⁻¹ * (I.wV φ)⁻¹ = I.wV (0, 0, 0, φ.2.2.1) := by
    rw [D.v_mat.conj, I.wV_inv, ← I.wV_add, vC_t_part]
  rw [hw, comm_mul, D.v_w₁, hve, D.w₁_mat.conj, M1C_ki, ← I.wV_add] at h1
  exact ⟨φ, cvw_add _ _ (I.wV_injective h1), hw⟩

theorem u_conj_w₂ : ∃ φ : V4, φ.2.2.1 = 0 ∧ D.u * D.w₂ * D.u⁻¹ = D.w₁ * D.w₂ * I.wV φ := by
  have huM := D.u_mat
  have huiM : I.Mat D.u⁻¹ xCols := huM.inv xCols_xCols
  have hvu : D.v * D.u = D.u * D.v := D.u_v.symm
  have hM : I.Mat (D.u * D.w₂ * D.u⁻¹) (M3C D.ε) := by
    have := (huM.mul D.w₂_mat).mul huiM
    rwa [xCols_M2C] at this
  have h12 : I.Mat (D.w₁ * D.w₂) (M3C D.ε) := by
    have := D.w₁_mat.mul D.w₂_mat
    rwa [M1C_M2C] at this
  have hφ : (D.w₁ * D.w₂)⁻¹ * (D.u * D.w₂ * D.u⁻¹) ∈ I.E :=
    D.mem_E_of_mem_Q₁ (mul_mem (inv_mem (mul_mem D.w₁_Q₁ D.w₂_Q₁))
      (D.conj_mem_Q₁ D.u_S₁ D.w₂_Q₁)) (h12.inv_mul_mem_centralizer hM)
  obtain ⟨φ, hφ'⟩ := I.eq_wV hφ
  have hw : D.u * D.w₂ * D.u⁻¹ = D.w₁ * D.w₂ * I.wV φ := by rw [← hφ']; group
  have h1 : D.v * (D.u * D.w₂ * D.u⁻¹) * D.v⁻¹ * (D.u * D.w₂ * D.u⁻¹)⁻¹ =
      I.wV (lin xCols (lin dCols (D.α, 0, 0, D.ε * D.α))) := by
    rw [comm_conj_of_commute hvu, D.v_w₂, huM.conj]
  have hid : D.v * (D.w₁ * D.w₂ * I.wV φ) * D.v⁻¹ * (D.w₁ * D.w₂ * I.wV φ)⁻¹ =
      (D.v * D.w₁ * D.v⁻¹ * D.w₁⁻¹) * (D.w₁ * (D.v * D.w₂ * D.v⁻¹ * D.w₂⁻¹) * D.w₁⁻¹) *
        ((D.w₁ * D.w₂) * (D.v * I.wV φ * D.v⁻¹ * (I.wV φ)⁻¹) * (D.w₁ * D.w₂)⁻¹) := by group
  have hve : D.v * I.wV φ * D.v⁻¹ * (I.wV φ)⁻¹ = I.wV (0, 0, 0, φ.2.2.1) := by
    rw [D.v_mat.conj, I.wV_inv, ← I.wV_add, vC_t_part]
  rw [hw, hid, D.v_w₁, D.v_w₂, hve, D.w₁_mat.conj, h12.conj, M3C_ki, ← I.wV_add,
    ← I.wV_add, xCols_cvw₂] at h1
  exact ⟨φ, cvw_add₂ _ _ _ (I.wV_injective h1), hw⟩

theorem u_normalizer : D.u ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) := by
  obtain ⟨hz, hy, hk⟩ := D.E0_gens D.u_mat xCols_E0
  refine D.mem_normalizer_Q0 hz hy hk ?_ ?_
  · obtain ⟨φ, hφt, hw⟩ := D.u_conj_w₁
    rw [hw]
    exact mul_mem (I.w₁_mem_Q0 _ _) (I.E0_le_Q0 _ _ (I.wV_mem_E0' hφt))
  · obtain ⟨φ, hφt, hw⟩ := D.u_conj_w₂
    rw [hw]
    exact mul_mem (mul_mem (I.w₁_mem_Q0 _ _) (I.w₂_mem_Q0 _ _))
      (I.E0_le_Q0 _ _ (I.wV_mem_E0' hφt))

include R in
theorem centralizer_normalizer {c : X} (hc : c ∈ centralizer (I.E : Set X))
    (hcQ : c ∈ normalizer (D.Q₁ : Set X)) : c ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) := by
  obtain ⟨e, he, k, hk, rfl⟩ := I.exists_mul_K hc
  have hkQ : k ∈ normalizer (D.Q₁ : Set X) := by
    have : e⁻¹ * (e * k) = k := by group
    rw [← this]
    exact mul_mem (inv_mem (le_normalizer (D.E_le_Q₁ he))) hcQ
  have hkN : k ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) := by
    refine mem_normalizer_of_conj_mem fun q hq => ?_
    have hqQ₁ : q ∈ D.Q₁ := by
      obtain ⟨a, b, f, hf, rfl⟩ := R.rel.mem_Q0_iff.mp hq
      exact mul_mem (mul_mem (pow_mem D.w₂_Q₁ _) (pow_mem D.w₁_Q₁ _))
        (D.E_le_Q₁ (I.E0_le_E hf))
    rw [I.commute_of_mem_K D.isPGroup_Q₁ D.Q₁_le_N hk hkQ hqQ₁, mul_inv_cancel_right]
    exact hq
  exact mul_mem (D.E_normalizer R he) hkN

include R in
theorem Q0_invariant {n : X}
    (hn : n ∈ normalizer (I.E : Set X) ⊓ normalizer (D.Q₁ : Set X)) :
    (S.Q0 I.yi I.ki D.w₁ D.w₂).map (MulAut.conj n).toMonoidHom = S.Q0 I.yi I.ki D.w₁ D.w₂ := by
  apply map_conj_eq_of_mem_normalizer
  obtain ⟨ε', hε', hcl⟩ := I.classify H
  rw [eps_eq hε' D.hε] at hcl
  obtain ⟨a, b, c, σ₁, h₁, σ₂, h₂, h12, hcols⟩ := hcl ⟨n, hn.1⟩
  have hnM : I.Mat n (comp (gC D.ε a b c) (sigCols σ₁ σ₂)) := ⟨hn.1, hcols⟩
  obtain ⟨ε'', hε'', v₀, hv₀, w₀, hw₀, w₀', hw₀', hv₀c, hw₀c, hw₀'c⟩ := I.exists_vww H
  rw [eps_eq hε'' D.hε] at hw₀c hw₀'c
  have hgM : I.Mat (v₀ ^ (c : ℕ) * (w₀ ^ (a : ℕ) * w₀' ^ (b : ℕ))) (gC D.ε a b c) :=
    (Mat.pw ⟨_, hv₀c⟩ c).mul ((Mat.pw ⟨_, hw₀c⟩ a).mul (Mat.pw ⟨_, hw₀'c⟩ b))
  obtain ⟨q, hq, hqM⟩ := D.exists_mem_Q₁ hgM (gC_transl D.ε a b c)
  obtain ⟨i, j, hij⟩ := (sig_decomp σ₁ h₁ σ₂ h₂).resolve_left h12
  have hgM' : I.Mat (D.d ^ (i : ℕ) * D.u ^ (j : ℕ)) (sigCols σ₁ σ₂) := by
    have := (D.d_mat.pw3 i).mul (D.u_mat.pw j)
    rwa [hij] at this
  set g := q * (D.d ^ (i : ℕ) * D.u ^ (j : ℕ)) with hg
  have hc' : g⁻¹ * n ∈ centralizer (I.E : Set X) := (hqM.mul hgM').inv_mul_mem_centralizer hnM
  have huQ : D.u ∈ normalizer (D.Q₁ : Set X) := D.S₁_le_normalizer_Q₁ D.u_S₁
  have hgQ : g ∈ normalizer (D.Q₁ : Set X) :=
    mul_mem (le_normalizer hq) (mul_mem (pow_mem D.d_Q₁ _) (pow_mem huQ _))
  have hcQ : g⁻¹ * n ∈ normalizer (D.Q₁ : Set X) := mul_mem (inv_mem hgQ) hn.2
  have hgN : g ∈ normalizer (S.Q0 I.yi I.ki D.w₁ D.w₂ : Set X) :=
    mul_mem (D.Q₁_le_normalizer R hq)
      (mul_mem (pow_mem (D.d_normalizer R) _) (pow_mem D.u_normalizer _))
  have hcN := D.centralizer_normalizer R hc' hcQ
  have e : n = g * (g⁻¹ * n) := by group
  rw [e]
  exact mul_mem hgN hcN

end Data6

end Inst

end A7Base

end CFSG.ComponentClassification.HSFLit
