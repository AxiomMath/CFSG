module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBLA
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.EvenSporadicStandard.M24Std.SplitB

open Matrix Subgroup

variable {G : Type} [Group G]

structure SplitHyp (U W : Subgroup G) (z : G) (ε : (Fin 4 → F2) → G) : Prop where
  z_mem : z ∈ W
  z_sq : z * z = 1
  z_not_mem : z ∉ U
  z_comm_U : ∀ u ∈ U, z * u = u * z
  U_le : U ≤ W
  central : ∀ w ∈ W, ∀ u ∈ U, w * u = u * w
  sq_mem : ∀ w ∈ W, w * w ∈ U
  phi_mem : ∀ w ∈ W, z * (w⁻¹ * z * w) ∈ U
  phi_surj : ∀ u ∈ U, ∃ w ∈ W, z * (w⁻¹ * z * w) = u
  ker_phi : ∀ w ∈ W, z * w = w * z → w ∈ U ⊔ zpowers z
  eps_add : ∀ c d, ε (c + d) = ε c * ε d
  eps_inj : Function.Injective ε
  eps_mem : ∀ c, ε c ∈ U
  eps_surj : ∀ u ∈ U, ∃ c, ε c = u

variable {U W : Subgroup G} {z : G} {ε : (Fin 4 → F2) → G}

theorem eps_zero (E : SplitHyp U W z ε) : ε 0 = 1 := by
  have h := E.eps_add 0 0
  rw [add_zero] at h
  have h' : ε 0 * 1 = ε 0 * ε 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel h').symm

theorem exists_coords (E : SplitHyp U W z ε) :
    ∃ cd : G → (Fin 4 → F2), (∀ c, cd (ε c) = c) ∧ (∀ u ∈ U, ε (cd u) = u) ∧
      (∀ u ∈ U, ∀ u' ∈ U, cd (u * u') = cd u + cd u') ∧ cd 1 = 0 := by
  classical
  obtain ⟨cd, hcd_eps, hcd_mem⟩ : ∃ cd : G → (Fin 4 → F2), (∀ c, cd (ε c) = c) ∧
      (∀ u ∈ U, ε (cd u) = u) := by
    refine ⟨fun u => if h : ∃ c, ε c = u then h.choose else 0, ?_, ?_⟩
    · intro c
      have h : ∃ c', ε c' = ε c := ⟨c, rfl⟩
      simp only [h, ↓reduceDIte]
      exact E.eps_inj h.choose_spec
    · intro u hu
      obtain ⟨c, hc⟩ := E.eps_surj u hu
      have h : ∃ c', ε c' = u := ⟨c, hc⟩
      simp only [h, ↓reduceDIte]
      exact h.choose_spec
  refine ⟨cd, hcd_eps, hcd_mem, ?_, ?_⟩
  · intro u hu u' hu'
    apply E.eps_inj
    rw [E.eps_add, hcd_mem u hu, hcd_mem u' hu', hcd_mem (u * u') (mul_mem hu hu')]
  · rw [← eps_zero E, hcd_eps]

theorem prod_map_mem {H : Subgroup G} {m : ℕ} {g : Fin m → G} (hgH : ∀ k, g k ∈ H)
    (l : List (Fin m)) : (l.map g).prod ∈ H :=
  Subgroup.list_prod_mem H (fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact hgH k)

theorem word_conj {m : ℕ} {g : Fin m → G} {A : Fin m → Mat4}
    (hact : ∀ k c, g k * ε c * (g k)⁻¹ = ε (c ᵥ* A k)) (l : List (Fin m)) (c : Fin 4 → F2) :
    (l.map g).prod * ε c * ((l.map g).prod)⁻¹ = ε (c ᵥ* wordMat A l) := by
  induction l generalizing c with
  | nil => simp [wordMat]
  | cons k r ih =>
    rw [List.map_cons, List.prod_cons]
    simp only [wordMat]
    rw [← Matrix.vecMul_vecMul, ← hact k (c ᵥ* wordMat A r), ← ih c]
    group

theorem prod_mem_U (E : SplitHyp U W z ε) {H : Subgroup G} {m : ℕ} {g : Fin m → G}
    {A : Fin m → Mat4} (hgH : ∀ k, g k ∈ H)
    (hcent : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h ∈ U)
    (hact : ∀ k c, g k * ε c * (g k)⁻¹ = ε (c ᵥ* A k)) {l : List (Fin m)}
    (hl : wordMat A l = 1) : (l.map g).prod ∈ U := by
  refine hcent _ (prod_map_mem hgH l) fun u hu => ?_
  obtain ⟨c, rfl⟩ := E.eps_surj u hu
  have e : (l.map g).prod * ε c * ((l.map g).prod)⁻¹ = ε c := by
    rw [word_conj hact l c, hl, Matrix.vecMul_one]
  calc (l.map g).prod * ε c = ((l.map g).prod * ε c * ((l.map g).prod)⁻¹) * (l.map g).prod := by
        group
    _ = ε c * (l.map g).prod := by rw [e]

theorem exists_conj_matrix (E : SplitHyp U W z ε) {h : G} (hU : ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    ∃ M : Mat4, ∀ c, h * ε c * h⁻¹ = ε (c ᵥ* M) := by
  obtain ⟨cd, hcd_eps, hcd_mem, hcd_mul, hcd_one⟩ := exists_coords E
  let ψ : (Fin 4 → F2) →+ (Fin 4 → F2) :=
    { toFun := fun c => cd (h * ε c * h⁻¹)
      map_zero' := by simp [eps_zero E, hcd_one]
      map_add' := by
        intro c d
        have e : h * ε (c + d) * h⁻¹ = (h * ε c * h⁻¹) * (h * ε d * h⁻¹) := by
          rw [E.eps_add]; group
        show cd (h * ε (c + d) * h⁻¹) = cd (h * ε c * h⁻¹) + cd (h * ε d * h⁻¹)
        rw [e]
        exact hcd_mul _ (hU _ (E.eps_mem c)) _ (hU _ (E.eps_mem d)) }
  let Φ : (Fin 4 → F2) →ₗ[F2] (Fin 4 → F2) := AddMonoidHom.toZModLinearMap 2 ψ
  refine ⟨Matrix.of fun i => Φ (Pi.single i 1), fun c => ?_⟩
  have hΦ : Φ c = c ᵥ* Matrix.of fun i => Φ (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' c]
    rw [map_sum, vecMul_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  rw [← hΦ]
  exact (hcd_mem _ (hU _ (E.eps_mem c))).symm

theorem exists_conj_matrices (E : SplitHyp U W z ε) {H : Subgroup G}
    (hHU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) {h : G} (hh : h ∈ H) :
    ∃ M N : Mat4, M * N = 1 ∧ ∀ c, h * ε c * h⁻¹ = ε (c ᵥ* M) := by
  obtain ⟨M, hM⟩ := exists_conj_matrix E (hHU h hh)
  obtain ⟨N, hN⟩ := exists_conj_matrix E (hHU h⁻¹ (H.inv_mem hh))
  refine ⟨M, N, ?_, hM⟩
  have hc : ∀ c, c ᵥ* (M * N) = c := by
    intro c
    apply E.eps_inj
    rw [← Matrix.vecMul_vecMul, ← hN (c ᵥ* M), ← hM c]
    group
  ext i j
  have := congrFun (hc (Pi.single i 1)) j
  simpa [Matrix.single_one_vecMul, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem exists_word_mul (E : SplitHyp U W z ε) {H : Subgroup G} {m : ℕ} {g : Fin m → G}
    {A : Fin m → Mat4} (hHU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (hgH : ∀ k, g k ∈ H)
    (hcent : ∀ h ∈ H, (∀ u ∈ U, h * u = u * h) → h ∈ U)
    (hgen : ∀ M N : Mat4, M * N = 1 → ∃ l : List (Fin m), wordMat A l = M)
    (hact : ∀ k c, g k * ε c * (g k)⁻¹ = ε (c ᵥ* A k)) {h : G} (hh : h ∈ H) :
    ∃ l : List (Fin m), (l.map g).prod⁻¹ * h ∈ U := by
  obtain ⟨M, N, hMN, hM⟩ := exists_conj_matrices E hHU hh
  obtain ⟨l, hl⟩ := hgen M N hMN
  refine ⟨l, hcent _ (H.mul_mem (H.inv_mem (prod_map_mem hgH l)) hh) fun u hu => ?_⟩
  obtain ⟨c, rfl⟩ := E.eps_surj u hu
  have e : h * ε c * h⁻¹ = (l.map g).prod * ε c * ((l.map g).prod)⁻¹ := by
    rw [hM c, word_conj hact l c, hl]
  calc (l.map g).prod⁻¹ * h * ε c = (l.map g).prod⁻¹ * (h * ε c * h⁻¹) * h := by group
    _ = ε c * ((l.map g).prod⁻¹ * h) := by rw [e]; group

end CFSG.EvenSporadicStandard.M24Std.SplitB
