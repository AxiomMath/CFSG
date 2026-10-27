module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Bar
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7E

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

abbrev d0 : Perm (Fin 7) := swap 1 3 * swap 1 2

abbrev d1 : Perm (Fin 7) := swap 0 4 * swap 0 1 * (swap 2 5 * swap 2 3)

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

variable (Λ : A7Sigma S.t S.L S.data)

theorem E_comm {yi : X} (hyi : yi ∈ S.data.R) {a b : X} (ha : a ∈ S.E yi) (hb : b ∈ S.E yi) :
    a * b = b * a := by
  have hT : ∀ v ∈ ({S.z, yi, S.t, S.k} : Set X), v ∈ S.data.T := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact S.z_mem.1
    · exact hyi.1
    · exact S.data.t_mem_T
    · exact S.k_mem
  have hzB : S.z ∈ S.B := subset_closure (by simp)
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hkB : S.k ∈ S.B := subset_closure (by simp)
  have hcomm : ({S.z, yi, S.t, S.k} : Set X).Pairwise Commute := by
    intro u hu v hv _
    have hvT := hT v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact S.central_of_mem_B hzB hvT
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact (S.central_of_mem_B hzB hyi.1).symm
      · exact Commute.refl _
      · exact (S.central_of_mem_B htB hyi.1).symm
      · exact (S.central_of_mem_B hkB hyi.1).symm
    · exact S.central_of_mem_B htB hvT
    · exact S.central_of_mem_B hkB hvT
  have h : (⟨a, ha⟩ : closure ({S.z, yi, S.t, S.k} : Set X)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    (isMulCommutative_closure hcomm).is_comm.comm _ _
  exact congrArg Subtype.val h

theorem E_sq {yi : X} (hyi : yi ∈ S.data.R) (hyi2 : yi ^ 2 = 1) {a : X} (ha : a ∈ S.E yi) :
    a ^ 2 = 1 := by
  have hz2 : S.z ^ 2 = 1 := S.sq_of_mem_B (subset_closure (by simp))
  induction ha using Subgroup.closure_induction with
  | mem u hu =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hz2
    · exact hyi2
    · exact S.t_sq
    · exact S.k_sq
  | one => exact one_pow 2
  | mul u v hu hv ihu ihv =>
    rw [(show Commute u v from S.E_comm hyi hu hv).mul_pow, ihu, ihv, one_mul]
  | inv u hu ih => rw [inv_pow, ih, inv_one]

theorem mem_C_of_mem_E {yi : X} (hyi : yi ∈ S.data.R) {a : X} (ha : a ∈ S.E yi) :
    a ∈ centralizer ({S.t} : Set X) :=
  S.data.T_le_centralizer (S.E_le_T hyi ha)

theorem act_prod {u v w q : X} (hu : u ∈ centralizer ({S.t} : Set X))
    (hv : v ∈ centralizer ({S.t} : Set X)) (hw : w ∈ centralizer ({S.t} : Set X))
    (hq : q ∈ centralizer ({S.t} : Set X)) (a b c d : ℕ) :
    S.act Λ (u ^ a * v ^ b * w ^ c * q ^ d) =
      S.act Λ u ^ a * S.act Λ v ^ b * S.act Λ w ^ c * S.act Λ q ^ d := by
  rw [S.act_mul Λ (mul_mem (mul_mem (pow_mem hu a) (pow_mem hv b)) (pow_mem hw c)) (pow_mem hq d),
    S.act_mul Λ (mul_mem (pow_mem hu a) (pow_mem hv b)) (pow_mem hw c),
    S.act_mul Λ (pow_mem hu a) (pow_mem hv b), S.act_pow Λ hu, S.act_pow Λ hv, S.act_pow Λ hw,
    S.act_pow Λ hq]

theorem exists_d {yi : X} (hyi : yi ∈ S.data.R) {σ : Perm (Fin 7)}
    (hσ : ∀ p ∈ S.E yi, ∃ p' ∈ S.E yi, S.act Λ p' = σ * S.act Λ p * σ⁻¹) {y₁ y₂ : X}
    (hy₁ : y₁ ∈ S.data.R) (hy₂ : y₂ ∈ S.data.R) (hy₁E : y₁ ∈ S.E yi) (hy₂E : y₂ ∈ S.E yi)
    (h₁ : S.act Λ y₁ = σ * S.act Λ S.z * σ⁻¹) (h₂ : S.act Λ y₂ = σ * S.act Λ yi * σ⁻¹) :
    ∃ d ∈ centralizer ({S.t} : Set X), d ∈ normalizer (S.E yi : Set X) ∧
      d * S.z * d⁻¹ = y₁ ∧ d * yi * d⁻¹ = y₂ := by
  have hEC : S.E yi ≤ centralizer ({S.t} : Set X) := fun a ha => S.mem_C_of_mem_E hyi ha
  have htE : S.t ∈ S.E yi := subset_closure (by simp)
  have hEp : IsPGroup 2 (S.E yi) := S.data.isPGroup_T.to_le (S.E_le_T hyi)
  obtain ⟨g, hgC, hgP, p₀, hp₀, hgact⟩ := S.exists_normalizer_act_eq Λ hEp hEC htE hσ
  have hgN : g ∈ normalizer (S.E yi : Set X) := mem_normalizer_of_conj_mem hgP
  have hgL : g ∈ normalizer (S.L : Set X) := S.centralizer_le_normalizer_L hgC
  have hp₀C := hEC hp₀
  have key : ∀ {u v : X}, u ∈ S.data.R → u ∈ S.E yi → v ∈ S.data.R → v ∈ S.E yi →
      S.act Λ v = σ * S.act Λ u * σ⁻¹ → g * u * g⁻¹ = v := by
    intro u v hu huE hv hvE huv
    have hguE : g * u * g⁻¹ ∈ S.E yi := (mem_normalizer_iff.mp hgN u).mp huE
    have hguR : g * u * g⁻¹ ∈ S.data.R :=
      ⟨S.E_le_T hyi hguE, (mem_normalizer_iff.mp hgL u).mp hu.2⟩
    have hact : S.act Λ (g * u * g⁻¹) = S.act Λ v := by
      have hcomm : S.act Λ p₀ * S.act Λ v = S.act Λ v * S.act Λ p₀ := by
        rw [← S.act_mul Λ hp₀C (hEC hvE), ← S.act_mul Λ (hEC hvE) hp₀C, S.E_comm hyi hp₀ hvE]
      rw [S.act_conj Λ hgC (hEC huE), hgact, mul_inv_rev]
      calc S.act Λ p₀ * σ * S.act Λ u * (σ⁻¹ * (S.act Λ p₀)⁻¹)
          = S.act Λ p₀ * (σ * S.act Λ u * σ⁻¹) * (S.act Λ p₀)⁻¹ := by group
        _ = S.act Λ v := by rw [← huv, hcomm]; group
    refine S.data.eq_of_ψ_eq hguR hv ?_
    rw [← S.act_of_mem_T Λ hguR.1, ← S.act_of_mem_T Λ hv.1, hact]
  exact ⟨g, hgC, hgN, key S.z_mem (subset_closure (by simp)) hy₁ hy₁E h₁,
    key hyi (subset_closure (by simp)) hy₂ hy₂E h₂⟩

theorem act_xy : S.act Λ (S.x * S.y) = rho0 * (c0 * b0) := by
  rw [S.act_mul Λ (S.data.T_le_centralizer S.x_mem.1) (S.data.T_le_centralizer S.y_mem.1),
    S.act_of_mem_T Λ S.x_mem.1, S.act_of_mem_T Λ S.y_mem.1, S.ψ_x, S.ψ_y]

theorem act_y : S.act Λ S.y = c0 * b0 := by rw [S.act_of_mem_T Λ S.y_mem.1, S.ψ_y]

theorem exists_d_xy_of_sigma (Λ : A7Sigma S.t S.L S.data) : ∃ d ∈ centralizer ({S.t} : Set X),
    d ∈ normalizer (S.E (S.x * S.y) : Set X) ∧ d * S.z * d⁻¹ = S.x * S.y ∧
      d * (S.x * S.y) * d⁻¹ = S.z * (S.x * S.y) ∧ d * S.k * d⁻¹ = S.k := by
  have hxy := S.xy_mem
  have hzxy : S.z * (S.x * S.y) ∈ S.data.R := mul_mem S.z_mem hxy
  have hzC := S.data.T_le_centralizer S.z_mem.1
  have hxyC := S.data.T_le_centralizer hxy.1
  have hzxyC := S.data.T_le_centralizer hzxy.1
  have hkC := S.data.T_le_centralizer S.k_mem
  have hσ : ∀ p ∈ S.E (S.x * S.y), ∃ p' ∈ S.E (S.x * S.y), S.act Λ p' = d0 * S.act Λ p * d0⁻¹ := by
    intro p hp
    obtain ⟨a, b, c, d, rfl⟩ := S.eq_of_mem_E hxy S.xy_sq (S.z_comm_of_mem_T hxy.1) hp
    have hxyE : S.x * S.y ∈ S.E (S.x * S.y) := subset_closure (by simp)
    have hzE : S.z ∈ S.E (S.x * S.y) := subset_closure (by simp)
    have htE : S.t ∈ S.E (S.x * S.y) := subset_closure (by simp)
    have hkE : S.k ∈ S.E (S.x * S.y) := subset_closure (by simp)
    refine ⟨(S.x * S.y) ^ (a : ℕ) * (S.z * (S.x * S.y)) ^ (b : ℕ) * S.t ^ (c : ℕ) * S.k ^ (d : ℕ),
      mul_mem (mul_mem (mul_mem (pow_mem hxyE _) (pow_mem (mul_mem hzE hxyE) _))
        (pow_mem htE _)) (pow_mem hkE _), ?_⟩
    rw [S.act_prod Λ hxyC hzxyC S.t_mem_centralizer hkC,
      S.act_prod Λ hzC hxyC S.t_mem_centralizer hkC,
      S.act_mul Λ hzC hxyC, S.act_xy Λ, S.act_z Λ, S.act_t Λ, S.act_k Λ, one_pow, mul_one, mul_one]
    clear hp
    revert a b d
    decide
  obtain ⟨g, hgC, hgN, hgz, hgxy⟩ := S.exists_d Λ hxy hσ hxy hzxy (subset_closure (by simp))
    (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
    (by rw [S.act_xy Λ, S.act_z Λ]; decide)
    (by rw [S.act_mul Λ hzC hxyC, S.act_xy Λ, S.act_z Λ]; decide)
  exact ⟨g, hgC, hgN, hgz, hgxy, S.conj_k_eq_of_mem_normalizer ⟨hgN, hgC⟩⟩

theorem exists_d_y_of_sigma (Λ : A7Sigma S.t S.L S.data) : ∃ d ∈ centralizer ({S.t} : Set X),
    d ∈ normalizer (S.E S.y : Set X) ∧ d * S.z * d⁻¹ = S.z * S.y ∧
      d * S.y * d⁻¹ = S.z ∧ d * (S.z * S.k) * d⁻¹ = S.z * S.k := by
  have hy := S.y_mem
  have hzy : S.z * S.y ∈ S.data.R := mul_mem S.z_mem hy
  have hzC := S.data.T_le_centralizer S.z_mem.1
  have hyC := S.data.T_le_centralizer hy.1
  have hzyC := S.data.T_le_centralizer hzy.1
  have hkC := S.data.T_le_centralizer S.k_mem
  have hykC := S.data.T_le_centralizer (mul_mem hy.1 S.k_mem)
  have hσ : ∀ p ∈ S.E S.y, ∃ p' ∈ S.E S.y, S.act Λ p' = d1 * S.act Λ p * d1⁻¹ := by
    intro p hp
    obtain ⟨a, b, c, d, rfl⟩ := S.eq_of_mem_E hy S.y_sq (S.z_comm_of_mem_T hy.1) hp
    have hyE : S.y ∈ S.E S.y := subset_closure (by simp)
    have hzE : S.z ∈ S.E S.y := subset_closure (by simp)
    have htE : S.t ∈ S.E S.y := subset_closure (by simp)
    have hkE : S.k ∈ S.E S.y := subset_closure (by simp)
    refine ⟨(S.z * S.y) ^ (a : ℕ) * S.z ^ (b : ℕ) * S.t ^ (c : ℕ) * (S.y * S.k) ^ (d : ℕ),
      mul_mem (mul_mem (mul_mem (pow_mem (mul_mem hzE hyE) _) (pow_mem hzE _))
        (pow_mem htE _)) (pow_mem (mul_mem hyE hkE) _), ?_⟩
    rw [S.act_prod Λ hzyC hzC S.t_mem_centralizer hykC,
      S.act_prod Λ hzC hyC S.t_mem_centralizer hkC,
      S.act_mul Λ hzC hyC, S.act_mul Λ hyC hkC, S.act_y Λ, S.act_z Λ, S.act_t Λ, S.act_k Λ, one_pow,
      mul_one, mul_one]
    clear hp
    revert a b d
    decide
  obtain ⟨g, hgC, hgN, hgz, hgy⟩ := S.exists_d Λ hy hσ hzy S.z_mem
    (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) (subset_closure (by simp))
    (by rw [S.act_mul Λ hzC hyC, S.act_y Λ, S.act_z Λ]; decide)
    (by rw [S.act_y Λ, S.act_z Λ]; decide)
  exact ⟨g, hgC, hgN, hgz, hgy, S.conj_zk_eq_of_mem_normalizer ⟨hgN, hgC⟩⟩

theorem exists_d_xy : ∃ d ∈ centralizer ({S.t} : Set X),
    d ∈ normalizer (S.E (S.x * S.y) : Set X) ∧ d * S.z * d⁻¹ = S.x * S.y ∧
      d * (S.x * S.y) * d⁻¹ = S.z * (S.x * S.y) ∧ d * S.k * d⁻¹ = S.k := by
  rcases S.facts with h | hΛ
  · exact h.d_xy
  · obtain ⟨Λ⟩ := hΛ
    exact S.exists_d_xy_of_sigma Λ

theorem exists_d_y : ∃ d ∈ centralizer ({S.t} : Set X),
    d ∈ normalizer (S.E S.y : Set X) ∧ d * S.z * d⁻¹ = S.z * S.y ∧
      d * S.y * d⁻¹ = S.z ∧ d * (S.z * S.k) * d⁻¹ = S.z * S.k := by
  rcases S.facts with h | hΛ
  · exact h.d_y
  · obtain ⟨Λ⟩ := hΛ
    exact S.exists_d_y_of_sigma Λ

end A7Base

end CFSG.ComponentClassification.HSFLit
