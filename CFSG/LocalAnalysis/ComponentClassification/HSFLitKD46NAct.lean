module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46NInst

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

structure Hyp (R : Subgroup X) : Prop where
  isPGroup : IsPGroup 2 R
  le : S.TE ≤ R
  le_normalizer : R ≤ normalizer (S.TE : Set X)
  card : Nat.card R = 4 * Nat.card S.TE
  fus : Fus S
  le_E₁ : R ≤ normalizer (S.E S.y : Set X)
  le_E₂ : R ≤ normalizer (S.E (S.x * S.y) : Set X)
  inf_C : R ⊓ centralizer ({t} : Set X) = S.TE

namespace Inst

variable {S} (I : Inst S) {R : Subgroup X}

theorem R_le (H : Hyp S R) : R ≤ normalizer (I.E : Set X) := by
  rcases I.E_or with h | h <;> rw [h]
  · exact H.le_E₁
  · exact H.le_E₂

theorem conj_ki_of_mem_NC {n : X}
    (hn : n ∈ normalizer (I.E : Set X) ⊓ centralizer ({t} : Set X)) : n * I.ki * n⁻¹ = I.ki := by
  obtain ⟨yi, ki, ui, h⟩ := I
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact S.k_fixed n hn
  · exact S.zk_fixed n hn

theorem wV_eq_zero_of_mem_L (v : V4) (h : I.wV v ∈ L) : v.2.2.1 = 0 ∧ v.2.2.2 = 0 := by
  obtain ⟨a, b, c, d⟩ := v
  simp only
  have hzyL : S.z ^ (a : ℕ) * I.yi ^ (b : ℕ) ∈ L :=
    mul_mem (pow_mem (z_mem S).2 _) (pow_mem I.yi_mem.2 _)
  have htkL : t ^ (c : ℕ) * I.ki ^ (d : ℕ) ∈ L := by
    have e : t ^ (c : ℕ) * I.ki ^ (d : ℕ) =
        (S.z ^ (a : ℕ) * I.yi ^ (b : ℕ))⁻¹ * I.wV (a, b, c, d) := by
      simp only [wV]; group
    rw [e]
    exact mul_mem (inv_mem hzyL) h
  have hkiT : I.ki ∈ A.T := I.E_le_T I.ki_mem_E
  have htkT : t ^ (c : ℕ) * I.ki ^ (d : ℕ) ∈ A.T := mul_mem (pow_mem A.t_mem_T _) (pow_mem hkiT _)
  have hR : t ^ (c : ℕ) * I.ki ^ (d : ℕ) ∈ A.R := Subgroup.mem_inf.mpr ⟨htkT, htkL⟩
  have hψ := ψX_mem_R8 hR
  rw [ψX_mul (pow_mem A.t_mem_T _) (pow_mem hkiT _), ψX_pow A.t_mem_T, ψX_t, one_pow, one_mul,
    ψX_pow hkiT] at hψ
  have hd : d = 0 := by
    rcases Fin.exists_fin_two.mp ⟨d, rfl⟩ with rfl | rfl
    · rfl
    · exfalso
      simp only [Fin.val_one, pow_one] at hψ
      rcases I.ki_eq with hk | hk <;> rw [hk] at hψ
      · rw [ψ_k] at hψ
        exact k8_not_mem_R8 hψ
      · rw [ψX_mul (z_mem_T S) (k_mem_T S), ψ_z, ψ_k] at hψ
        exact z8_mul_k8_not_mem_R8 hψ
  subst hd
  refine ⟨?_, rfl⟩
  rcases Fin.exists_fin_two.mp ⟨c, rfl⟩ with rfl | rfl
  · rfl
  · exfalso
    apply A.config.not_mem
    simpa using htkL

theorem conj_mem_three {n : X} (hn : n ∈ normalizer (I.E : Set X) ⊓ centralizer ({t} : Set X))
    {e : X} (he : e = S.z ∨ e = I.yi ∨ e = S.z * I.yi) :
    n * e * n⁻¹ = S.z ∨ n * e * n⁻¹ = I.yi ∨ n * e * n⁻¹ = S.z * I.yi := by
  have heE : e ∈ I.E := by
    rcases he with rfl | rfl | rfl
    · exact I.z_mem_E
    · exact I.yi_mem_E
    · exact mul_mem I.z_mem_E I.yi_mem_E
  have heL : e ∈ L := by
    rcases he with rfl | rfl | rfl
    · exact (z_mem S).2
    · exact I.yi_mem.2
    · exact mul_mem (z_mem S).2 I.yi_mem.2
  have hne1 : e ≠ 1 := by
    rcases he with rfl | rfl | rfl
    · exact z_ne_one S
    · intro h
      apply I.yi_not_mem_B
      rw [h]
      exact one_mem _
    · intro h
      apply I.yi_not_mem_B
      have : I.yi = S.z⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact inv_mem (mem_B_z S)
  have hneE : n * e * n⁻¹ ∈ I.E := (mem_normalizer_iff.mp (mem_inf.mp hn).1 _).mp heE
  have hneL : n * e * n⁻¹ ∈ L := conj_mem_L (A := A) (mem_inf.mp hn).2 heL
  obtain ⟨v, hv⟩ := I.eq_wV hneE
  obtain ⟨hc, hd⟩ := I.wV_eq_zero_of_mem_L v (hv ▸ hneL)
  have hne : I.wV v ≠ 1 := by
    rw [← hv]
    intro h1
    apply hne1
    calc e = n⁻¹ * (n * e * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨a, b, c, d⟩ := v
  simp only at hc hd
  subst hc hd
  rw [hv]
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
  · exact absurd (by simp [wV]) hne
  · right; left; simp [wV]
  · left; simp [wV]
  · right; right; simp [wV]

theorem d_rels {d : X} (hd : d ∈ normalizer (I.E : Set X) ⊓ centralizer ({t} : Set X))
    (hdz : d * S.z * d⁻¹ = I.yi) (hdy : d * I.yi * d⁻¹ = S.z * I.yi) :
    d⁻¹ * I.yi * d = S.z ∧ d⁻¹ * S.z * d = S.z * I.yi ∧ d * (S.z * I.yi) * d⁻¹ = S.z ∧
      d * t * d⁻¹ = t ∧ d⁻¹ * t * d = t ∧ d⁻¹ * I.ki * d = I.ki ∧
      d * I.ki * d⁻¹ = I.ki := by
  have hzy : S.z * I.yi = I.yi * S.z := z_comm S I.yi_mem.1
  have hdk := I.conj_ki_of_mem_NC hd
  have hdt : d * t * d⁻¹ = t := t_conj_of_mem_C (mem_inf.mp hd).2
  have h3 : d * (S.z * I.yi) * d⁻¹ = S.z := by
    calc d * (S.z * I.yi) * d⁻¹ = d * S.z * d⁻¹ * (d * I.yi * d⁻¹) := by group
      _ = I.yi * I.yi * S.z := by rw [hdz, hdy, hzy, mul_assoc]
      _ = S.z := by rw [← pow_two, I.yi_sq, one_mul]
  refine ⟨?_, ?_, h3, hdt, ?_, ?_, hdk⟩
  · calc d⁻¹ * I.yi * d = d⁻¹ * (d * S.z * d⁻¹) * d := by rw [hdz]
      _ = S.z := by group
  · calc d⁻¹ * S.z * d = d⁻¹ * (d * (S.z * I.yi) * d⁻¹) * d := by rw [h3]
      _ = S.z * I.yi := by group
  · calc d⁻¹ * t * d = d⁻¹ * (d * t * d⁻¹) * d := by rw [hdt]
      _ = t := by group
  · calc d⁻¹ * I.ki * d = d⁻¹ * (d * I.ki * d⁻¹) * d := by rw [hdk]
      _ = I.ki := by group

theorem ui_mem : I.ui ∈ A.R := by
  rcases I.spec with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · exact xy_mem S
  · exact mul_mem (z_mem S) S.y_mem

theorem ui_mem_TE : I.ui ∈ S.TE := R_le_TE S I.ui_mem

theorem yi_mem_TE : I.yi ∈ S.TE := R_le_TE S I.yi_mem

theorem ui_sq : I.ui ^ 2 = 1 := by
  rcases I.spec with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h]
  · exact xy_sq S
  · rw [(show Commute S.z S.y from z_comm_y S).mul_pow, z_sq S, S.y_sq, one_mul]

theorem x_conj_y : S.x * S.y * S.x⁻¹ = S.z * S.y := by
  calc S.x * S.y * S.x⁻¹ = S.x * (S.y * S.x * S.y⁻¹)⁻¹ * S.y := by group
    _ = S.z * S.y := by rw [S.y_inv, inv_inv, ← pow_two]; rfl

theorem x_conj_xy : S.x * (S.x * S.y) * S.x⁻¹ = S.z * (S.x * S.y) := by
  calc S.x * (S.x * S.y) * S.x⁻¹ = S.x * (S.x * S.y * S.x⁻¹) := by group
    _ = S.x * (S.z * S.y) := by rw [x_conj_y]
    _ = S.z * (S.x * S.y) := by
        rw [← mul_assoc, ← mul_assoc, ← z_comm S (x_mem_T S)]

theorem x_conj_yi : S.x * I.yi * S.x⁻¹ = S.z * I.yi := by
  rcases I.yi_or with h | h <;> rw [h]
  · exact x_conj_y
  · exact x_conj_xy

theorem ui_conj_yi : I.ui * I.yi * I.ui⁻¹ = S.z * I.yi := by
  obtain ⟨yi, ki, ui, h⟩ := I
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · show S.x * S.y * S.y * (S.x * S.y)⁻¹ = S.z * S.y
    calc S.x * S.y * S.y * (S.x * S.y)⁻¹ = S.x * S.y * S.x⁻¹ := by group
      _ = S.z * S.y := x_conj_y
  · show S.z * S.y * (S.x * S.y) * (S.z * S.y)⁻¹ = S.z * (S.x * S.y)
    have hx3 : S.x⁻¹ = S.z * S.x := by
      rw [z_def, ← pow_succ, inv_eq_of_mul_eq_one_right]
      rw [← pow_succ', x_pow_four S]
    calc S.z * S.y * (S.x * S.y) * (S.z * S.y)⁻¹ = S.z * (S.y * S.x * S.y⁻¹) * S.y * S.z⁻¹ := by
          group
      _ = S.z * (S.z * S.x) * S.y * S.z := by rw [S.y_inv, hx3, z_inv S]
      _ = S.z * (S.x * S.y) := by
          rw [show S.z * (S.z * S.x) * S.y * S.z = S.z * S.z * S.x * (S.y * S.z) by group,
            ← pow_two, z_sq S, one_mul, ← z_comm S (y_mem_T S), ← mul_assoc,
            ← z_comm S (x_mem_T S), mul_assoc]

end Inst

end CFSG.ComponentClassification.HSFLit.KD46
