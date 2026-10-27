module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JC2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {H : Type} [Group H] [Finite H]

@[expose] noncomputable def zjMat (y z v₁ v₂ g : H) : ℕ :=
  zjCode y z v₁ v₂ (g * y * g⁻¹) ||| (zjCode y z v₁ v₂ (g * z * g⁻¹) <<< 4) |||
  (zjCode y z v₁ v₂ (g * v₁ * g⁻¹) <<< 8) ||| (zjCode y z v₁ v₂ (g * v₂ * g⁻¹) <<< 12)

private theorem pack_col :
    ∀ a0 a1 a2 a3 : Fin 16,
      ZJFin.col ((a0 : ℕ) ||| ((a1 : ℕ) <<< 4) ||| ((a2 : ℕ) <<< 8) |||
          ((a3 : ℕ) <<< 12)) 0 = a0 ∧
      ZJFin.col ((a0 : ℕ) ||| ((a1 : ℕ) <<< 4) ||| ((a2 : ℕ) <<< 8) |||
          ((a3 : ℕ) <<< 12)) 1 = a1 ∧
      ZJFin.col ((a0 : ℕ) ||| ((a1 : ℕ) <<< 4) ||| ((a2 : ℕ) <<< 8) |||
          ((a3 : ℕ) <<< 12)) 2 = a2 ∧
      ZJFin.col ((a0 : ℕ) ||| ((a1 : ℕ) <<< 4) ||| ((a2 : ℕ) <<< 8) |||
          ((a3 : ℕ) <<< 12)) 3 = a3 := by
  decide +kernel

private theorem pack_lt :
    ∀ a0 a1 a2 a3 : Fin 16,
      ((a0 : ℕ) ||| ((a1 : ℕ) <<< 4) ||| ((a2 : ℕ) <<< 8) ||| ((a3 : ℕ) <<< 12)) <
        65536 := by
  decide +kernel

private theorem conj_zjVec (y z v₁ v₂ g : H) (n : ℕ) :
    g * zjVec y z v₁ v₂ n * g⁻¹ =
      (g * y * g⁻¹) ^ (n &&& 1) * (g * z * g⁻¹) ^ ((n >>> 1) &&& 1) *
      (g * v₁ * g⁻¹) ^ ((n >>> 2) &&& 1) * (g * v₂ * g⁻¹) ^ ((n >>> 3) &&& 1) := by
  unfold zjVec
  rw [← conj_mul, ← conj_mul, ← conj_mul]
  rw [← conj_pow, ← conj_pow, ← conj_pow, ← conj_pow]

private theorem range_card_index {N α : Type*} [Group N] (K : Subgroup N) (f : N → α)
    (hf : ∀ n m : N, f n = f m ↔ n⁻¹ * m ∈ K) : Nat.card (Set.range f) = K.index := by
  let g : N ⧸ K → α := Quotient.lift f fun a b hab =>
    (hf a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro a b hab
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr ((hf _ _).mp hab)
  have hrange : Set.range f = Set.range g := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : N ⧸ K), rfl⟩
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H n => exact ⟨n, rfl⟩
  rw [hrange, Nat.card_range_of_injective hg]
  rfl

private theorem isP_of (x : ℕ) (hx : x < 65536) (h0 : 1 ≤ ZJFin.col x 0)
    (h0' : ZJFin.col x 0 ≤ 3) (h1 : 1 ≤ ZJFin.col x 1) (h1' : ZJFin.col x 1 ≤ 3)
    (h01 : ZJFin.col x 0 ≠ ZJFin.col x 1) (h2 : 4 ≤ ZJFin.col x 2)
    (h3 : 4 ≤ ZJFin.col x 3) (h23 : 4 ≤ ZJFin.col x 2 ^^^ ZJFin.col x 3) :
    ZJFin.isP x = true := by
  simp only [ZJFin.isP, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, and_assoc]
  exact ⟨hx, h0, h0', h1, h1', h01, h2, h3, h23⟩

namespace ZJBase

variable {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}
variable (h : ZJBase Q Y V V' B ρ t τ l y z v₁ v₂) include h

private theorem code_pow_conj {g u : H} (hu : u ∈ Y) {b : ℕ} (hb : b < 2) :
    zjCode y z v₁ v₂ ((g * u * g⁻¹) ^ b) =
      (if b != 0 then zjCode y z v₁ v₂ (g * u * g⁻¹) else 0) := by
  interval_cases b
  · simpa using h.code_one
  · simp

private theorem code_mul4 {a b c d : H} (ha : a ∈ Y) (hb : b ∈ Y) (hc : c ∈ Y)
    (hd : d ∈ Y) :
    zjCode y z v₁ v₂ (a * b * c * d) =
      zjCode y z v₁ v₂ a ^^^ zjCode y z v₁ v₂ b ^^^ zjCode y z v₁ v₂ c ^^^
        zjCode y z v₁ v₂ d := by
  rw [h.code_mul (mul_mem (mul_mem ha hb) hc) hd, h.code_mul (mul_mem ha hb) hc,
    h.code_mul ha hb]

theorem mat_col (g : H) :
    ZJFin.col (zjMat y z v₁ v₂ g) 0 = zjCode y z v₁ v₂ (g * y * g⁻¹) ∧
    ZJFin.col (zjMat y z v₁ v₂ g) 1 = zjCode y z v₁ v₂ (g * z * g⁻¹) ∧
    ZJFin.col (zjMat y z v₁ v₂ g) 2 = zjCode y z v₁ v₂ (g * v₁ * g⁻¹) ∧
    ZJFin.col (zjMat y z v₁ v₂ g) 3 = zjCode y z v₁ v₂ (g * v₂ * g⁻¹) := by
  have h0 : zjCode y z v₁ v₂ (g * y * g⁻¹) < 16 := h.code_lt (h.normal_Y g y h.y_mem)
  have h1 : zjCode y z v₁ v₂ (g * z * g⁻¹) < 16 := h.code_lt (h.normal_Y g z h.z_mem)
  have h2 : zjCode y z v₁ v₂ (g * v₁ * g⁻¹) < 16 := h.code_lt (h.normal_Y g v₁ h.v₁_mem)
  have h3 : zjCode y z v₁ v₂ (g * v₂ * g⁻¹) < 16 := h.code_lt (h.normal_Y g v₂ h.v₂_mem)
  unfold zjMat
  exact pack_col ⟨_, h0⟩ ⟨_, h1⟩ ⟨_, h2⟩ ⟨_, h3⟩

theorem mat_lt (g : H) : zjMat y z v₁ v₂ g < 65536 := by
  have h0 : zjCode y z v₁ v₂ (g * y * g⁻¹) < 16 := h.code_lt (h.normal_Y g y h.y_mem)
  have h1 : zjCode y z v₁ v₂ (g * z * g⁻¹) < 16 := h.code_lt (h.normal_Y g z h.z_mem)
  have h2 : zjCode y z v₁ v₂ (g * v₁ * g⁻¹) < 16 := h.code_lt (h.normal_Y g v₁ h.v₁_mem)
  have h3 : zjCode y z v₁ v₂ (g * v₂ * g⁻¹) < 16 := h.code_lt (h.normal_Y g v₂ h.v₂_mem)
  unfold zjMat
  exact pack_lt ⟨_, h0⟩ ⟨_, h1⟩ ⟨_, h2⟩ ⟨_, h3⟩

theorem mat_app {n : ℕ} (hn : n < 16) (g : H) :
    ZJFin.app (zjMat y z v₁ v₂ g) n = zjCode y z v₁ v₂ (g * zjVec y z v₁ v₂ n * g⁻¹) := by
  obtain ⟨hc0, hc1, hc2, hc3⟩ := h.mat_col g
  have hy : g * y * g⁻¹ ∈ Y := h.normal_Y g y h.y_mem
  have hz : g * z * g⁻¹ ∈ Y := h.normal_Y g z h.z_mem
  have hv1 : g * v₁ * g⁻¹ ∈ Y := h.normal_Y g v₁ h.v₁_mem
  have hv2 : g * v₂ * g⁻¹ ∈ Y := h.normal_Y g v₂ h.v₂_mem
  have hbit : ∀ k : ℕ, k &&& 1 < 2 := fun k => by
    have := Nat.and_le_right (n := k) (m := 1)
    omega
  have e0 := h.code_pow_conj (g := g) h.y_mem (b := n &&& 1) (hbit n)
  have e1 := h.code_pow_conj (g := g) h.z_mem (b := (n >>> 1) &&& 1) (hbit _)
  have e2 := h.code_pow_conj (g := g) h.v₁_mem (b := (n >>> 2) &&& 1) (hbit _)
  have e3 := h.code_pow_conj (g := g) h.v₂_mem (b := (n >>> 3) &&& 1) (hbit _)
  unfold ZJFin.app
  rw [hc0, hc1, hc2, hc3]
  rw [conj_zjVec]
  rw [h.code_mul4 (pow_mem hy (n &&& 1)) (pow_mem hz ((n >>> 1) &&& 1))
    (pow_mem hv1 ((n >>> 2) &&& 1)) (pow_mem hv2 ((n >>> 3) &&& 1))]
  simp only [e0, e1, e2, e3]
  interval_cases n <;> simp

theorem mat_mul (g g' : H) :
    zjMat y z v₁ v₂ (g * g') = ZJFin.mmul (zjMat y z v₁ v₂ g) (zjMat y z v₁ v₂ g') := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := h.mat_col g'
  have hcy : g' * y * g'⁻¹ ∈ Y := h.normal_Y g' y h.y_mem
  have hcz : g' * z * g'⁻¹ ∈ Y := h.normal_Y g' z h.z_mem
  have hcv1 : g' * v₁ * g'⁻¹ ∈ Y := h.normal_Y g' v₁ h.v₁_mem
  have hcv2 : g' * v₂ * g'⁻¹ ∈ Y := h.normal_Y g' v₂ h.v₂_mem
  have hc0 : zjCode y z v₁ v₂ (g' * y * g'⁻¹) < 16 := h.code_lt hcy
  have hc1 : zjCode y z v₁ v₂ (g' * z * g'⁻¹) < 16 := h.code_lt hcz
  have hc2 : zjCode y z v₁ v₂ (g' * v₁ * g'⁻¹) < 16 := h.code_lt hcv1
  have hc3 : zjCode y z v₁ v₂ (g' * v₂ * g'⁻¹) < 16 := h.code_lt hcv2
  unfold ZJFin.mmul
  rw [hb0, hb1, hb2, hb3]
  rw [h.mat_app hc0 g, h.mat_app hc1 g, h.mat_app hc2 g, h.mat_app hc3 g]
  rw [h.vec_code hcy, h.vec_code hcz, h.vec_code hcv1, h.vec_code hcv2]
  have e0 : zjCode y z v₁ v₂ (g * (g' * y * g'⁻¹) * g⁻¹) =
      zjCode y z v₁ v₂ ((g * g') * y * (g * g')⁻¹) := congrArg _ (by group)
  have e1 : zjCode y z v₁ v₂ (g * (g' * z * g'⁻¹) * g⁻¹) =
      zjCode y z v₁ v₂ ((g * g') * z * (g * g')⁻¹) := congrArg _ (by group)
  have e2 : zjCode y z v₁ v₂ (g * (g' * v₁ * g'⁻¹) * g⁻¹) =
      zjCode y z v₁ v₂ ((g * g') * v₁ * (g * g')⁻¹) := congrArg _ (by group)
  have e3 : zjCode y z v₁ v₂ (g * (g' * v₂ * g'⁻¹) * g⁻¹) =
      zjCode y z v₁ v₂ ((g * g') * v₂ * (g * g')⁻¹) := congrArg _ (by group)
  unfold zjMat
  simp only [e0, e1, e2, e3]

theorem mat_one : zjMat y z v₁ v₂ (1 : H) = ZJFin.one := by
  obtain ⟨hb0, hb1, hb2, hb4, hb8⟩ := h.vec_basis
  have c1 : zjCode y z v₁ v₂ y = 1 := by
    have hv := h.code_vec (n := 1) (by norm_num)
    rwa [hb1] at hv
  have c2 : zjCode y z v₁ v₂ z = 2 := by
    have hv := h.code_vec (n := 2) (by norm_num)
    rwa [hb2] at hv
  have c4 : zjCode y z v₁ v₂ v₁ = 4 := by
    have hv := h.code_vec (n := 4) (by norm_num)
    rwa [hb4] at hv
  have c8 : zjCode y z v₁ v₂ v₂ = 8 := by
    have hv := h.code_vec (n := 8) (by norm_num)
    rwa [hb8] at hv
  unfold zjMat ZJFin.one
  rw [show (1 : H) * y * 1⁻¹ = y by group, show (1 : H) * z * 1⁻¹ = z by group,
    show (1 : H) * v₁ * 1⁻¹ = v₁ by group, show (1 : H) * v₂ * 1⁻¹ = v₂ by group]
  rw [c1, c2, c4, c8]
  decide

theorem mat_eq_iff (g g' : H) :
    zjMat y z v₁ v₂ g = zjMat y z v₁ v₂ g' ↔ g⁻¹ * g' ∈ centralizer (Y : Set H) := by
  constructor
  · intro heq
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨n, hn, rfl⟩ := h.vec_surj hu
    have h1 : ZJFin.app (zjMat y z v₁ v₂ g) n = ZJFin.app (zjMat y z v₁ v₂ g') n := by
      rw [heq]
    rw [h.mat_app hn g, h.mat_app hn g'] at h1
    have hy1 : g * zjVec y z v₁ v₂ n * g⁻¹ ∈ Y := h.normal_Y g _ (h.vec_mem n)
    have hy2 : g' * zjVec y z v₁ v₂ n * g'⁻¹ ∈ Y := h.normal_Y g' _ (h.vec_mem n)
    have hee : g * zjVec y z v₁ v₂ n * g⁻¹ = g' * zjVec y z v₁ v₂ n * g'⁻¹ :=
      h.eq_of_code_eq hy1 hy2 h1
    calc zjVec y z v₁ v₂ n * (g⁻¹ * g')
        = g⁻¹ * (g * zjVec y z v₁ v₂ n * g⁻¹) * g' := by group
      _ = g⁻¹ * (g' * zjVec y z v₁ v₂ n * g'⁻¹) * g' := by rw [hee]
      _ = (g⁻¹ * g') * zjVec y z v₁ v₂ n := by group
  · intro hc
    have key : ∀ e ∈ ({y, z, v₁, v₂} : Set H), g * e * g⁻¹ = g' * e * g'⁻¹ := by
      intro e he
      have heY : e ∈ Y := by
        rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using he :
          e = y ∨ e = z ∨ e = v₁ ∨ e = v₂) with rfl | rfl | rfl | rfl
        · exact h.y_mem
        · exact h.z_mem
        · exact h.v₁_mem
        · exact h.v₂_mem
      have hcomm : e * (g⁻¹ * g') = (g⁻¹ * g') * e :=
        (Subgroup.mem_centralizer_iff.mp hc) e heY
      calc g * e * g⁻¹ = g * (e * (g⁻¹ * g')) * g'⁻¹ := by group
        _ = g * ((g⁻¹ * g') * e) * g'⁻¹ := by rw [hcomm]
        _ = g' * e * g'⁻¹ := by group
    have e0 : zjCode y z v₁ v₂ (g * y * g⁻¹) = zjCode y z v₁ v₂ (g' * y * g'⁻¹) :=
      congrArg _ (key y (by simp))
    have e1 : zjCode y z v₁ v₂ (g * z * g⁻¹) = zjCode y z v₁ v₂ (g' * z * g'⁻¹) :=
      congrArg _ (key z (by simp))
    have e2 : zjCode y z v₁ v₂ (g * v₁ * g⁻¹) = zjCode y z v₁ v₂ (g' * v₁ * g'⁻¹) :=
      congrArg _ (key v₁ (by simp))
    have e3 : zjCode y z v₁ v₂ (g * v₂ * g⁻¹) = zjCode y z v₁ v₂ (g' * v₂ * g'⁻¹) :=
      congrArg _ (key v₂ (by simp))
    unfold zjMat
    simp only [e0, e1, e2, e3]

theorem mat_mem_P (g : H) : zjMat y z v₁ v₂ g ∈ ZJFin.Plist := by
  have hyV : y ∈ V := by rw [h.V_eq]; exact Subgroup.subset_closure (by simp)
  have hzV : z ∈ V := by rw [h.V_eq]; exact Subgroup.subset_closure (by simp)
  have hcy : g * y * g⁻¹ ∈ Y := h.normal_Y g y h.y_mem
  have hcz : g * z * g⁻¹ ∈ Y := h.normal_Y g z h.z_mem
  have hcv1 : g * v₁ * g⁻¹ ∈ Y := h.normal_Y g v₁ h.v₁_mem
  have hcv2 : g * v₂ * g⁻¹ ∈ Y := h.normal_Y g v₂ h.v₂_mem
  have hv1V' : v₁ ∈ V' := by rw [h.V'_eq]; exact Subgroup.subset_closure (by simp)
  have hv2V' : v₂ ∈ V' := by rw [h.V'_eq]; exact Subgroup.subset_closure (by simp)
  have hc0le : zjCode y z v₁ v₂ (g * y * g⁻¹) ≤ 3 := by
    have := (h.code_lt_four_iff hcy).mpr (h.normal_V g y hyV)
    omega
  have hc1le : zjCode y z v₁ v₂ (g * z * g⁻¹) ≤ 3 := by
    have := (h.code_lt_four_iff hcz).mpr (h.normal_V g z hzV)
    omega
  have hc0ne : zjCode y z v₁ v₂ (g * y * g⁻¹) ≠ 0 := by
    intro hz0
    have hgy : g * y * g⁻¹ = 1 := by
      have hv := h.vec_code hcy
      rw [hz0] at hv
      rw [h.vec_basis.1] at hv
      exact hv.symm
    have hy1 : y = 1 := by
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [hgy]; group
    exact h.y_ne_one hy1
  have hc1ne : zjCode y z v₁ v₂ (g * z * g⁻¹) ≠ 0 := by
    intro hz0
    have hgz : g * z * g⁻¹ = 1 := by
      have hv := h.vec_code hcz
      rw [hz0] at hv
      rw [h.vec_basis.1] at hv
      exact hv.symm
    have hz1 : z = 1 := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [hgz]; group
    exact h.z_ne_one hz1
  have hc01 : zjCode y z v₁ v₂ (g * y * g⁻¹) ≠ zjCode y z v₁ v₂ (g * z * g⁻¹) := by
    intro he
    have hyz : g * y * g⁻¹ = g * z * g⁻¹ := h.eq_of_code_eq hcy hcz he
    have : y = z := by
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [hyz]
        _ = z := by group
    exact h.y_ne_z this
  have hv1notV : g * v₁ * g⁻¹ ∉ V := by
    intro hmem
    have hv1V : v₁ ∈ V := by
      have hvv := h.normal_V g⁻¹ (g * v₁ * g⁻¹) hmem
      rwa [show g⁻¹ * (g * v₁ * g⁻¹) * (g⁻¹)⁻¹ = v₁ by group] at hvv
    have : v₁ = 1 := by
      have hmem' : v₁ ∈ V ⊓ V' := ⟨hv1V, hv1V'⟩
      rw [h.V_inf_V'] at hmem'
      simpa using hmem'
    exact h.v₁_ne_one this
  have hv2notV : g * v₂ * g⁻¹ ∉ V := by
    intro hmem
    have hv2V : v₂ ∈ V := by
      have hvv := h.normal_V g⁻¹ (g * v₂ * g⁻¹) hmem
      rwa [show g⁻¹ * (g * v₂ * g⁻¹) * (g⁻¹)⁻¹ = v₂ by group] at hvv
    have : v₂ = 1 := by
      have hmem' : v₂ ∈ V ⊓ V' := ⟨hv2V, hv2V'⟩
      rw [h.V_inf_V'] at hmem'
      simpa using hmem'
    exact h.v₂_ne_one this
  have hc2 : 4 ≤ zjCode y z v₁ v₂ (g * v₁ * g⁻¹) := by
    have := (h.code_lt_four_iff hcv1).not.mpr hv1notV
    omega
  have hc3 : 4 ≤ zjCode y z v₁ v₂ (g * v₂ * g⁻¹) := by
    have := (h.code_lt_four_iff hcv2).not.mpr hv2notV
    omega
  have hcm : zjCode y z v₁ v₂ (g * v₁ * g⁻¹) ^^^ zjCode y z v₁ v₂ (g * v₂ * g⁻¹) =
      zjCode y z v₁ v₂ (g * (v₁ * v₂) * g⁻¹) := by
    rw [← h.code_mul hcv1 hcv2]
    congr 1
    group
  have hv12Y : v₁ * v₂ ∈ Y := mul_mem h.v₁_mem h.v₂_mem
  have hv12notV : g * (v₁ * v₂) * g⁻¹ ∉ V := by
    intro hmem
    have hv12V : v₁ * v₂ ∈ V := by
      have hvv := h.normal_V g⁻¹ (g * (v₁ * v₂) * g⁻¹) hmem
      rwa [show g⁻¹ * (g * (v₁ * v₂) * g⁻¹) * (g⁻¹)⁻¹ = v₁ * v₂ by group] at hvv
    have hv12V' : v₁ * v₂ ∈ V' := mul_mem hv1V' hv2V'
    have h1 : v₁ * v₂ = 1 := by
      have hmem' : v₁ * v₂ ∈ V ⊓ V' := ⟨hv12V, hv12V'⟩
      rw [h.V_inf_V'] at hmem'
      simpa using hmem'
    have hv1eqv2 : v₁ = v₂ := by
      have hv2sq : v₂ * v₂ = 1 := h.Y_sq v₂ h.v₂_mem
      calc v₁ = v₁ * (v₂ * v₂) := by rw [hv2sq, mul_one]
        _ = (v₁ * v₂) * v₂ := by group
        _ = v₂ := by rw [h1, one_mul]
    exact h.v₁_ne_v₂ hv1eqv2
  have hc23 : 4 ≤ zjCode y z v₁ v₂ (g * v₁ * g⁻¹) ^^^ zjCode y z v₁ v₂ (g * v₂ * g⁻¹) := by
    rw [hcm]
    have := (h.code_lt_four_iff (h.normal_Y g (v₁ * v₂) hv12Y)).not.mpr hv12notV
    omega
  rw [ZJFin.mem_Plist_iff]
  refine ⟨h.mat_lt g, isP_of (zjMat y z v₁ v₂ g) (h.mat_lt g) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rw [(h.mat_col g).1]; omega
  · rw [(h.mat_col g).1]; exact hc0le
  · rw [(h.mat_col g).2.1]; omega
  · rw [(h.mat_col g).2.1]; exact hc1le
  · rw [(h.mat_col g).1, (h.mat_col g).2.1]; exact hc01
  · rw [(h.mat_col g).2.2.1]; exact hc2
  · rw [(h.mat_col g).2.2.2]; exact hc3
  · rw [(h.mat_col g).2.2.1, (h.mat_col g).2.2.2]; exact hc23

theorem card_range_mat :
    Nat.card (Set.range (zjMat y z v₁ v₂)) * Nat.card (centralizer (Y : Set H)) =
      Nat.card H := by
  have hK := range_card_index (centralizer (Y : Set H)) (zjMat y z v₁ v₂)
    (fun a b => h.mat_eq_iff a b)
  rw [hK]
  exact Subgroup.index_mul_card _

end ZJBase

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
