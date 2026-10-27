module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Gen
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Field
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaFactsProof
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaKernel

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint CFSG.EvenSmallLie.UnitarySix.YamadaEnd
open scoped MatrixGroups

variable {G : Type} [Group G]

structure Section3Out (F : Type) [Field F] [Finite F] [CharP F 2] [Finite G]
    (d : YamadaData G) : Prop where
  setting : StandardSetting G d.L
  center_eq : center d.L = ⊥
  lie : LieModel (d.L ⧸ center d.L) .PSU 6 2 1
  card_field : Nat.card F = 4
  order_t : orderOf d.t = 2
  t_mem : d.t ∈ centralizer (d.L : Set G)
  kernel : centralizer (d.L : Set G) ⊓ d.H = zpowers d.t
  sylow : IsSylowOf 2 d.S d.L
  card_normalizer : Nat.card (normalizer (d.S : Set G) ⊓ d.L : Subgroup G) = 2 ^ 15 * 3
  w₁_mem : d.w₁ ∈ d.L
  w₂_mem : d.w₂ ∈ d.L
  w₃_mem : d.w₃ ∈ d.L
  w₁_sq : d.w₁ * d.w₁ = 1
  w₂_sq : d.w₂ * d.w₂ = 1
  w₃_sq : d.w₃ * d.w₃ = 1
  braid : d.w₁ * d.w₂ * d.w₁ = d.w₂ * d.w₁ * d.w₂
  word_a : d.w₃ * d.w₂ * d.w₃ * d.w₁ * d.w₂ * d.w₃ * d.w₁ * d.w₂ = d.w₀ * d.w₁
  word_b : d.w₃ * d.w₂ * d.w₃ * d.w₁ * d.w₂ * d.w₃ * d.w₂ * d.w₁ = d.w₀ * d.w₂
  word_b' : d.w₁ * d.w₂ * d.w₃ * d.w₂ * d.w₁ * d.w₃ * d.w₂ * d.w₃ = d.w₀ * d.w₂
  word_c : d.w₁ * d.w₂ * d.w₃ * d.w₂ * d.w₁ * d.w₂ * d.w₃ * d.w₂ = d.w₀ * d.w₃
  word_c' : d.w₁ * d.w₂ * d.w₁ * d.w₃ * d.w₂ * d.w₃ * d.w₁ * d.w₂ = d.w₀ * d.w₃
  card_X₁ : Nat.card d.X₁ = 4
  card_X₂ : Nat.card d.X₂ = 4
  card_X₃ : Nat.card d.X₃ = 2
  w₁_gen : d.w₁ ∈ d.X₁ ⊔ conjR d.X₁ d.w₁
  w₂_gen : d.w₂ ∈ d.X₂ ⊔ conjR d.X₂ d.w₂
  w₃_gen : d.w₃ ∈ d.X₃ ⊔ conjR d.X₃ d.w₃
  X₂_quasisimple : CFSG.Open.IsQuasisimple (d.X₂ ⊔ conjR d.X₂ d.w₂ : Subgroup G)
  K₁_model : ∃ χ : msigma F ≃* d.K₁,
    (∀ A : msigma F, (A : SL(4, F)) = sY F 0 * sY F 2 → (χ A : G) = d.w₂) ∧
    (∀ A : msigma F, (A : SL(4, F)) = sY F 1 → (χ A : G) = d.w₃) ∧
    ∀ A : msigma F, (A : SL(4, F)) ∈ pstd F → (χ A : G) ∈ d.S ⊓ conjR d.S d.u₁
  K₂_pair : ∃ θ : SL(3, F) →* G, θ.range = d.K₂ ∧ θ.ker = center SL(3, F) ∧
    (CFSG.ClassicalInvolution.WeakCT.B12 F).map θ = d.X₁ ⊔ conjR d.X₁ d.w₁ ∧
    (CFSG.ClassicalInvolution.WeakCT.B23 F).map θ = d.X₂ ⊔ conjR d.X₂ d.w₂
  K₂_lie : LieModel d.K₂ .PSL 3 2 2
  L_gen : d.L ≤ d.X₁ ⊔ d.X₂ ⊔ d.X₃ ⊔ zpowers d.w₁ ⊔ zpowers d.w₂ ⊔ zpowers d.w₃
  K₂_gen : d.K₂ = d.X₁ ⊔ d.X₂ ⊔ zpowers d.w₁ ⊔ zpowers d.w₂
  K₁_gen : d.K₁ = d.X₂ ⊔ d.X₃ ⊔ zpowers d.w₂ ⊔ zpowers d.w₃
  K₁_le : d.K₁ ≤ d.L
  K₂_le : d.K₂ ≤ d.L
  A₁_le : d.A₁ ≤ d.S
  A₂_le : d.A₂ ≤ d.S
  K₁_A₁ : d.K₁ ⊓ d.A₁ = ⊥
  K₂_A₂ : d.K₂ ⊓ d.A₂ = ⊥
  KA₁ : (d.K₁ ⊔ d.A₁) ⊓ conjR (d.K₁ ⊔ d.A₁) d.u₁ = d.K₁
  KA₂ : (d.K₂ ⊔ d.A₂) ⊓ conjR (d.K₂ ⊔ d.A₂) d.u₂ = d.K₂
  S_w₀ : d.S ⊓ conjR d.S d.w₀ = ⊥
  S_a : (d.S ⊓ conjR d.S d.u₂) ⊓ conjR (d.S ⊓ conjR d.S d.u₂) (d.w₁ * d.w₂) = d.X₁
  S_b : (d.S ⊓ conjR d.S d.u₂) ⊓ conjR (d.S ⊓ conjR d.S d.u₂) (d.w₂ * d.w₁) = d.X₂
  S_c : (d.S ⊓ conjR d.S d.u₁) ⊓ conjR (d.S ⊓ conjR d.S d.u₁) (d.w₂ * d.w₃ * d.w₂) = d.X₃
  S_aba : (d.S ⊓ conjR d.S d.u₂) ⊓ conjR (d.S ⊓ conjR d.S d.u₂) (d.w₁ * d.w₂ * d.w₁) = ⊥
  card_S₂ : Nat.card (d.S ⊓ conjR d.S d.u₂ : Subgroup G) = 2 ^ 6

section Proof

open CFSG.Fischer

theorem sw_mem_sX {L : Subgroup G} {e : L ≃* T46} {k : ℕ} (hk : k < 18)
    {H : Subgroup (Equiv.Perm (Fin 693))} (h : gP k ∈ H) : phiG e (yamGen k) ∈ toG e H := by
  rw [phiG_mem_toG, psi0_yamGen hk]
  exact h

theorem phiG_w_inv {L : Subgroup G} {e : L ≃* T46} {k : ℕ} (h : yamGen k * yamGen k = 1) :
    (phiG e (yamGen k))⁻¹ = phiG e (yamGen k) := by
  rw [inv_eq_iff_mul_eq_one, ← map_mul, h, map_one]

theorem w_gen_mem {L : Subgroup G} {e : L ≃* T46} {k j : ℕ} {X : Subgroup G}
    (hsq : yamGen k * yamGen k = 1)
    (hgen : yamGen k = yamGen j * (yamGen k * yamGen j * yamGen k) * yamGen j)
    (hX : phiG e (yamGen j) ∈ X) : phiG e (yamGen k) ∈ X ⊔ conjR X (phiG e (yamGen k)) := by
  have h1 : phiG e (yamGen k) = phiG e (yamGen j) *
      ((phiG e (yamGen k))⁻¹ * phiG e (yamGen j) * phiG e (yamGen k)) * phiG e (yamGen j) := by
    rw [phiG_w_inv hsq]
    conv_lhs => rw [hgen]
    simp only [map_mul]
  have hmem : phiG e (yamGen j) *
      ((phiG e (yamGen k))⁻¹ * phiG e (yamGen j) * phiG e (yamGen k)) * phiG e (yamGen j) ∈
      X ⊔ conjR X (phiG e (yamGen k)) :=
    mul_mem (mul_mem (mem_sup_left hX) (mem_sup_right (conj_mem_conjR hX))) (mem_sup_left hX)
  rwa [← h1] at hmem

theorem section3Out {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hZ : center L = ⊥) (hQ : LieModel (L ⧸ center L) .PSU 6 2 1)
    {t : G} (htL : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (F : Type) [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (e : L ≃* T46) (V₁ D₁ D₂ N₁ N₂ P : Subgroup G) :
    Section3Out F (sec3Data e t V₁ D₁ D₂ N₁ N₂ P) where
  setting := hset
  center_eq := hZ
  lie := hQ
  card_field := hF
  order_t := ht
  t_mem := htL
  kernel := by
    obtain ⟨D, hD⟩ := Yamada.exists_setting hset hZ hQ htL ht
    exact hD.inf_centralizer_eq
  sylow := isSylowOf_sS
  card_normalizer := card_normalizer_sS
  w₁_mem := phiG_mem _
  w₂_mem := phiG_mem _
  w₃_mem := phiG_mem _
  w₁_sq := by
    show phiG e (yamGen 15) * phiG e (yamGen 15) = 1
    rw [← map_mul, w₁_sq, map_one]
  w₂_sq := by
    show phiG e (yamGen 16) * phiG e (yamGen 16) = 1
    rw [← map_mul, w₂_sq, map_one]
  w₃_sq := by
    show phiG e (yamGen 17) * phiG e (yamGen 17) = 1
    rw [← map_mul, w₃_sq, map_one]
  braid := by
    show phiG e (yamGen 15) * phiG e (yamGen 16) * phiG e (yamGen 15) =
      phiG e (yamGen 16) * phiG e (yamGen 15) * phiG e (yamGen 16)
    simp only [← map_mul, braid₁₂]
  word_a := by
    show _ = (phiG e (yamGen 15) * phiG e (yamGen 16) * phiG e (yamGen 17)) ^ 3 * _
    simp only [sec3Data, sw, Nat.add_zero, ← map_mul, ← map_pow]
    rw [word_a, yw₀]
  word_b := by
    show _ = (phiG e (yamGen 15) * phiG e (yamGen 16) * phiG e (yamGen 17)) ^ 3 * _
    simp only [sec3Data, sw, Nat.add_zero, ← map_mul, ← map_pow]
    rw [word_b, yw₀]
  word_b' := by
    show _ = (phiG e (yamGen 15) * phiG e (yamGen 16) * phiG e (yamGen 17)) ^ 3 * _
    simp only [sec3Data, sw, Nat.add_zero, ← map_mul, ← map_pow]
    rw [word_b', yw₀]
  word_c := by
    show _ = (phiG e (yamGen 15) * phiG e (yamGen 16) * phiG e (yamGen 17)) ^ 3 * _
    simp only [sec3Data, sw, Nat.add_zero, ← map_mul, ← map_pow]
    rw [word_c, yw₀]
  word_c' := by
    show _ = (phiG e (yamGen 15) * phiG e (yamGen 16) * phiG e (yamGen 17)) ^ 3 * _
    simp only [sec3Data, sw, Nat.add_zero, ← map_mul, ← map_pow]
    rw [word_c', yw₀]
  card_X₁ := card_sX₁
  card_X₂ := card_sX₂
  card_X₃ := card_sX₃
  w₁_gen := w_gen_mem (k := 15) (j := 0) w₁_sq w₁_gen
    (sw_mem_sX (by norm_num) (by rw [← wP_single]; exact wP_mem_grp (by simp [chX1])))
  w₂_gen := w_gen_mem (k := 16) (j := 2) w₂_sq w₂_gen
    (sw_mem_sX (by norm_num) (by rw [← wP_single]; exact wP_mem_grp (by simp [chX2])))
  w₃_gen := w_gen_mem (k := 17) (j := 4) w₃_sq w₃_gen
    (sw_mem_sX (by norm_num) (by rw [← wP_single]; exact wP_mem_grp (by simp [chX3])))
  X₂_quasisimple := X₂_quasisimple_F4
  K₁_model := K₁_model_of_field (fieldEquivF4 F hF)
  K₂_pair := K₂_pair_of_field (fieldEquivF4 F hF)
  K₂_lie := K₂_lie_F4
  L_gen := L_le_gen
  K₂_gen := sK₂_eq_gen
  K₁_gen := sK₁_eq_gen
  K₁_le := sK₁_le
  K₂_le := sK₂_le
  A₁_le := sA₁_le
  A₂_le := sA₂_le
  K₁_A₁ := sK₁_inf_sA₁
  K₂_A₂ := sK₂_inf_sA₂
  KA₁ := KA₁_eq
  KA₂ := KA₂_eq
  S_w₀ := S_w₀_eq
  S_a := by
    show (sS e ⊓ conjR (sS e) (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2)) ⊓ conjR (sS e ⊓ conjR (sS e) (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2))
      (sw e 0 * sw e 1) = sX₁ e
    rw [S_u₂_eq]
    exact S_a_eq
  S_b := by
    show (sS e ⊓ conjR (sS e) (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2)) ⊓ conjR (sS e ⊓ conjR (sS e) (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2))
      (sw e 1 * sw e 0) = sX₂ e
    rw [S_u₂_eq]
    exact S_b_eq
  S_c := by
    show (sS e ⊓ conjR (sS e) (sw e 0 * sw e 1 * sw e 2 * sw e 1 * sw e 0)) ⊓ conjR (sS e ⊓ conjR (sS e) (sw e 0 * sw e 1 * sw e 2 * sw e 1 * sw e 0))
      (sw e 1 * sw e 2 * sw e 1) = sX₃ e
    rw [S_u₁_eq]
    exact S_c_eq
  S_aba := by
    show (sS e ⊓ conjR (sS e) (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2)) ⊓ conjR (sS e ⊓ conjR (sS e) (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2))
      (sw e 0 * sw e 1 * sw e 0) = ⊥
    rw [S_u₂_eq]
    exact S_aba_eq
  card_S₂ := by
    show Nat.card (sS e ⊓ conjR (sS e) (sw e 2 * sw e 1 * sw e 2 * sw e 0 * sw e 1 * sw e 2) :
      Subgroup G) = _
    rw [S_u₂_eq]
    exact card_T2

end Proof

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
