module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7S5Syl

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup

theorem coords_decomp : ∀ q : DihedralGroup 4 × DihedralGroup 2, ∃ i : Fin 4, ∃ j a b : Fin 2,
    q = (r 1, 1) ^ (i : ℕ) * (sr 0, 1) ^ (j : ℕ) * (1, r 1) ^ (a : ℕ) * (1, sr 0) ^ (b : ℕ) := by
  decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

variable (S) in
theorem T_decomp {τ : X} (hτ : τ ∈ S.data.T) : ∃ i : Fin 4, ∃ j a b : Fin 2,
    τ = S.x ^ (i : ℕ) * S.y ^ (j : ℕ) * S.t ^ (a : ℕ) * S.k ^ (b : ℕ) := by
  obtain ⟨i, j, a, b, h⟩ := coords_decomp (S.coords ⟨τ, hτ⟩)
  refine ⟨i, j, a, b, ?_⟩
  have e : (⟨τ, hτ⟩ : S.data.T) = (⟨S.x, S.x_mem.1⟩ : S.data.T) ^ (i : ℕ) *
      (⟨S.y, S.y_mem.1⟩ : S.data.T) ^ (j : ℕ) * (⟨S.t, S.data.t_mem_T⟩ : S.data.T) ^ (a : ℕ) *
      (⟨S.k, S.k_mem⟩ : S.data.T) ^ (b : ℕ) := by
    apply S.coords.injective
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, S.coords_x, S.coords_y,
      S.coords_t, S.coords_k]
    exact h
  exact congrArg Subtype.val e

variable (S) in
theorem sq_xy_mem (i : Fin 4) (j : Fin 2) : (S.x ^ (i : ℕ) * S.y ^ (j : ℕ)) ^ 2 = 1 ∨
    (S.x ^ (i : ℕ) * S.y ^ (j : ℕ)) ^ 2 = S.z := by
  have hmem : S.x ^ (i : ℕ) * S.y ^ (j : ℕ) ∈ S.data.T :=
    mul_mem (pow_mem S.x_mem.1 _) (pow_mem S.y_mem.1 _)
  have key : ∀ i : Fin 4, ∀ j : Fin 2, ((r 1, 1) ^ (i : ℕ) * (sr 0, 1) ^ (j : ℕ) :
      DihedralGroup 4 × DihedralGroup 2) ^ 2 = 1 ∨
      ((r 1, 1) ^ (i : ℕ) * (sr 0, 1) ^ (j : ℕ) : DihedralGroup 4 × DihedralGroup 2) ^ 2 =
        (r 2, 1) := by decide
  have e : S.coords ⟨S.x ^ (i : ℕ) * S.y ^ (j : ℕ), hmem⟩ =
      (r 1, 1) ^ (i : ℕ) * (sr 0, 1) ^ (j : ℕ) := by
    have : (⟨S.x ^ (i : ℕ) * S.y ^ (j : ℕ), hmem⟩ : S.data.T) =
        (⟨S.x, S.x_mem.1⟩ : S.data.T) ^ (i : ℕ) * (⟨S.y, S.y_mem.1⟩ : S.data.T) ^ (j : ℕ) := rfl
    rw [this, map_mul, map_pow, map_pow, S.coords_x, S.coords_y]
  rcases key i j with h | h
  · left
    have : (⟨S.x ^ (i : ℕ) * S.y ^ (j : ℕ), hmem⟩ : S.data.T) ^ 2 = 1 :=
      S.coords.injective (by rw [map_pow, e, h, map_one])
    exact congrArg Subtype.val this
  · right
    have : (⟨S.x ^ (i : ℕ) * S.y ^ (j : ℕ), hmem⟩ : S.data.T) ^ 2 = ⟨S.z, S.z_mem.1⟩ :=
      S.coords.injective (by rw [map_pow, e, h, S.coords_z])
    exact congrArg Subtype.val this

namespace Sec5Hyp

variable {T₁ : Subgroup X} (H : S.Sec5Hyp T₁)
include H

theorem exists_w₀' : ∃ w₀ ∈ S.T₂of T₁, w₀ ∉ S.data.T ∧ w₀ * S.x = S.x * w₀ ∧
    w₀ * S.y = S.y * w₀ ∧ w₀ * S.k = S.k * w₀ ∧ w₀ * S.t * w₀⁻¹ = S.t * S.z := by
  obtain ⟨w, hw, hwT, hwM⟩ := H.exists_tz S.inst₁
  have hwN₂ := H.T₂of_le_normalizer S.inst₂ hw
  have hwt := H.conj_w₀_t hw hwT
  have hwk : w * S.k * w⁻¹ = S.k := by
    have := hwM.conj_ki
    simpa [transCols, Inst.wV, inst₁] using this
  have hwxy : w * (S.x * S.y) * w⁻¹ = S.x * S.y := by
    have := hwM.conj_yi
    simpa [transCols, Inst.wV, inst₁] using this
  have hwz : w * S.z * w⁻¹ = S.z := S.conj_z_eq (H.le_normalizer (T₂of_le hw))
  obtain ⟨a', b', hy⟩ := H.conj_E00 S.inst₂ hwN₂ 0 1
  rw [show S.inst₂.wV (0, 1, 0, 0) = S.y by simp [Inst.wV, inst₂]] at hy
  have hyB : w * S.y * w⁻¹ ∉ S.B := fun h => S.y_not_mem_B (by
    have := S.conj_mem_B (inv_mem (H.le_normalizer (T₂of_le hw))) h
    simpa [mul_assoc] using this)
  rw [hy, S.inst₂.wV_mem_B_iff] at hyB
  have hb' : b' = 1 := by
    rcases Fin.exists_fin_two.mp ⟨b', rfl⟩ with rfl | rfl
    · exact absurd rfl hyB
    · rfl
  subst hb'
  have hcomm : ∀ {g e : X}, g * e * g⁻¹ = e → g * e = e * g := by
    intro g e h
    calc g * e = g * e * g⁻¹ * g := by group
      _ = e * g := by rw [h]
  have hxyT := S.xy_mem.1
  have hxy_y : (S.x * S.y) * S.y * (S.x * S.y)⁻¹ = S.z * S.y := by
    calc (S.x * S.y) * S.y * (S.x * S.y)⁻¹ = S.x * S.y * S.x⁻¹ := by group
      _ = S.z * S.y := S.inst₂.x_conj_yi
  rcases Fin.exists_fin_two.mp ⟨a', rfl⟩ with rfl | rfl
  ·
    have hwy : w * S.y * w⁻¹ = S.y := by rw [hy]; simp [Inst.wV, inst₂]
    have hx : w * S.x * w⁻¹ = S.x := by
      calc w * S.x * w⁻¹ = w * (S.x * S.y) * w⁻¹ * (w * S.y * w⁻¹)⁻¹ := by group
        _ = S.x := by rw [hwxy, hwy]; group
    exact ⟨w, hw, hwT, hcomm hx, hcomm hwy, hcomm hwk, hwt⟩
  ·
    have hwy : w * S.y * w⁻¹ = S.z * S.y := by rw [hy]; simp [Inst.wV, inst₂]
    set w' := w * (S.x * S.y) with hw'
    have hw'T₂ : w' ∈ S.T₂of T₁ := mul_mem hw (H.T_le_T₂of hxyT)
    have hw'T : w' ∉ S.data.T := fun h => hwT (by
      have := mul_mem h (inv_mem hxyT)
      rwa [hw', mul_inv_cancel_right] at this)
    have hcx : ∀ e : X, w' * e * w'⁻¹ = w * ((S.x * S.y) * e * (S.x * S.y)⁻¹) * w⁻¹ := fun e => by
      rw [hw']; group
    have hy' : w' * S.y * w'⁻¹ = S.y := by
      rw [hcx, hxy_y]
      calc w * (S.z * S.y) * w⁻¹ = (w * S.z * w⁻¹) * (w * S.y * w⁻¹) := by group
        _ = S.y := by
            rw [hwz, hwy, ← mul_assoc, ← pow_two, S.z_sq, one_mul]
    have hxy' : w' * (S.x * S.y) * w'⁻¹ = S.x * S.y := by
      rw [hcx]
      calc w * ((S.x * S.y) * (S.x * S.y) * (S.x * S.y)⁻¹) * w⁻¹ = w * (S.x * S.y) * w⁻¹ := by
            group
        _ = S.x * S.y := hwxy
    have hk' : w' * S.k * w'⁻¹ = S.k := by
      rw [hcx, show (S.x * S.y) * S.k * (S.x * S.y)⁻¹ = S.k by
        rw [← S.central_of_mem_B (subset_closure (by simp)) hxyT]; group, hwk]
    have ht' : w' * S.t * w'⁻¹ = S.t * S.z := by
      rw [hcx, show (S.x * S.y) * S.t * (S.x * S.y)⁻¹ = S.t by
        rw [S.data.commute_t hxyT]; group, hwt]
    have hx : w' * S.x * w'⁻¹ = S.x := by
      calc w' * S.x * w'⁻¹ = w' * (S.x * S.y) * w'⁻¹ * (w' * S.y * w'⁻¹)⁻¹ := by group
        _ = S.x := by rw [hxy', hy']; group
    exact ⟨w', hw'T₂, hw'T, hcomm hx, hcomm hy', hcomm hk', ht'⟩

omit H in
theorem B_prod (a b : Fin 2) :
    (S.t * S.z) ^ (a : ℕ) * S.k ^ (b : ℕ) * (S.t ^ (a : ℕ) * S.k ^ (b : ℕ)) = S.z ^ (a : ℕ) := by
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  have hkt : S.k * S.t = S.t * S.k := (S.data.commute_t S.k_mem)
  have hzk : S.z * S.k = S.k * S.z := S.z_comm_of_mem_T S.k_mem
  have ht2 : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]
  have hk2 : S.k * S.k = 1 := by rw [← pow_two, S.k_sq]
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl <;>
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, one_mul]
  · exact hk2
  · calc S.t * S.z * S.t = S.t * (S.z * S.t) := by group
      _ = S.z := by rw [hzt, ← mul_assoc, ht2, one_mul]
  · calc S.t * S.z * S.k * (S.t * S.k) = S.t * S.z * (S.k * S.t) * S.k := by group
      _ = S.t * (S.z * S.t) * (S.k * S.k) := by rw [hkt]; group
      _ = S.z := by rw [hzt, hk2, ← mul_assoc, ht2, one_mul, mul_one]

omit H in
theorem sq_mul_mem {w₀ : X} (hx : w₀ * S.x = S.x * w₀) (hy : w₀ * S.y = S.y * w₀)
    (hk : w₀ * S.k = S.k * w₀) (ht : w₀ * S.t * w₀⁻¹ = S.t * S.z) {τ : X} (hτ : τ ∈ S.data.T) :
    (w₀ * τ) ^ 2 = w₀ ^ 2 ∨ (w₀ * τ) ^ 2 = w₀ ^ 2 * S.z := by
  obtain ⟨i, j, a, b, rfl⟩ := S.T_decomp hτ
  have hw₀z : w₀ * S.z = S.z * w₀ := by
    rw [show S.z = S.x ^ 2 from rfl, pow_two, ← mul_assoc, hx, mul_assoc, hx, mul_assoc]
  have hinv : ∀ {e : X}, w₀ * e = e * w₀ → w₀⁻¹ * e * w₀ = e := fun h => by
    rw [mul_assoc, ← h]; group
  have hzz : S.z * S.z = 1 := by rw [← pow_two, S.z_sq]
  have hti : w₀⁻¹ * S.t * w₀ = S.t * S.z := by
    have h1 : (w₀⁻¹ * S.t * w₀) * S.z = S.t := by
      calc (w₀⁻¹ * S.t * w₀) * S.z = (w₀⁻¹ * S.t * w₀) * (w₀⁻¹ * S.z * w₀) := by
            rw [hinv hw₀z]
        _ = w₀⁻¹ * (w₀ * S.t * w₀⁻¹) * w₀ := by rw [ht]; group
        _ = S.t := by group
    calc w₀⁻¹ * S.t * w₀ = (w₀⁻¹ * S.t * w₀) * S.z * S.z := by rw [mul_assoc _ S.z, hzz, mul_one]
      _ = S.t * S.z := by rw [h1]
  set r := S.x ^ (i : ℕ) * S.y ^ (j : ℕ) with hr
  have hrT : r ∈ S.data.T := mul_mem (pow_mem S.x_mem.1 _) (pow_mem S.y_mem.1 _)
  have hcB : (S.t * S.z) ^ (a : ℕ) * S.k ^ (b : ℕ) ∈ S.B :=
    mul_mem (pow_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp))) _)
      (pow_mem (subset_closure (by simp)) _)
  have hconj : w₀⁻¹ * (r * S.t ^ (a : ℕ) * S.k ^ (b : ℕ)) * w₀ =
      r * ((S.t * S.z) ^ (a : ℕ) * S.k ^ (b : ℕ)) := by
    have e : ∀ e : X, w₀⁻¹ * e * w₀ = MulAut.conj w₀⁻¹ e := fun e => by simp
    rw [hr, e, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, ← e, ← e, ← e, ← e,
      hinv hx, hinv hy, hti, hinv hk, mul_assoc]
  have hsq : (w₀ * (r * S.t ^ (a : ℕ) * S.k ^ (b : ℕ))) ^ 2 = w₀ ^ 2 * r ^ 2 * S.z ^ (a : ℕ) := by
    calc (w₀ * (r * S.t ^ (a : ℕ) * S.k ^ (b : ℕ))) ^ 2 =
        w₀ ^ 2 * (w₀⁻¹ * (r * S.t ^ (a : ℕ) * S.k ^ (b : ℕ)) * w₀) *
          (r * (S.t ^ (a : ℕ) * S.k ^ (b : ℕ))) := by
          simp only [pow_two]; group
      _ = w₀ ^ 2 * (r * ((S.t * S.z) ^ (a : ℕ) * S.k ^ (b : ℕ))) *
          (r * (S.t ^ (a : ℕ) * S.k ^ (b : ℕ))) := by rw [hconj]
      _ = w₀ ^ 2 * r * (((S.t * S.z) ^ (a : ℕ) * S.k ^ (b : ℕ)) * r) *
          (S.t ^ (a : ℕ) * S.k ^ (b : ℕ)) := by group
      _ = w₀ ^ 2 * r * (r * ((S.t * S.z) ^ (a : ℕ) * S.k ^ (b : ℕ))) *
          (S.t ^ (a : ℕ) * S.k ^ (b : ℕ)) := by rw [S.central_of_mem_B hcB hrT]
      _ = w₀ ^ 2 * (r * r) * ((S.t * S.z) ^ (a : ℕ) * S.k ^ (b : ℕ) *
          (S.t ^ (a : ℕ) * S.k ^ (b : ℕ))) := by group
      _ = w₀ ^ 2 * r ^ 2 * S.z ^ (a : ℕ) := by rw [B_prod, pow_two r]
  rw [show S.x ^ (i : ℕ) * S.y ^ (j : ℕ) * S.t ^ (a : ℕ) * S.k ^ (b : ℕ) =
    r * S.t ^ (a : ℕ) * S.k ^ (b : ℕ) from rfl, hsq]
  rcases S.sq_xy_mem i j with h | h <;> rw [← hr] at h <;> rw [h] <;>
    rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; simp [mul_assoc, hzz]

theorem sq_not_mem_T_of_not_mem {g : X} (hg : g ∈ T₁) (hgT : g ∉ S.T₂of T₁) :
    g ^ 2 ∉ S.data.T := by
  have hgN : g ∉ normalizer (S.E (S.x * S.y) : Set X) := fun h => hgT (mem_inf.mpr ⟨hg, h⟩)
  have hgk := H.conj_g_k (H.swap_of_not_mem hg hgN).1
  rcases H.conj_g_t hg hgT with hgt | hgt
  · exact H.sq_not_mem_T hg hgt hgk
  · intro h
    have hz : g * S.z * g⁻¹ = S.z := S.conj_z_eq (H.le_normalizer hg)
    have hzk : S.z * S.k = S.k * S.z := S.z_comm_of_mem_T S.k_mem
    have h2 : g ^ 2 * S.t * (g ^ 2)⁻¹ = S.t * S.z := by
      calc g ^ 2 * S.t * (g ^ 2)⁻¹ = g * (g * S.t * g⁻¹) * g⁻¹ := by rw [pow_two]; group
        _ = g * (S.t * S.z * S.k) * g⁻¹ := by rw [hgt]
        _ = (g * S.t * g⁻¹) * (g * S.z * g⁻¹) * (g * S.k * g⁻¹) := by group
        _ = S.t * S.z * S.k * S.z * (S.z * S.k) := by rw [hgt, hz, hgk]
        _ = S.t * S.z * (S.k * S.z) * (S.z * S.k) := by group
        _ = S.t * S.z * (S.z * S.k) * (S.z * S.k) := by rw [hzk]
        _ = S.t * (S.z * S.z) * (S.k * S.z) * S.k := by group
        _ = S.t * (S.z * S.z) * (S.z * S.k) * S.k := by rw [hzk]
        _ = S.t * S.z * ((S.z * S.z) * (S.k * S.k)) := by group
        _ = S.t * S.z := by rw [← pow_two, S.z_sq, ← pow_two, S.k_sq, mul_one, mul_one]
    rw [S.data.commute_t h, mul_inv_cancel_right] at h2
    apply S.z_ne_one
    calc S.z = S.t⁻¹ * (S.t * S.z) := by group
      _ = 1 := by rw [← h2]; group

theorem exists_involution : ∃ u ∈ S.T₂of T₁, u ∉ S.data.T ∧ u ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hinvT : ∀ v ∈ T₁, v ^ 2 = 1 → v ∈ S.data.T := by
    intro v hv hv2
    by_cases hvT₂ : v ∈ S.T₂of T₁
    · by_contra hvT
      exact hcon v hvT₂ hvT hv2
    · exact absurd (hv2 ▸ one_mem _ : v ^ 2 ∈ S.data.T) (H.sq_not_mem_T_of_not_mem hv hvT₂)
  have hne : ∀ P : Sylow 2 X, (P : Subgroup X) ≠ T₁ := by
    intro P hP
    obtain ⟨Q, hQ, hlt⟩ := H.not_sylow
    rw [← hP] at hlt
    have := P.is_maximal' hQ hlt.le
    exact hlt.ne this.symm
  obtain ⟨n, hnN, hnT, hnp⟩ := exists_mem_normalizer_not_mem H.isPGroup hne
  have hconjT : ∀ {e : X}, e ∈ S.data.T → e ^ 2 = 1 → n * e * n⁻¹ ∈ S.data.T := by
    intro e he he2
    refine hinvT _ ((mem_normalizer_iff.mp hnN e).mp (H.le he)) ?_
    rw [conj_pow, he2]; group
  have hxy := hconjT S.xy_mem.1 S.xy_sq
  have hy := hconjT S.y_mem.1 S.y_sq
  have ht := hconjT S.data.t_mem_T S.t_sq
  have hk := hconjT S.k_mem S.k_sq
  have hx : n * S.x * n⁻¹ ∈ S.data.T := by
    have e : n * S.x * n⁻¹ = (n * (S.x * S.y) * n⁻¹) * (n * S.y * n⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem hxy (inv_mem hy)
  have hnNT : n ∈ normalizer (S.data.T : Set X) := by
    refine mem_normalizer_of_conj_mem fun τ hτ => ?_
    obtain ⟨i, j, a, b, rfl⟩ := S.T_decomp hτ
    have e : ∀ e : X, n * e * n⁻¹ = MulAut.conj n e := fun e => rfl
    rw [e, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, ← e, ← e, ← e, ← e]
    exact mul_mem (mul_mem (mul_mem (pow_mem hx _) (pow_mem hy _)) (pow_mem ht _))
      (pow_mem hk _)
  have hle : T₁ ⊔ zpowers n ≤ normalizer (S.data.T : Set X) :=
    sup_le H.le_normalizer (zpowers_le.mpr hnNT)
  have heq := H.maximal _ hnp le_sup_left hle
  exact hnT (heq ▸ mem_sup_right (mem_zpowers n))

theorem exists_w : ∃ w ∈ S.T₂of T₁, w ∉ S.data.T ∧ w ^ 2 = 1 ∧ w * S.x = S.x * w ∧
    w * S.y = S.y * w ∧ w * S.k = S.k * w ∧ w * S.t * w⁻¹ = S.t * S.z := by
  obtain ⟨w₀, hw₀, hw₀T, hx, hy, hk, ht⟩ := H.exists_w₀'
  obtain ⟨u, hu, huT, hu2⟩ := H.exists_involution
  have hτ : w₀⁻¹ * u ∈ S.data.T := ((H.mem_T₂of_iff hw₀ hw₀T).mp hu).resolve_left huT
  have hu' : u = w₀ * (w₀⁻¹ * u) := by group
  have hzz : S.z * S.z = 1 := by rw [← pow_two, S.z_sq]
  have hsq : w₀ ^ 2 = 1 ∨ w₀ ^ 2 = S.z := by
    rcases sq_mul_mem hx hy hk ht hτ with h | h <;> rw [← hu', hu2] at h
    · exact Or.inl h.symm
    · right
      calc w₀ ^ 2 = w₀ ^ 2 * S.z * S.z := by rw [mul_assoc, hzz, mul_one]
        _ = S.z := by rw [← h, one_mul]
  have htx : S.t * S.x = S.x * S.t := (S.data.commute_t S.x_mem.1).symm
  have hty : S.t * S.y = S.y * S.t := (S.data.commute_t S.y_mem.1).symm
  have htk : S.t * S.k = S.k * S.t := (S.data.commute_t S.k_mem).symm
  rcases hsq with h | h
  · exact ⟨w₀, hw₀, hw₀T, h, hx, hy, hk, ht⟩
  · refine ⟨w₀ * S.t, mul_mem hw₀ (H.T_le_T₂of S.data.t_mem_T), fun h' => hw₀T (by
      have := mul_mem h' (inv_mem S.data.t_mem_T)
      rwa [mul_inv_cancel_right] at this), ?_, ?_, ?_, ?_, ?_⟩
    · calc (w₀ * S.t) ^ 2 = (w₀ * S.t * w₀⁻¹) * w₀ ^ 2 * S.t := by rw [pow_two, pow_two]; group
        _ = S.t * S.z * S.z * S.t := by rw [ht, h]
        _ = 1 := by rw [mul_assoc S.t, hzz, mul_one, ← pow_two, S.t_sq]
    · rw [mul_assoc, htx, ← mul_assoc, hx, mul_assoc]
    · rw [mul_assoc, hty, ← mul_assoc, hy, mul_assoc]
    · rw [mul_assoc, htk, ← mul_assoc, hk, mul_assoc]
    · calc w₀ * S.t * S.t * (w₀ * S.t)⁻¹ = w₀ * S.t * w₀⁻¹ := by group
        _ = S.t * S.z := ht

end Sec5Hyp

end A7Base

end CFSG.ComponentClassification.HSFLit
