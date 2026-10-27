module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAG
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8ACase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abT2e

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab

open Sec8

variable {X : Type} [Group X] {t : X} {L : Subgroup X}

structure SPkg (A : L2Data t L) where
  T₂ : Subgroup X
  Tp : Subgroup X
  z : X
  k : X
  w : X
  isPGroup : IsPGroup 2 T₂
  Tp_le : Tp ≤ T₂
  Tp_le_C : Tp ≤ centralizer ({t} : Set X)
  card_T_le : Nat.card A.T ≤ Nat.card Tp
  t_mem : t ∈ T₂
  z_mem : z ∈ T₂
  k_mem : k ∈ T₂
  w_mem : w ∈ T₂
  zz : z * z = 1
  kk : k * k = 1
  ww : w * w = 1
  kw : k * w = w * k
  z_ne : z ≠ 1
  k_ne₁ : k ≠ 1
  k_ne_z : k ≠ z
  w_ne₁ : w ≠ 1
  w_ne_z : w ≠ z
  w_ne_k : w ≠ k
  w_ne_zk : w ≠ z * k
  z_central : ∀ g ∈ T₂, g * z = z * g
  center : ∀ g ∈ T₂, (∀ h ∈ T₂, g * h = h * g) → g = 1 ∨ g = z
  conj_k : ∀ g ∈ T₂, g * k * g⁻¹ = k ∨ g * k * g⁻¹ = z * k
  conj_w : ∀ g ∈ T₂, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = z * w
  Y : ∀ g ∈ T₂, (∀ h ∈ T₂, h * g * h⁻¹ = g ∨ h * g * h⁻¹ = z * g) →
      g = 1 ∨ g = z ∨ g = k ∨ g = z * k ∨ g = w ∨ g = z * w ∨ g = k * w ∨ g = z * k * w
  t_k : t * k * t⁻¹ = k
  t_w : t * w * t⁻¹ = z * w
  fus : ∀ x ∈ T₂, ConjTo t x →
      (∃ g ∈ T₂, x = g * t * g⁻¹) ∨ (x * k * x⁻¹ = z * k ∧ x * w * x⁻¹ = z * w)
  noconj : ∀ x ∈ T₂, x * w = w * x → ¬ ConjTo t x

namespace SPkg

variable {A : L2Data t L} (P : SPkg A)

theorem z_inv : P.z⁻¹ = P.z := inv_eq_of_mul_eq_one_right P.zz

theorem zk_comm : P.z * P.k = P.k * P.z := (P.z_central _ P.k_mem).symm

theorem zw_comm : P.z * P.w = P.w * P.z := (P.z_central _ P.w_mem).symm

theorem mem_Tp_of_comm [Finite X] {Q : Subgroup X} (hQ : IsPGroup 2 Q) (hPQ : P.T₂ ≤ Q) {g : X}
    (hg : g ∈ Q) (hgt : g * t = t * g) : g ∈ P.Tp := by
  have hle : P.Tp ⊔ zpowers g ≤ centralizer ({t} : Set X) :=
    sup_le P.Tp_le_C (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hgt))
  have hQ' : IsPGroup 2 (P.Tp ⊔ zpowers g : Subgroup X) :=
    hQ.to_le (sup_le (P.Tp_le.trans hPQ) (zpowers_le.mpr hg))
  have heq : P.Tp = P.Tp ⊔ zpowers g := Subgroup.eq_of_le_of_card_ge le_sup_left
    ((card_le_T A hQ' hle).trans P.card_T_le)
  exact heq ▸ mem_sup_right (mem_zpowers g)

theorem sq_of_conjTo {x : X} (hx : ConjTo t x) (ht2 : t * t = 1) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := hx
  rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht2, mul_one,
    mul_inv_cancel]

@[expose] noncomputable def U₁ : Subgroup X := P.T₂ ⊓ centralizer ({P.w} : Set X)

theorem mem_U₁ {g : X} : g ∈ P.U₁ ↔ g ∈ P.T₂ ∧ g * P.w = P.w * g := by
  rw [U₁, Subgroup.mem_inf, mem_centralizer_singleton_iff]

theorem comm_of_conj {g a : X} (h : g * a * g⁻¹ = a) : g * a = a * g := by
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [h]

theorem t_not_mem_U₁ : t ∉ P.U₁ := by
  intro h
  have h1 := (P.mem_U₁.mp h).2
  have h2 : t * P.w * t⁻¹ = P.w := by rw [h1, mul_inv_cancel_right]
  rw [P.t_w] at h2
  exact P.z_ne (mul_eq_right.mp h2)

theorem conj_z {g : X} (hg : g ∈ P.T₂) : g * P.z * g⁻¹ = P.z := by
  rw [P.z_central g hg, mul_inv_cancel_right]

theorem t_inv_w : t⁻¹ * P.w * t = P.z * P.w := by
  have h1 : t⁻¹ * (t * P.w * t⁻¹) * t = P.w := by group
  have hz' : t⁻¹ * P.z * t = P.z := by
    have := P.conj_z (inv_mem P.t_mem); rwa [inv_inv] at this
  rw [P.t_w, show t⁻¹ * (P.z * P.w) * t = (t⁻¹ * P.z * t) * (t⁻¹ * P.w * t) by group, hz'] at h1
  calc t⁻¹ * P.w * t = P.z * (P.z * (t⁻¹ * P.w * t)) := by rw [← mul_assoc, P.zz, one_mul]
    _ = P.z * P.w := by rw [h1]

theorem t_mem_normalizer_U₁ [Finite X] : t ∈ normalizer (P.U₁ : Set X) := by
  refine mem_normalizer_of_conj_le fun g hg => P.mem_U₁.mpr ⟨?_, ?_⟩
  · exact mul_mem (mul_mem P.t_mem (P.mem_U₁.mp hg).1) (inv_mem P.t_mem)
  · have hgw := (P.mem_U₁.mp hg).2
    have hzg : g * P.z = P.z * g := P.z_central g (P.mem_U₁.mp hg).1
    have e1 : g * (P.z * P.w) = (P.z * P.w) * g := by
      rw [← mul_assoc, hzg, mul_assoc, hgw, ← mul_assoc]
    calc t * g * t⁻¹ * P.w = t * (g * (t⁻¹ * P.w * t)) * t⁻¹ := by group
      _ = t * ((P.z * P.w) * g) * t⁻¹ := by rw [P.t_inv_w, e1]
      _ = (t * (P.z * P.w) * t⁻¹) * (t * g * t⁻¹) := by group
      _ = P.w * (t * g * t⁻¹) := by
          rw [show t * (P.z * P.w) * t⁻¹ = (t * P.z * t⁻¹) * (t * P.w * t⁻¹) by group,
            P.conj_z P.t_mem, P.t_w, show P.z * (P.z * P.w) = P.w by
              rw [← mul_assoc, P.zz, one_mul]]

theorem T₂_eq [Finite X] : P.T₂ = P.U₁ ⊔ zpowers t := by
  refine le_antisymm (fun g hg => ?_) (sup_le inf_le_left (zpowers_le.mpr P.t_mem))
  rcases P.conj_w g hg with h | h
  · exact mem_sup_left (P.mem_U₁.mpr ⟨hg, comm_of_conj h⟩)
  · have htg : t * g ∈ P.U₁ := by
      refine P.mem_U₁.mpr ⟨mul_mem P.t_mem hg, comm_of_conj ?_⟩
      rw [show t * g * P.w * (t * g)⁻¹ = t * (g * P.w * g⁻¹) * t⁻¹ by group, h,
        show t * (P.z * P.w) * t⁻¹ = (t * P.z * t⁻¹) * (t * P.w * t⁻¹) by group, P.t_w,
        P.conj_z P.t_mem, ← mul_assoc, P.zz, one_mul]
    rw [show g = t⁻¹ * (t * g) by group]
    exact mul_mem (mem_sup_right (inv_mem (mem_zpowers t))) (mem_sup_left htg)

theorem relIndex_U₁ [Finite X] (ht2 : t * t = 1) : P.U₁.relIndex P.T₂ = 2 := by
  rw [P.T₂_eq]
  exact relIndex_sup_zpowers P.t_mem_normalizer_U₁ (by rw [ht2]; exact one_mem _)
    P.t_not_mem_U₁

theorem card_T₂ [Finite X] (ht2 : t * t = 1) : Nat.card P.T₂ = 2 * Nat.card P.U₁ := by
  rw [P.T₂_eq]
  exact card_sup_zpowers P.t_mem_normalizer_U₁ (by rw [ht2]; exact one_mem _) P.t_not_mem_U₁

theorem false_of_max [Finite X] [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (ht : orderOf t = 2) (hmax : ∀ R : Subgroup X, IsPGroup 2 R → P.T₂ ≤ R → R = P.T₂) : False := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  exact false_of_transfer' hX ht P.isPGroup hmax inf_le_left (P.relIndex_U₁ ht2)
    fun m hm => P.noconj m (P.mem_U₁.mp hm).1 (P.mem_U₁.mp hm).2

end SPkg

end KD8ab

end CFSG.ComponentClassification.HSFLit
