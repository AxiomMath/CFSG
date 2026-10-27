module

public import CFSG.Assembly.Defs

public section

namespace CFSG.GH74.GLS.Th2.AlphaStep

open Equiv Equiv.Perm Subgroup

theorem exists_conj_of_odd_mul {G : Type*} [Group G] {t y : G} (ht : t * t = 1)
    (hy : Odd (orderOf y)) (hyt : (y * t) * (y * t) = 1) : ∃ w : G, w * t * w⁻¹ = y * t := by
  obtain ⟨j, hj⟩ := hy
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * y * t = y⁻¹ := by
    have h : y * (t * y * t) = 1 := by
      calc y * (t * y * t) = (y * t) * (y * t) := by group
        _ = 1 := hyt
    exact eq_inv_of_mul_eq_one_right h
  have h2 : t * y ^ (j + 1) * t = (y⁻¹) ^ (j + 1) := by
    have h := conj_pow (a := t) (b := y) (i := j + 1)
    rw [ht'] at h
    rw [← h, h1]
  have h3 : y ^ (j + 1) * y ^ (j + 1) = y := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have h4 : t * (y ^ (j + 1))⁻¹ * t = y ^ (j + 1) := by
    have h5 : t * (y ^ (j + 1))⁻¹ * t = (t * y ^ (j + 1) * t)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, ht', mul_assoc]
    rw [h5, h2, inv_pow, inv_inv]
  refine ⟨y ^ (j + 1), ?_⟩
  have key : y ^ (j + 1) * (t * (y ^ (j + 1))⁻¹ * t) * t = y ^ (j + 1) * t * (y ^ (j + 1))⁻¹ := by
    calc y ^ (j + 1) * (t * (y ^ (j + 1))⁻¹ * t) * t
        = y ^ (j + 1) * t * (y ^ (j + 1))⁻¹ * (t * t) := by group
      _ = y ^ (j + 1) * t * (y ^ (j + 1))⁻¹ := by rw [ht, mul_one]
  rw [← key, h4, h3]

structure PsiData {G : Type*} [Group G] (C K : Subgroup G) (psi : G → Perm (Fin 7)) : Prop where
  K_le : K ≤ C
  K_norm : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K
  mul : ∀ g ∈ C, ∀ h ∈ C, psi (g * h) = psi g * psi h
  ker_odd : ∀ k ∈ K, psi k = 1 → Odd (orderOf k)
  surj : ∀ h : Perm (Fin 7), sign h = 1 → ∃ k ∈ K, psi k = h

namespace PsiData

variable {G : Type*} [Group G] {C K : Subgroup G} {psi : G → Perm (Fin 7)}

theorem one (D : PsiData C K psi) : psi 1 = 1 := by
  have h := D.mul 1 C.one_mem 1 C.one_mem
  rw [mul_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem inv (D : PsiData C K psi) {g : G} (hg : g ∈ C) : psi g⁻¹ = (psi g)⁻¹ := by
  have h := D.mul g hg g⁻¹ (C.inv_mem hg)
  rw [mul_inv_cancel, D.one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem exists_conj_step (D : PsiData C K psi) {f m : G} (hf : f ∈ C) (hm : m ∈ K)
    (hff : f * f = 1) (hmm : m * m = 1) (hfm : m * f = f * m) {g : Perm (Fin 7)}
    (hg : sign g = 1) (hgc : g * psi f * g⁻¹ = psi m * psi f) :
    ∃ h : G, h * f * h⁻¹ = m * f := by
  obtain ⟨c, hcK, hc⟩ := D.surj g hg
  have hcC : c ∈ C := D.K_le hcK
  have hmC : m ∈ C := D.K_le hm
  obtain ⟨k, hkdef⟩ : ∃ k : G, k = c * (f * c⁻¹ * f⁻¹) := ⟨_, rfl⟩
  have hfc : f * c⁻¹ * f⁻¹ ∈ K := D.K_norm f hf c⁻¹ (K.inv_mem hcK)
  have hk : k ∈ K := by rw [hkdef]; exact K.mul_mem hcK hfc
  have hpsik : psi k = psi m := by
    have hfcC : f * c⁻¹ * f⁻¹ ∈ C := D.K_le hfc
    have h1 : f * c⁻¹ ∈ C := C.mul_mem hf (C.inv_mem hcC)
    rw [hkdef, D.mul c hcC _ hfcC, D.mul _ h1 _ (C.inv_mem hf), D.mul f hf _ (C.inv_mem hcC),
      D.inv hcC, D.inv hf, hc]
    calc g * (psi f * g⁻¹ * (psi f)⁻¹) = (g * psi f * g⁻¹) * (psi f)⁻¹ := by group
      _ = psi m * psi f * (psi f)⁻¹ := by rw [hgc]
      _ = psi m := by group
  have hy : k * m⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hm)
  have hpsiy : psi (k * m⁻¹) = 1 := by
    rw [D.mul k (D.K_le hk) m⁻¹ (C.inv_mem hmC), D.inv hmC, hpsik]
    exact mul_inv_cancel _
  have hyodd : Odd (orderOf (k * m⁻¹)) := D.ker_odd _ hy hpsiy
  have hu : c * f * c⁻¹ = (k * m⁻¹) * (m * f) := by rw [hkdef]; group
  have hux : (k * m⁻¹) * (m * f) * ((k * m⁻¹) * (m * f)) = 1 := by
    rw [← hu]
    calc c * f * c⁻¹ * (c * f * c⁻¹) = c * (f * f) * c⁻¹ := by group
      _ = 1 := by rw [hff]; group
  have htt : (m * f) * (m * f) = 1 := by
    calc m * f * (m * f) = m * (f * m) * f := by group
      _ = m * (m * f) * f := by rw [hfm]
      _ = (m * m) * (f * f) := by group
      _ = 1 := by rw [hmm, hff]; group
  obtain ⟨w, hw⟩ := exists_conj_of_odd_mul htt hyodd hux
  refine ⟨w⁻¹ * c, ?_⟩
  calc w⁻¹ * c * f * (w⁻¹ * c)⁻¹ = w⁻¹ * (c * f * c⁻¹) * w := by group
    _ = w⁻¹ * ((k * m⁻¹) * (m * f)) * w := by rw [hu]
    _ = w⁻¹ * (w * (m * f) * w⁻¹) * w := by rw [hw]
    _ = m * f := by group

end PsiData

end CFSG.GH74.GLS.Th2.AlphaStep
