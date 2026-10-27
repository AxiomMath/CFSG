module

public import CFSG.ClassicalInvolution.Q3.Q3T6DHexB
public import CFSG.ClassicalInvolution.Q3.Q3CLSeven1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.late_zt_comm (d : Std20Three K K' J S R R' W V z t) : z * t = t * z :=
  d.late_hWc z d.late_z_mem_W t d.late_t_mem_W

structure HexData3 (_d : Std20Three K K' J S R R' W V z t) (u r v t₀ : G) (T : Subgroup G) :
    Prop where
  hd : Sec71.DData (CoreAssembly.conjClass K) W R K u r z
  hd' : Sec71.DData (CoreAssembly.conjClass K) W T J v t₀ t
  hrt : r * t * r⁻¹ = t * z
  htz : t₀ * z * t₀⁻¹ = z * t
  hrW₀ : conjSub r (Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
    Subgroup.zpowers u ⊔ Subgroup.zpowers v
  ht₀W₀ : conjSub t₀ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
    Subgroup.zpowers u ⊔ Subgroup.zpowers v


theorem Std20Three.late_exists_hex (d : Std20Three K K' J S R R' W V z t) :
    ∃ (u r v t₀ : G) (T : Subgroup G), HexData3 d u r v t₀ T := by
  have hΩ := d.late_hΩ
  have hJW := d.late_JW
  obtain ⟨T, hTD, hTJ⟩ := Q3CL.Thompson.exists_sylow_mem_DSet hΩ d.hW d.hWS d.late_mem_J hJW
    inf_le_left (inf_le_right.trans d.hWS)
  obtain ⟨u, r, hd⟩ := late_exists_dDataGen hΩ d.hW d.late_R_mem_D d.late_mem_K d.hR
    d.viol.hzK
  obtain ⟨v, t₀, hd'⟩ := late_exists_dDataGen hΩ d.hW hTD d.late_mem_J hTJ d.viol.hzJ
  obtain ⟨i, k, hio, hko, hi, hk, hrt, htz⟩ := late_pairGen hΩ d.late_cls d.late_hWc hd hd'
    d.late_J_ne_K.symm d.late_ne_inv.symm d.viol.not_nbr
  have hr : conjSub r (Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    refine Sec7.conjSub_eq_of_le_self (late_conjSub_W₀_le ?_ ?_)
    · rw [hd.conj_u]
      exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
    · rw [hi]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
        (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) i))
  have ht : conjSub t₀ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    refine Sec7.conjSub_eq_of_le_self (late_conjSub_W₀_le ?_ ?_)
    · rw [hk]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
        (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers v) k))
    · rw [hd'.conj_u]
      exact Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers v))
  exact ⟨u, r, v, t₀, T, ⟨hd, hd', hrt, htz, hr, ht⟩⟩

namespace HexData3

variable {d : Std20Three K K' J S R R' W V z t} {u r v t₀ : G} {T : Subgroup G}
  (hh : HexData3 d u r v t₀ T)
include hh

theorem hrz : r * z * r⁻¹ = z :=
  hh.hd.uinv.conj_eq (conjSub_eq_self_of_mem hh.hd.r_memK)

theorem ht₀t : t₀ * t * t₀⁻¹ = t :=
  hh.hd'.uinv.conj_eq (conjSub_eq_self_of_mem hh.hd'.r_memK)

theorem W₀_eq : Subgroup.zpowers u ⊔ Subgroup.zpowers v = (K ⊓ W) ⊔ (J ⊓ W) := by
  rw [hh.hd.inf_eq, hh.hd'.inf_eq]

theorem KW_le : K ⊓ W ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  rw [hh.hd.inf_eq]
  exact le_sup_left

theorem JW_le : J ⊓ W ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  rw [hh.hd'.inf_eq]
  exact le_sup_right

theorem r_mem_pair : r ∈ pairNormalizers K J z t := by
  refine Subgroup.mem_sup_left ⟨hh.hd.r_memK, ?_⟩
  refine Sec71.mem_normalizer_closure_pair ?_ ?_
  · rw [hh.hrz]
    exact Subgroup.subset_closure (by simp)
  · rw [hh.hrt]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

theorem t₀_mem_pair : t₀ ∈ pairNormalizers K J z t := by
  refine Subgroup.mem_sup_right ⟨hh.hd'.r_memK, ?_⟩
  refine Sec71.mem_normalizer_closure_pair ?_ ?_
  · rw [hh.htz]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · rw [hh.ht₀t]
    exact Subgroup.subset_closure (by simp)

theorem r_normW : r ∈ Subgroup.normalizer (W : Set G) := hh.hd.r_normW

theorem t₀_normW : t₀ ∈ Subgroup.normalizer (W : Set G) := hh.hd'.r_normW

theorem conj_J : conjSub (t₀ * r) J = K' := by
  have hmt : (t₀ * r) * t * (t₀ * r)⁻¹ = z := by
    calc (t₀ * r) * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
      _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
      _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
      _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]
  have hmem : conjSub (t₀ * r) J ∈ twinSet (CoreAssembly.conjClass K) K :=
    ⟨d.hyp.conjInvariant _ J d.late_mem_J, z, d.viol.hzK, hmt ▸ d.viol.hzJ.conj (t₀ * r)⟩
  rw [d.twins] at hmem
  rcases hmem with h | h
  · exfalso
    have hJ : conjSub (t₀ * r)⁻¹ K = J := by rw [← h, conjSub_inv_conjSub]
    refine d.viol.no_conj (t₀ * r)⁻¹ (Subgroup.inv_mem _ (Subgroup.mul_mem _
      hh.t₀_mem_pair hh.r_mem_pair)) hJ
  · exact h

theorem line_le {L : Subgroup G} {e : G} (hL : L ∈ CoreAssembly.conjClass K)
    (he : IsUniqueInvolution L e) (hZ : e = z ∨ e = t ∨ e = z * t) :
    L ⊓ W ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  have hW₀ : ∀ {m : G}, m ∈ Subgroup.normalizer (W : Set G) →
      conjSub m (Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
        Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      m * e * m⁻¹ = z → L ⊓ W ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    intro m hmN hmW₀ hme
    have hmemL : conjSub m L ∈ twinSet (CoreAssembly.conjClass K) K :=
      ⟨d.hyp.conjInvariant m L hL, z, d.viol.hzK, hme ▸ he.conj m⟩
    rw [d.twins] at hmemL
    have hLe : L = conjSub m⁻¹ (conjSub m L) := (conjSub_inv_conjSub m L).symm
    have hmW : conjSub m⁻¹ W = W := Sec7.conjSub_inv_eq (mem_normalizer_iff_conjSub_eq.mp hmN)
    have hmW₀' : conjSub m⁻¹ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
        Subgroup.zpowers u ⊔ Subgroup.zpowers v := Sec7.conjSub_inv_eq hmW₀
    have hline : ∀ {A : Subgroup G}, A ⊓ W ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
        conjSub m⁻¹ A ⊓ W ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
      intro A hA
      calc conjSub m⁻¹ A ⊓ W = conjSub m⁻¹ (A ⊓ W) := by rw [late_conjSub_inf, hmW]
        _ ≤ conjSub m⁻¹ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := conjSub_mono hA
        _ = _ := hmW₀'
    rw [hLe]
    rcases hmemL with h | h
    · rw [h]
      exact hline hh.KW_le
    · rw [h]
      refine hline ?_
      have hcW : conjSub (t₀ * r) W = W := mem_normalizer_iff_conjSub_eq.mp
        (Subgroup.mul_mem _ hh.t₀_normW hh.r_normW)
      calc K' ⊓ W = conjSub (t₀ * r) J ⊓ W := by rw [hh.conj_J]
        _ = conjSub (t₀ * r) (J ⊓ W) := by rw [late_conjSub_inf, hcW]
        _ ≤ conjSub (t₀ * r) (Subgroup.zpowers u ⊔ Subgroup.zpowers v) := conjSub_mono hh.JW_le
        _ = _ := by rw [conjSub_mul, hh.hrW₀, hh.ht₀W₀]
  rcases hZ with h | h | h
  · refine hW₀ (m := 1) (Subgroup.one_mem _) (conjSub_one _) ?_
    rw [h]
    group
  · refine hW₀ (m := t₀ * r) (Subgroup.mul_mem _ hh.t₀_normW hh.r_normW) ?_ ?_
    · rw [conjSub_mul, hh.hrW₀, hh.ht₀W₀]
    · rw [h]
      calc (t₀ * r) * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
        _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
        _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
        _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
        _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]
  · refine hW₀ (m := t₀) hh.t₀_normW ?_ ?_
    · rw [hh.ht₀W₀]
    · rw [h]
      calc t₀ * (z * t) * t₀⁻¹ = (t₀ * z * t₀⁻¹) * (t₀ * t * t₀⁻¹) := by group
        _ = (z * t) * t := by rw [hh.htz, hh.ht₀t]
        _ = z := by rw [mul_assoc, d.viol.hzJ.sq, mul_one]

end HexData3

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
