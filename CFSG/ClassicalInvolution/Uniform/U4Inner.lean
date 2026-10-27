module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR12
public import CFSG.ClassicalInvolution.Uniform.U4Twin

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem exists_dual_twin {K : Subgroup F} {z : F} (hK : Mem3 K z) {J : Subgroup F}
    {t : F} (hJ : Mem3 J t) (hne : t ≠ z) {a : F} (haK : a ∈ K) (ha2 : a * a = z)
    (hta : t * a = a * t) (haJ : a ∉ Subgroup.normalizer (J : Set F))
    (hzJ : z ∈ Subgroup.normalizer (J : Set F)) (hnt : ¬ ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) :
    ∃ K₃ : Subgroup F, Mem3 K₃ z ∧ K₃ ≠ K ∧ a * t ∈ K₃ := by
  have hKz : IsUniqueInvolution K z := hK.isUniqueInvolution
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := hJ.mul_self
  have haord : orderOf a = 4 := AscFusion.orderOf_eq_four_of_sq_eq hz2 hKz.ne_one ha2
  have hnt' : ¬ ∀ j ∈ J, ⁅a * a, j⁆ ∈ oddCoreOf J := by rwa [ha2]
  obtain ⟨κ, hκJ, hκ2, hκn, hκc⟩ :=
    exists_kappa hJ haord hta.symm haJ (by rw [ha2]; exact hzJ) hnt'
  obtain ⟨δ, hδ2, hzδ, hδa⟩ := AscFusion.dual_delta_facts hz2 ht2 ha2 hta hκ2 hκn hκc
  have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
  have hzδ' : δ⁻¹ * z = z * δ⁻¹ := by rw [hδi]; exact hzδ.symm
  set K₃ : Subgroup F := conjSub δ⁻¹ K with hK₃
  have hK₃z : Mem3 K₃ z := hK.conj_of_commute hzδ'
  have hb₃ : a * t ∈ K₃ := by
    have := conj_mem_conjSub (n := δ⁻¹) haK
    rw [inv_inv] at this
    rwa [hδa] at this
  refine ⟨K₃, hK₃z, ?_, hb₃⟩
  intro h
  have htK : t ∈ K := by
    have h1 : a * t ∈ K := h ▸ hb₃
    have := K.mul_mem (K.inv_mem haK) h1
    simpa using this
  rcases hKz.unique t htK ht2 with h1 | h1
  · exact (hJ.isUniqueInvolution).ne_one h1
  · exact hne h1

theorem exists_inner_order_four {K : Subgroup F} {z : F} (hK : Mem3 K z)
    {J : Subgroup F} {t : F} (hJ : Mem3 J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hv4 : orderOf v = 4) (hvz : v * z = z * v)
    (hv : v ∉ Subgroup.normalizer (K : Set F)) {R : Subgroup F}
    (hRcomm : ∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub v⁻¹ K, q * q' = q' * q)
    (hRinv : ∀ q ∈ R ⊓ K, v⁻¹ * q * v ∈ R ⊓ conjSub v⁻¹ K) {a₀ : F} (ha₀ : a₀ ∈ R ⊓ K)
    (ha₀2 : a₀ * a₀ = z) (hta₀ : t * a₀ = a₀ * t)
    (hZ : (∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J) → False) :
    ∃ k ∈ K, k * k = z ∧ ∀ y ∈ K, t * y * t⁻¹ * (k * y * k⁻¹)⁻¹ ∈ oddCoreOf K := by
  classical
  have hKz : IsUniqueInvolution K z := hK.isUniqueInvolution
  have hJt : IsUniqueInvolution J t := hJ.isUniqueInvolution
  have hz2 : z * z = 1 := hKz.sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hvv : v * v = t := by
    have hv22 : (v * v) * (v * v) = 1 := by
      have : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
      simpa [pow_succ, mul_assoc] using this
    rcases hJt.unique (v * v) (J.mul_mem hvJ hvJ) hv22 with h | h
    · exfalso
      have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hv4] at this
      omega
    · exact h
  have htz : t * z = z * t := by
    rw [← hvv]
    calc v * v * z = v * (v * z) := by group
      _ = v * (z * v) := by rw [hvz]
      _ = (v * z) * v := by group
      _ = (z * v) * v := by rw [hvz]
      _ = z * (v * v) := by group
  have hvK'' : conjSub v⁻¹ K ≠ K := conjSub_inv_ne hv
  obtain ⟨hK'mem, -, -, -⟩ := hK.twin_facts_conj (inv_comm_of_comm hvz) hvK''.symm
  set K' : Subgroup F := conjSub v⁻¹ K with hK'
  have hKK' : K ≠ K' := hvK''.symm
  obtain ⟨ha₀R, ha₀K⟩ := ha₀
  have ha₀pg : IsPGroup 2 (Subgroup.zpowers a₀) := AscFusion.isPGroup_zpowers_of_sq_eq hz2 ha₀2
  have ha₀ord : orderOf a₀ = 4 := AscFusion.orderOf_eq_four_of_sq_eq hz2 hKz.ne_one ha₀2
  have hzv : v⁻¹ * z * v = z := conj_eq_of_comm hvz
  set a₀' : F := v⁻¹ * a₀ * v with ha₀'
  obtain ⟨ha₀'R, ha₀'K'⟩ := hRinv a₀ ⟨ha₀R, ha₀K⟩
  have ha₀cm : a₀ * a₀' = a₀' * a₀ := hRcomm a₀ ⟨ha₀R, ha₀K⟩ a₀' ⟨ha₀'R, ha₀'K'⟩
  have ha₀'2 : a₀' * a₀' = z := by
    calc a₀' * a₀' = v⁻¹ * (a₀ * a₀) * v := by rw [ha₀']; group
      _ = z := by rw [ha₀2, hzv]
  by_cases hJa : a₀ ∈ Subgroup.normalizer (J : Set F)
  ·
    have hc : a₀ * a₀'⁻¹ = a₀'⁻¹ * a₀ := (Commute.inv_right (show Commute a₀ a₀' from ha₀cm)).eq
    have hσJ : a₀'⁻¹ * a₀ ∈ J := by
      have h1 : a₀⁻¹ * v * a₀ ∈ J := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (J : Set F)).inv_mem hJa) v).mp hvJ
        simpa using this
      have : a₀'⁻¹ * a₀ = v⁻¹ * (a₀⁻¹ * v * a₀) := by rw [ha₀']; group
      rw [this]
      exact J.mul_mem (J.inv_mem hvJ) h1
    have hσ2 : (a₀'⁻¹ * a₀) * (a₀'⁻¹ * a₀) = 1 := by
      calc (a₀'⁻¹ * a₀) * (a₀'⁻¹ * a₀) = a₀'⁻¹ * (a₀ * a₀'⁻¹) * a₀ := by group
        _ = a₀'⁻¹ * (a₀'⁻¹ * a₀) * a₀ := by rw [hc]
        _ = (a₀' * a₀')⁻¹ * (a₀ * a₀) := by group
        _ = 1 := by rw [ha₀'2, ha₀2]; exact inv_mul_cancel z
    have hσt : a₀'⁻¹ * a₀ = t := by
      rcases hJt.unique _ hσJ hσ2 with h | h
      · exfalso
        have hee : a₀' = a₀ := inv_mul_eq_one.mp h
        exact hKK' (hK.eq_of_mem_of_mem_same hK'mem ha₀K (hee ▸ ha₀'K') ha₀pg (by omega))
      · exact h
    refine ⟨a₀, ha₀K, ha₀2, ?_⟩
    refine AscFusion.inner_of_mul_trivial ha₀K (x := a₀'⁻¹)
      (hK.commutator_mem_of_twin hK'mem hKK' (K'.inv_mem ha₀'K')) ?_
    rw [← hσt, hc]
  · have hv3 : 3 ≤ Nat.card (Subgroup.zpowers v) := by rw [Nat.card_zpowers, hv4]; omega
    have hzJ : z ∈ Subgroup.normalizer (J : Set F) :=
      hJ.mem_normalizer_of_commute_of_mem_noncentral hvJ hv2 hv3 hvz.symm
    by_cases hζ : ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J
    · exact (hZ hζ).elim
    ·
      obtain ⟨K₃, hK₃z, hK₃K, hb₃⟩ := exists_dual_twin hK hJ hne ha₀K ha₀2 hta₀ hJa hzJ hζ
      refine ⟨a₀⁻¹, K.inv_mem ha₀K, ?_, ?_⟩
      · calc a₀⁻¹ * a₀⁻¹ = (a₀ * a₀)⁻¹ := by group
          _ = z := by rw [ha₀2, hzi]
      · exact AscFusion.inner_of_mul_trivial (K.inv_mem ha₀K) (x := a₀ * t)
          (hK.commutator_mem_of_twin hK₃z (Ne.symm hK₃K) hb₃) (by group)

end CFSG.ClassicalInvolution.Uniform.U4
