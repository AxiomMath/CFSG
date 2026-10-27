module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreBig

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem big_order_contradiction {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    {J : Subgroup F} {t : F} (hJ : IsClassical2A7 ⊤ J t) (hne : t ≠ z)
    (htK : t ∈ Subgroup.normalizer (K : Set F)) {v : F} (hvJ : v ∈ J)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (h8 : 8 ≤ orderOf v) (hvz : v * z = z * v)
    (hvK2 : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F)) : False := by
  classical
  have hKz : IsUniqueInvolution K z := isUniqueInvolution hK
  have hJt : IsUniqueInvolution J t := isUniqueInvolution hJ
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := hJt.sq
  have hvK : conjSub v⁻¹ K ≠ K := conjSub_inv_ne hv
  have hvz' : v⁻¹ * z * v = z := conj_eq_of_comm hvz
  have htz : z * t = t * z := by
    have h := hKz.conj_eq (conjSub_eq_of_mem_normalizer htK)
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hvt : v * t = t * v := (hJt.commute_of_mem hvJ).symm
  have hn2 : IsPGroup 2 (Subgroup.zpowers (v * v)) :=
    hv2.to_le (Subgroup.zpowers_le.mpr
      ((Subgroup.zpowers v).mul_mem (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v)))
  have hnn1 : (v * v) * (v * v) ≠ 1 := by
    intro h
    have h4 : v ^ 4 = 1 := by
      calc v ^ 4 = (v * v) * (v * v) := by simp [pow_succ, mul_assoc]
        _ = 1 := h
    have := orderOf_le_of_pow_eq_one (by norm_num) h4
    omega
  have h4n : 4 ≤ orderOf (v * v) := AscFusion.four_le_orderOf_of_sq_ne_one hn2 hnn1
  have htn : t ∈ Subgroup.zpowers ((v * v) * (v * v)) :=
    AscFusion.mem_zpowers_sq_of_isUniqueInvolution hJt (J.mul_mem hvJ hvJ) hn2 h4n
  obtain ⟨R, hR2, hvR, -, hRK, -, hcomm, hconj⟩ := exists_twin_sylow hK hv2 hvz hvK hvK2
  have htR : t ∈ R :=
    Subgroup.zpowers_le.mpr (R.mul_mem (R.mul_mem hvR hvR) (R.mul_mem hvR hvR)) htn
  have hnt := not_forall_comm_of_twin hK hJ htz htK hvJ hvz hvK hR2 htR hRK hcomm hconj
  obtain ⟨κ, hκ, hκ2, hκt⟩ := exists_inverted hK hR2 hRK htR ht2 htK hnt
  have hκ'mem : v⁻¹ * κ * v ∈ R ⊓ conjSub v⁻¹ K := hconj κ hκ
  have hcomκ : κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ := hcomm κ hκ _ hκ'mem
  have hκ'2 : (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = z := by
    calc (v⁻¹ * κ * v) * (v⁻¹ * κ * v) = v⁻¹ * (κ * κ) * v := by group
      _ = v⁻¹ * z * v := by rw [hκ2]
      _ = z := hvz'
  have hxx : (κ * (v⁻¹ * κ * v)) * (κ * (v⁻¹ * κ * v)) = 1 := by
    calc (κ * (v⁻¹ * κ * v)) * (κ * (v⁻¹ * κ * v))
        = κ * ((v⁻¹ * κ * v) * κ) * (v⁻¹ * κ * v) := by group
      _ = κ * (κ * (v⁻¹ * κ * v)) * (v⁻¹ * κ * v) := by rw [hcomκ]
      _ = (κ * κ) * ((v⁻¹ * κ * v) * (v⁻¹ * κ * v)) := by group
      _ = 1 := by rw [hκ2, hκ'2, hz2]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htκ : t * κ * t⁻¹ = κ⁻¹ := by
    have : t * κ * t⁻¹ = t⁻¹ * κ * t := by rw [hti]
    rw [this]
    exact hκt
  have htvt : t * v * t⁻¹ = v := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hvt.symm
  have htvt' : t * v⁻¹ * t⁻¹ = v⁻¹ := by
    calc t * v⁻¹ * t⁻¹ = (t * v * t⁻¹)⁻¹ := by group
      _ = v⁻¹ := by rw [htvt]
  have htκ' : t * (v⁻¹ * κ * v) * t⁻¹ = (v⁻¹ * κ * v)⁻¹ := by
    calc t * (v⁻¹ * κ * v) * t⁻¹ = (t * v⁻¹ * t⁻¹) * (t * κ * t⁻¹) * (t * v * t⁻¹) := by group
      _ = v⁻¹ * κ⁻¹ * v := by rw [htvt', htκ, htvt]
      _ = (v⁻¹ * κ * v)⁻¹ := by group
  have hxt : (κ * (v⁻¹ * κ * v)) * t = t * (κ * (v⁻¹ * κ * v)) := by
    have h1 : t * (κ * (v⁻¹ * κ * v)) * t⁻¹ = κ * (v⁻¹ * κ * v) := by
      calc t * (κ * (v⁻¹ * κ * v)) * t⁻¹
          = (t * κ * t⁻¹) * (t * (v⁻¹ * κ * v) * t⁻¹) := by group
        _ = κ⁻¹ * (v⁻¹ * κ * v)⁻¹ := by rw [htκ, htκ']
        _ = ((v⁻¹ * κ * v) * κ)⁻¹ := by group
        _ = (κ * (v⁻¹ * κ * v))⁻¹ := by rw [hcomκ]
        _ = κ * (v⁻¹ * κ * v) := inv_eq_of_mul_eq_one_right hxx
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hy : v * ((v * v)⁻¹ * κ * (v * v) * κ⁻¹) =
      (κ * (v⁻¹ * κ * v)) * v * (κ * (v⁻¹ * κ * v))⁻¹ := by
    rw [AscFusion.twin_conj_identity hcomκ]
    group
  have hyR : (v * v)⁻¹ * κ * (v * v) * κ⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem (R.inv_mem (R.mul_mem hvR hvR)) hκ.1)
      (R.mul_mem hvR hvR)) (R.inv_mem hκ.1)
  have hyK : (v * v)⁻¹ * κ * (v * v) * κ⁻¹ ∈ K := by
    refine K.mul_mem ?_ (K.inv_mem hκ.2)
    exact (mem_conj_iff_of_mem_normalizer hvK2 κ).mpr hκ.2
  have hyc := eq_one_or_eq_of_twin_conj hK hJ hne hvJ hvz hR2 hvR hvK hxt hy hyR hyK
  have hκz : z * κ = κ⁻¹ := by
    have h4 : (κ * κ) * (κ * κ) = 1 := by rw [hκ2, hz2]
    calc z * κ = κ⁻¹ * ((κ * κ) * (κ * κ)) := by rw [← hκ2]; group
      _ = κ⁻¹ := by rw [h4, mul_one]
  have hinvconj : ∀ m : F, m⁻¹ * κ⁻¹ * m = (m⁻¹ * κ * m)⁻¹ := fun m => by group
  have hmκ : ((v * v) * (v * v))⁻¹ * κ * ((v * v) * (v * v)) = κ := by
    rcases hyc with h1 | h1
    · have h2 : (v * v)⁻¹ * κ * (v * v) = κ := mul_inv_eq_one.mp h1
      calc ((v * v) * (v * v))⁻¹ * κ * ((v * v) * (v * v))
          = (v * v)⁻¹ * ((v * v)⁻¹ * κ * (v * v)) * (v * v) := by group
        _ = κ := by rw [h2, h2]
    · have h2 : (v * v)⁻¹ * κ * (v * v) = κ⁻¹ := by
        have h3 : (v * v)⁻¹ * κ * (v * v) = z * κ := by
          calc (v * v)⁻¹ * κ * (v * v) = ((v * v)⁻¹ * κ * (v * v) * κ⁻¹) * κ := by group
            _ = z * κ := by rw [h1]
        rw [h3, hκz]
      calc ((v * v) * (v * v))⁻¹ * κ * ((v * v) * (v * v))
          = (v * v)⁻¹ * ((v * v)⁻¹ * κ * (v * v)) * (v * v) := by group
        _ = (v * v)⁻¹ * κ⁻¹ * (v * v) := by rw [h2]
        _ = ((v * v)⁻¹ * κ * (v * v))⁻¹ := hinvconj (v * v)
        _ = κ := by rw [h2, inv_inv]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htn
  have hκm : κ * ((v * v) * (v * v)) = ((v * v) * (v * v)) * κ := by
    calc κ * ((v * v) * (v * v))
        = ((v * v) * (v * v)) * (((v * v) * (v * v))⁻¹ * κ * ((v * v) * (v * v))) := by group
      _ = ((v * v) * (v * v)) * κ := by rw [hmκ]
  have hκt' : κ * t = t * κ := by
    rw [← hk]
    exact (Commute.zpow_right (show Commute κ ((v * v) * (v * v)) from hκm) k).eq
  have h1 : t⁻¹ * κ * t = κ := by
    calc t⁻¹ * κ * t = t⁻¹ * (κ * t) := by group
      _ = t⁻¹ * (t * κ) := by rw [hκt']
      _ = κ := by group
  have h2 : κ = κ⁻¹ := h1.symm.trans hκt
  have h3 : κ * κ = 1 := by
    calc κ * κ = κ * κ⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel κ
  exact hKz.ne_one (hκ2.symm.trans h3)

end CFSG.ClassicalInvolution.A7Core
