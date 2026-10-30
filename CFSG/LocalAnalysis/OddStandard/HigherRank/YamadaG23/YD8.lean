module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

set_option synthInstance.maxSize 400 in
private theorem d8_check_six : ∀ x y w : DihedralGroup 4, x ^ 2 = 1 → y ^ 2 = 1 →
    x * y ≠ y * x → w ^ 2 = 1 →
    (w = 1 ∨ w = (y * x) ^ 2 ∨ w = x ∨ w = (y * x) ^ 2 * x ∨ w = y ∨
      w = (y * x) ^ 2 * y) := by decide

set_option synthInstance.maxSize 400 in
private theorem d8_check_basic : ∀ x y : DihedralGroup 4, x ^ 2 = 1 → y ^ 2 = 1 →
    x * y ≠ y * x →
    ((y * x) ^ 2) ^ 2 = 1 ∧ (y * x) ^ 2 * x = x * (y * x) ^ 2 ∧
      (y * x) ^ 2 * y = y * (y * x) ^ 2 := by decide

private theorem d8_not_commute {C : Subgroup G} {t d : G} (hC : C = closure {t, d})
    (hD : Nonempty (↥C ≃* DihedralGroup 4)) : t * d ≠ d * t := by
  obtain ⟨e⟩ := hD
  have htC : t ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hdC : d ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  let T : ↥C := ⟨t, htC⟩
  let Dd : ↥C := ⟨d, hdC⟩
  intro hcomm
  have hTD : T * Dd = Dd * T := by
    apply Subtype.ext
    show t * d = d * t
    exact hcomm
  have hall : ∀ a ∈ ({t, d} : Set G), ∀ b ∈ ({t, d} : Set G), Commute a b := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb]
    · rw [ha, hb]; show t * d = d * t; exact hcomm
    · rw [ha, hb]; show d * t = t * d; exact hcomm.symm
    · rw [ha, hb]
  have hpair : ({t, d} : Set G).Pairwise Commute := fun a ha b hb _ => hall a ha b hb
  have hCcomm : IsMulCommutative ↥C := hC.symm ▸ isMulCommutative_closure hpair
  have hD8comm : IsMulCommutative (DihedralGroup 4) := by
    letI := hCcomm
    exact IsMulCommutative.of_comm fun a b => by
      have h := congrArg e (mul_comm' (e.symm a) (e.symm b))
      simpa using h
  exact DihedralGroup.not_commutative (n := 4) (by norm_num) (by norm_num) hD8comm

private theorem d8_basic {C : Subgroup G} {t d : G} (hC : C = closure {t, d})
    (hD : Nonempty (↥C ≃* DihedralGroup 4)) (ht : orderOf t = 2) (hd : orderOf d = 2) :
    ((d * t) ^ 2) ^ 2 = 1 ∧ (d * t) ^ 2 * t = t * (d * t) ^ 2 ∧
      (d * t) ^ 2 * d = d * (d * t) ^ 2 := by
  have hnc : t * d ≠ d * t := d8_not_commute hC hD
  obtain ⟨e⟩ := hD
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hd2 : d ^ 2 = 1 := by simpa [hd] using pow_orderOf_eq_one d
  have htC : t ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hdC : d ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hzC : (d * t) ^ 2 ∈ C := pow_mem (mul_mem hdC htC) 2
  let T : ↥C := ⟨t, htC⟩
  let Dd : ↥C := ⟨d, hdC⟩
  let Z : ↥C := ⟨(d * t) ^ 2, hzC⟩
  have hT2 : T ^ 2 = 1 := by apply Subtype.ext; show t ^ 2 = 1; exact ht2
  have hDd2 : Dd ^ 2 = 1 := by apply Subtype.ext; show d ^ 2 = 1; exact hd2
  have hx2 : (e T) ^ 2 = 1 := by rw [← map_pow, hT2, map_one]
  have hy2 : (e Dd) ^ 2 = 1 := by rw [← map_pow, hDd2, map_one]
  have hxyne : e T * e Dd ≠ e Dd * e T := by
    intro h
    apply hnc
    have hTD : T * Dd = Dd * T := by
      apply e.injective
      rw [map_mul, map_mul]
      exact h
    simpa [T, Dd] using congrArg Subtype.val hTD
  have hZ : e Z = (e Dd * e T) ^ 2 := by
    have hZeq : Z = (Dd * T) ^ 2 := by apply Subtype.ext; rfl
    rw [hZeq, map_pow, map_mul]
  obtain ⟨h1, h2, h3⟩ := d8_check_basic (e T) (e Dd) hx2 hy2 hxyne
  refine ⟨?_, ?_, ?_⟩
  · have hZ2 : Z ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, hZ, h1, map_one]
    simpa [Z] using congrArg Subtype.val hZ2
  · have hZT : Z * T = T * Z := by
      apply e.injective
      rw [map_mul, map_mul, hZ, h2]
    simpa [Z, T] using congrArg Subtype.val hZT
  · have hZD : Z * Dd = Dd * Z := by
      apply e.injective
      rw [map_mul, map_mul, hZ, h3]
    simpa [Z, Dd] using congrArg Subtype.val hZD

private theorem sq_one_mem_six {C : Subgroup G} {t d w : G} (hC : C = closure {t, d})
    (hD : Nonempty (↥C ≃* DihedralGroup 4)) (ht : orderOf t = 2) (hd : orderOf d = 2)
    (hwC : w ∈ C) (hw2 : w ^ 2 = 1) :
    w = 1 ∨ w = (d * t) ^ 2 ∨ w = t ∨ w = (d * t) ^ 2 * t ∨ w = d ∨
      w = (d * t) ^ 2 * d := by
  have hnc : t * d ≠ d * t := d8_not_commute hC hD
  obtain ⟨e⟩ := hD
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hd2 : d ^ 2 = 1 := by simpa [hd] using pow_orderOf_eq_one d
  have htC : t ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hdC : d ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hzC : (d * t) ^ 2 ∈ C := pow_mem (mul_mem hdC htC) 2
  let T : ↥C := ⟨t, htC⟩
  let Dd : ↥C := ⟨d, hdC⟩
  let W : ↥C := ⟨w, hwC⟩
  let Z : ↥C := ⟨(d * t) ^ 2, hzC⟩
  have hT2 : T ^ 2 = 1 := by apply Subtype.ext; show t ^ 2 = 1; exact ht2
  have hDd2 : Dd ^ 2 = 1 := by apply Subtype.ext; show d ^ 2 = 1; exact hd2
  have hW2' : W ^ 2 = 1 := by apply Subtype.ext; show w ^ 2 = 1; exact hw2
  have hx2 : (e T) ^ 2 = 1 := by rw [← map_pow, hT2, map_one]
  have hy2 : (e Dd) ^ 2 = 1 := by rw [← map_pow, hDd2, map_one]
  have hW2 : (e W) ^ 2 = 1 := by rw [← map_pow, hW2', map_one]
  have hxyne : e T * e Dd ≠ e Dd * e T := by
    intro h
    apply hnc
    have hTD : T * Dd = Dd * T := by
      apply e.injective
      rw [map_mul, map_mul]
      exact h
    simpa [T, Dd] using congrArg Subtype.val hTD
  have hZ : e Z = (e Dd * e T) ^ 2 := by
    have hZeq : Z = (Dd * T) ^ 2 := by apply Subtype.ext; rfl
    rw [hZeq, map_pow, map_mul]
  have hZT : (e Dd * e T) ^ 2 * e T = e (Z * T) := by
    rw [← hZ, ← map_mul]
  have hZD : (e Dd * e T) ^ 2 * e Dd = e (Z * Dd) := by
    rw [← hZ, ← map_mul]
  have h6 := d8_check_six (e T) (e Dd) (e W) hx2 hy2 hxyne hW2
  rcases h6 with h | h | h | h | h | h
  · left
    have hW : W = 1 := e.injective (by simpa using h)
    simpa [W] using congrArg Subtype.val hW
  · right; left
    have hW : W = Z := e.injective (h.trans hZ.symm)
    simpa [W, Z] using congrArg Subtype.val hW
  · right; right; left
    have hW : W = T := e.injective h
    simpa [W, T] using congrArg Subtype.val hW
  · right; right; right; left
    have hW : W = Z * T := e.injective (h.trans hZT)
    simpa [W, Z, T] using congrArg Subtype.val hW
  · right; right; right; right; left
    have hW : W = Dd := e.injective h
    simpa [W, Dd] using congrArg Subtype.val hW
  · right; right; right; right; right
    have hW : W = Z * Dd := e.injective (h.trans hZD)
    simpa [W, Z, Dd] using congrArg Subtype.val hW

private theorem d8_subset_Q_or_Q' {C : Subgroup G} {t d : G} (hC : C = closure {t, d})
    (hD : Nonempty (↥C ≃* DihedralGroup 4)) (ht : orderOf t = 2) (hd : orderOf d = 2)
    (E : Subgroup G) (hEC : E ≤ C) (hE2 : IsElemAbelian 2 E) :
    E ≤ closure {(d * t) ^ 2, t} ∨ E ≤ closure {(d * t) ^ 2, d} := by
  have hbasic := d8_basic hC hD ht hd
  let z : G := (d * t) ^ 2
  have hz2 : z ^ 2 = 1 := hbasic.1
  have hzt : z * t = t * z := hbasic.2.1
  have hzd : z * d = d * z := hbasic.2.2
  have htd : d * t ≠ t * d := fun h => d8_not_commute hC hD h.symm
  by_contra h
  push Not at h
  obtain ⟨hnotQ, hnotQ'⟩ := h
  rw [SetLike.not_le_iff_exists] at hnotQ hnotQ'
  obtain ⟨w, hwE, hwQ⟩ := hnotQ
  obtain ⟨v, hvE, hvQ'⟩ := hnotQ'
  have hw2 : w ^ 2 = 1 := hE2.2 w hwE
  have hv2 : v ^ 2 = 1 := hE2.2 v hvE
  have h6w := sq_one_mem_six hC hD ht hd (hEC hwE) hw2
  have h6v := sq_one_mem_six hC hD ht hd (hEC hvE) hv2
  have hw_d : w = d ∨ w = z * d := by
    rcases h6w with h1 | hz | ht' | hzt' | hd' | hzd'
    · exfalso
      apply hwQ
      rw [h1]; exact Subgroup.one_mem _
    · exfalso
      apply hwQ
      rw [hz]; exact Subgroup.subset_closure (by simp)
    · exfalso
      apply hwQ
      rw [ht']; exact Subgroup.subset_closure (by simp)
    · exfalso
      apply hwQ
      rw [hzt']
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact Or.inl hd'
    · exact Or.inr hzd'
  have hv_t : v = t ∨ v = z * t := by
    rcases h6v with h1 | hz | ht' | hzt' | hd' | hzd'
    · exfalso
      apply hvQ'
      rw [h1]; exact Subgroup.one_mem _
    · exfalso
      apply hvQ'
      rw [hz]; exact Subgroup.subset_closure (by simp)
    · exact Or.inl ht'
    · exact Or.inr hzt'
    · exfalso
      apply hvQ'
      rw [hd']; exact Subgroup.subset_closure (by simp)
    · exfalso
      apply hvQ'
      rw [hzd']
      exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hcomm : w * v = v * w := hE2.comm hwE hvE
  rcases hw_d with hwd | hwd <;> rcases hv_t with hvt | hvt
  · rw [hwd, hvt] at hcomm
    exact htd hcomm
  · apply htd
    have h' : z * (d * t) = z * (t * d) := by
      have h := hcomm
      rw [hwd, hvt] at h
      rw [← mul_assoc d z t, hzd.symm, mul_assoc, mul_assoc] at h
      exact h
    exact mul_left_cancel h'
  · apply htd
    have h' : z * (d * t) = z * (t * d) := by
      have h := hcomm
      rw [hwd, hvt] at h
      rw [mul_assoc, ← mul_assoc t z d, hzt.symm, mul_assoc] at h
      exact h
    exact mul_left_cancel h'
  · apply htd
    have h := hcomm
    rw [hwd, hvt] at h
    have hL : (z * d) * (z * t) = d * t := by
      rw [mul_assoc, ← mul_assoc d z t, hzd.symm, mul_assoc, ← mul_assoc z z (d * t),
        ← pow_two, hz2, one_mul]
    have hR : (z * t) * (z * d) = t * d := by
      rw [mul_assoc, ← mul_assoc t z d, hzt.symm, mul_assoc, ← mul_assoc z z (t * d),
        ← pow_two, hz2, one_mul]
    exact hL.symm.trans (h.trans hR)

theorem dihedral_of_involutions' {C : Subgroup G} {t d : G} (hC : C = closure {t, d})
    (ht : orderOf t = 2) (hd : orderOf d = 2) (h4 : orderOf (d * t) = 4) :
    Nonempty (↥C ≃* DihedralGroup 4) := by
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hd2 : d ^ 2 = 1 := by simpa [hd] using pow_orderOf_eq_one d
  have htm : t * t = 1 := by rw [← pow_two]; exact ht2
  have hdm : d * d = 1 := by rw [← pow_two]; exact hd2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htm
  have hd_inv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdm
  let K : Subgroup G := closure ({d, t} : Set G)
  have htK : t ∈ K := by
    change t ∈ closure ({d, t} : Set G); exact Subgroup.subset_closure (by simp)
  have hdK : d ∈ K := by
    change d ∈ closure ({d, t} : Set G); exact Subgroup.subset_closure (by simp)
  let T : ↥K := ⟨t, htK⟩
  let Dd : ↥K := ⟨d, hdK⟩
  let ρ : ↥K := Dd * T
  let σ : ↥K := T
  have hT2 : T ^ 2 = 1 := by
    apply Subtype.ext
    show t ^ 2 = 1
    exact ht2
  have hDd2 : Dd ^ 2 = 1 := by
    apply Subtype.ext
    show d ^ 2 = 1
    exact hd2
  have hT2m : T * T = 1 := by rw [← pow_two]; exact hT2
  have hσ2 : σ ^ 2 = 1 := by
    change T ^ 2 = 1
    exact hT2
  have hset : ({T, Dd} : Set ↥K) = K.subtype ⁻¹' ({d, t} : Set G) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rintro (h | h)
      · exact Or.inr (Subtype.ext h)
      · exact Or.inl (Subtype.ext h)
  have htop : (⊤ : Subgroup ↥K) = Subgroup.closure ({T, Dd} : Set ↥K) := by
    rw [hset]
    exact (Subgroup.closure_preimage_eq_top ({d, t} : Set G)).symm
  have hDds : Dd = ρ * σ := by
    change Dd = (Dd * T) * T
    rw [mul_assoc, ← pow_two, hT2, mul_one]
  have hgen : (⊤ : Subgroup ↥K) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    rw [htop]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers T)
      · rw [hDds]
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
    · apply sup_le
      · rw [Subgroup.zpowers_le]
        exact mul_mem (Subgroup.subset_closure (by simp : Dd ∈ ({T, Dd} : Set ↥K)))
          (Subgroup.subset_closure (by simp : T ∈ ({T, Dd} : Set ↥K)))
      · rw [Subgroup.zpowers_le]
        exact Subgroup.subset_closure (by simp : T ∈ ({T, Dd} : Set ↥K))
  have hord : orderOf ρ = 4 := by
    rw [← Subgroup.orderOf_coe ρ]
    simpa [ρ, Dd, T] using h4
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    apply Subtype.ext
    change t * (d * t) * t⁻¹ = (d * t)⁻¹
    conv_rhs => rw [mul_inv_rev, hd_inv, ht_inv]
    group
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    have hcomm : σ * ρ = ρ * σ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hk]
      exact (Commute.zpow_self ρ k).eq
    have hTD : T * Dd = Dd * T := by
      have h := hcomm
      calc T * Dd = (T * (Dd * T)) * T := by
            simp only [mul_assoc, hT2m, mul_one]
        _ = ((Dd * T) * T) * T := by rw [h]
        _ = Dd * T := by simp only [mul_assoc, hT2m, mul_one]
    have hρ2 : ρ ^ 2 = 1 := by
      change (Dd * T) ^ 2 = 1
      have hsq : (Dd * T) * (Dd * T) = Dd * Dd * (T * T) := by
        calc (Dd * T) * (Dd * T) = Dd * (T * Dd) * T := by group
          _ = Dd * (Dd * T) * T := by rw [hTD]
          _ = Dd * Dd * (T * T) := by group
      rw [pow_two, hsq, ← pow_two, hDd2, one_mul, ← pow_two, hT2]
    have hdvd : orderOf ρ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hρ2
    rw [hord] at hdvd
    norm_num at hdvd
  obtain ⟨φ⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  rw [hord] at φ
  have hCK : C = closure ({d, t} : Set G) := by rw [hC, Set.pair_comm]
  exact ⟨(MulEquiv.subgroupCongr hCK).trans φ⟩

theorem d8_rel {t d z : G} (ht : orderOf t = 2) (hd : orderOf d = 2) (h4 : (d * t) ^ 4 = 1)
    (hz : (d * t) ^ 2 = z) : d * t * d⁻¹ = z * t ∧ t * d * t⁻¹ = z * d := by
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hd2 : d ^ 2 = 1 := by simpa [hd] using pow_orderOf_eq_one d
  have htm : t * t = 1 := by rw [← pow_two]; exact ht2
  have hdm : d * d = 1 := by rw [← pow_two]; exact hd2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htm
  have hd_inv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdm
  have hz2 : z ^ 2 = 1 := by
    rw [← hz, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num, h4]
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz2)
  have htd2 : (t * d) ^ 2 = z := by
    have hinv : (d * t)⁻¹ = t * d := by rw [mul_inv_rev, hd_inv, ht_inv]
    rw [← hinv, inv_pow, hz, hz_inv]
  constructor
  · calc d * t * d⁻¹ = d * t * d := by rw [hd_inv]
      _ = (d * t) ^ 2 * t := by
        rw [pow_two]
        simp only [mul_assoc, htm, mul_one]
      _ = z * t := by rw [hz]
  · calc t * d * t⁻¹ = t * d * t := by rw [ht_inv]
      _ = (t * d) ^ 2 * d := by
        rw [pow_two]
        simp only [mul_assoc, hdm, mul_one]
      _ = z * d := by rw [htd2]

theorem d8_maxElemAbelian {C : Subgroup G} {t d : G} (hC : C = closure {t, d})
    (hD : Nonempty (↥C ≃* DihedralGroup 4)) (ht : orderOf t = 2) (hd : orderOf d = 2) :
    maxElemAbelian C = {closure {(d * t) ^ 2, t}, closure {(d * t) ^ 2, d}} := by
  have hbasic := d8_basic hC hD ht hd
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have hd2 : d ^ 2 = 1 := by simpa [hd] using pow_orderOf_eq_one d
  have htC : t ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hdC : d ∈ C := by rw [hC]; exact Subgroup.subset_closure (by simp)
  have hzC : (d * t) ^ 2 ∈ C := pow_mem (mul_mem hdC htC) 2
  let z : G := (d * t) ^ 2
  have hz2 : z ^ 2 = 1 := hbasic.1
  have hzt : z * t = t * z := hbasic.2.1
  have hzd : z * d = d * z := hbasic.2.2
  have htd : d * t ≠ t * d := fun h => d8_not_commute hC hD h.symm
  let Q : Subgroup G := closure {z, t}
  let Q' : Subgroup G := closure {z, d}
  change maxElemAbelian C = ({Q, Q'} : Set (Subgroup G))
  have hQleC : Q ≤ C := by
    change closure {z, t} ≤ C
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzC
    · exact htC
  have hQ'leC : Q' ≤ C := by
    change closure {z, d} ≤ C
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzC
    · exact hdC
  have hQelem : IsElemAbelian 2 Q := by
    change IsElemAbelian 2 (closure {z, t})
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hzt
      · exact hzt.symm
      · rfl
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hz2
      · exact ht2
  have hQ'elem : IsElemAbelian 2 Q' := by
    change IsElemAbelian 2 (closure {z, d})
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hzd
      · exact hzd.symm
      · rfl
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hz2
      · exact hd2
  have hQmax : ∀ Y' : Subgroup G, Q ≤ Y' → Y' ≤ C → IsElemAbelian 2 Y' → Y' = Q := by
    intro Y' hQY hY'C hY'2
    apply le_antisymm
    · intro w hw
      have hw2 : w ^ 2 = 1 := hY'2.2 w hw
      have h6 := sq_one_mem_six hC hD ht hd (hY'C hw) hw2
      have htQ : t ∈ Q := by
        change t ∈ closure {z, t}
        exact Subgroup.subset_closure (by simp)
      have hwt : w * t = t * w := hY'2.comm hw (hQY htQ)
      rcases h6 with h1 | hz | ht' | hzt' | hd' | hzd'
      · rw [h1]; exact Q.one_mem
      · rw [hz]; change z ∈ closure {z, t}; exact Subgroup.subset_closure (by simp)
      · rw [ht']; change t ∈ closure {z, t}; exact Subgroup.subset_closure (by simp)
      · rw [hzt']; change z * t ∈ closure {z, t}
        exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      · exfalso
        apply htd
        rw [hd'] at hwt
        exact hwt
      · exfalso
        apply htd
        have h' : z * (d * t) = z * (t * d) := by
          have h := hwt
          rw [hzd'] at h
          change (z * d) * t = t * (z * d) at h
          rw [mul_assoc, ← mul_assoc t z d, hzt.symm, mul_assoc] at h
          exact h
        exact mul_left_cancel h'
    · exact hQY
  have hQ'max : ∀ Y' : Subgroup G, Q' ≤ Y' → Y' ≤ C → IsElemAbelian 2 Y' → Y' = Q' := by
    intro Y' hQ'Y hY'C hY'2
    apply le_antisymm
    · intro w hw
      have hw2 : w ^ 2 = 1 := hY'2.2 w hw
      have h6 := sq_one_mem_six hC hD ht hd (hY'C hw) hw2
      have hdQ' : d ∈ Q' := by
        change d ∈ closure {z, d}
        exact Subgroup.subset_closure (by simp)
      have hwd : w * d = d * w := hY'2.comm hw (hQ'Y hdQ')
      rcases h6 with h1 | hz | ht' | hzt' | hd' | hzd'
      · rw [h1]; exact Q'.one_mem
      · rw [hz]; change z ∈ closure {z, d}; exact Subgroup.subset_closure (by simp)
      · exfalso
        apply htd
        rw [ht'] at hwd
        exact hwd.symm
      · exfalso
        apply htd
        have h' : z * (t * d) = z * (d * t) := by
          have h := hwd
          rw [hzt'] at h
          change (z * t) * d = d * (z * t) at h
          rw [mul_assoc, ← mul_assoc d z t, hzd.symm, mul_assoc] at h
          exact h
        exact (mul_left_cancel h').symm
      · rw [hd']; change d ∈ closure {z, d}; exact Subgroup.subset_closure (by simp)
      · rw [hzd']; change z * d ∈ closure {z, d}
        exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    · exact hQ'Y
  apply le_antisymm
  · intro E hE
    have hEC : E ≤ C := hE.1
    have hE2 : IsElemAbelian 2 E := hE.2.1
    rcases d8_subset_Q_or_Q' hC hD ht hd E hEC hE2 with h | h
    · have hEQ : E = Q := (hE.2.2 Q h hQleC hQelem).symm
      rw [hEQ]
      exact Set.mem_insert _ _
    · have hEQ' : E = Q' := (hE.2.2 Q' h hQ'leC hQ'elem).symm
      rw [hEQ']
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · intro E hE
    rcases hE with hE | hE
    · rw [hE]; exact ⟨hQleC, hQelem, hQmax⟩
    · rw [hE]; exact ⟨hQ'leC, hQ'elem, hQ'max⟩

theorem d8_involution_outside {C : Subgroup G} {t d w : G} (hC : C = closure {t, d})
    (hD : Nonempty (↥C ≃* DihedralGroup 4)) (ht : orderOf t = 2) (hd : orderOf d = 2) (hwC : w ∈ C)
    (hw : orderOf w = 2) (hwn : w ∉ closure {(d * t) ^ 2, t}) :
    w = d ∨ w = (d * t) ^ 2 * d := by
  have hw2 : w ^ 2 = 1 := by simpa [hw] using pow_orderOf_eq_one w
  have h6 := sq_one_mem_six hC hD ht hd hwC hw2
  let z : G := (d * t) ^ 2
  rcases h6 with h1 | hz | ht' | hzt' | hd' | hzd'
  · exfalso
    rw [h1] at hw
    simp at hw
  · exfalso
    apply hwn
    rw [hz]
    change z ∈ closure {z, t}
    exact Subgroup.subset_closure (by simp)
  · exfalso
    apply hwn
    rw [ht']
    change t ∈ closure {z, t}
    exact Subgroup.subset_closure (by simp)
  · exfalso
    apply hwn
    rw [hzt']
    change z * t ∈ closure {z, t}
    exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · left; exact hd'
  · right; exact hzd'

end CFSG.OddStandard.HigherRank.YamadaG23
