module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.HypCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.HypCentre
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.KGroups.U33

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup CFSG.Blueprint

theorem relIndex_twoCore_sup_le_two
    {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hC : SmallF3Cyclic G L) (hQ : LieModel (L ⧸ center L) .PSU 3 3 1) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    (twoCore t ⊔ L).relIndex (invCent t) ≤ 2 := by
  let H : Subgroup G := invCent t
  have hZ : Subgroup.center L = ⊥ := center_eq_bot_of_psu33 hC hQ
  obtain ⟨hHN, hLH, hLn, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hC.standard htL ht
  have hPH : twoCore t ≤ H := Subgroup.map_subtype_le _
  have h1 : Subgroup.centralizer (L : Set G) ⊓ H = twoCore t :=
    centralizer_inf_invCent_eq_twoCore hC ht htL
  let φ : ↥H →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hHN)
  have hφ_apply : ∀ (x : ↥H) (l : ↥L),
      ((φ x l : ↥L) : G) = (x : G) * (l : G) * (x : G)⁻¹ := fun x l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hHN x) l
  have hkerC : φ.ker = (Subgroup.centralizer (L : Set G)).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : G)) hx
      rw [MulAut.one_apply, hφ_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      simpa using h.symm
    · intro hx
      ext l
      rw [MulAut.one_apply, hφ_apply, mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hx (l : G) l.2).symm
  have hCsg : (Subgroup.centralizer (L : Set G)).subgroupOf H = (twoCore t).subgroupOf H := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rw [← h1]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  have hker : φ.ker = (twoCore t).subgroupOf H := hkerC.trans hCsg
  have hφ_conj : ∀ l : ↥L, φ ⟨(l : G), hLH l.2⟩ = MulAut.conj l := by
    intro l
    refine MulEquiv.ext fun y => ?_
    apply Subtype.ext
    rw [hφ_apply, MulAut.conj_apply]
    rfl
  set Kimg : Subgroup (MulAut ↥L) := (L.subgroupOf H).map φ with hKimg
  have hK : Kimg = (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rw [hKimg]
    ext f
    constructor
    · intro hf
      rw [Subgroup.mem_map] at hf
      obtain ⟨x, hx, rfl⟩ := hf
      refine ⟨⟨(x : G), hx⟩, ?_⟩
      exact (hφ_conj ⟨(x : G), hx⟩).symm.trans (congrArg φ (Subtype.ext rfl))
    · intro hf
      rw [MonoidHom.mem_range] at hf
      obtain ⟨l, rfl⟩ := hf
      exact Subgroup.mem_map.mpr ⟨⟨(l : G), hLH l.2⟩, l.2, hφ_conj l⟩
  have hker_conj : (MulAut.conj : ↥L →* MulAut ↥L).ker = ⊥ := by
    rw [← hZ]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx y
      have h := congrArg (fun f : MulAut ↥L => f y) hx
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    · intro hx
      refine MulEquiv.ext fun y => ?_
      rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
      exact (hx y).symm
  have hcard_range : Nat.card (MulAut.conj : ↥L →* MulAut ↥L).range = Nat.card ↥L := by
    have h := Subgroup.card_ker_mul_card_range (MulAut.conj : ↥L →* MulAut ↥L)
    rw [hker_conj, Subgroup.card_bot, one_mul] at h
    exact h
  have hLieL : LieModel ↥L .PSU 3 3 1 := LieModel.of_quotient_center hZ hQ
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hLieL
  have hcardL : Nat.card ↥L = 6048 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.GH74.KGroups.card_group CFSG.GH74.KGroups.U33.QP
        CFSG.GH74.KGroups.U33.QP_ok, CFSG.GH74.KGroups.U33.QP_valid.2]
  have hcardMulAut : Nat.card (MulAut ↥L) = 12096 :=
    CFSG.GH74.KGroups.U33.card_mulAut e
  have hcardK : Nat.card Kimg = 6048 := by
    rw [hK, hcard_range, hcardL]
  have hKindex : Kimg.index = 2 := by
    have h := Subgroup.card_mul_index Kimg
    rw [hcardK, hcardMulAut] at h
    omega
  have hle : Kimg.relIndex φ.range ≤ 2 := by
    have hdiv : Kimg.relIndex φ.range ∣ Kimg.index := by
      rw [hKimg]
      exact Subgroup.relIndex_dvd_index_of_le (Subgroup.map_le_range φ (L.subgroupOf H))
    rw [hKindex] at hdiv
    exact Nat.le_of_dvd (by norm_num) hdiv
  have hcomap : Kimg.comap φ = (twoCore t ⊔ L).subgroupOf H := by
    rw [hKimg, Subgroup.comap_map_eq, hker, ← Subgroup.subgroupOf_sup (B := H) hLH hPH,
      sup_comm]
  have hindex : ((twoCore t ⊔ L).subgroupOf H).index = Kimg.relIndex φ.range := by
    rw [← hcomap]
    exact Subgroup.index_comap (H := Kimg) φ
  show ((twoCore t ⊔ L).subgroupOf H).index ≤ 2
  rw [hindex]
  exact hle

end CFSG.OddStandard.SmallF3.HarrisU33
