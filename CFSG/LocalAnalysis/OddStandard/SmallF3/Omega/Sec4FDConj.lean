module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDVocab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4FD_exists_conj (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1))
    {u u' : OGroup Q} (hu : u ∈ Sec4FDDt hQ t) (hu' : u' ∈ Sec4FDDt hQ t) (huu : u * u = 1)
    (hu'u' : u' * u' = 1) (hF : fixSp t ≤ commSp u) (hF' : fixSp t ≤ commSp u')
    (hty : invType u = invType u') : ∃ c ∈ Sec4FDDt hQ t, c * u * c⁻¹ = u' := by
  have huC : u * t = t * u := ((mem_sec4FDDt_iff hQ).mp hu).2
  have hu'C : u' * t = t * u' := ((mem_sec4FDDt_iff hQ).mp hu').2
  obtain ⟨b, hbb, hu_eq⟩ := sec4FD_exists_block_neg hQ htt huC huu hF
  obtain ⟨b', hb'b', hu'_eq⟩ := sec4FD_exists_block_neg hQ htt hu'C hu'u' hF'
  have ht_dim : Module.finrank (ZMod 3) (commSp t) = 6 := by
    have := congrArg Prod.fst ht6
    simpa only [invType, invDim] using this
  have hU : 2 ≤ Module.finrank (ZMod 3) (commSp t) := by rw [ht_dim]; decide
  have h3U : 3 ≤ Module.finrank (ZMod 3) (commSp t) := by rw [ht_dim]; decide
  have htype_u : invType u = (1 + invDim b, invSign b * (-1) ^ invDim b) := by
    rw [hu_eq]
    exact sec4FD_invType_mul_block hQ hdim hσ htt ht6 hbb
  have htype_u' : invType u' = (1 + invDim b', invSign b' * (-1) ^ invDim b') := by
    rw [hu'_eq]
    exact sec4FD_invType_mul_block hQ hdim hσ htt ht6 hb'b'
  have hpairs : (1 + invDim b, invSign b * (-1) ^ invDim b) =
      (1 + invDim b', invSign b' * (-1) ^ invDim b') :=
    htype_u.symm.trans (hty.trans htype_u')
  have hb_dim : invDim b = invDim b' := by
    have := congrArg Prod.fst hpairs
    omega
  have hb_sign : invSign b = invSign b' := by
    have hsnd := congrArg Prod.snd hpairs
    rw [hb_dim] at hsnd
    exact mul_right_cancel hsnd
  have hb_type : invType b = invType b' := by
    simp only [invType]
    exact Prod.ext hb_dim hb_sign
  obtain ⟨c, hc, hcb⟩ := exists_mem_omegaGroup_conj (nondegenerate_restrict_commSp hQ htt)
    h3U hbb hb'b' hb_type
  refine ⟨blockInr htt c, ?_, ?_⟩
  · rw [mem_sec4FDDt_iff hQ]
    exact ⟨blockInr_mem_omegaGroup hQ htt hU hc,
      Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ htt c)⟩
  · have hπg : blockInr htt c * piOrth Q = piOrth Q * blockInr htt c :=
      Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (blockInr htt c)
    have hgt : blockInr htt c * t = t * blockInr htt c :=
      Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ htt c)
    have hg_inv : blockInr htt c * (piOrth Q * t) = (piOrth Q * t) * blockInr htt c := by
      calc blockInr htt c * (piOrth Q * t)
          = (blockInr htt c * piOrth Q) * t := by group
        _ = (piOrth Q * blockInr htt c) * t := by rw [hπg]
        _ = piOrth Q * (blockInr htt c * t) := by group
        _ = piOrth Q * (t * blockInr htt c) := by rw [hgt]
        _ = (piOrth Q * t) * blockInr htt c := by group
    have hgmap : blockInr htt c * blockInr htt b * (blockInr htt c)⁻¹ =
        blockInr htt (c * b * c⁻¹) := by
      rw [← map_mul, ← map_inv, ← map_mul]
    calc blockInr htt c * u * (blockInr htt c)⁻¹
        = blockInr htt c * ((piOrth Q * t) * blockInr htt b) * (blockInr htt c)⁻¹ := by
            rw [hu_eq]
      _ = (blockInr htt c * (piOrth Q * t)) *
            (blockInr htt b * (blockInr htt c)⁻¹) := by group
      _ = ((piOrth Q * t) * blockInr htt c) *
            (blockInr htt b * (blockInr htt c)⁻¹) := by rw [hg_inv]
      _ = (piOrth Q * t) *
            (blockInr htt c * blockInr htt b * (blockInr htt c)⁻¹) := by group
      _ = (piOrth Q * t) * blockInr htt (c * b * c⁻¹) := by rw [hgmap]
      _ = (piOrth Q * t) * blockInr htt b' := by rw [hcb]
      _ = u' := hu'_eq.symm

theorem sec4FD_exists_swap (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1))
    {u : OGroup Q} (hu : u ∈ Sec4FDDt hQ t) (huu : u * u = 1) (hF : fixSp t ≤ commSp u)
    (hty : invType u = (2, -1)) : ∃ c ∈ omegaGroup hQ, c * t * c⁻¹ = t * u := by
  have huC : u * t = t * u := ((mem_sec4FDDt_iff hQ).mp hu).2
  obtain ⟨b, hbb, hu_eq⟩ := sec4FD_exists_block_neg hQ htt huC huu hF
  have htype_u : invType u = (1 + invDim b, invSign b * (-1) ^ invDim b) := by
    rw [hu_eq]
    exact sec4FD_invType_mul_block hQ hdim hσ htt ht6 hbb
  have hpairs : (2, -1) = (1 + invDim b, invSign b * (-1) ^ invDim b) :=
    hty.symm.trans htype_u
  have hb_dim : invDim b = 1 := by
    have := congrArg Prod.fst hpairs
    omega
  have hb_sign : invSign b = 1 := by
    have hsnd := congrArg Prod.snd hpairs
    rw [hb_dim, pow_one] at hsnd
    have h1 : (1 : ℤˣ) * (-1) = invSign b * (-1) := by rw [one_mul]; exact hsnd
    exact (mul_right_cancel h1).symm
  have htu : t * u = piOrth Q * blockInr htt b := by
    rw [hu_eq]
    have hπt : t * piOrth Q = piOrth Q * t :=
      Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t
    calc t * ((piOrth Q * t) * blockInr htt b)
        = (t * (piOrth Q * t)) * blockInr htt b := by group
      _ = ((t * piOrth Q) * t) * blockInr htt b := by group
      _ = ((piOrth Q * t) * t) * blockInr htt b := by rw [hπt]
      _ = (piOrth Q * (t * t)) * blockInr htt b := by group
      _ = piOrth Q * blockInr htt b := by rw [htt]; simp
  have hπb_type : invType (piOrth Q * blockInr htt b) = (6, 1) := by
    have h7 : 7 - 1 = (6 : ℕ) := by norm_num
    rw [sec4FD_invType_pi_block hQ hdim hσ htt hbb, hb_dim, hb_sign, h7]
  have htu_sq : (t * u) * (t * u) = 1 := by
    calc (t * u) * (t * u) = t * (u * t) * u := by group
      _ = t * (t * u) * u := by rw [huC]
      _ = (t * t) * (u * u) := by group
      _ = 1 := by rw [htt, huu]; simp
  have htype : invType t = invType (t * u) := by
    rw [htu, hπb_type, ht6]
  have h3 : 3 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; decide
  exact exists_mem_omegaGroup_conj hQ h3 htt htu_sq htype

end CFSG.OddStandard.SmallF3.Omega
