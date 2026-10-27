module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDVocab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDOrder
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDBlock

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4FD_shape (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1))
    {u : OGroup Q} (hu : u ∈ Sec4FDDt hQ t) (huu : u * u = 1) (hu1 : u ≠ 1)
    (hdvd : 25920 ∣ Nat.card ↥(Sec4FDDt hQ t ⊓ Subgroup.centralizer ({u} : Set (OGroup Q)))) :
    (invType u = (2, -1) ∨ invType u = (6, -1)) ∧ fixSp t ≤ commSp u := by
  have huC : u * t = t * u := ((mem_sec4FDDt_iff hQ).mp hu).2
  have huΩ : u ∈ omegaGroup hQ := ((mem_sec4FDDt_iff hQ).mp hu).1
  have htypes : invType u = (2, -1) ∨ invType u = (6, -1) :=
    sec4FD_types_of_dvd hQ hdim huΩ huu hu1
      (H := Sec4FDDt hQ t ⊓ Subgroup.centralizer ({u} : Set (OGroup Q))) inf_le_right hdvd
  refine ⟨htypes, ?_⟩
  have ht_dim : invDim t = 6 := by
    have := congrArg Prod.fst ht6
    simpa only [invType] using this
  have ht_sign : invSign t = 1 := by
    have := congrArg Prod.snd ht6
    simpa only [invType] using this
  have hU : Module.finrank (ZMod 3) (commSp t) = 6 := by
    simpa only [invDim] using ht_dim
  have h1 : Module.finrank (ZMod 3) (fixSp t) = 1 := by
    have hsum := finrank_fixSp_add_finrank_commSp t
    rw [hdim, hU] at hsum
    omega
  rcases sec4FD_fixSp_dichotomy h1 huC huu with hle | hfix
  · exact hle
  · exfalso
    obtain ⟨b, hb⟩ := sec4FD_exists_blockInr hQ htt huC hfix
    have hbb : b * b = 1 := by
      apply blockInr_injective htt
      rw [map_mul, map_one, ← hb, huu]
    have hub : invDim u = invDim b := by
      have h := congrArg Prod.fst (invType_blockInr hQ htt hbb)
      simp only [invType] at h
      rwa [← hb] at h
    have hww : (t * u) * (t * u) = 1 := by
      calc (t * u) * (t * u) = t * (u * t) * u := by group
        _ = t * (t * u) * u := by rw [huC]
        _ = 1 := by rw [← mul_assoc, htt, one_mul, huu]
    have hw_dim : invDim (t * u) = 6 - invDim u := by
      have h := sec4FD_invDim_mul_blockInr hQ htt hbb
      rw [← hb, ← hub, hU] at h
      exact h
    have hHw : (Sec4FDDt hQ t ⊓ Subgroup.centralizer ({u} : Set (OGroup Q))) ≤
        Subgroup.centralizer ({(t * u)} : Set (OGroup Q)) := by
      intro h hh
      rw [Subgroup.mem_inf] at hh
      obtain ⟨hh1, hh2⟩ := hh
      rw [mem_sec4FDDt_iff hQ] at hh1
      obtain ⟨_, hht⟩ := hh1
      have hhu : h * u = u * h := Subgroup.mem_centralizer_singleton_iff.mp hh2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h * (t * u) = (h * t) * u := by rw [mul_assoc]
        _ = (t * h) * u := by rw [hht]
        _ = t * (h * u) := by rw [mul_assoc]
        _ = t * (u * h) := by rw [hhu]
        _ = (t * u) * h := by rw [mul_assoc]
    rcases htypes with h2 | h6
    · have hu2 : invDim u = 2 := by
        have := congrArg Prod.fst h2
        simpa only [invType] using this
      have hw4 : invDim (t * u) = 4 := by rw [hw_dim, hu2]
      exact (sec4FD_not_dvd_four hQ hdim hww hw4 hHw) hdvd
    · have hu6 : invDim u = 6 := by
        have := congrArg Prod.fst h6
        simpa only [invType] using this
      have hw0 : invDim (t * u) = 0 := by rw [hw_dim, hu6]
      have hw1 : t * u = 1 := (invDim_eq_zero_iff hww).mp hw0
      have hut : u = t := by
        have h := congrArg (fun x => t * x) hw1
        rw [mul_one, ← mul_assoc, htt, one_mul] at h
        exact h
      have htΩ : t ∈ omegaGroup hQ := hut ▸ huΩ
      rw [involution_mem_omegaGroup_iff hQ htt] at htΩ
      rw [ht_dim, ht_sign] at htΩ
      exact absurd htΩ.2 (by decide)

end CFSG.OddStandard.SmallF3.Omega
