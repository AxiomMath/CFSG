module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairPODefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Lift
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardDefs

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

theorem HasPOmegaMember.lift (hC2 : POmegaPlusCentreExpTwo) {L Q : Type} [Group L] [Finite L]
    [Group Q] [Finite Q] (π : L →* Q) (hπ : Function.Surjective π) (hk : π.ker ≤ center L)
    (h : HasPOmegaMember Q) : HasPOmegaMember L := by
  obtain ⟨J', ū, hJ⟩ := h
  have hJ'perf : ⁅J', J'⁆ = J' := Subgroup.isPerfect_iff.mp hJ.block.quasisimple.1
  obtain ⟨J, hJle, hJnorm, hJperf, hJmap⟩ := exists_perfect_cover_subgroup π hπ J' hJ'perf
  obtain ⟨ρ, hρs, hρπ, hρk⟩ := exists_hom_of_map_eq π hk hJmap
  haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJperf
  have hqs : IsQuasisimple ↥J :=
    isQuasisimple_of_central_cover ρ hρs hρk inferInstance hJ.block.quasisimple
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_of_central_cover ρ hρs hρk inferInstance
  obtain ⟨n, hn, hm⟩ := hJ.block.shape
  have hmJ : CFSG.Blueprint.LieModel (↥J ⧸ center ↥J) .POmegaPlus n 3 1 :=
    ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv eZ.symm hm
  have hsq : ∀ x ∈ center ↥J, x * x = 1 := hC2 ↥J hqs n hn hmJ
  have hZp : IsPGroup 2 ↥(center ↥J) := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hsq (g : ↥J) g.2)⟩
  let b : ↥J' := ⟨ū, hJ.mem⟩
  have hb2 : orderOf b = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hJ.orderOf_eq_two
  have hb1 : b ≠ 1 := by
    intro hb
    rw [hb, orderOf_one] at hb2
    omega
  have hbcenter : b ∈ center ↥J' := hJ.mem_center
  obtain ⟨u, hu⟩ := hρs b
  have hcenter : (center ↥J').comap ρ = center ↥J :=
    comap_center_eq_of_central_cover ρ hρs hρk inferInstance
  have hu_center : u ∈ center ↥J := by
    rw [← hcenter, Subgroup.mem_comap, hu]
    exact hbcenter
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, map_one] at hu
    exact hb1 hu.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : orderOf u = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hsq u hu_center) hu1
  let u' : L := (u : L)
  have hu'2 : orderOf u' = 2 := by
    show orderOf ((u : ↥J) : L) = 2
    rw [Subgroup.orderOf_coe]
    exact hu2
  have hπu : π u' = ū := by
    have h := hρπ u
    rw [hu] at h
    exact h.symm
  have hu'mem : u' ∈ J := by
    show ((u : ↥J) : L) ∈ J
    exact u.2
  have hJcent : J ≤ Subgroup.centralizer ({u'} : Set L) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    show x * ((u : ↥J) : L) = ((u : ↥J) : L) * x
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hu_center (⟨x, hx⟩ : ↥J))
  have hsub : IsSubnormal J (Subgroup.centralizer ({u'} : Set L)) := by
    have hchain : IsSubnormal J ((Subgroup.centralizer ({ū} : Set Q)).comap π) :=
      IsSubnormal.trans (IsSubnormal.step hJle hJnorm (IsSubnormal.refl _))
        (IsSubnormal.comap π hJ.subnormal)
    have hcentle : Subgroup.centralizer ({u'} : Set L) ≤
        (Subgroup.centralizer ({ū} : Set Q)).comap π := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      rw [← hπu]
      simpa using congrArg π hx
    have h := hchain.inf_of_le hcentle
    rwa [inf_eq_left.mpr hJcent] at h
  have hu'_not_center : u' ∉ center L := by
    intro hc
    apply hJ.not_mem_center
    rw [← hπu]
    rw [Subgroup.mem_center_iff] at hc
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := hπ q
    rw [← map_mul, ← map_mul, hc l]
  exact ⟨J, u', ⟨hu'2, hu'mem, hu'_not_center, hsub, ⟨hqs, hZp, ⟨n, hn, hmJ⟩⟩⟩⟩

end CFSG.OddStandard.HigherRank.F3
