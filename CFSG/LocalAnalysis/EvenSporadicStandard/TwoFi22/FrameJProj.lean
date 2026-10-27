module

public import CFSG.Sporadic.Fi23.Centralizer

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section


@[expose] noncomputable def piC : Cd →* CFSG.Sporadic.Fi22.J where
  toFun c := quotCenterEquiv (c : Cd ⧸ Subgroup.center Cd)
  map_one' := by rw [QuotientGroup.mk_one, map_one]
  map_mul' a b := by rw [QuotientGroup.mk_mul, map_mul]

theorem piC_apply (c : Cd) :
    piC c = quotCenterEquiv (c : Cd ⧸ Subgroup.center Cd) := rfl

theorem pi22_piC (c : Cd) : pi22 (piC c) = rho c := pi22_quotCenterEquiv c

theorem piC_surjective : Function.Surjective piC := by
  intro y
  obtain ⟨q, hq⟩ := quotCenterEquiv.surjective y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨c, hq⟩

theorem ker_piC : piC.ker = Subgroup.center Cd := by
  ext c
  rw [MonoidHom.mem_ker, piC_apply, map_eq_one_iff _ quotCenterEquiv.injective,
    QuotientGroup.eq_one_iff]

theorem piC_dCd : piC dCd = 1 := by
  have : dCd ∈ piC.ker := by
    rw [ker_piC, center_C]
    exact Subgroup.mem_zpowers _
  exact this

theorem card_ker_piC : Nat.card piC.ker = 2 := by
  rw [ker_piC]
  exact card_center_C

theorem piC_ofStar_ptE (u : Fin 3510) :
    piC (ofStar (ptE u)) = CFSG.Sporadic.Fi22.conjPt u.val := by
  apply pi22_injective
  rw [pi22_piC]
  have hi := phiP_lt u.2
  have e : ofStar (ptE u) = starCd (phiP[u.val]!) hi := by
    apply Subtype.ext
    rw [ofStar_val, starCd_val, ptE_apply]
  rw [e, rho_starCd, phiD_phiP u.2]

theorem piC_ofStar_mem_D (x : star) : piC (ofStar x) ∈ CFSG.Sporadic.Fi22.D := by
  obtain ⟨u, rfl⟩ := ptE.surjective x
  rw [piC_ofStar_ptE]
  exact CFSG.Sporadic.Fi22.mem_D_iff.2 ⟨u.val, u.2, rfl⟩

theorem ofStar_injective_of_piC {x y : star} (h : piC (ofStar x) = piC (ofStar y)) : x = y := by
  obtain ⟨u, rfl⟩ := ptE.surjective x
  obtain ⟨v, rfl⟩ := ptE.surjective y
  rw [piC_ofStar_ptE, piC_ofStar_ptE] at h
  have h' := CFSG.Sporadic.Fi22.conjPt_inj (by rw [CFSG.Sporadic.Fi22.orb_size]; exact u.2)
    (by rw [CFSG.Sporadic.Fi22.orb_size]; exact v.2) h
  rw [Fin.ext h']

end

end CFSG.EvenSporadicStandard.TwoFi22.FrameJ
