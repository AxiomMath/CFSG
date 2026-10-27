module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.L2Aut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GFH
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GSetup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.GH74.GLS.Th2.P412

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X] {t z : G} {T : Subgroup G}
  {π : ↥(centralizer ({z} : Set G)) →* X}

private theorem sec5op5_img_eq_cls {t z : G} {T : Subgroup G}
    {π : ↥(centralizer ({z} : Set G)) →* X} (hyp : Sec5OPHyp t z T π)
    {x : Sec5GBar (sec5op_Tb z T π)} (hx : x ∈ Sec5GImg (sec5op_Tb z T π)) :
    ∃ (τ : G) (hτ : τ ∈ T), x = sec5op_cls hyp ⟨τ, hyp.TY hτ⟩ := by
  obtain ⟨a, ha, hax⟩ := (sec5g_mem_img (A := sec5op_Tb z T π)).mp hx
  rw [sec5op_Tb] at ha
  obtain ⟨τh, hτh, hτa⟩ := Subgroup.mem_map.mp ha
  subst a
  refine ⟨(τh : G), Subgroup.mem_subgroupOf.mp hτh, ?_⟩
  have hthis : (⟨π τh, subset_normalClosure ha⟩ :
      ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) =
      ⟨π ⟨(τh : G), sec5op_Y_le hyp.tH (hyp.TY (Subgroup.mem_subgroupOf.mp hτh))⟩,
        sec5op_pi_mem hyp (hyp.TY (Subgroup.mem_subgroupOf.mp hτh))⟩ := by
    apply Subtype.ext
    exact congrArg π (Subtype.ext rfl)
  rw [← hax, hthis]
  rfl

private theorem sec5op5_cls_mem_img {t z : G} {T : Subgroup G}
    {π : ↥(centralizer ({z} : Set G)) →* X} (hyp : Sec5OPHyp t z T π) {τ : G} (hτ : τ ∈ T) :
    sec5op_cls hyp ⟨τ, hyp.TY hτ⟩ ∈ Sec5GImg (sec5op_Tb z T π) := by
  rw [Sec5GImg]
  refine Subgroup.mem_map.mpr ⟨⟨π ⟨τ, sec5op_Y_le hyp.tH (hyp.TY hτ)⟩,
    sec5op_pi_mem hyp (hyp.TY hτ)⟩, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_map.mpr ⟨⟨τ, hyp.TH hτ⟩, Subgroup.mem_subgroupOf.mpr hτ,
      congrArg π (Subtype.ext rfl)⟩)

private theorem sec5op5_orderOf_cls_t {t z : G} {T : Subgroup G}
    {π : ↥(centralizer ({z} : Set G)) →* X} (hyp : Sec5OPHyp t z T π) :
    orderOf (sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩) = 2 := by
  haveI : Finite X := Finite.of_surjective π hyp.surj
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hyp.ht, pow_two] at h
    exact h
  have htY : (⟨t, sec5op_t_mem_Y t z⟩ : ↥(sec5op_Y t z)) *
      ⟨t, sec5op_t_mem_Y t z⟩ = 1 := by
    apply Subtype.ext
    simpa [pow_two] using htt
  have hcls2 : sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul, htY, map_one]
  have hcXne : π ⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩ ≠ 1 := by
    intro h1
    have hmem : (⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩ :
        ↥(centralizer ({z} : Set G))) ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact h1
    rw [hyp.ker] at hmem
    exact hyp.t_not_mem (Subgroup.mem_subgroupOf.mp hmem)
  have htH2 : (⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩ :
      ↥(centralizer ({z} : Set G))) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using htt
  have hcX2 : π ⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩ ^ 2 = 1 := by
    rw [← map_pow, htH2, map_one]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcXorder : orderOf (π ⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩) = 2 :=
    orderOf_eq_prime hcX2 hcXne
  have hpi_eq : sec5g_pi (sec5op_Tb z T π)
      ⟨π ⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩,
        sec5op_pi_mem hyp (sec5op_t_mem_Y t z)⟩ =
      sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ := rfl
  have hcMorder : orderOf (⟨π ⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩,
      sec5op_pi_mem hyp (sec5op_t_mem_Y t z)⟩ :
      ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hcXorder
  have hclsne : sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ ≠ 1 := by
    intro h1
    have hpi1 : sec5g_pi (sec5op_Tb z T π)
        ⟨π ⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩,
          sec5op_pi_mem hyp (sec5op_t_mem_Y t z)⟩ = 1 := hpi_eq.trans h1
    have hmem : (⟨π ⟨t, sec5op_Y_le hyp.tH (sec5op_t_mem_Y t z)⟩,
        sec5op_pi_mem hyp (sec5op_t_mem_Y t z)⟩ :
        ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) ∈
        goldschmidtOddCore ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X)) :=
      (QuotientGroup.eq_one_iff _).1 hpi1
    have h2dvd : 2 ∣ Nat.card (goldschmidtOddCore
        ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X))) := by
      rw [← hcMorder]
      exact Subgroup.orderOf_dvd_natCard _ hmem
    exact (odd_card_goldschmidtOddCore (M :=
      ↥(normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X)))).not_two_dvd_nat h2dvd
  exact orderOf_eq_prime hcls2 hclsne

theorem sec5op_rho_eq_one
    (hyp : Sec5OPHyp t z T π)
    (hA : Sec5GCaseI (sec5op_Tb z T π) ∨ Sec5GCaseII (sec5op_Tb z T π))
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    {k : G} (hk : k ∈ centralizer ({z} : Set G)) (hkodd : Odd (orderOf k))
    (hkT : ∀ a ∈ T, k * a * k⁻¹ = a)
    (hkY : ∀ y ∈ sec5op_Y t z, y * t = t * y → Odd (orderOf y) → k * y * k⁻¹ = y) :
    sec5op_rho z T π ⟨k, hk⟩ = 1 := by
  rcases hA with hI | hII
  ·
    ext x
    obtain ⟨τ, hτ, hx⟩ := sec5op5_img_eq_cls hyp (by rw [hI]; exact Subgroup.mem_top x)
    rw [hx, sec5op_rho_cls hyp hk ⟨τ, hyp.TY hτ⟩]
    exact congrArg (sec5op_cls hyp) (Subtype.ext (hkT τ hτ))
  ·
    obtain ⟨F, hF, hFfin, h5F, h8F, ⟨e⟩, P, hP⟩ := sec5g_caseII_field hII
    letI : Field F := hF
    letI : Finite F := hFfin
    haveI : Finite X := Finite.of_surjective π hyp.surj
    set u : Sec5GBar (sec5op_Tb z T π) := sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ with hu_def
    have hu : orderOf u = 2 := by
      rw [hu_def]
      exact sec5op5_orderOf_cls_t hyp
    have huP : u ∈ (P : Subgroup (Sec5GBar (sec5op_Tb z T π))) := by
      rw [hP, hu_def,
        show (⟨t, sec5op_t_mem_Y t z⟩ : ↥(sec5op_Y t z)) = ⟨t, hyp.TY hyp.tT⟩ from
          Subtype.ext rfl]
      exact sec5op5_cls_mem_img hyp hyp.tT
    have hidx : Odd (P : Subgroup (Sec5GBar (sec5op_Tb z T π))).index := by
      rw [← Nat.not_even_iff_odd]
      intro hEven
      exact Sylow.not_dvd_index P (even_iff_two_dvd.mp hEven)
    have hPc : ∀ x ∈ (P : Subgroup (Sec5GBar (sec5op_Tb z T π))), x * u = u * x := by
      intro x hx
      rw [hP] at hx
      obtain ⟨τ, hτ, hxτ⟩ := sec5op5_img_eq_cls hyp hx
      rw [hxτ, hu_def, ← map_mul, ← map_mul]
      exact congrArg (sec5op_cls hyp) (Subtype.ext (hTab τ hτ t hyp.tT))
    have hPfix : ∀ x ∈ (P : Subgroup (Sec5GBar (sec5op_Tb z T π))),
        sec5op_rho z T π ⟨k, hk⟩ x = x := by
      intro x hx
      rw [hP] at hx
      obtain ⟨τ, hτ, hxτ⟩ := sec5op5_img_eq_cls hyp hx
      rw [hxτ, sec5op_rho_cls hyp hk ⟨τ, hyp.TY hτ⟩]
      exact congrArg (sec5op_cls hyp) (Subtype.ext (hkT τ hτ))
    have hodd : ∀ c ∈ Subgroup.centralizer ({u} : Set (Sec5GBar (sec5op_Tb z T π))),
        Odd (orderOf c) → sec5op_rho z T π ⟨k, hk⟩ c = c := by
      intro c hc hcodd
      have hct : c * sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ =
          sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ * c := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hc
        rw [hu_def] at h
        exact h
      obtain ⟨y, hy, hyt, hyodd, hycls⟩ := sec5op_lift_odd hyp c hcodd hct
      rw [← hycls, sec5op_rho_cls hyp hk ⟨y, hy⟩]
      exact congrArg (sec5op_cls hyp) (Subtype.ext (hkY y hy hyt hyodd))
    have hfix := sec5op_fix_centralizer (sec5op_rho z T π ⟨k, hk⟩)
      (P : Subgroup (Sec5GBar (sec5op_Tb z T π))) P.isPGroup' hidx hPc hPfix hodd
    have hc2 : Odd (orderOf (⟨k, hk⟩ : ↥(centralizer ({z} : Set G)))) := by
      simpa only [Subgroup.orderOf_mk] using hkodd
    exact l2aut_action_odd_trivial e h5F h8F (sec5op_rho z T π) (c := ⟨k, hk⟩) hc2 hu hfix

end CFSG.OddStandard.SmallF3.Omega
