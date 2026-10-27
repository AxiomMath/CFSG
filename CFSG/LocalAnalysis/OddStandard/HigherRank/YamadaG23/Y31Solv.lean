module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict1
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

private theorem innerAut_normal' (Q : Type) [Group Q] : (innerAut Q).Normal where
  conj_mem n hn β := by
    obtain ⟨g, rfl⟩ := hn
    refine ⟨β g, ?_⟩
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

private theorem isSolvable_of_isCyclic_sylow_two {K : Type} [Group K] [Finite K]
    (S : Sylow 2 K) (hS : IsCyclic ↥(S : Subgroup K)) : Group.IsSolvable K := by
  obtain ⟨N, hNnormal, hNS⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two S hS
  haveI := hNnormal
  have hNodd : Odd (Nat.card ↥N) := by
    rw [← hNS.index_eq_card]
    exact Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp S.not_dvd_index)
  haveI hNsolv : Group.IsSolvable ↥N := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥N hNodd
  haveI hSsolv : Group.IsSolvable ↥(S : Subgroup K) := by
    haveI := hS
    infer_instance
  have hQsolv : Group.IsSolvable (K ⧸ N) := by
    haveI := hSsolv
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' N).comp (S : Subgroup K).subtype) ?_
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hk : k ∈ (N ⊔ (S : Subgroup K)) := by rw [hNS.sup_eq_top]; trivial
    obtain ⟨n, hn, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    refine ⟨⟨t, ht⟩, ?_⟩
    show QuotientGroup.mk' N t = QuotientGroup.mk' N (n * t)
    rw [map_mul]
    rw [show (QuotientGroup.mk' N) n = 1 from (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  haveI := hQsolv
  exact Group.isSolvable_of_subgroup_quotient N

theorem s3_centEl_solvable_of_odd (hS : HRSetting G L)
    (hOut : (innerAut (L ⧸ center L)).index = 2) (y : G)
    (hodd : Odd (Nat.card ↥(centEl L (y * s.t * y⁻¹) ⊓ conjSub y L))) :
    Group.IsSolvable ↥(centEl L (y * s.t * y⁻¹)) := by
  let Inn : Subgroup (MulAut (L ⧸ center L)) := innerAut (L ⧸ center L)
  haveI hInnN : Inn.Normal := innerAut_normal' (L ⧸ center L)
  let N0 : Subgroup ↥s.H := L.subgroupOf s.H
  haveI hN0N : N0.Normal := s3_L_normal_H s hS
  haveI hPerf : Group.IsPerfect ↥L := isPerfect_of_hrSetting hS
  have hCsolv : Group.IsSolvable ↥(centralizer (L : Set G)) := by
    obtain ⟨S, hScyc⟩ := hS.cyclic
    exact isSolvable_of_isCyclic_sylow_two S hScyc
  let φ : ↥s.H →* MulAut (L ⧸ center L) := jOn L (s3_H_le_N s hS)
  let g₀ : ↥s.H →* MulAut (L ⧸ center L) ⧸ Inn := (QuotientGroup.mk' Inn).comp φ
  have hker : N0 ≤ g₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine (QuotientGroup.eq_one_iff (N := Inn) (φ x)).mpr ?_
    rw [show Inn = jSub L L from (jSub_self L).symm]
    exact (mem_jSub L).mpr ⟨(x : G), Subgroup.mem_subgroupOf.mp hx,
      jOn_actsAs L (s3_H_le_N s hS) x⟩
  let g : ↥s.H ⧸ N0 →* MulAut (L ⧸ center L) ⧸ Inn := QuotientGroup.lift N0 g₀ hker
  have hinf : centIn s.H L ≤ s.H := inf_le_left
  let f : ↥(centIn s.H L) →* ↥s.H ⧸ N0 :=
    (QuotientGroup.mk' N0).comp (Subgroup.inclusion hinf)
  haveI hCentSolv : Group.IsSolvable ↥(centIn s.H L) := by
    haveI := hCsolv
    let e := Subgroup.subgroupOfEquivOfLe (H := centIn s.H L)
      (K := centralizer (L : Set G)) inf_le_right
    exact Group.isSolvable_of_ker_le_range (G'' := PUnit.{1}) e.toMonoidHom
      (1 : ↥(centIn s.H L) →* PUnit) (by
        intro x _
        exact e.surjective x)
  haveI hOutSolv : Group.IsSolvable (MulAut (L ⧸ center L) ⧸ Inn) := by
    have hcard : Nat.card (MulAut (L ⧸ center L) ⧸ Inn) = 2 := by
      rw [← Subgroup.index_eq_card (H := Inn)]
      exact hOut
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic (MulAut (L ⧸ center L) ⧸ Inn) := isCyclic_of_prime_card hcard
    infer_instance
  have hfg : g.ker ≤ f.range := by
    intro q hq
    obtain ⟨hh, rfl⟩ := QuotientGroup.mk'_surjective N0 q
    have hg0 : g₀ hh = 1 := by
      have h1 : g ((QuotientGroup.mk' N0) hh) = 1 := MonoidHom.mem_ker.mp hq
      rwa [show g ((QuotientGroup.mk' N0) hh) = g₀ hh from
        QuotientGroup.lift_mk' (N := N0) (φ := g₀) hker hh] at h1
    have hφInn : jOn L (s3_H_le_N s hS) hh ∈ Inn := by
      rw [← QuotientGroup.ker_mk' Inn, MonoidHom.mem_ker]
      simpa [g₀, φ, MonoidHom.comp_apply] using hg0
    have hφj : jOn L (s3_H_le_N s hS) hh ∈ jSub L L := by
      rw [jSub_self L]
      exact hφInn
    obtain ⟨l, hlL, hlacts⟩ := (mem_jSub L).mp hφj
    have hlH : l ∈ s.H := s3_L_le_H s hS hlL
    have hcin : l⁻¹ * (hh : G) ∈ centIn s.H L := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact s.H.mul_mem (s.H.inv_mem hlH) hh.2
      · have h1 : ActsAs L l⁻¹ (jOn L (s3_H_le_N s hS) hh)⁻¹ := actsAs_inv L hlacts
        have h2 : ActsAs L (hh : G) (jOn L (s3_H_le_N s hS) hh) :=
          jOn_actsAs L (s3_H_le_N s hS) hh
        have h3 : ActsAs L (l⁻¹ * (hh : G))
            ((jOn L (s3_H_le_N s hS) hh)⁻¹ * jOn L (s3_H_le_N s hS) hh) :=
          actsAs_mul L h1 h2
        exact (actsAs_one_iff L).mp (by simpa using h3)
    let c : ↥(centIn s.H L) := ⟨l⁻¹ * (hh : G), hcin⟩
    refine ⟨c, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hinf c)
        : ↥s.H ⧸ N0) = (QuotientGroup.mk hh : ↥s.H ⧸ N0)
    rw [QuotientGroup.eq_iff_div_mem]
    rw [show N0 = L.subgroupOf s.H from rfl, Subgroup.mem_subgroupOf]
    have hdiv : (Subgroup.inclusion hinf c) / hh
        = (⟨l, hlH⟩ : ↥s.H)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_div, Subgroup.coe_inv, Subgroup.coe_inclusion]
      simp only [c, Subtype.coe_mk]
      rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]
    rw [hdiv]
    simpa using L.inv_mem hlL
  haveI hHQuotSolv : Group.IsSolvable (↥s.H ⧸ N0) :=
    Group.isSolvable_of_ker_le_range f g hfg
  let X : Subgroup G := centEl L (y * s.t * y⁻¹)
  let conjHom : ↥X →* G := (MulAut.conj y⁻¹).toMonoidHom.comp X.subtype
  have hmemH : ∀ x : ↥X, conjHom x ∈ s.H := by
    intro x
    change conjHom x ∈ Subgroup.centralizer ({s.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [conjHom, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    have hxC : (x : G) ∈ Subgroup.centralizer ({(y * s.t * y⁻¹)} : Set G) :=
      (Subgroup.mem_inf.mp x.2).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC
    have h1 : y * s.t = (y * s.t * y⁻¹) * y := by group
    have h2 : y⁻¹ * (y * s.t * y⁻¹) = s.t * y⁻¹ := by group
    calc (y⁻¹ * (x : G) * y) * s.t
        = y⁻¹ * (x : G) * (y * s.t) := by group
      _ = y⁻¹ * (x : G) * ((y * s.t * y⁻¹) * y) := by
          conv_lhs => rw [h1]
      _ = y⁻¹ * ((x : G) * (y * s.t * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * s.t * y⁻¹) * (x : G)) * y := by rw [hxC]
      _ = (y⁻¹ * (y * s.t * y⁻¹)) * (x : G) * y := by group
      _ = (s.t * y⁻¹) * (x : G) * y := by
          conv_lhs => rw [h2]
      _ = s.t * (y⁻¹ * (x : G) * y) := by group
  let fH : ↥X →* ↥s.H := conjHom.codRestrict s.H hmemH
  have hfH : ∀ x : ↥X, ((fH x : ↥s.H) : G) = y⁻¹ * (x : G) * y := by
    intro x
    simp only [fH, MonoidHom.codRestrict_apply, conjHom, MonoidHom.comp_apply,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  let ψ : ↥X →* ↥s.H ⧸ N0 := (QuotientGroup.mk' N0).comp fH
  have hψmem : ∀ x : ↥X, x ∈ ψ.ker ↔ y⁻¹ * (x : G) * y ∈ L := by
    intro x
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (fH x) : ↥s.H ⧸ N0) = 1 ↔ y⁻¹ * (x : G) * y ∈ L
    rw [QuotientGroup.eq_one_iff]
    rw [show N0 = L.subgroupOf s.H from rfl, Subgroup.mem_subgroupOf, hfH x]
  have hψker_eq : ψ.ker = (conjSub y L).subgroupOf X := by
    ext x
    rw [hψmem x, Subgroup.mem_subgroupOf, conjSub, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨y⁻¹ * (x : G) * y, hx, ?_⟩
      show (MulAut.conj y) (y⁻¹ * (x : G) * y) = (x : G)
      rw [MulAut.conj_apply]
      group
    · rintro ⟨l, hlL, hlx⟩
      have hxl : y⁻¹ * (x : G) * y = l := by
        rw [← hlx]
        change y⁻¹ * (MulAut.conj y) l * y = l
        rw [MulAut.conj_apply]
        group
      rw [hxl]
      exact hlL
  have hcardker : Nat.card ↥ψ.ker = Nat.card ↥(X ⊓ conjSub y L) := by
    rw [hψker_eq, ← Subgroup.inf_subgroupOf_left (conjSub y L) X]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ conjSub y L ≤ X)).toEquiv
  have hkerodd : Odd (Nat.card ↥ψ.ker) := by
    rw [hcardker]
    exact hodd
  haveI hkerSolv : Group.IsSolvable ↥ψ.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard ↥ψ.ker hkerodd
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ (by rw [Subgroup.range_subtype])

end CFSG.OddStandard.HigherRank.YamadaG23
