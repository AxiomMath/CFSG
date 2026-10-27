module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6X
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK7

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem orderOf_mk_eight {K : Type} [Group K] [Finite K] {g : K} (hg : orderOf g = 8) :
    orderOf (QuotientGroup.mk g : K ⧸ fusionOddCore K) = 8 := by
  have h8 : (QuotientGroup.mk g : K ⧸ fusionOddCore K) ^ 8 = 1 := by
    rw [← QuotientGroup.mk_pow, ← hg, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h4 : (QuotientGroup.mk g : K ⧸ fusionOddCore K) ^ 4 ≠ 1 := by
    intro h
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
    have hg4 : orderOf (g ^ 4) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
    have h1 := eq_one_of_mem_fusionOddCore h ⟨1, by rw [hg4]; norm_num⟩
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hg] at h2
    omega
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (by simpa using h4) (by simpa using h8)
  simpa using this

theorem mk_ne_one_of_invol {K : Type} [Group K] [Finite K] {g : K} (h2 : g * g = 1) (h1 : g ≠ 1) :
    (QuotientGroup.mk g : K ⧸ fusionOddCore K) ≠ 1 := by
  intro h
  rw [QuotientGroup.eq_one_iff] at h
  have hord : orderOf g = 2 :=
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    orderOf_eq_prime (by rw [pow_two]; exact h2) h1
  exact h1 (eq_one_of_mem_fusionOddCore h ⟨1, by rw [hord]; norm_num⟩)

section Ctx

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G} {Q : Sylow 2 G}
  {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}

namespace OuterS16Ctx

theorem exists_order_eight (c : OuterS16Ctx G L z t T E Q x B β S) :
    ∃ s ∈ S, orderOf s = 8 := by
  rcases c.shape with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine ⟨(e.symm (DihedralGroup.r 1) : G), (e.symm (DihedralGroup.r 1)).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  · obtain ⟨y, hy⟩ := CFSG.ABGDGroups.semidihedral_exists_orderOf_eq_eight (n := 4) (le_refl 4)
    refine ⟨(e.symm y : G), (e.symm y).2, ?_⟩
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]

theorem exists_theta (c : OuterS16Ctx G L z t T E Q x B β S) :
    Nonempty ((↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext) := by
  obtain ⟨hz, hconc⟩ := c.hyp.lemma96
  obtain ⟨-, hdisj⟩ := hconc
  rcases hdisj with ⟨N, hNn, ⟨e⟩, hC⟩ | hθ
  swap
  · exact hθ
  exfalso
  haveI := hNn
  have hcfg := c.hyp.outerE.cfg
  obtain ⟨s, hsS, hs8⟩ := c.exists_order_eight
  have hsK : s ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2 (c.BS β c.hyp.outerB.beta_mem s hsS).symm
  have hz2 : (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))) :
      ↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) *
      QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))) = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))) * ⟨z, hz⟩ = 1 := Subtype.ext hcfg.z_sq
    rw [this, QuotientGroup.mk_one]
  have hz1 : (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))) :
      ↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≠ 1 :=
    mk_ne_one_of_invol (Subtype.ext hcfg.z_sq) (fun h => hcfg.z_ne (congrArg Subtype.val h))
  obtain ⟨eAb⟩ := c.hyp.Dbar_iso
  obtain ⟨-, hF8, hFD, -⟩ := c.hyp.Fbar
  have hs8' : orderOf (QuotientGroup.mk (⟨s, hsK⟩ : ↥(centralizer ({β} : Set G))) :
      ↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) = 8 :=
    orderOf_mk_eight (by rw [← Subgroup.orderOf_coe]; exact hs8)
  refine A6X.a6x A6X.a6AutFacts e hC hz2 hz1 eAb ?_ c.hyp.card_cent_zbar hFD hF8 hs8' ?_
  · intro y hy
    exact mem_centralizer_singleton_iff.1 (c.hyp.Dbar_le_cent_zbar hy)
  · rintro _ ⟨y, hy, rfl⟩
    show QuotientGroup.mk (⟨s, hsK⟩ : ↥(centralizer ({β} : Set G))) * QuotientGroup.mk y =
      QuotientGroup.mk y * QuotientGroup.mk (⟨s, hsK⟩ : ↥(centralizer ({β} : Set G)))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 (c.SC hsS) y hy.1).symm

end OuterS16Ctx

end Ctx

end CFSG.EvenSporadicStandard.Fin76b
