module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Sec
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Comp
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613

open CFSG CFSG.LocalCores CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
open CFSG.ComponentClassification.OuterAutomorphisms

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_order_p_centralizes {p : ℕ} (hp : p.Prime)
    (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) (hcard : 1 < Nat.card (ComponentIndex Y))
    {x z : Y} (hxp : x ^ p = 1) (hxz : x * z = z * x) (hz1 : z ≠ 1) (hzp : z ^ p = 1)
    (hzL : z ∈ layer Y)
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C')
    {U : Subgroup Y} (hxU : x ∈ U) (hzU : z ∈ U) (hUc : ∀ g ∈ U, g * x = x * g)
    (hrank : Open.pRank p U ≤ 2) (C₀ : ComponentIndex Y) {c : Y} (hcU : c ∈ U)
    (hcC₀ : c ∈ centralizer (C₀.1 : Set Y)) (hcp : c ^ p = 1) (hc1 : c ≠ 1) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcx : c * x = x * c := hUc c hcU
  have hcall := mem_centralizer_of_centralizes_component hcx htrans hcC₀
  have hcL : c ∈ centralizer (layer Y : Set Y) :=
    mem_centralizer_layer_of_forall c fun C d hd => (mem_centralizer_iff.mp (hcall C) d hd).symm
  have hzc : z * c = c * z := mem_centralizer_iff.mp hcL z hzL
  have hczn : c ∉ zpowers z := by
    intro hcz
    exact hc1 (eq_one_of_mem_layer_of_centralizes hZ ((zpowers_le.mpr hzL) hcz) hcall)
  have hzN : z ∈ normalizer (C₀.1 : Set Y) := mem_normalizer_of_mem_layer hZ C₀ hzL
  have hcN : c ∈ normalizer (C₀.1 : Set Y) :=
    (Subgroup.centralizer_le_normalizer (C₀.1 : Set Y)) hcC₀
  have hxN : x ∉ normalizer (C₀.1 : Set Y) := fun h =>
    cjComp_ne_self htrans hcard C₀ ((cjComp_eq_iff x C₀).mpr h)
  have hxE₀ : x ∉ zpowers z ⊔ zpowers c := fun h =>
    hxN (sup_le (zpowers_le.mpr hzN) (zpowers_le.mpr hcN) h)
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hcard1 : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, hzord]
  have hcommz : ∀ e ∈ zpowers z, e * c = c * e := fun e he => by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp he
    exact ((Commute.zpow_left (show Commute z c from hzc) j)).eq
  have hcard2 : Nat.card ↥(zpowers z ⊔ zpowers c) = p * p := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers z) hcp hczn hcommz, hcard1]
  have hE₀x : zpowers z ⊔ zpowers c ≤ centralizer ({x} : Set Y) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxz.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hcx))
  have hcommx : ∀ e ∈ zpowers z ⊔ zpowers c, e * x = x * e := fun e he =>
    mem_centralizer_singleton_iff.mp (hE₀x he)
  have hcard3 : Nat.card ↥((zpowers z ⊔ zpowers c) ⊔ zpowers x) = p ^ 3 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp _ hxp hxE₀ hcommx, hcard2]
    ring
  have hze : CFSG.IsElementaryAbelian p (zpowers z) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hzp
  have hce : CFSG.IsElementaryAbelian p (zpowers c) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hcp
  have hxe : CFSG.IsElementaryAbelian p (zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have hE₀e : CFSG.IsElementaryAbelian p ↥(zpowers z ⊔ zpowers c) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr
      (mem_centralizer_iff.mpr fun e he => hcommz e he))
  have hEe : CFSG.IsElementaryAbelian p ↥((zpowers z ⊔ zpowers c) ⊔ zpowers x) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr
      (mem_centralizer_iff.mpr fun e he => hcommx e he))
  have hEU : (zpowers z ⊔ zpowers c) ⊔ zpowers x ≤ U :=
    sup_le (sup_le (zpowers_le.mpr hzU) (zpowers_le.mpr hcU)) (zpowers_le.mpr hxU)
  have h3 := CFSG.SectionRank.le_pRank hp.one_lt hEU
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hEe) hcard3
  omega

theorem section_card_dvd_component {p : ℕ} (hp : p.Prime)
    (hZ : ∀ C : ComponentIndex Y, center C.1 = ⊥) (hcard : Nat.card (ComponentIndex Y) = p)
    {x z : Y} (hxp : x ^ p = 1) (hxz : x * z = z * x) (hz1 : z ≠ 1) (hzp : z ^ p = 1)
    (hzL : z ∈ layer Y)
    (htrans : ∀ C C' : ComponentIndex Y, ∃ k : ℕ, cjComp (x ^ k) C = C')
    {U : Subgroup Y} (hxU : x ∈ U) (hzU : z ∈ U) (hUc : ∀ g ∈ U, g * x = x * g)
    (hrank : Open.pRank p U ≤ 2) (C₀ : ComponentIndex Y)
    (hcat : IsCatalogGroup ↥C₀.1) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {S : Type} [Group S] [IsSimpleGroup S] (hnab : ¬ ∀ a b : S, a * b = b * a)
    (hpS : p ∣ Nat.card S) (hS : IsSecOf U S) : Nat.card S ∣ Nat.card ↥C₀.1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard1 : 1 < Nat.card (ComponentIndex Y) := hcard ▸ hp.one_lt
  have hsimp : IsSimpleGroup ↥C₀.1 := isSimpleGroup_of_component C₀.2 (hZ C₀)
  have hCnab := exists_noncomm_of_component C₀.2 (hZ C₀)
  have hc : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ normalizer (C₀.1 : Set Y) :=
    fun a ha b hb =>
      ⟨U.mul_mem (U.mul_mem (U.mul_mem ha hb) (U.inv_mem ha)) (U.inv_mem hb),
        commutator_mem_normalizer (hUc a ha) (hUc b hb) htrans C₀⟩
  have h1 : IsSecOf (U ⊓ normalizer (C₀.1 : Set Y)) S := hS.of_commutator_mem hnab inf_le_left hc
  have h2 : IsSecOf ((U ⊓ normalizer (C₀.1 : Set Y)).subgroupOf (normalizer (C₀.1 : Set Y))) S :=
    h1.subgroupOf inf_le_right
  have hker : ¬ p ∣ Nat.card ((Subgroup.normalizerMonoidHom C₀.1).ker ⊓
      (U ⊓ normalizer (C₀.1 : Set Y)).subgroupOf (normalizer (C₀.1 : Set Y)) :
        Subgroup ↥(normalizer (C₀.1 : Set Y))) := by
    intro hdvd
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hcord : orderOf ((c : ↥(normalizer (C₀.1 : Set Y))) : Y) = p := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hc
    have hcp : ((c : ↥(normalizer (C₀.1 : Set Y))) : Y) ^ p = 1 := by
      rw [← hcord]
      exact pow_orderOf_eq_one _
    have hc1 : ((c : ↥(normalizer (C₀.1 : Set Y))) : Y) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hcord
      exact hp.one_lt.ne hcord
    obtain ⟨hcker, hcW⟩ := Subgroup.mem_inf.mp c.2
    have hcU : ((c : ↥(normalizer (C₀.1 : Set Y))) : Y) ∈ U :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hcW)).1
    have hcC₀ : ((c : ↥(normalizer (C₀.1 : Set Y))) : Y) ∈ centralizer (C₀.1 : Set Y) := by
      exact Subgroup.mem_subgroupOf.mp
        ((Subgroup.ext_iff.mp (Subgroup.normalizerMonoidHom_ker (H := C₀.1)) _).mp hcker)
    exact false_of_order_p_centralizes hp hZ hcard1 hxp hxz hz1 hzp hzL htrans hxU hzU hUc hrank
      C₀ hcU hcC₀ hcp hc1
  have h3 := h2.map_hom (Subgroup.normalizerMonoidHom C₀.1) hpS hker hnab
  haveI hsolv : Group.IsSolvable (Outer ↥C₀.1) := hSch ↥C₀.1 hsimp hCnab hcat
  have h4 := IsSecOf.ker_of_solvable hnab (QuotientGroup.mk' (inner ↥C₀.1)) (h3.mono le_top)
  rw [QuotientGroup.ker_mk', inf_top_eq] at h4
  have h5 : IsSecOf (⊤ : Subgroup ↥C₀.1) S :=
    (h4.comap (MulAut.conj : ↥C₀.1 →* MulAut ↥C₀.1) (le_of_eq rfl)).mono le_top
  have h6 := h5.card_dvd
  rwa [Subgroup.card_top] at h6

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613
