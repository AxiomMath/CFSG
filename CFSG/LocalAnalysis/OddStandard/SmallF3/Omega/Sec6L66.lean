module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L66In
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec66_nonabelian [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hcenter : Subgroup.center ↥L = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (h y x)
  haveI : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
    rw [QuotientGroup.subsingleton_iff]
    exact hcenter
  haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hS.component.isQuasisimple.2.1.toNontrivial
  obtain ⟨a, b, hab⟩ :=
    (inferInstance : Nontrivial (↥L ⧸ Subgroup.center ↥L)).exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem sec66_exists_conj [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) :
    ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧ g⁻¹ * t * g ≠ t :=
  sec7_zstar hS.simple (sec66_nonabelian hS) hS.involution

theorem sec66_exists_X [Finite G] (hM : Asc82Tab6M) {L : Subgroup G} (hL : IsOm6M L) {s : G}
    (hs2 : orderOf s = 2) (hsN : s ∈ normalizer (L : Set G)) (hout : ¬ InnerOn L s) :
    ∃ X : Subgroup G, Asc82XSub L s (-1) X ∧ XOut L s = X := by
  by_cases h : layerCent L s = ⊥
  · rcases (hM.layer_trivial G L hL s hs2 hsN).mp h with h4 | ⟨α, hα⟩
    · exact absurd ((hM.inner_iff G L hL s hs2 hsN).mpr h4).1 hout
    · refine ⟨CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G))),
        Or.inr ⟨⟨α, hα⟩, rfl⟩, ?_⟩
      exact hM.xout_i3 G L hL s hs2 hsN ⟨α, hα⟩
  · exact ⟨layerCent L s, Or.inl rfl, hM.xout_eq G L hL s hs2 hsN h⟩

theorem sec66_outer_u [Finite G] (h82 : Asc82Lemma82) (hM : Asc82Tab6M) (hO : Asc82Outside)
    {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hst : g⁻¹ * t * g ≠ t)
    (hsN : g⁻¹ * t * g ∈ normalizer (L : Set G)) (hout : ¬ InnerOn L (g⁻¹ * t * g)) :
    ∃ u : G, orderOf u = 2 ∧ u ∈ CFSG.conjugate L g ∧
      (g⁻¹ * t * g) * u ∈ conjClassIn L (g⁻¹ * t * g) := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by rw [orderOf_conjugate_eq]; exact hS.involution
  obtain ⟨u, hu, hu2, hsu⟩ := hM.ex_u_outer G L hLM (g⁻¹ * t * g) hs2 hsN hout
  obtain ⟨X, hX, hXeq⟩ := sec66_exists_X hM hLM hs2 hsN hout
  have huX : u ∈ XOut L (g⁻¹ * t * g) := mem_twoPrimeRes_of_orderOf_two hu hu2
  have hu' : u ∈ twoPrimeRes X := mem_twoPrimeRes_of_orderOf_two (hXeq ▸ huX) hu2
  have hle := hO.thm2L G t L hS (h82 G t L hS hL6)
    (asc82OddInnerOm6_holds G L (Or.inr (Or.inr hLM))) (-1) g hsC hst X hX
  exact ⟨u, hu2, hle hu', hsu⟩

theorem sec66_outer_case [Finite G] (h82 : Asc82Lemma82) (hM : Asc82Tab6M)
    (hO : Asc82Outside) {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    (hL6 : IsOmega6Minus L) {g : G} (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hst : g⁻¹ * t * g ≠ t) (hsN : g⁻¹ * t * g ∈ normalizer (L : Set G))
    (hout : ¬ InnerOn L (g⁻¹ * t * g)) {z : G} (hz2 : orderOf z = 2) (hzL : z ∈ L) :
    IsConj t (t * z) := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  obtain ⟨u, hu2, huJ, hsu⟩ := sec66_outer_u h82 hM hO hS hL6 hsC hst hsN hout
  have hu'L : g * u * g⁻¹ ∈ L := (mem_conjugate_iff L g u).mp huJ
  have hu'2 : orderOf (g * u * g⁻¹) = 2 := by
    rw [show g * u * g⁻¹ = (g⁻¹)⁻¹ * u * g⁻¹ by rw [inv_inv], orderOf_conjugate_eq, hu2]
  obtain ⟨k, hk, hzk⟩ :=
    hM.inv_one_class G L hLM (g * u * g⁻¹) z hu'L hzL hu'2 hz2
  obtain ⟨l, _, hsl⟩ := hsu
  have hkt : k * t = t * k :=
    Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hk)
  have htu : t * (g * u * g⁻¹) = (g * l * g⁻¹) * t * (g * l * g⁻¹)⁻¹ := by
    calc t * (g * u * g⁻¹)
        = g * ((g⁻¹ * t * g) * u) * g⁻¹ := by group
      _ = g * (l * (g⁻¹ * t * g) * l⁻¹) * g⁻¹ := by rw [hsl]
      _ = (g * l * g⁻¹) * t * (g * l * g⁻¹)⁻¹ := by group
  have htz : t * z = k * (t * (g * u * g⁻¹)) * k⁻¹ := by
    calc t * z = t * (k * (g * u * g⁻¹) * k⁻¹) := by rw [hzk]
      _ = (t * k) * (g * u * g⁻¹) * k⁻¹ := by group
      _ = (k * t) * (g * u * g⁻¹) * k⁻¹ := by rw [← hkt]
      _ = k * (t * (g * u * g⁻¹)) * k⁻¹ := by group
  refine isConj_iff.mpr ⟨k * g * l * g⁻¹, ?_⟩
  calc (k * g * l * g⁻¹) * t * (k * g * l * g⁻¹)⁻¹
      = k * ((g * l * g⁻¹) * t * (g * l * g⁻¹)⁻¹) * k⁻¹ := by group
    _ = k * (t * (g * u * g⁻¹)) * k⁻¹ := by rw [← htu]
    _ = t * z := by rw [← htz]

theorem asc82Lemma66_of (h34c : Asc82Lemma34c) (h36 : Asc82Lemma36) (h82 : Asc82Lemma82)
    (hM : Asc82Tab6M) (hF : Asc82AutFacts) (hO : Asc82Outside) : Asc82Lemma66 := by
  intro G _ _ t L hS hL6 z hz2 hzL
  obtain ⟨g, hsC, hst⟩ := sec66_exists_conj hS
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by rw [orderOf_conjugate_eq]; exact hS.involution
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS (g⁻¹ * t * g) hsC)
  by_cases hin : InnerOn L (g⁻¹ * t * g)
  · exact sec66_inner_case h34c h36 h82 hM hF hS hL6 hsC hst hin hz2 hzL
  · exact sec66_outer_case h82 hM hO hS hL6 hsC hst hsN hin hz2 hzL

end CFSG.OddStandard.SmallF3.Omega
