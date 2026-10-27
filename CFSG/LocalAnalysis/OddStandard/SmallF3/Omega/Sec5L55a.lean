module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec5_case_central [Finite G] (h52a : Asc82Lemma52a) {t : G} {L : Subgroup G}
    (h : Sec5Setting G t L) {g : G} (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hne : g⁻¹ * t * g ≠ t) (hc : g⁻¹ * t * g ∈ centralizer (L : Set G)) : False := by
  set s : G := g⁻¹ * t * g with hsdef
  have hs2 : orderOf s = 2 := by
    simpa [hsdef, orderOf_conjugate_eq] using h.involution
  have hs1 : s * s = 1 := by
    rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer h.toSec3Setting
  have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp hsC
  rcases sec4_eq_of_commute (h52a G t L h) hc htC hs1 h.involution hst with h1 | h1
  · rw [h1, orderOf_one] at hs2
    exact absurd hs2 (by decide)
  · exact hne h1

theorem sec5_case_inner [Finite G] (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) (tab : Asc82Tab5) {t : G} {L S : Subgroup G} {z : G}
    (h : Sec5Ctx G t L S z) {g : G} (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G))
    (hne : g⁻¹ * t * g ≠ t) (hk : Kind5 L (g⁻¹ * t * g) 0) :
    ∃ h' : G, h'⁻¹ * t * h' = t * z := by
  set s : G := g⁻¹ * t * g with hsdef
  have hs2 : orderOf s = 2 := by
    simpa [hsdef, orderOf_conjugate_eq] using h.involution
  have hsL : s ∈ L := sec5_inner_decomp h52a h52b tab h.toSec5Setting hs2 hsC hk
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b h.toSec5Setting
  rcases tab.inv_classes G L h.toSec5Setting.isOm6Z2 t htZ h.involution z h.pocket s hsL hs2 hne
    with hzu | htz
  · obtain ⟨a, haL, hsa⟩ := hzu
    exfalso
    refine sec5_t_not_conj_z h37 h ((g * a)⁻¹) ?_
    rw [inv_inv]
    have hgt : (g * a)⁻¹ * t * (g * a) = z := by
      have key : (g * a)⁻¹ * t * (g * a) = a⁻¹ * s * a := by rw [hsdef]; group
      rw [key, hsa]
      group
    rw [← hgt]
    group
  · obtain ⟨a, haL, hsa⟩ := htz
    refine ⟨g * a, ?_⟩
    have key : (g * a)⁻¹ * t * (g * a) = a⁻¹ * s * a := by rw [hsdef]; group
    rw [key, hsa]
    group

theorem sec5_case_cover [Finite G] (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a)
    (h52b : Asc82Lemma52b) (h54 : Asc82Lemma54) (hO : Asc82Outside) (tab : Asc82Tab5) {t : G}
    {L S : Subgroup G} {z : G} (h : Sec5Ctx G t L S z) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hne : g⁻¹ * t * g ≠ t)
    (hk : Kind5 L (g⁻¹ * t * g) 3 ∨ Kind5 L (g⁻¹ * t * g) 4 ∨ Kind5 L (g⁻¹ * t * g) 5) :
    ∃ h' : G, h'⁻¹ * t * h' = t * z := by
  set s : G := g⁻¹ * t * g with hsdef
  have hs2 : orderOf s = 2 := by
    simpa [hsdef, orderOf_conjugate_eq] using h.involution
  have hOm : IsOm6Z2 L := h.toSec5Setting.isOm6Z2
  have hsN : s ∈ normalizer (L : Set G) := sec4_mem_normalizer h36 h.toSec3SettingLB s hsC
  obtain ⟨u, huX, hu2, huP, hsu⟩ := tab.cover_i4 G L hOm s hs2 hsN hk
  have hX : Asc82XSub L s (-1) (XOut L s) := by
    rcases hk with hk3 | hk45
    · exact Or.inr ⟨hk3, tab.xout_i3 G L hOm s hs2 hsN hk3⟩
    · refine Or.inl (tab.xout_eq G L hOm s hs2 hsN ?_)
      intro hbot
      rcases tab.layer_trivial G L hOm s hs2 hsN hbot with hk0 | hk3'
      · rcases hk45 with hk4 | hk5
        · exact tab.excl G L hOm s hs2 hsN 4 0 (by norm_num) (by norm_num) (by norm_num) hk4 hk0
        · exact tab.excl G L hOm s hs2 hsN 5 0 (by norm_num) (by norm_num) (by norm_num) hk5 hk0
      · rcases hk45 with hk4 | hk5
        · exact tab.excl G L hOm s hs2 hsN 4 3 (by norm_num) (by norm_num) (by norm_num) hk4 hk3'
        · exact tab.excl G L hOm s hs2 hsN 5 3 (by norm_num) (by norm_num) (by norm_num) hk5 hk3'
  have hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic ↥P :=
    fun P hP => sec5_isCyclic_of_isSylow2Of (h52a G t L h.toSec5Setting) hP
  have hc : Sec5Setting G s (CFSG.conjugate L g) := by
    rw [hsdef]
    exact Sec5Setting.conjugate h.toSec5Setting g
  have hle : twoPrimeRes (XOut L s) ≤ CFSG.conjugate L g :=
    hO.thm2L G t L h.toSec3SettingLB hcyc (asc82OddInnerOm6_holds G L (Or.inl hOm)) (-1) g hsC
      hne (XOut L s) hX
  have huJ : u ∈ CFSG.conjugate L g := hle (mem_twoPrimeRes_of_orderOf_two huX hu2)
  have huC : u ∈ centralizer ({s} : Set G) := (xout_le L s huX).2
  obtain ⟨a, haL, hua⟩ := sec5_pocket_class h52b tab h huP
  have hctx : Sec5Ctx G s (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g) := by
    rw [hsdef]
    exact Sec5Ctx.conjugate h g
  have heq : (g⁻¹ * a⁻¹)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * a⁻¹) = u := by
    rw [hua]
    group
  have hC' : (g⁻¹ * a⁻¹)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * a⁻¹) ∈ centralizer ({s} : Set G) := by
    rw [heq]
    exact huC
  obtain h54res := h54 G s (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g) hctx
    (g⁻¹ * a⁻¹) hC'
  rw [heq] at h54res
  rcases h54res with hcl | ⟨α, hα⟩
  · obtain ⟨b, hbJ, hub⟩ := hcl
    have hbs : b * s = s * b :=
      Subgroup.mem_centralizer_singleton_iff.mp (hc.component.le hbJ)
    obtain ⟨a₁, ha₁L, hsu'⟩ := hsu
    have hEq : a₁ * s * a₁⁻¹ = b * (g⁻¹ * (t * z) * g) * b⁻¹ := by
      rw [← hsu', hub]
      calc s * (b * (g⁻¹ * z * g) * b⁻¹)
          = (s * b) * (g⁻¹ * z * g) * b⁻¹ := by group
        _ = (b * s) * (g⁻¹ * z * g) * b⁻¹ := by rw [hbs]
        _ = b * (g⁻¹ * (t * z) * g) * b⁻¹ := by rw [hsdef]; group
    refine ⟨g * a₁⁻¹ * b * g⁻¹, ?_⟩
    calc (g * a₁⁻¹ * b * g⁻¹)⁻¹ * t * (g * a₁⁻¹ * b * g⁻¹)
        = g * b⁻¹ * (a₁ * (g⁻¹ * t * g) * a₁⁻¹) * b * g⁻¹ := by group
      _ = g * b⁻¹ * (a₁ * s * a₁⁻¹) * b * g⁻¹ := by rw [hsdef]
      _ = g * b⁻¹ * (b * (g⁻¹ * (t * z) * g) * b⁻¹) * b * g⁻¹ := by rw [hEq]
      _ = t * z := by group
  · exfalso
    have hk3' : Kind5 (CFSG.conjugate L g) u 3 := ⟨α, hα⟩
    have hOm' : IsOm6Z2 (CFSG.conjugate L g) := isOm6Z2_conjugate hOm g
    have hNu : u ∈ normalizer ((CFSG.conjugate L g) : Set G) := Subgroup.le_normalizer huJ
    have hnc : u ∉ centralizer ((CFSG.conjugate L g) : Set G) :=
      tab.kind_ne_central G (CFSG.conjugate L g) hOm' u hu2 hNu
        (Or.inr (Or.inr (Or.inl hk3')))
    have h0 : Kind5 (CFSG.conjugate L g) u 0 := ⟨Subgroup.mem_sup_left huJ, hnc⟩
    exact tab.excl G (CFSG.conjugate L g) hOm' u hu2 hNu 0 3 (by norm_num) (by norm_num)
      (by norm_num) h0 hk3'

end CFSG.OddStandard.SmallF3.Omega
