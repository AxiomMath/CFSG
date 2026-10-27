module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7EndM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec66_odd_of_mem_inf [Finite G] {L : Subgroup G} (hL : IsOm6M L) {x : G}
    (hx : x ∈ L ⊓ centralizer (L : Set G)) : Odd (orderOf x) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  have h2 : 2 ∣ orderOf x := even_iff_two_dvd.mp hne
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hy2 : orderOf (x ^ (orderOf x / 2)) = 2 := orderOf_pow_orderOf_div hpos h2
  have hyL : x ^ (orderOf x / 2) ∈ L := L.pow_mem hx.1 _
  have hyC : x ^ (orderOf x / 2) ∈ centralizer (L : Set G) :=
    (centralizer (L : Set G)).pow_mem hx.2 _
  exact sec711M_not_central hL hyL hy2 hyC

theorem sec66_decomp [Finite G] {L : Subgroup G} (hL : IsOm6M L) {s l c : G}
    (hs2 : orderOf s = 2) (hl : l ∈ L) (hc : c ∈ centralizer (L : Set G)) (hs : s = l * c) :
    ∃ v ∈ L, ∃ c' ∈ centralizer (L : Set G), v * v = 1 ∧ c' * c' = 1 ∧ s = v * c' := by
  set n := orderOf (l * l) with hn
  have hs1 : s * s = 1 := by rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
  have hcl : c * l = l * c := hlc.symm
  have hmul : (l * c) * (l * c) = (l * l) * (c * c) := by
    calc (l * c) * (l * c) = l * (c * l) * c := by group
      _ = l * (l * c) * c := by rw [hcl]
      _ = (l * l) * (c * c) := by group
  have h1 : (l * l) * (c * c) = 1 := by rw [← hmul, ← hs, hs1]
  have hll : l * l = (c * c)⁻¹ := mul_eq_one_iff_eq_inv.mp h1
  have hcc : c * c = (l * l)⁻¹ := by rw [hll, inv_inv]
  have hw : l * l ∈ L ⊓ centralizer (L : Set G) :=
    ⟨L.mul_mem hl hl, by
      rw [hll]
      exact (centralizer (L : Set G)).inv_mem (mul_mem hc hc)⟩
  have hodd : Odd n := by
    rw [hn]
    exact sec66_odd_of_mem_inf hL hw
  have hns : s ^ n = s := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_add, pow_mul, pow_two, hs1, one_pow, one_mul, pow_one]
  have hvv : l ^ n * l ^ n = 1 := by
    rw [← Commute.mul_pow (Commute.refl l) n, hn, pow_orderOf_eq_one]
  have hcc1 : c ^ n * c ^ n = 1 := by
    rw [← Commute.mul_pow (Commute.refl c) n, hcc, inv_pow, hn, pow_orderOf_eq_one, inv_one]
  have hsc : s = l ^ n * c ^ n := by
    rw [← hns, hs, Commute.mul_pow (show Commute l c from hlc) n]
  exact ⟨l ^ n, L.pow_mem hl n, c ^ n, (centralizer (L : Set G)).pow_mem hc n,
    hvv, hcc1, hsc⟩

theorem sec66_inner_decomp [Finite G] (h82 : Asc82Lemma82) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) {s : G} (hs2 : orderOf s = 2)
    (hsC : s ∈ centralizer ({t} : Set G)) (hst : s ≠ t) (hin : InnerOn L s) :
    ∃ v ∈ L, orderOf v = 2 ∧ (s = v ∨ s = v * t) := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  obtain ⟨l, hl, c, hc, hslc⟩ := innerOn_decompose hin
  obtain ⟨v, hvL, c', hc', hvv, hcc, hsv⟩ := sec66_decomp hLM hs2 hl hc hslc
  have htC : t ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hx)
  have hc'mem : c' ∈ centralizer ({t} : Set G) := by
    have hc'eq : c' = v⁻¹ * s := by rw [hsv]; group
    rw [hc'eq]
    exact mul_mem (inv_mem (hS.component.le hvL)) hsC
  have hc't : c' * t = t * c' := Subgroup.mem_centralizer_singleton_iff.mp hc'mem
  have hcyc := h82 G t L hS hL6
  rcases eq_one_or_eq_of_commute hcyc hc' htC hcc hS.involution hc't with hc1 | hct
  · have hsv' : s = v := by rw [hsv, hc1, mul_one]
    exact ⟨v, hvL, hsv' ▸ hs2, Or.inl hsv'⟩
  · have hsv' : s = v * t := by rw [hsv, hct]
    have hv_ne : v ≠ 1 := by
      intro hv
      exact hst (by rw [hsv', hv, one_mul])
    have hv2 : orderOf v = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hv_ne
    exact ⟨v, hvL, hv2, Or.inr hsv'⟩

theorem sec66_not_mem [Finite G] (h34c : Asc82Lemma34c) (h36 : Asc82Lemma36)
    (hM : Asc82Tab6M) (hF : Asc82AutFacts) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) {g : G}
    (hvL : g⁻¹ * t * g ∈ L) (hv2 : orderOf (g⁻¹ * t * g) = 2) : False := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  have hI4 : IsI4PlusIn L (g⁻¹ * t * g) := sec711M_pocket hM hF hLM hvL hv2
  obtain ⟨K, hD⟩ := exists_sec3PocketData_of_isI4PlusIn hS.involution hS.component
    (inFStar_of_inF hS.inF) (conjugate_eq_self_of_lemma36 h36 hS) hI4
  have hSg : Sec3SettingLB G (g⁻¹ * t * g) (CFSG.conjugate L g) := hS.conjugate g
  exact h34c G t L hS t L (g⁻¹ * t * g) K hD (CFSG.conjugate L g)
    hSg.component (inFStar_of_inF hSg.inF)

theorem sec66_inner_case [Finite G] (h34c : Asc82Lemma34c) (h36 : Asc82Lemma36)
    (h82 : Asc82Lemma82) (hM : Asc82Tab6M) (hF : Asc82AutFacts) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hst : g⁻¹ * t * g ≠ t)
    (hin : InnerOn L (g⁻¹ * t * g)) {z : G} (hz2 : orderOf z = 2) (hzL : z ∈ L) :
    IsConj t (t * z) := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := by
    rw [orderOf_conjugate_eq]
    exact hS.involution
  obtain ⟨v, hvL, hv2, hcase⟩ := sec66_inner_decomp h82 hS hL6 hs2 hsC hst hin
  rcases hcase with hsv | hsv
  · have hvL' : g⁻¹ * t * g ∈ L := by rw [hsv]; exact hvL
    exact (sec66_not_mem h34c h36 hM hF hS hL6 hvL' hs2).elim
  · obtain ⟨h, hh, hzh⟩ := hM.inv_one_class G L hLM v z hvL hzL hv2 hz2
    have hcomm : ∀ x ∈ L, x * t = t * x := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hx)
    have hht : h * t * h⁻¹ = t := by rw [hcomm h hh]; group
    refine isConj_iff_inv_mul.mpr ⟨g * h⁻¹, ?_⟩
    rw [mul_inv_rev, inv_inv]
    calc h * g⁻¹ * t * (g * h⁻¹) = h * (g⁻¹ * t * g) * h⁻¹ := by group
      _ = h * (v * t) * h⁻¹ := by rw [hsv]
      _ = (h * v * h⁻¹) * (h * t * h⁻¹) := by group
      _ = (h * v * h⁻¹) * t := by rw [hht]
      _ = z * t := by rw [← hzh]
      _ = t * z := hcomm z hzL

end CFSG.OddStandard.SmallF3.Omega
