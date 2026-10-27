module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106D

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10L106_no_sq_t [Finite G] (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h103 : Asc82Lemma103) (h105 : Asc82Lemma105) (hK0 : Asc82Lemma10K0)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hCK : Asc82FactCentK5)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) {x : G} (hxL : x ∈ centralizer (L : Set G)) (hxS : x ∈ S)
    (hx : x * x = t) : False := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  have htC : t ∈ centralizer (L : Set G) := (hb G t L S z hctx.toSec10Z).2.1
  have hz2 : orderOf z = 2 := hctx.pocket.1
  obtain ⟨g, -, hgt, hgz⟩ := sec10_exists_g h37 h103 h105 hb hctx
  have hgtz : g * (t * z) * g⁻¹ = t := by rw [← hgt]; group
  have hzconj : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz]
      _ = z := by group
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hzL' : z ∈ CFSG.conjugate L g := by
    rw [mem_conjugate_iff', hzconj]
    exact hzL
  have hL' : IsPSp43 (CFSG.conjugate L g) := isPSp43_conjugate hpsp g
  have hK1' : Sl23PocketIn (CFSG.conjugate L g) z (CFSG.conjugate K1 g) := by
    have h := hctx.pocket1.conjugate g
    rwa [hgz] at h
  have hK2' : Sl23PocketIn (CFSG.conjugate L g) z (CFSG.conjugate K2 g) := by
    have h := hctx.pocket2.conjugate g
    rwa [hgz] at h
  have hne' : CFSG.conjugate K1 g ≠ CFSG.conjugate K2 g := by
    intro h
    refine hctx.ne (Subgroup.map_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective ?_)
    exact h
  have hxt : t * x = x * t :=
    Subgroup.mem_centralizer_iff.1 (hctx.sylow.1 hxS) t (Set.mem_singleton t)
  have hxz : x * z = z * x := hctx.central x hxS
  have hgxC : g * x * g⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    have hxtz : x * (t * z) = (t * z) * x := by
      calc x * (t * z) = (x * t) * z := by group
        _ = (t * x) * z := by rw [hxt]
        _ = t * (x * z) := by group
        _ = t * (z * x) := by rw [hxz]
        _ = (t * z) * x := by group
    have h1 : (g * x * g⁻¹) * t = g * (x * (t * z)) * g⁻¹ := by
      rw [← hgt]; group
    have h2 : g * (x * (t * z)) * g⁻¹ = t * (g * x * g⁻¹) := by
      rw [hxtz]
      calc g * ((t * z) * x) * g⁻¹
          = (g * (t * z) * g⁻¹) * (g * x * g⁻¹) := by group
        _ = t * (g * x * g⁻¹) := by rw [hgtz]
    exact (h1.trans h2).symm
  have hgxN : g * x * g⁻¹ ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB (g * x * g⁻¹) hgxC
  have hxN' : x ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hgxN ⊢
    intro y
    rw [mem_conjugate_iff', mem_conjugate_iff']
    have hxy : g * (x * y * x⁻¹) * g⁻¹
        = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
    rw [hxy]
    exact hgxN (g * y * g⁻¹)
  have hcomm : ∀ k ∈ CFSG.conjugate K1 g ⊔ CFSG.conjugate K2 g, x * k = k * x :=
    sec10L106_comm h36 hK0 hP5 hC5 hb hctx hgt hgz hxL hxN'
  have hxsup : x ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) ⊔ zpowers z :=
    hCK G (CFSG.conjugate L g) hL' z hz2 (CFSG.conjugate K1 g) (CFSG.conjugate K2 g)
      hK1' hK2' hne' x hxN' hcomm
  have hcommLK : ∀ h ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G),
      ∀ k ∈ zpowers z, h * k = k * h := by
    intro h hh k hk
    have hzh : Commute z h := Subgroup.mem_centralizer_iff.1 hh z hzL'
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [← hi]
    exact (hzh.zpow_left i).symm
  obtain ⟨c, hc_mem, z', hz'_mem, hxz'⟩ :=
    exists_mul_of_mem_sup_of_commute hcommLK hxsup
  have hz'2 : z' * z' = 1 := by
    have hdvd : orderOf z' ∣ 2 := by
      simpa [hz2] using orderOf_dvd_of_mem_zpowers hz'_mem
    simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp hdvd
  have ht_eq_cc : t = c * c := by
    have hcz' : c * z' = z' * c := hcommLK c hc_mem z' hz'_mem
    calc t = x * x := hx.symm
      _ = (c * z') * (c * z') := by rw [hxz']
      _ = c * (z' * c) * z' := by group
      _ = c * (c * z') * z' := by rw [← hcz']
      _ = (c * c) * (z' * z') := by group
      _ = c * c := by rw [hz'2, mul_one]
  have ht_mem : t ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [ht_eq_cc]
    exact (Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)).mul_mem
      hc_mem hc_mem
  have htz_mem : t * z ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [← hgt]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : g * a * g⁻¹ ∈ L := (mem_conjugate_iff' (H := L) (g := g) (x := a)).1 ha
    have hlt : (g * a * g⁻¹) * t = t * (g * a * g⁻¹) :=
      Subgroup.mem_centralizer_iff.1 htC (g * a * g⁻¹) ha'
    calc a * (g⁻¹ * t * g) = g⁻¹ * ((g * a * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * a * g⁻¹)) * g := by rw [hlt]
      _ = (g⁻¹ * t * g) * a := by group
  have hz_mem : z ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    have hprod : t * (t * z) ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
      (Subgroup.centralizer ((CFSG.conjugate L g : Subgroup G) : Set G)).mul_mem
        ht_mem htz_mem
    have htz_eq : t * (t * z) = z := by
      have ht2 : t * t = 1 := by simpa [hctx.involution, pow_two] using pow_orderOf_eq_one t
      rw [← mul_assoc, ht2, one_mul]
    rwa [htz_eq] at hprod
  have hzbot : z ∈ (CFSG.conjugate L g : Subgroup G) ⊓
      centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := ⟨hzL', hz_mem⟩
  rw [inf_centralizer_eq_bot_of_psp43
    (isQuasisimple_conjugate hctx.component.isQuasisimple g) hL'] at hzbot
  rw [Subgroup.mem_bot] at hzbot
  rw [hzbot, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

end CFSG.OddStandard.SmallF3.Omega
