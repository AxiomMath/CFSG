module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec12Frame_of (hp : Asc82Pre11) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2)
    (halt1 : Sec1011Alt1 t S L) : Sec12Frame t L S := by
  obtain ⟨hpsp, htC, -, -, -, hsyl⟩ := hp.basic G t L S z hctx.toSec10Z
  have hLC : L ⊓ centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_psp43 hctx.component.isQuasisimple hpsp
  have hCt : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    sec4_mem_normalizer hp.s3.l36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have hSM : S ≤ secM t S L :=
    (Subgroup.le_normalizer : S ≤ normalizer (S : Set G)).trans
      (hp.r10.l109 G t L S z K1 K2 hctx)
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hLle : L ≤ centralizer ({t} : Set G) := hctx.component.le
  refine ⟨hctx.involution, htC, hLC, hCt, hSM,
    sec10BData_of hp.basic hp.facts.b5 hctx.toSec10Z, ?_, ?_, halt1,
    sec10K0_oddCore_le_centralizer hpsp hzL hz2 hLle hCt, ?_, ?_⟩
  · intro g hgN hgcomm
    exact hp.facts.centB5 G L hpsp (S ⊓ L) hsyl g hgN hgcomm
  · intro m hm b hb
    exact (hp.r10.l1010 G t L S z K1 K2 hctx).1 m hm b hb
  · intro c hcL hct hodd
    exact sec10K0_mem_oddCoreIn (hp.r10.l102 G t L hctx.toSec10Setting) hCt hcL hct hodd
  · intro c hcL hct hpow
    obtain ⟨k, hc2⟩ := hpow
    have hPz : IsPGroup 2 ↥(Subgroup.zpowers c) := by
      apply IsPGroup.of_card_dvd_pow (n := k)
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hc2
    have hzpc : Subgroup.zpowers c ≤ centralizer ({t} : Set G) := Subgroup.zpowers_le.mpr hct
    obtain ⟨Q, hQ, hzpcQ⟩ := exists_isSylow2Of_ge hPz hzpc
    obtain ⟨a, haC, ha_conj⟩ := IsSylow2Of.exists_conj_mem hctx.sylow hQ
    have haN : a ∈ normalizer (L : Set G) := hCt haC
    have hconjS : a⁻¹ * c * a ∈ S := (ha_conj c).mp (hzpcQ (Subgroup.mem_zpowers c))
    have hconjC : a⁻¹ * c * a ∈ centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp haN l).mp hl
      have hcl : (a * l * a⁻¹) * c = c * (a * l * a⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hcL) (a * l * a⁻¹) hl'
      calc l * (a⁻¹ * c * a) = a⁻¹ * ((a * l * a⁻¹) * c) * a := by group
        _ = a⁻¹ * (c * (a * l * a⁻¹)) * a := by rw [hcl]
        _ = (a⁻¹ * c * a) * l := by group
    have h106 := hp.r10.l106 G t L S z K1 K2 hctx
    have hconj_mem : a⁻¹ * c * a ∈ zpowers t := by
      have hmem : a⁻¹ * c * a ∈ centralizer (L : Set G) ⊓ S := ⟨hconjC, hconjS⟩
      rwa [h106] at hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hconj_mem
    have ha_comm : Commute a t := ((Subgroup.mem_centralizer_iff.mp haC) t (by simp)).symm
    have hconj_eq : a * t ^ i * a⁻¹ = t ^ i := by
      have h := (ha_comm.zpow_right i).eq
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    have hc_eq : c = t ^ i := by
      calc c = a * (a⁻¹ * c * a) * a⁻¹ := by group
        _ = a * t ^ i * a⁻¹ := by rw [← hi]
        _ = t ^ i := hconj_eq
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, hc_eq.symm⟩

end CFSG.OddStandard.SmallF3.Omega
