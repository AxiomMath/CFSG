module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24Outer
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24U

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.Sporadic.FischerOddCore
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.Fi24 (R jR jR_injective range_jR)
open CFSG.LocalAnalysis.GLTheoremA.H1017 (fi24R2_mul_self)


private theorem fi24QR_center :
    timmesfeldIsExtraspecial ↥(fi24QC.map fi24CR) ∧
      (Subgroup.center ↥(fi24QC.map fi24CR)).map (fi24QC.map fi24CR).subtype =
        Subgroup.zpowers zR := by
  haveI := fi24C_finite
  haveI := fi24QC_extraspecial
  have hQC : timmesfeldIsExtraspecial ↥fi24QC :=
    (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_iff _).2
      (CFSG.IsExtraspecial.isExtraspecialPGroup (p := 2) (P := ↥fi24QC))
  have key := CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv
    (H := ↥fi24QC) (K := ↥(fi24QC.map fi24CR))
  have hQ : timmesfeldIsExtraspecial ↥(fi24QC.map fi24CR) :=
    key (fi24QC.equivMapOfInjective fi24CR fi24CR_injective) hQC
  refine ⟨hQ, ?_⟩
  have hzR : zR = jR fi24R2 := rfl
  have hzQ : zR ∈ fi24QC.map fi24CR := ⟨⟨fi24R2, fi24R2_mem_C⟩, by
    show fi24Rho _ ∈ fi24N
    rw [fi24Rho_z]
    exact Subgroup.one_mem _, fi24CR_z⟩
  have hzZ : (⟨zR, hzQ⟩ : ↥(fi24QC.map fi24CR)) ∈ Subgroup.center ↥(fi24QC.map fi24CR) :=
    Subgroup.mem_center_iff.2 fun q => by
      obtain ⟨c, -, hc⟩ := q.2
      refine Subtype.ext ?_
      show (q : R) * zR = zR * q
      rw [← hc, ← fi24CR_z, ← map_mul, ← map_mul]
      exact congrArg fi24CR (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2))
  have hz2 : orderOf zR = 2 := orderOf_eq_prime
    (by rw [hzR, pow_two, ← map_mul, fi24R2_mul_self, map_one])
    (fun h => fi24R2_ne_one (jR_injective (by rw [← hzR, h, map_one])))
  have hle : Subgroup.zpowers zR ≤
      (Subgroup.center ↥(fi24QC.map fi24CR)).map (fi24QC.map fi24CR).subtype :=
    Subgroup.zpowers_le.2 ⟨_, hzZ, rfl⟩
  refine (Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)).symm
  rw [Subgroup.card_map_of_injective (fi24QC.map fi24CR).subtype_injective, hQ.2.2.2,
    Nat.card_zpowers, hz2]

private theorem fi24QR_at {F : Subgroup R} (hFJ : F ≤ jR.range)
    (hFz : F ≤ Subgroup.centralizer ({zR} : Set R)) (hF : IsElemAbelian 3 F)
    (hc : Nat.card F = 243) :
    fi24QC.map fi24CR ⊓ Subgroup.centralizer (F : Set R) ≤ Subgroup.zpowers zR ∧
      (∀ H : Subgroup R, H ≤ F → Nat.card H * 3 = Nat.card F →
        Nat.card ↥(fi24QC.map fi24CR ⊓ Subgroup.centralizer (H : Set R)) ≤ 2 ^ 3) ∧
      (∀ T : Subgroup R, IsPGroup 2 T → T ≤ Subgroup.centralizer ({zR} : Set R) →
        F ≤ Subgroup.normalizer (T : Set R) → T ≤ fi24QC.map fi24CR) ∧
      F ≤ Subgroup.normalizer ((fi24QC.map fi24CR : Subgroup R) : Set R) := by
  haveI := fi24C_finite
  have hrange : ∀ X : Subgroup R, X ≤ jR.range → X ≤ Subgroup.centralizer ({zR} : Set R) →
      X ≤ fi24CR.range := fun X hXJ hXz => by
    rw [fi24CR_range, ← range_jR]
    exact le_inf hXJ hXz
  have hFφ := hrange F hFJ hFz
  have hF'map : (F.comap fi24CR).map fi24CR = F := Subgroup.map_comap_eq_self hFφ
  have hF' : IsElemAbelian 3 (F.comap fi24CR) := hF.comap fi24CR_injective
  have hF'c : Nat.card (F.comap fi24CR) = 243 := by
    rw [← Subgroup.card_map_of_injective fi24CR_injective, hF'map, hc]
  have hcent : ∀ P H : Subgroup ↥fi24C, P.map fi24CR ⊓
      Subgroup.centralizer ((H.map fi24CR : Subgroup R) : Set R) ≤
        (P ⊓ Subgroup.centralizer (H : Set ↥fi24C)).map fi24CR := by
    rintro P H _ ⟨⟨q, hq, rfl⟩, hqH⟩
    refine ⟨q, ⟨hq, Subgroup.mem_centralizer_iff.2 fun h hh => fi24CR_injective ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.1 hqH _ ⟨h, hh, rfl⟩
  obtain ⟨hCF, hCH⟩ := fi24QC_inf_centralizer_le hF' hF'c
  refine ⟨?_, fun H hHF hH => ?_, fun T hT hTz hFT => ?_, ?_⟩
  ·
    have h := hcent fi24QC (F.comap fi24CR)
    rw [hF'map] at h
    refine h.trans ?_
    rw [← fi24CR_z, ← MonoidHom.map_zpowers]
    exact Subgroup.map_mono hCF
  ·
    have hHφ : (H.comap fi24CR).map fi24CR = H := Subgroup.map_comap_eq_self (hHF.trans hFφ)
    have hH' : Nat.card (H.comap fi24CR) * 3 = Nat.card (F.comap fi24CR) := by
      rw [← Subgroup.card_map_of_injective fi24CR_injective, hHφ, hH, hc, hF'c]
    have h := hcent fi24QC (H.comap fi24CR)
    rw [hHφ] at h
    calc Nat.card ↥(fi24QC.map fi24CR ⊓ Subgroup.centralizer (H : Set R))
        ≤ Nat.card ↥((fi24QC ⊓ Subgroup.centralizer
          ((H.comap fi24CR : Subgroup ↥fi24C) : Set ↥fi24C)).map fi24CR) :=
          Subgroup.card_le_of_le h
      _ = Nat.card ↥(fi24QC ⊓ Subgroup.centralizer
          ((H.comap fi24CR : Subgroup ↥fi24C) : Set ↥fi24C)) :=
          Subgroup.card_map_of_injective fi24CR_injective
      _ ≤ 2 ^ 3 := hCH _ (Subgroup.comap_mono hHF) hH'
  ·
    have hTφ := hrange T (le_range_jR_of_elemAbelian hFJ hF (hc.trans (by norm_num)) hFz hT
      hTz hFT) hTz
    rw [← Subgroup.map_comap_eq_self hTφ]
    exact Subgroup.map_mono (le_of_parrottData_elemAbelian fi24C_parrottData hF' hF'c
      (hT.comap_of_injective fi24CR fi24CR_injective)
      ((Subgroup.comap_mono hFT).trans (Subgroup.le_normalizer_comap fi24CR)))
  ·
    haveI := fi24QC_normal
    rw [← hF'map]
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map fi24CR)
    rw [Subgroup.normalizer_eq_top]
    exact le_top

theorem fi24QR_local :
    timmesfeldIsExtraspecial ↥fi24QR ∧
      (Subgroup.center ↥fi24QR).map fi24QR.subtype = Subgroup.zpowers zR ∧
      ∀ F : Subgroup R, F ≤ jR.range → F ≤ Subgroup.centralizer ({zR} : Set R) →
        IsElemAbelian 3 F → Nat.card F = 243 →
        fi24QR ⊓ Subgroup.centralizer (F : Set R) ≤ Subgroup.zpowers zR ∧
          (∀ H : Subgroup R, H ≤ F → Nat.card H * 3 = Nat.card F →
            Nat.card ↥(fi24QR ⊓ Subgroup.centralizer (H : Set R)) ≤ 2 ^ 3) ∧
          (∀ T : Subgroup R, IsPGroup 2 T → T ≤ Subgroup.centralizer ({zR} : Set R) →
            F ≤ Subgroup.normalizer (T : Set R) → T ≤ fi24QR) ∧
          F ≤ Subgroup.normalizer (fi24QR : Set R) :=
  ⟨fi24QR_center.1, fi24QR_center.2, fun _ hFJ hFz hF hc => fi24QR_at hFJ hFz hF hc⟩

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
