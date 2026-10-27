module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888HtF
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F7M
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F7L
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFThetaAdapt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma f7_comm_of_mem_sup {G : Type} [Group G] {r z : G} {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian 2 B) (hBr : B ≤ centralizer ({r} : Set G))
    (hz : z ∈ zpowers r ⊔ B) : ∀ b ∈ B, b * z = z * b := by
  haveI : IsMulCommutative ↥B := hB.1
  have hle : zpowers r ⊔ B ≤ centralizer (B : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hBr hb)
    · intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      exact setLike_mul_comm hb' hb
  intro b hb
  exact Subgroup.mem_centralizer_iff.mp (hle hz) b hb

theorem asc82Fact512M8_holds : Asc82Fact512M8 := by
  intro G _ _ L _ t ht2 hct r _ hind B hBle hB32 htB _ _ z hz hzA
  obtain ⟨_, V, _, _, _, Q, hQ, e, _, hdim, hsgn, _, _⟩ := hind
  obtain ⟨fr⟩ := exists_nframe_six hQ hdim hsgn
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hBL : B ≤ L := hBle.trans inf_le_left
  have hzL : z ∈ L := by
    obtain ⟨-, K, hzK, hKle, -, -⟩ := hz
    exact (Subgroup.mem_inf.mp (hKle hzK)).1
  have hcard : Nat.card ↥(Subgroup.center ↥L) = 2 := f7_card_center ht2 hct
  have hcenB : ∀ k : ↥L, k ∈ Subgroup.center ↥L → (k : G) ∈ B :=
    fun k hk => f7_center_mem hct htB hk
  have hzB : ∀ b ∈ B, b * z = z * b :=
    f7_comm_of_mem_sup hB32.1 (hBle.trans inf_le_right) hzA
  have hker0 : (ff6mPhi e).ker = Subgroup.center ↥L := ff6mPhi_ker e
  have hE : IsElemAb2 (ffImg (ff6mPhi e) B) 4 :=
    f7_ffImg_isElemAb2 hBL hB32
      (by rw [hker0]; exact fun k hk => Subgroup.mem_subgroupOf.mpr (hcenB k hk))
      (by rw [hker0]; exact hcard)
  obtain ⟨y, hy⟩ := ff_star_E16_conj hQ hdim hsgn h2 fr hE
  have hB1 : ffImg (ff6mPhi (ffAdapt h2 e y)) B = ffB1 hQ fr :=
    ffImg_ffAdapt h2 e y B (ffB1 hQ fr) hy
  set φ : ↥L →* ↥(omegaProj hQ) := ff6mPhi (ffAdapt h2 e y) with hφ
  have hker : φ.ker = Subgroup.center ↥L := ff6mPhi_ker (ffAdapt h2 e y)
  have hsurj : Function.Surjective φ := ff6mPhi_surjective (ffAdapt h2 e y)
  have hkerB : φ.ker ≤ B.subgroupOf L := by
    rw [hker]
    exact fun k hk => Subgroup.mem_subgroupOf.mpr (hcenB k hk)
  let s : ↥L := ⟨z, hzL⟩
  have hcomm : ∀ b ∈ ffB1 hQ fr, φ s * b = b * φ s := by
    intro b hb
    rw [← hB1] at hb
    obtain ⟨l, hl, rfl⟩ := mem_ffImg_iff.mp hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzB (l : G) hl).symm
  have hmem : φ s ∈ ffB1 hQ fr := ff_star_cent_omega hQ hdim hsgn fr (φ s) hcomm
  have hmem' : φ s ∈ ffStar hQ (ffB0 fr) := hmem
  obtain ⟨g, hgB0, hgs⟩ := (mem_ffStar_iff hQ).mp hmem'
  obtain ⟨J, hJe, hgJ⟩ := (mem_ffB0_iff fr).mp hgB0
  let F : ↥L →* ProjOrth Q := (omegaProj hQ).subtype.comp φ
  have hFs : F s = toProj Q (fr.signChange J) := by
    change ((φ s : ↥(omegaProj hQ)) : ProjOrth Q) = _
    rw [← hgs, coe_omegaToProj, hgJ]
  have hFker : ∀ k : ↥L, F k = 1 → k ∈ Subgroup.center ↥L := by
    intro k hk
    rw [← hker, MonoidHom.mem_ker]
    exact Subtype.ext hk
  have hFtop : (⊤ : Subgroup ↥L).map F = omegaProj hQ := by
    ext x
    constructor
    · rintro ⟨l, -, rfl⟩
      exact (φ l).2
    · intro hx
      obtain ⟨l, hl⟩ := hsurj ⟨x, hx⟩
      exact ⟨l, Subgroup.mem_top _, congrArg Subtype.val hl⟩
  obtain ⟨J', hJ'4, hJ'eq⟩ := f7_exists_big fr hJe
  obtain ⟨P, hP8, hPmem, hPinj⟩ := f7_model hQ fr hJ'4
  have hlift : ∀ A ∈ P, ∃ l : ↥L, (l : G) ∈ (zpowers r ⊔ B) ⊓
      twoRes (L ⊓ centralizer ({z} : Set G)) ∧ F l = toProj Q (fr.signChange A) := by
    intro A hA
    obtain ⟨hAe, hAmem⟩ := hPmem A hA
    obtain ⟨b, hbB, hbF⟩ : ∃ b : ↥L, (b : G) ∈ B ∧ F b = toProj Q (fr.signChange A) := by
      have h0 : fr.signChange A ∈ ffB0 fr := signChange_mem_ffB0 fr hAe
      have h1 : omegaToProj hQ ⟨fr.signChange A, ffB0_le_omega hQ fr h0⟩ ∈ ffB1 hQ fr :=
        (mem_ffStar_iff hQ).mpr ⟨⟨fr.signChange A, ffB0_le_omega hQ fr h0⟩, h0, rfl⟩
      rw [← hB1] at h1
      obtain ⟨b, hbB, hb⟩ := mem_ffImg_iff.mp h1
      refine ⟨b, hbB, ?_⟩
      change ((φ b : ↥(omegaProj hQ)) : ProjOrth Q) = _
      rw [hb, coe_omegaToProj]
    rw [hJ'eq, ← hFs, ← hFtop] at hAmem
    obtain ⟨k, hkF, hkK⟩ := f7_exists_lift F (fun k hk => hFker k hk)
      (fun k hk => f7_center_sq hcard (hFker k hk)) s hAmem
    have hkB : (k : G) ∈ B :=
      f7_lift_mem hkerB hbB (Subtype.ext (by rw [← hbF] at hkF; exact hkF))
    exact ⟨k, Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hkB, hkK⟩, hkF⟩
  choose! f hfT hfF using hlift
  have hinj : Function.Injective (fun A : ↥P =>
      (⟨(f A.1 : G), hfT A.1 A.2⟩ :
        ↥((zpowers r ⊔ B) ⊓ twoRes (L ⊓ centralizer ({z} : Set G))))) := by
    intro A A' h
    have h0 : ((f A.1 : ↥L) : G) = ((f A'.1 : ↥L) : G) := Subtype.mk.inj h
    have h1 : f A.1 = f A'.1 := Subtype.ext h0
    have h2' : toProj Q (fr.signChange A.1) = toProj Q (fr.signChange A'.1) := by
      rw [← hfF A.1 A.2, ← hfF A'.1 A'.2, h1]
    exact Subtype.ext (hPinj A.1 A.2 A'.1 A'.2 h2')
  have hcardle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hcardle
  exact hP8.trans hcardle

end CFSG.OddStandard.SmallF3.Omega
