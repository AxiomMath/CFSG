module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrCE4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18F
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem lf18_5d_of (hS : HRSetting G L) (hZ : Nat.card ↥(center ↥L) ∣ 3)
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) : LF18_5d s := by
  have hZodd : Odd (Nat.card ↥(center ↥L)) := Odd.of_dvd_nat (by decide) hZ
  have hA : LFactsA s := lfactsA_of_setting hS hZodd s
  have hAS : s.fr.A ≤ s.fr.S := s3_A_le_S s
  have hAL : s.fr.A ≤ L := hAS.trans (s3_S_le_L s)
  have hFS : s.fr.F ≤ s.fr.S := (s3_F_le_A s).trans hAS
  have hFL : s.fr.F ≤ L := hFS.trans (s3_S_le_L s)
  have hA2 : IsPGroup 2 ↥s.fr.A := s3_isPGroup_of_le s hAS
  have hAF : s.fr.A ≤ normIn L s.fr.F := by
    refine le_inf hAL ?_
    intro a ha
    change a ∈ Subgroup.normalizer (s.fr.F : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      have hcomm : ⁅a, f⁆ ∈ s.fr.Z := hA.comm_A a ha f (s3_F_le_A s hf)
      have heq : a * f * a⁻¹ = ⁅a, f⁆ * f := by rw [commutatorElement_def]; group
      rw [heq]
      exact Subgroup.mul_mem s.fr.F (s3_Z_le_F s hcomm) hf
    · intro hf
      have hcomm : ⁅a⁻¹, a * f * a⁻¹⁆ ∈ s.fr.Z :=
        hA.comm_A a⁻¹ (s.fr.A.inv_mem ha) (a * f * a⁻¹) (s3_F_le_A s hf)
      have heq : a⁻¹ * (a * f * a⁻¹) * a =
          ⁅a⁻¹, a * f * a⁻¹⁆ * (a * f * a⁻¹) := by
        rw [commutatorElement_def]; group
      have hfeq : f = a⁻¹ * (a * f * a⁻¹) * a := by group
      rw [hfeq, heq]
      exact Subgroup.mul_mem s.fr.F (s3_Z_le_F s hcomm) hf
  have hZN : zL L ≤ normIn L s.fr.F := zL_le_normIn hFL
  have hZ3 : Nat.card ↥(zL L) ∣ 3 := by
    have hcard : Nat.card ↥(zL L) = Nat.card ↥(center ↥L) := by
      simpa [zL] using
        Subgroup.card_map_of_injective (K := center ↥L) (f := L.subtype) L.subtype_injective
    rw [hcard]; exact hZ
  have hZc : ∀ z ∈ zL L, ∀ g ∈ normIn L s.fr.F, z * g = g * z := by
    intro z hz g hg
    have hzC : z ∈ centralizer (L : Set G) := ((mem_zL_iff (L := L)).mp hz).2
    have hgL : g ∈ L := (Subgroup.mem_inf.mp hg).1
    exact (Subgroup.mem_centralizer_iff.mp hzC g hgL).symm
  have hFN : s.fr.F ≤ normIn L s.fr.F := le_inf hFL Subgroup.le_normalizer
  have hFE : IsE 3 ↥s.fr.F := s3_isE3_F hS hZodd hOut s
  have hFn : ∀ g ∈ normIn L s.fr.F, ∀ f ∈ s.fr.F, g * f * g⁻¹ ∈ s.fr.F := by
    intro g hg f hf
    have hgN : g ∈ normalizer (s.fr.F : Set G) := (Subgroup.mem_inf.mp hg).2
    exact (Subgroup.mem_normalizer_iff.mp hgN f).mp hf
  have h5a : centIn L s.fr.F = zL L ⊔ s.fr.F := lf18_5a_of hS hZodd s
  have hCF : ∀ g ∈ normIn L s.fr.F, (∀ f ∈ s.fr.F, g * f = f * g) →
      g ∈ zL L ⊔ s.fr.F := by
    intro g hg hgcomm
    have hgL : g ∈ L := (Subgroup.mem_inf.mp hg).1
    have hgc : g ∈ centralizer (s.fr.F : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun f hf => (hgcomm f hf).symm
    have hmem : g ∈ centIn L s.fr.F := ⟨hgL, hgc⟩
    rwa [h5a] at hmem
  have hQ : SecProp (normIn L s.fr.F) (zL L ⊔ s.fr.F)
      (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) :=
    lf18_5b_of hS hZodd s
  have hN₁ : normIn L s.fr.A ⊓ normIn L s.fr.F ≤ normIn L s.fr.F := inf_le_right
  have hZA : zL L ⊔ s.fr.A ≤ normIn L s.fr.A ⊓ normIn L s.fr.F := by
    refine sup_le (le_inf (zL_le_normIn hAL) (zL_le_normIn hFL)) ?_
    exact le_inf (le_inf hAL Subgroup.le_normalizer) hAF
  have hAn : ∀ g ∈ normIn L s.fr.A ⊓ normIn L s.fr.F, ∀ a ∈ s.fr.A,
      g * a * g⁻¹ ∈ s.fr.A := by
    intro g hg a ha
    have hgN : g ∈ normalizer (s.fr.A : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2
    exact (Subgroup.mem_normalizer_iff.mp hgN a).mp ha
  have hQ₁ : SecProp (normIn L s.fr.A ⊓ normIn L s.fr.F) (zL L ⊔ s.fr.A)
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) :=
    lf18_5e_of hS hZodd s
  obtain ⟨h1, h2⟩ := centExt_comm_complement (N := normIn L s.fr.F)
    (N₁ := normIn L s.fr.A ⊓ normIn L s.fr.F) (Z := zL L) (A := s.fr.A) (F := s.fr.F)
    hZN hZc hZ3 hFN hFE hFn hCF hQ hN₁ hZA hA2 hAn hQ₁
  exact ⟨h1.symm, h2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
