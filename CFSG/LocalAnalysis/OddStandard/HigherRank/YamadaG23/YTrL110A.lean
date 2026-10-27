module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18Def
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJSec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrImg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrSigA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private def IsPerm3Prod (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))

theorem lf110_1_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1)
    (hg : ActsAs L g s.fr'.σ) : LF110_1 s g := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have h110 := s.facts.2.2.2.2.2.2.2.2.2
  have hgN : g ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L hg
  have hAL : s.fr.A ≤ L := (s3_A_le_S s).trans (s3_S_le_L s)
  have hA2 : IsPGroup 2 ↥s.fr.A := s3_isPGroup_of_le s (s3_A_le_S s)
  have hNA : normIn L s.fr.A ≤ normalizer (L : Set G) :=
    inf_le_left.trans Subgroup.le_normalizer
  have hclG : closure ({g} : Set G) ≤ normalizer (L : Set G) :=
    (closure_le (normalizer (L : Set G))).mpr (by rintro x rfl; exact hgN)
  have hV : normIn L s.fr.A ⊔ closure ({g} : Set G) ≤ normalizer (L : Set G) :=
    sup_le hNA hclG
  have hNV : zL L ⊔ s.fr.A ≤ normIn L s.fr.A ⊔ closure ({g} : Set G) := by
    refine sup_le ?_ ?_
    · exact (zL_le_normIn (L := L) hAL).trans le_sup_left
    · exact (le_inf hAL le_normalizer).trans le_sup_left
  have hVle : normIn L s.fr.A ⊔ closure ({g} : Set G) ≤ L ⊔ closure ({g} : Set G) :=
    sup_le_sup_right inf_le_left _
  have hK : ∀ x ∈ normIn L s.fr.A ⊔ closure ({g} : Set G),
      x ∈ centralizer (L : Set G) → x ∈ zL L ⊔ s.fr.A := by
    intro x hx hxc
    exact Subgroup.mem_sup_left (s3_kernel_Vg (L := L) hS hOut s hg2 hg (hVle hx) hxc)
  have hjG : jSub L (closure ({g} : Set G)) =
      closure ({s.fr'.σ} : Set (MulAut (L ⧸ center L))) := by
    have h := jSub_closure_of_actsAs (L := L) ({g} : Set G)
      (by rintro x rfl; exact hgN) (fun _ => s.fr'.σ) (by rintro x rfl; exact hg)
    simpa using h
  have hjV : jSub L (normIn L s.fr.A ⊔ closure ({g} : Set G)) =
      normIn (innerAut (L ⧸ center L)) s.fr'.A ⊔
        closure ({s.fr'.σ} : Set (MulAut (L ⧸ center L))) := by
    rw [jSub_sup (L := L) hNA hclG, jSub_normIn (L := L) hZ hAL hA2, jSub_self L,
      s3_jSub_A s, hjG]
  have hjN : jSub L (zL L ⊔ s.fr.A) = s.fr'.A := by
    rw [jSub_sup_zL (L := L) hAL, s3_jSub_A s]
  refine (secProp_jSub (L := L) hV hNV hK IsPerm3Prod
    (fun Y Y' _ _ e => ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩)).mpr ?_
  rw [hjV, hjN]
  exact h110.1.1

theorem lf110_4_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1)
    (hg : ActsAs L g s.fr'.σ) : LF110_4 s g := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have h110 := s.facts.2.2.2.2.2.2.2.2.2
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans ((s3_A_le_S s).trans (s3_S_le_L s))
  have hF2 : IsPGroup 2 ↥s.fr.F := s3_isPGroup_of_le s ((s3_F_le_A s).trans (s3_A_le_S s))
  refine (mem_normalizer_iff_jSub (L := L) hZ hFL hF2 hg).mpr ?_
  rw [s3_jSub_F (L := L) hS hZ s]
  exact h110.2.1

theorem lf110_5_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) (s : Setting3 G L) {g : G} (hg2 : g ^ 2 = 1)
    (hg : ActsAs L g s.fr'.σ) : LF110_5 s g := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have h110 := s.facts.2.2.2.2.2.2.2.2.2
  have hgN : g ∈ normalizer (L : Set G) := mem_normalizer_of_actsAs L hg
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans ((s3_A_le_S s).trans (s3_S_le_L s))
  have hF2 : IsPGroup 2 ↥s.fr.F := s3_isPGroup_of_le s ((s3_F_le_A s).trans (s3_A_le_S s))
  intro x hx
  have hxL : x ∈ L := (inf_le_left : normIn L s.fr.F ≤ L) hx
  let ξ : MulAut (L ⧸ center L) := MulAut.conj (QuotientGroup.mk (⟨x, hxL⟩ : ↥L))
  have hξacts : ActsAs L x ξ := actsAs_of_mem L hxL
  have hξN : ξ ∈ normalizer (jSub L s.fr.F : Set (MulAut (L ⧸ center L))) :=
    (mem_normIn_iff_jSub (L := L) hZ hFL hF2 hxL hξacts).mp hx
  have hξF' : ξ ∈ normalizer (s.fr'.F : Set (MulAut (L ⧸ center L))) := by
    rwa [s3_jSub_F (L := L) hS hZ s] at hξN
  have hξmem : ξ ∈ normIn (innerAut (L ⧸ center L)) s.fr'.F :=
    ⟨⟨QuotientGroup.mk (⟨x, hxL⟩ : ↥L), rfl⟩, hξF'⟩
  have hcommF' : ⁅s.fr'.σ, ξ⁆ ∈ s.fr'.F := h110.2.2 ξ hξmem
  have hcomm_acts : ActsAs L ⁅g, x⁆ ⁅s.fr'.σ, ξ⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    exact actsAs_mul L (actsAs_mul L (actsAs_mul L hg hξacts) (actsAs_inv L hg))
      (actsAs_inv L hξacts)
  have hcommL : ⁅g, x⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN x).mp hxL) (L.inv_mem hxL)
  have hmem : ⁅g, x⁆ ∈ zL L ⊔ s.fr.F :=
    mem_zL_sup_of_actsAs (L := L) hFL hcommL hcomm_acts
      (by rw [s3_jSub_F (L := L) hS hZ s]; exact hcommF')
  simpa [sup_comm] using hmem

end CFSG.OddStandard.HigherRank.YamadaG23
