module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.DatumOf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.DiagCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.NcData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.QuotAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem false_of_pump_diagonal (hI : Phase1Inputs) (hA7 : TwoA7RankOne) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Catalog G) (hcat : ¬ Catalog G) {y z : G} {K T N : Subgroup G}
    {q₀ : ℕ} (h : NcData G y z K T N q₀)
    (hbal : oddCore ↥(centralizer ({z} : Set G)) = ⊥) {M : Subgroup G}
    (hM : Omega.IsComponentIn M (centralizer ({z} : Set G)))
    (hne : M.map (MulAut.conj y).toMonoidHom ≠ M)
    (hcomm : ⁅M, M.map (MulAut.conj y).toMonoidHom⁆ = ⊥) (φ : ↥M →* G)
    (hφ : ∀ m : ↥M, φ m = (m : G) * (y * m * y⁻¹)) (hTφ : T = φ.range)
    (hker : φ.ker ≤ center ↥M) : False := by
  have hZ2 : IsPGroup 2 ↥(center ↥M) := isPGroup_two_center_of_isComponentIn hbal hM
  have hMq : IsQuasisimple ↥M := Omega.IsComponentIn.isQuasisimple hM
  have hMq2 : HarrisLit.IsTwoQuasisimple ↥M := isTwoQuasisimple_of_isQuasisimple hMq hZ2
  have hN_range : N ≤ φ.range := hTφ ▸ h.hNT
  obtain ⟨P, hPP, hPSL, hPmap, hPinj⟩ :=
    exists_sl2_cover hI.griess φ hker hZ2 hN_range h.hqodd h.hq5 h.hSL
  have hzPmap : z ∈ P.map φ := hPmap.symm ▸ h.hzN
  obtain ⟨c0, hc0P, hφc0⟩ := Subgroup.mem_map.mp hzPmap
  have hordP : orderOf (⟨c0, hc0P⟩ : ↥P) = 2 := by
    have h1 : orderOf ((φ.comp P.subtype) ⟨c0, hc0P⟩) = orderOf (⟨c0, hc0P⟩ : ↥P) :=
      orderOf_injective (φ.comp P.subtype) hPinj _
    have h2 : orderOf ((φ.comp P.subtype) ⟨c0, hc0P⟩) = 2 := by
      rw [show (φ.comp P.subtype) ⟨c0, hc0P⟩ = z from hφc0, h.oz]
    exact h1 ▸ h2
  have hordc0 : orderOf c0 = 2 := by
    have h2 : orderOf ((⟨c0, hc0P⟩ : ↥P) : ↥M) = orderOf (⟨c0, hc0P⟩ : ↥P) :=
      Subgroup.orderOf_coe _
    have h3 : ((⟨c0, hc0P⟩ : ↥P) : ↥M) = c0 := rfl
    rw [h3] at h2
    exact h2.trans hordP
  let d : G := y * (c0 : G) * y⁻¹
  have hd_mem : d ∈ M.map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.mem_map]
    exact ⟨(c0 : G), c0.2, by simp [d]⟩
  have hcomm_le : M ≤ centralizer (M.map (MulAut.conj y).toMonoidHom) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcenter_le_Z : (center ↥M : Subgroup ↥M) ≤ Open.fusionZStar ↥M := by
    intro x hx
    show QuotientGroup.mk' (Open.fusionOddCore ↥M) x ∈ center (↥M ⧸ Open.fusionOddCore ↥M)
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Open.fusionOddCore ↥M) q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx w]
  have hcenter : c0 ∈ center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro m
    have hdm : d * (m : G) = (m : G) * d :=
      (Subgroup.mem_centralizer_iff.mp (hcomm_le m.2)) d hd_mem
    have hzm : z * (m : G) = (m : G) * z :=
      (Subgroup.mem_centralizer_iff.mp (hM.1 m.2)) z (Set.mem_singleton z)
    have hz_eq : z = (c0 : G) * d := by
      show z = (c0 : G) * (y * (c0 : G) * y⁻¹)
      rw [← hφc0, hφ c0]
    have hcm : (m : G) * (c0 : G) = (c0 : G) * (m : G) := by
      have h' := hzm
      rw [hz_eq] at h'
      have h'' : ((m : G) * (c0 : G)) * d = ((c0 : G) * (m : G)) * d := by
        calc ((m : G) * (c0 : G)) * d
            = (m : G) * ((c0 : G) * d) := by group
          _ = ((c0 : G) * d) * (m : G) := h'.symm
          _ = (c0 : G) * (d * (m : G)) := by group
          _ = (c0 : G) * ((m : G) * d) := by rw [hdm]
          _ = ((c0 : G) * (m : G)) * d := by group
      exact mul_right_cancel h''
    exact Subtype.ext hcm
  let f : ↥M →* ↥T := (MulEquiv.subgroupCongr hTφ.symm).toMonoidHom.comp φ.rangeRestrict
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hTφ.symm).surjective.comp (MonoidHom.rangeRestrict_surjective φ)
  have hfker : f.ker ≤ center ↥M := by
    intro x hx
    have hx1 : (MulEquiv.subgroupCongr hTφ.symm) (φ.rangeRestrict x) = 1 := by
      have hx' := hx
      rw [MonoidHom.mem_ker] at hx'
      exact hx'
    have hrr : φ.rangeRestrict x = 1 := by
      apply (MulEquiv.subgroupCongr hTφ.symm).injective
      rw [hx1, map_one]
    have hphi : φ x = 1 := by
      have hc := congrArg (fun y : ↥(φ.range) => (y : G)) hrr
      simpa [MonoidHom.coe_rangeRestrict] using hc
    apply hker
    rw [MonoidHom.mem_ker]
    exact hphi
  obtain ⟨eZ0⟩ := (central_quotient_two_quasisimple f hf hfker hMq2).2
  have hSLquot : HarrisLit.IsSLTwoOver q₀ (↥P ⧸ pPrimeCore 2 ↥P) :=
    isSLTwoOver_quotient h.hqodd h.hq5 hPSL
  have hPcent : P ≤ centralizer ({c0} : Set ↥M) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact (Subgroup.mem_center_iff.mp hcenter p).symm
  have hc0Z : c0 ∈ Open.fusionZStar ↥M := hcenter_le_Z hcenter
  have hTypM : TypU ↥M :=
    (diagonalTransfer_typU hI.griess hI.schur q₀) ↥T ↥M h.hT.2.2 hMq2 h.hTypU
      ⟨eZ0.symm⟩ P hPP hSLquot c0 hordc0 hc0P hPcent hc0Z
  have hSL' : HarrisLit.IsSLTwoOver q₀ ↥(P.map M.subtype) :=
    isSLTwoOver_of_mulEquiv
      (Subgroup.equivMapOfInjective P M.subtype M.subtype_injective) hPSL
  have hc_ord : orderOf ((c0 : ↥M) : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hordc0
  have hc_mem : ((c0 : ↥M) : G) ∈ P.map M.subtype :=
    Subgroup.mem_map.mpr ⟨c0, hc0P, rfl⟩
  have hc_center : ((c0 : ↥M) : G) ∈ (center ↥M).map M.subtype :=
    Subgroup.mem_map.mpr ⟨c0, hcenter, rfl⟩
  exact false_of_datum_typU hI hA7 G hnonab hKP hcat q₀ h.hqodd h.hq5 z M
    (P.map M.subtype) ((c0 : ↥M) : G)
    (isDatum_of_central h.oz hM (Subgroup.map_subtype_le P) h.hqodd h.hq5 hSL'
      hc_ord hc_mem hc_center)
    hTypM

end CFSG.OddStandard.SmallF3.HypA2
