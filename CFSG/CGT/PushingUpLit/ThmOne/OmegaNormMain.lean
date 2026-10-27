module

public import CFSG.CGT.PushingUpLit.ThmOne.OmegaNormAmb
public import CFSG.CGT.PushingUpLit.ThmOne.OmegaNormLine

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Quasithin
open CFSG.Quasithin.XMod CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.BHS6
open CFSG.CGT.PushingUpLit.ThmOne.OmegaNorm
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_blockU_of_omegaFourOutcomeSharp {V Y D : Subgroup G}
    (hV : IsElemAbelian 2 V) (hDV : D ≤ Subgroup.normalizer (V : Set G))
    (hO : OmegaFourOutcomeSharp V Y D) (hYD : Y ≤ D) (hY : IsShortGroup ↥Y)
    (hU : ⁅V, Y⁆ = blockU Y) {r : G} (hrD : r ∈ Subgroup.normalizer (D : Set G))
    (hrV : r ∈ Subgroup.normalizer (V : Set G)) {k : ℕ} (hrk : r ^ 2 ^ k = 1)
    (hrc : ∀ y ∈ Y, ⁅r, y⁆ ∈ V) {w : G} (hw : w ∈ ⁅D, V⁆) : ⁅r, w⁆ ∈ blockU Y := by
  obtain ⟨n, hW, -, hWV, -, hUmap, hS, hYS, hirr, hlt, hcard, -, -⟩ :=
    omega_setup hV hDV hO hYD hY hU
  have hrW : r ∈ Subgroup.normalizer ((⁅D, V⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator_omega hrD hrV
  have hP : ∀ p : ↥⁅D, V⁆, p ^ 2 = 1 := fun p => Subtype.ext (by simpa using hW.2 p p.2)
  have htk : conjAct ⁅D, V⁆ ⟨r, hrW⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨r, hrW⟩ : ↥(Subgroup.normalizer ((⁅D, V⁆ : Subgroup G) : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hrk)
    rw [this, map_one]
  have key := @mul_inv_mem_commV ↥⁅D, V⁆ (commGroupOfElemAbelian hW) _ hP (autOn D ⁅D, V⁆)
    (autOn Y ⁅D, V⁆) hS hYS hirr hlt hcard (conjAct ⁅D, V⁆ ⟨r, hrW⟩)
    (conjAct_normalizes_autOn hrW hrD) (conjAct_commute_of_commutator_mem hV hWV hrW hrc) k
    htk ⟨w, hw⟩
  have h1 : ((conjAct ⁅D, V⁆ ⟨r, hrW⟩ ⟨w, hw⟩ * (⟨w, hw⟩ : ↥⁅D, V⁆)⁻¹ : ↥⁅D, V⁆) : G) ∈
      blockU Y := hUmap ▸ ⟨_, key, rfl⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, BHS.conjAct_apply'] at h1
  rw [commutatorElement_def]
  exact h1

theorem commutator_le_blockU_of_omegaFourOutcomeSharp {V Y D R : Subgroup G}
    (hV : IsElemAbelian 2 V) (hDV : D ≤ Subgroup.normalizer (V : Set G))
    (hO : OmegaFourOutcomeSharp V Y D) (hYD : Y ≤ D) (hY : IsShortGroup ↥Y)
    (hU : ⁅V, Y⁆ = blockU Y) (hR : IsPGroup 2 R) (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (hRY : ∀ r ∈ R, ∀ y ∈ Y, ⁅r, y⁆ ∈ blockU Y) :
    ⁅R, ⁅D, V⁆⁆ ≤ blockU Y := by
  refine Subgroup.commutator_le.mpr fun r hr w hw => ?_
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  exact commutator_mem_blockU_of_omegaFourOutcomeSharp hV hDV hO hYD hY hU (hRD hr) (hRV hr)
    (k := k) (by simpa using congrArg Subtype.val hk)
    (fun y hy => blockU_le_of_omega hYD hDV hU (hRY r hr y hy)) hw

theorem commutator_le_blockU_of_omegaFourOutcomeSharp_of_le_centralizerModCore
    {V Y D R : Subgroup G} (hV : IsElemAbelian 2 V) (hDV : D ≤ Subgroup.normalizer (V : Set G))
    (hO : OmegaFourOutcomeSharp V Y D) (hYD : Y ≤ D) (hY : IsShortGroup ↥Y)
    (hU : ⁅V, Y⁆ = blockU Y) (hR : IsPGroup 2 R) (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hRV : R ≤ Subgroup.normalizer (V : Set G)) (hRC : R ≤ centralizerModCore Y) :
    ⁅R, ⁅D, V⁆⁆ ≤ blockU Y :=
  commutator_le_blockU_of_omegaFourOutcomeSharp hV hDV hO hYD hY hU hR hRD hRV fun r hr y hy => by
    rw [commutatorElement_def]
    exact commutator_mem_blockU_of_mem_centralizerModCore hY.residual_eq (hRC hr) hy

end CFSG.CGT.PushingUpLit.ThmOne
