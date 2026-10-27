module

public import CFSG.Quasithin.H13.L32A53c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A53b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace T53

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.T53.Ctx

variable {T L V V₂ Y : Subgroup G} (C : Ctx_F4 G T L V V₂ Y)
include C

theorem charTwo_hY_F4 (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) : CharTwo (hY T L V₂ Y) := by
  have hT := C.hyp.fsu.sylow
  refine charTwo_of_inH C.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2) ⟨?_, hQ⟩
  rw [IsPGroup.toSylow_coe]
  exact le_sup_right

theorem vH_le_center_F4 (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) :
    vH T L V V₂ Y ≤ centerOf (pCoreOf 2 (hY T L V₂ Y)) ∧ IsElemAbelian 2 (vH T L V V₂ Y) := by
  have hS := C.isSylowTwoOf_T_F4 (K := hY T L V₂ Y) le_sup_right
  exact conjClosure_le_centerOf_pCoreOf_of_sylowIn hS.1 hS.2.1 hS.2.2 (C.charTwo_hY_F4 hQ) V1_le_Z

theorem isTwoReducedIn_vH_F4 (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) :
    IsTwoReducedIn (hY T L V₂ Y) (vH T L V V₂ Y) := by
  have hS := C.isSylowTwoOf_T_F4 (K := hY T L V₂ Y) le_sup_right
  exact isTwoReducedIn_conjClosure_of_sylowIn hS.1 hS.2.1 hS.2.2 (C.charTwo_hY_F4 hQ) V1_le_Z

theorem xL_not_le_centralizer_F4 : ¬ xL L V₂ ≤ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  intro h
  have : IsMulCommutative ↥V := C.isMulCommutative_V_F4
  have S := C.set14_F4
  have hle : conjClosure (fsuV1 T V) (xL L V₂) ≤ fsuV1 T V := conjClosure_le fun x hx z hz => by
    have hz' : z ∈ vH T L V V₂ Y := le_conjClosure _ _ hz
    rw [← Subgroup.mem_centralizer_iff.mp (h hx) z hz', mul_inv_cancel_right]
    exact hz
  rw [C.conjClosure_V1_X_F4] at hle
  have h1 := Subgroup.card_le_of_le hle
  rw [C.hV2.2.2.2, S.card_V1_F4] at h1
  omega

theorem inf_xT_le_F4 (h4 : Lemma14_7_4_two_three_F4) :
    (xL L V₂ ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) ≤ pCoreOf 2 (xL L V₂ ⊔ T) := by
  have hXH : xL L V₂ ⊔ T ≤ hY T L V₂ Y :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  refine le_pCoreOf_of_normal_of_S3 (C.quot_xT_F4 h4).1 inf_le_left ?_ ?_
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_centralizer_vH hXH hx⟩
  · rw [C.oTwoUpper_xT_F4]
    intro h
    exact C.xL_not_le_centralizer_F4 (h.trans inf_le_right)

theorem inf_yT_le_F4 :
    (Y ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) ≤ pCoreOf 2 (Y ⊔ T) := by
  have hYH : Y ⊔ T ≤ hY T L V₂ Y := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  refine le_pCoreOf_of_normal_of_S3 C.hS3 inf_le_left ?_ ?_
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_centralizer_vH hYH hx⟩
  · rw [C.oTwoUpper_yT_F4]
    intro h
    have hYC : Y ≤ cH T L V V₂ Y :=
      le_inf (le_sup_right.trans le_sup_left) (h.trans inf_le_right)
    apply C.not_le_normalizer_F4
    intro y hy
    have hyC := hYC hy
    rw [Subgroup.mem_normalizer_iff]

    have hCn : hY T L V₂ Y ≤ Subgroup.normalizer (cH T L V V₂ Y : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        le_normalizer_centralizer_vH le_rfl hg⟩
    have hXC := xL_le_normalizer_cH (T := T) (L := L) (V := V) (V₂ := V₂) (Y := Y)
    have hset : ((xL L V₂ ⊔ cH T L V V₂ Y : Subgroup G) : Set G) =
        (xL L V₂ : Set G) * (cH T L V V₂ Y : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXC
    have hyH : y ∈ hY T L V₂ Y := hyC.1
    intro w
    constructor
    · intro hw
      rw [← SetLike.mem_coe, hset] at hw ⊢
      obtain ⟨x, hx, c, hc, rfl⟩ := hw
      refine ⟨x, hx, (x⁻¹ * y * x) * c * y⁻¹, ?_, by group⟩
      have h1 : x⁻¹ * y * x ∈ cH T L V V₂ Y := by
        have := (Subgroup.mem_normalizer_iff.mp (hXC (inv_mem hx)) y).mp hyC
        simpa [mul_assoc] using this
      exact mul_mem (mul_mem h1 hc) (inv_mem hyC)
    · intro hw
      rw [← SetLike.mem_coe, hset] at hw ⊢
      obtain ⟨x, hx, c, hc, hxc⟩ := hw
      have hxc' : x * c = y * w * y⁻¹ := hxc
      refine ⟨x, hx, x⁻¹ * y⁻¹ * x * c * y, ?_, ?_⟩
      · have h1 : x⁻¹ * y⁻¹ * x ∈ cH T L V V₂ Y := by
          have := (Subgroup.mem_normalizer_iff.mp (hXC (inv_mem hx)) y⁻¹).mp (inv_mem hyC)
          simpa [mul_assoc] using this
        exact mul_mem (mul_mem h1 hc) hyC
      · show x * (x⁻¹ * y⁻¹ * x * c * y) = w
        calc x * (x⁻¹ * y⁻¹ * x * c * y) = y⁻¹ * (x * c) * y := by group
          _ = w := by rw [hxc']; group

theorem pCoreOf_hY_eq_F4 (h4 : Lemma14_7_4_two_three_F4) (hQ : pCoreOf 2 (hY T L V₂ Y) ≠ ⊥) :
    pCoreOf 2 (hY T L V₂ Y) = T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ hY T L V₂ Y := le_sup_right
  apply le_antisymm
  · refine le_inf (pCoreOf_le_of_le C.hyp hTH) fun q hq => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (((C.vH_le_center_F4 hQ).1 hv).2 q hq).symm
  · set R := T ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G)
    have hXT : (xL L V₂ ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) = R := by
      refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ le_sup_right)
      exact (C.inf_xT_le_F4 h4).trans (pCoreOf_le_of_le C.hyp le_sup_right)
    have hYT : (Y ⊔ T) ⊓ Subgroup.centralizer (vH T L V V₂ Y : Set G) = R := by
      refine le_antisymm (le_inf ?_ inf_le_right) (inf_le_inf_right _ le_sup_right)
      exact C.inf_yT_le_F4.trans (pCoreOf_le_of_le C.hyp le_sup_right)
    have hXN : xL L V₂ ⊔ T ≤ Subgroup.normalizer (R : Set G) := by
      rw [← hXT]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
        le_normalizer_centralizer_vH (sup_le (le_sup_left.trans le_sup_left) le_sup_right) hx⟩
    have hYN : Y ⊔ T ≤ Subgroup.normalizer (R : Set G) := by
      rw [← hYT]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
        le_normalizer_centralizer_vH (sup_le (le_sup_right.trans le_sup_left) le_sup_right) hx⟩
    have hHN : hY T L V₂ Y ≤ Subgroup.normalizer (R : Set G) := by
      exact sup_le (sup_le (le_sup_left.trans hXN) (le_sup_left.trans hYN))
        (le_sup_right.trans hXN)
    exact le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hTH) hHN
      (C.hyp.fsu.sylow.1.to_le inf_le_left)

end Ctx_F4

@[expose] def Contra14_5_3_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ Y : Subgroup G), Ctx_F4 G T L V V₂ Y → False

theorem thm14_5_3_of_F4 (h : Contra14_5_3_F4) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : Thm14_5_3_F4 := by
  intro G _ _ T L V hyp Y V₂ hV2 hYo hYG1 hTY hS3
  by_contra hc
  exact h G T L V V₂ Y ⟨hyp, h1222, h1332, h1334, hV2, hYo, hYG1, hTY, hS3, hc⟩

end T53

end CFSG.Quasithin.H13.L32A
