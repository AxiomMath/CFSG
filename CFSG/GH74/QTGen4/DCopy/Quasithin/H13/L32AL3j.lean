module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2f
public import CFSG.Quasithin.H13.L32AL3c

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K (fsuV1 T V) t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]
  {F : Type} [Field F] [Finite F] [CharP F 2] (e : Hat V (A6.g1 T V) (fsuV1 T V) ≃* VM F)
  {t : ↥(A6.g1 T V)} {z z' : G} {hz'U : z' ∈ conjClosure V (A6.g1 T V)}

omit [Finite F] [CharP F 2] in

theorem mem_R1_of_img_F4 (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {x : ↥(A6.g1 T V)}
    (hx : MulAut.congr e (X.top.act x) ∈
      (X.img (pCoreOf 2 (l1 T L V ⊔ T))).map (MulAut.congr e).toMonoidHom) :
    (x : G) ∈ pCoreOf 2 (l1 T L V ⊔ T) := by
  obtain ⟨r, hrR, hr⟩ := (mem_map_img_iff e).mp hx
  have h1 : X.top.act (r⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact (MulAut.congr e).injective hr
  rw [X.act_eq_one_iff_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334] at h1
  have h2 := (pCoreOf 2 (l1 T L V ⊔ T)).mul_mem hrR (Setting147.O2H_le_R1 X.R.S h1)
  simpa using h2

omit [Finite F] [CharP F 2] [IsMulCommutative ↥(conjClosure V (A6.g1 T V))] in
include X in

theorem V_le_TY_F4 (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (hz'U : z' ∈ conjClosure V (A6.g1 T V)) :
    V ≤ pCoreOf 2 (l1 T L V ⊔ T) ⊓
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
  have S := X.R.S
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨hVel, -, hLTV, -, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have : IsMulCommutative ↥V := hVel.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hL1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hVR : V ≤ pCoreOf 2 (l1 T L V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (S14.VT_F4.trans le_sup_right)
      ((sup_le_sup_right hL1L T).trans hLTV) (F7.isPGroup_of_isElemAbelian hVel)
  refine le_inf hVR fun v hv => ?_

  have hUe := hF.F911_3
  have hVYU : fsuV1 T V ⊔ Subgroup.zpowers z' ≤ conjClosure V (A6.g1 T V) :=
    sup_le (hF.toHypF91.V₁_le_V.trans (le_conjClosure V _)) (Subgroup.zpowers_le.mpr hz'U)
  have hvU : v ∈ conjClosure V (A6.g1 T V) := le_conjClosure V _ hv
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have hcomm : ∀ w ∈ conjClosure V (A6.g1 T V), v * w * v⁻¹ = w := fun w hw => by
    rw [F7.isElemAbelian_comm hUe hvU hw, mul_inv_cancel_right]
  constructor
  · intro hw
    rw [hcomm w (hVYU hw)]
    exact hw
  · intro hw
    have hwU : w ∈ conjClosure V (A6.g1 T V) := by
      have h2 := hVYU hw
      rw [hcomm w ?_] at h2
      · exact h2
      · have h3 : v⁻¹ * (v * w * v⁻¹) * v = w := by group
        rw [← h3]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hvU) h2) hvU
    rw [hcomm w hwU] at hw
    exact hw

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
