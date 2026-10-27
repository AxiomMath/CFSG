module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.NativeChecks
public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.Blueprint.Catalog
public import CFSG.GH74.KGroups.PermAction
public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LieType.Ree.SuzukiLocalData
public import CFSG.LieType.Ree.SuzukiOvoidWeyl
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.LieType.Simplicity.Suzuki
public meta import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.NativeChecks
public meta import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.GH74.KGroups.Sz8Inputs
public meta import CFSG.GH74.KGroups.Sz8Inputs
public import Certificates.Certificate5128
public import Certificates.Certificate113

public section

namespace CFSG.GH74.KGroups.Sz8

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Quasithin CFSG.LieType.Ree CFSG.Blueprint Matrix
open scoped LinearAlgebra.Projectivization

theorem QP_valid :
    QP.check = true ∧ QP.orderCertificate = 29120 :=
  Certificates.certificate5128.1

theorem QA_valid :
    QA.check = true ∧ QA.orderCertificate = 87360 :=
  Certificates.certificate5128.2.1

theorem QP_ok : ValidSchreier QP := QP_valid.1

theorem QA_ok : ValidSchreier QA := QA_valid.1

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem orders_ok :
    orderIs pa 2 = true ∧ orderIs pb 4 = true ∧ pairInvB ws pa pb = true :=
  Certificates.certificate5128.2.2.1

theorem count_ok_check : NativeChecks.pairCountE QP 2 4 ws = 87360 :=
  Certificates.certificate5128.2.2.2.2.2.2

theorem count_ok : pairCountB QP 2 4 ws = QA.orderCertificate := by
  rw [QA_valid.2, NativeChecks.pairCountB_eq_E]; exact count_ok_check

theorem norm_ok :
    normCheck QP QA.original.toList pa pb = true :=
  Certificates.certificate5128.2.2.2.1

theorem cent_ok : centTrivCheck (elemsT QA) pa pb = true :=
  Certificates.certificate5128.2.2.2.2.1

theorem solv_ok : solvCheck (elemsT QA) (elemsT QP) = true :=
  Certificates.certificate5128.2.2.2.2.2.1

theorem ws_pos : ∀ wk ∈ ws, 0 < wk.2 := by
  intro wk hwk
  simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hwk
  rcases hwk with rfl | rfl <;> norm_num

@[expose] def vecP (i : Fin 65) : Fin 4 → GF8 :=
  if i.val = 0 then ![0, 0, 0, 1]
  else ![1, GF8.ofNat' ((i.val - 1) / 8), GF8.ofNat' ((i.val - 1) % 8),
    suzukiN 1 (GF8.ofNat' ((i.val - 1) / 8)) (GF8.ofNat' ((i.val - 1) % 8))]

theorem vecP_ne : ∀ i, vecP i ≠ 0 := by decide

theorem vecP_inj : ∀ i j : Fin 65, ∀ c : GF8, c • vecP j = vecP i → i = j := by
  decide +kernel

theorem lines_covered : ∀ u v : GF8, ∃ i : Fin 65, vecP i = ![1, u, v, suzukiN 1 u v] := by
  decide +kernel

theorem vecP_zero (i : Fin 65) (h : i.val = 0) : vecP i = ![0, 0, 0, 1] := by simp [vecP, h]

theorem vecP_pos (i : Fin 65) (h : i.val ≠ 0) :
    vecP i = ![1, GF8.ofNat' ((i.val - 1) / 8), GF8.ofNat' ((i.val - 1) % 8),
      suzukiN 1 (GF8.ofNat' ((i.val - 1) / 8)) (GF8.ofNat' ((i.val - 1) % 8))] := by
  simp [vecP, h]

theorem card_GF8 : Nat.card GF8 = 2 ^ (2 * 1 + 1) := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] noncomputable def ptE (i : Fin 65) : ℙ GF8 (Fin 4 → GF8) :=
  Projectivization.mk GF8 (vecP i) (vecP_ne i)

theorem ptE_mem (i : Fin 65) : ptE i ∈ suzukiOmega 1 GF8 := by
  by_cases h : i.val = 0
  · right
    show ptE i = suzukiInfty GF8
    rw [ptE, suzukiInfty, Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, vecP_zero i h]⟩
  · left
    refine ⟨(GF8.ofNat' ((i.val - 1) / 8), GF8.ofNat' ((i.val - 1) % 8)), ?_⟩
    show suzukiLine 1 GF8 _ _ = ptE i
    rw [ptE, suzukiLine, Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, vecP_pos i h]⟩

theorem ptE_inj : Function.Injective ptE := by
  intro i j hij
  rw [ptE, ptE, Projectivization.mk_eq_mk_iff'] at hij
  obtain ⟨c, hc⟩ := hij
  exact vecP_inj i j c hc

theorem ptE_surj : ∀ p ∈ suzukiOmega 1 GF8, ∃ i, ptE i = p := by
  intro p hp
  rcases mem_suzukiOmega_iff.1 hp with rfl | ⟨u, v, rfl⟩
  · refine ⟨⟨0, by norm_num⟩, ?_⟩
    rw [ptE, suzukiInfty, Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, vecP_zero _ rfl]⟩
  · obtain ⟨i, hi⟩ := lines_covered u v
    refine ⟨i, ?_⟩
    rw [ptE, suzukiLine, Projectivization.mk_eq_mk_iff']
    exact ⟨1, by rw [one_smul, hi]⟩

@[expose] noncomputable def Eov :
    Fin 65 ≃ ↥(suzukiOmegaSub (a := 1) (K := GF8) card_GF8) :=
  Equiv.ofBijective (fun i => ⟨ptE i, ptE_mem i⟩)
    ⟨fun i j h => ptE_inj (congrArg Subtype.val h), fun ⟨p, hp⟩ => by
      obtain ⟨i, hi⟩ := ptE_surj p hp
      exact ⟨i, Subtype.ext hi⟩⟩

@[expose] noncomputable def ovoidHom :
    suzukiGroup 1 GF8 →* Equiv.Perm (Fin 65) :=
  permHomOf _ Eov

theorem ovoidHom_injective : Function.Injective ovoidHom := by
  have := (suzuki_ovoid_faithful (a := 1) (K := GF8) le_rfl card_GF8).2
  exact permHomOf_injective Eov

theorem ovoidHom_eq (g : suzukiGroup 1 GF8) (p : Equiv.Perm (Fin 65))
    (h : ∀ i : Fin 65, ∃ c : GF8,
      c • (((g : GL (Fin 4) GF8) : Matrix (Fin 4) (Fin 4) GF8) *ᵥ vecP i) = vecP (p i)) :
    ovoidHom g = p := by
  refine permHomOf_eq Eov g p fun i => ?_
  apply Subtype.ext
  show ptE (p i) = g • ptE i
  rw [ptE, ptE, Subgroup.smul_def, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact h i

@[expose] def pW : Equiv.Perm (Fin 65) :=
  List.formPerm [0, 1] * List.formPerm [2, 9] * List.formPerm [3, 49] * List.formPerm [4, 57] * List.formPerm [5, 17] * List.formPerm [6, 25] * List.formPerm [7, 33] * List.formPerm [8, 41] * List.formPerm [11, 35] * List.formPerm [12, 51] * List.formPerm [13, 53] * List.formPerm [14, 21] * List.formPerm [15, 23] * List.formPerm [16, 39] * List.formPerm [18, 31] * List.formPerm [19, 28] * List.formPerm [20, 22] * List.formPerm [24, 45] * List.formPerm [26, 59] * List.formPerm [27, 54] * List.formPerm [29, 42] * List.formPerm [30, 44] * List.formPerm [32, 60] * List.formPerm [34, 43] * List.formPerm [36, 63] * List.formPerm [37, 46] * List.formPerm [38, 40] * List.formPerm [47, 58] * List.formPerm [48, 62] * List.formPerm [50, 61] * List.formPerm [52, 56] * List.formPerm [55, 64]

@[expose] def pS10 : Equiv.Perm (Fin 65) :=
  List.formPerm [1, 9, 2, 10] * List.formPerm [3, 11, 4, 12] * List.formPerm [5, 13, 6, 14] * List.formPerm [7, 15, 8, 16] * List.formPerm [17, 27, 18, 28] * List.formPerm [19, 25, 20, 26] * List.formPerm [21, 31, 22, 32] * List.formPerm [23, 29, 24, 30] * List.formPerm [33, 45, 34, 46] * List.formPerm [35, 47, 36, 48] * List.formPerm [37, 41, 38, 42] * List.formPerm [39, 43, 40, 44] * List.formPerm [49, 63, 50, 64] * List.formPerm [51, 61, 52, 62] * List.formPerm [53, 59, 54, 60] * List.formPerm [55, 57, 56, 58]

@[expose] def pS01 : Equiv.Perm (Fin 65) :=
  List.formPerm [1, 2] * List.formPerm [3, 4] * List.formPerm [5, 6] * List.formPerm [7, 8] * List.formPerm [9, 10] * List.formPerm [11, 12] * List.formPerm [13, 14] * List.formPerm [15, 16] * List.formPerm [17, 18] * List.formPerm [19, 20] * List.formPerm [21, 22] * List.formPerm [23, 24] * List.formPerm [25, 26] * List.formPerm [27, 28] * List.formPerm [29, 30] * List.formPerm [31, 32] * List.formPerm [33, 34] * List.formPerm [35, 36] * List.formPerm [37, 38] * List.formPerm [39, 40] * List.formPerm [41, 42] * List.formPerm [43, 44] * List.formPerm [45, 46] * List.formPerm [47, 48] * List.formPerm [49, 50] * List.formPerm [51, 52] * List.formPerm [53, 54] * List.formPerm [55, 56] * List.formPerm [57, 58] * List.formPerm [59, 60] * List.formPerm [61, 62] * List.formPerm [63, 64]

@[expose] def pS20 : Equiv.Perm (Fin 65) :=
  List.formPerm [1, 17, 8, 24] * List.formPerm [2, 18, 7, 23] * List.formPerm [3, 19, 6, 22] * List.formPerm [4, 20, 5, 21] * List.formPerm [9, 31, 16, 26] * List.formPerm [10, 32, 15, 25] * List.formPerm [11, 29, 14, 28] * List.formPerm [12, 30, 13, 27] * List.formPerm [33, 54, 40, 51] * List.formPerm [34, 53, 39, 52] * List.formPerm [35, 56, 38, 49] * List.formPerm [36, 55, 37, 50] * List.formPerm [41, 60, 48, 61] * List.formPerm [42, 59, 47, 62] * List.formPerm [43, 58, 46, 63] * List.formPerm [44, 57, 45, 64]

@[expose] def pS02 : Equiv.Perm (Fin 65) :=
  List.formPerm [1, 3] * List.formPerm [2, 4] * List.formPerm [5, 7] * List.formPerm [6, 8] * List.formPerm [9, 11] * List.formPerm [10, 12] * List.formPerm [13, 15] * List.formPerm [14, 16] * List.formPerm [17, 19] * List.formPerm [18, 20] * List.formPerm [21, 23] * List.formPerm [22, 24] * List.formPerm [25, 27] * List.formPerm [26, 28] * List.formPerm [29, 31] * List.formPerm [30, 32] * List.formPerm [33, 35] * List.formPerm [34, 36] * List.formPerm [37, 39] * List.formPerm [38, 40] * List.formPerm [41, 43] * List.formPerm [42, 44] * List.formPerm [45, 47] * List.formPerm [46, 48] * List.formPerm [49, 51] * List.formPerm [50, 52] * List.formPerm [53, 55] * List.formPerm [54, 56] * List.formPerm [57, 59] * List.formPerm [58, 60] * List.formPerm [61, 63] * List.formPerm [62, 64]

@[expose] def pS40 : Equiv.Perm (Fin 65) :=
  List.formPerm [1, 33, 4, 36] * List.formPerm [2, 34, 3, 35] * List.formPerm [5, 37, 8, 40] * List.formPerm [6, 38, 7, 39] * List.formPerm [9, 43, 12, 42] * List.formPerm [10, 44, 11, 41] * List.formPerm [13, 47, 16, 46] * List.formPerm [14, 48, 15, 45] * List.formPerm [17, 53, 20, 56] * List.formPerm [18, 54, 19, 55] * List.formPerm [21, 49, 24, 52] * List.formPerm [22, 50, 23, 51] * List.formPerm [25, 63, 28, 62] * List.formPerm [26, 64, 27, 61] * List.formPerm [29, 59, 32, 58] * List.formPerm [30, 60, 31, 57]

@[expose] def pD2 : Equiv.Perm (Fin 65) :=
  List.formPerm [2, 5, 7, 6, 3, 4, 8] * List.formPerm [9, 41, 57, 49, 25, 33, 17] * List.formPerm [10, 45, 63, 54, 27, 36, 24] * List.formPerm [11, 44, 64, 50, 29, 39, 22] * List.formPerm [12, 48, 58, 53, 31, 38, 19] * List.formPerm [13, 47, 62, 51, 28, 40, 18] * List.formPerm [14, 43, 60, 56, 26, 37, 23] * List.formPerm [15, 46, 59, 52, 32, 34, 21] * List.formPerm [16, 42, 61, 55, 30, 35, 20]

theorem actW : ∀ i : Fin 65, ∃ c : GF8, c • (suzukiW GF8 *ᵥ vecP i) = vecP (pW i) := by
  decide +kernel

theorem actS10 : ∀ i : Fin 65, ∃ c : GF8,
    c • (suzukiS 1 (GF8.ofNat' 1) (GF8.ofNat' 0) *ᵥ vecP i) = vecP (pS10 i) := by
  decide +kernel

theorem actS01 : ∀ i : Fin 65, ∃ c : GF8,
    c • (suzukiS 1 (GF8.ofNat' 0) (GF8.ofNat' 1) *ᵥ vecP i) = vecP (pS01 i) := by
  decide +kernel

theorem actS20 : ∀ i : Fin 65, ∃ c : GF8,
    c • (suzukiS 1 (GF8.ofNat' 2) (GF8.ofNat' 0) *ᵥ vecP i) = vecP (pS20 i) := by
  decide +kernel

theorem actS02 : ∀ i : Fin 65, ∃ c : GF8,
    c • (suzukiS 1 (GF8.ofNat' 0) (GF8.ofNat' 2) *ᵥ vecP i) = vecP (pS02 i) := by
  decide +kernel

theorem actS40 : ∀ i : Fin 65, ∃ c : GF8,
    c • (suzukiS 1 (GF8.ofNat' 4) (GF8.ofNat' 0) *ᵥ vecP i) = vecP (pS40 i) := by
  decide +kernel

theorem actD2 : ∀ i : Fin 65, ∃ c : GF8,
    c • (suzukiD 1 (Units.mk0 (GF8.ofNat' 2) (by decide)) *ᵥ vecP i) = vecP (pD2 i) := by
  decide +kernel

@[expose] noncomputable def gW : suzukiGroup 1 GF8 := suzukiWElt 1 GF8

@[expose] noncomputable def gS10 : suzukiGroup 1 GF8 :=
  suzukiSElt 1 GF8 (GF8.ofNat' 1) (GF8.ofNat' 0)

@[expose] noncomputable def gS01 : suzukiGroup 1 GF8 :=
  suzukiSElt 1 GF8 (GF8.ofNat' 0) (GF8.ofNat' 1)

@[expose] noncomputable def gS20 : suzukiGroup 1 GF8 :=
  suzukiSElt 1 GF8 (GF8.ofNat' 2) (GF8.ofNat' 0)

@[expose] noncomputable def gS02 : suzukiGroup 1 GF8 :=
  suzukiSElt 1 GF8 (GF8.ofNat' 0) (GF8.ofNat' 2)

@[expose] noncomputable def gS40 : suzukiGroup 1 GF8 :=
  suzukiSElt 1 GF8 (GF8.ofNat' 4) (GF8.ofNat' 0)

@[expose] noncomputable def gD2 : suzukiGroup 1 GF8 :=
  suzukiDElt 1 GF8 (Units.mk0 (GF8.ofNat' 2) (by decide))

theorem hom_gW : ovoidHom gW = pW :=
  ovoidHom_eq _ _ (by rw [gW, coe_suzukiWElt]; exact actW)

theorem hom_gS10 : ovoidHom gS10 = pS10 :=
  ovoidHom_eq _ _ (by rw [gS10, coe_suzukiSElt]; exact actS10)

theorem hom_gS01 : ovoidHom gS01 = pS01 :=
  ovoidHom_eq _ _ (by rw [gS01, coe_suzukiSElt]; exact actS01)

theorem hom_gS20 : ovoidHom gS20 = pS20 :=
  ovoidHom_eq _ _ (by rw [gS20, coe_suzukiSElt]; exact actS20)

theorem hom_gS02 : ovoidHom gS02 = pS02 :=
  ovoidHom_eq _ _ (by rw [gS02, coe_suzukiSElt]; exact actS02)

theorem hom_gS40 : ovoidHom gS40 = pS40 :=
  ovoidHom_eq _ _ (by rw [gS40, coe_suzukiSElt]; exact actS40)

theorem hom_gD2 : ovoidHom gD2 = pD2 :=
  ovoidHom_eq _ _ (by rw [gD2, coe_suzukiDElt]; exact actD2)

@[expose] noncomputable def ga :
    suzukiGroup 1 GF8 := gS20 * gS02 * gW * gS40 * gW * gS01 * gW

@[expose] noncomputable def gb :
    suzukiGroup 1 GF8 := gS01 * gS40 * gW * gD2 * gS10

theorem pa_word : pS20 * pS02 * pW * pS40 * pW * pS01 * pW = pa := by decide +kernel

theorem pb_word : pS01 * pS40 * pW * pD2 * pS10 = pb := by decide +kernel

theorem hom_ga : ovoidHom ga = pa := by
  simp only [ga, map_mul, hom_gW, hom_gS01, hom_gS20, hom_gS02, hom_gS40]
  exact pa_word

theorem hom_gb : ovoidHom gb = pb := by
  simp only [gb, map_mul, hom_gW, hom_gS10, hom_gS01, hom_gS40, hom_gD2]
  exact pb_word

theorem equiv_suz_P :
    Nonempty (suzukiGroup 1 GF8 ≃* QP.originalSubgroup) := by
  refine equiv_closure_of_hom ovoidHom ovoidHom_injective ga gb pa pb hom_ga hom_gb
    QP.originalSubgroup QP_closure ?_
  rw [card_group QP QP_ok, QP_valid.2, suzuki_order card_GF8]
  norm_num

theorem suz_equiv_matrix (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 1 + 1)) :
    Nonempty (suzukiGroup 1 K ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) :=
  ⟨(MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 1 K)).trans
    ((CFSG.ShultStronglyClosedTI.glaSzEquivNative 1 le_rfl hK).trans
      (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv 1))⟩

theorem equiv_of_lieModel
    {K : Type} [Group K] (h : LieModel K .twistedB2 0 2 3) :
    Nonempty (K ≃* QP.originalSubgroup) := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · obtain ⟨-, a, ha, F, _, _, hf, hF, ⟨e⟩⟩ := hS
    have ha1 : a = 1 := by omega
    subst ha1
    obtain ⟨e1⟩ := suz_equiv_matrix F hF
    obtain ⟨e2⟩ := suz_equiv_matrix GF8 card_GF8
    obtain ⟨e3⟩ := equiv_suz_P
    exact ⟨e.trans (e1.trans (e2.symm.trans e3))⟩

theorem autModel
    {K : Type} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin 65)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  have ho := orders_ok
  exact autModel_exists QP QA QP_ok QA_ok pa pb QP_closure 2 4 (by norm_num) (by norm_num) ws
    ws_pos ((orderIs_iff _ (by norm_num)).1 ho.1) ((orderIs_iff _ (by norm_num)).1 ho.2.1)
    ((pairInvB_iff ws ws_pos _ _).1 ho.2.2) count_ok norm_ok cent_ok e

section Consequences

variable {K : Type} [Group K] (e : K ≃* QP.originalSubgroup)

include e

theorem finite_K : Finite K := Finite.of_equiv QP.originalSubgroup e.symm.toEquiv

theorem finite_mulAut : Finite (MulAut K) := by
  obtain ⟨M, -, -⟩ := autModel e
  exact Finite.of_equiv M.A M.Φ.symm.toEquiv

theorem card_mulAut : Nat.card (MulAut K) = 87360 := by
  obtain ⟨M, hP, hA⟩ := autModel e
  rw [M.card_mulAut, hA, card_group QA QA_ok, QA_valid.2]

theorem autRank3_le_two
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 9 := by
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) 3 R hR 2 (by rw [card_mulAut e]; norm_num)
  simpa using this

theorem autRank3_le_one
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 3 := by
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) 3 R hR 1 (by rw [card_mulAut e]; norm_num)
  simpa using this

theorem autRank_ge5
    (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup (MulAut K))
    (hB : ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_mulAut e
  have := elemAb_card_le (G := MulAut K) p B hB 1 (by
    rw [card_mulAut e]
    intro hdvd
    have hle : p ^ 2 ≤ 87360 := Nat.le_of_dvd (by norm_num) hdvd
    have : p ≤ 295 := by nlinarith
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num))
  simpa using this

theorem fixed_solvable
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L : Subgroup K)
    (hL : ∀ x ∈ L, α x = x) : Group.IsSolvable L := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have hs := solvCheck_sound QA QP QA_ok QP_ok solv_ok
  refine M.fixed_solvable (fun τ hτ h2 h1 => ?_) α hα2 hα1 L hL
  have hτ' : τ ∈ QA.originalSubgroup := hA ▸ hτ
  have := hs τ hτ' h2 h1
  rwa [← hP] at this

end Consequences

end CFSG.GH74.KGroups.Sz8
