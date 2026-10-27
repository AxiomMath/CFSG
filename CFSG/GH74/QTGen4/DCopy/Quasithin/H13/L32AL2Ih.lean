module

public import CFSG.Quasithin.H13.L32AL2Ih
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2Ic

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem pCoreOf_l1_le_T_F4 (h1332 : Stmt13_3_2_F4) : pCoreOf 2 (l1 T L V) ≤ T := by
  have hTN := Setting147.T_le_N_l1_F4 D.S h1332
  have h1 : pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 (l1 T L V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 _) (hTN.trans (normalizer_le_normalizer_pCoreOf 2 _)))
      (pCoreOf_isPGroup 2 _)
  exact h1.trans (pCoreOf_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo D.S.hyp.fsu.sylow le_sup_right))

theorem isQuotientOfSQTKTC_autOn_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) :
    IsQuotientOfSQTKTC ↥(autOn (iI T L V z z') (vI T L V z z')) := by
  have hS := D.sqtk_iI_F4 h1222 h1332 h1334
  exact ⟨↥(iI T L V z z'), inferInstance, inferInstance, fun p hp hp2 => hS.1 p hp hp2, hS.2,
    InternalSec.autOnHom (iI_le_normalizer_vI T L V z z'),
    InternalSec.autOnHom_surjective (iI_le_normalizer_vI T L V z z')⟩

theorem false_of_le_normalizer_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4)
    (hN : autOn (iI T L V z z') (vI T L V z z') ≤
      Subgroup.normalizer (autOn (l1 T L V) (vI T L V z z') : Set (MulAut ↥(vI T L V z z')))) :
    False := by
  obtain ⟨-, -, hred⟩ := D.vI_spec_F4 h1222 h1332 h1334
  have hIW := iI_le_normalizer_vI T L V z z'
  set W := vI T L V z z' with hW
  set Λ := autOn (l1 T L V) W with hΛ
  set Qp := autOn (pCoreOf 2 (l1 T L V)) W with hQp
  have hΛI : Λ ≤ autOn (iI T L V z z') W := InternalSec.autOn_le_autOn_of_le l1_le_iI
  have hQΛ : Qp ≤ Λ := InternalSec.autOn_le_autOn_of_le (pCoreOf_le 2 _)
  have hΛQ : Λ ≤ Subgroup.normalizer (Qp : Set (MulAut ↥W)) :=
    le_normalizer_of_conj (InternalSec.autOn_normal_of (le_normalizer_pCoreOf 2 _))
  have hQ2 : IsPGroup 2 Qp :=
    D.isSylowTwoOf_autOn_T.2.1.to_le (InternalSec.autOn_le_autOn_of_le (D.pCoreOf_l1_le_T_F4 h1332))
  have h1 : Qp ≤ pCoreOf 2 Λ := le_pCoreOf_of_le_normalizer 2 hQΛ hΛQ hQ2
  have h2 : pCoreOf 2 Λ ≤ pCoreOf 2 (autOn (iI T L V z z') W) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Λ).trans hΛI)
      (hN.trans (normalizer_le_normalizer_pCoreOf 2 Λ)) (pCoreOf_isPGroup 2 Λ)
  rw [Setup.pCoreOf_autOn_eq_bot hred] at h2
  have hQC : pCoreOf 2 (l1 T L V) ≤ Subgroup.centralizer (W : Set G) := by
    intro q hq
    have hqN : q ∈ Subgroup.normalizer (W : Set G) := hIW (l1_le_iI (pCoreOf_le 2 _ hq))
    have h3 := (h1.trans h2) (A1b.conjAct_mem_autOn hqN hq)
    rw [Subgroup.mem_bot] at h3
    exact A1b.conjAct_eq_one_iff.mp h3
  exact D.hL1 ((hQC.trans (D.centralizer_vI_le.trans inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _))

theorem l1_le_sup_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {x' : G}
    (hx'L : x' ∈ l1 T L V) (hx'3 : x' ^ 3 = 1) (hx'1 : x' ≠ 1) :
    l1 T L V ≤ pCoreOf 2 (l1 T L V) ⊔ Subgroup.zpowers x' := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14_F4 h1222 h1332 h1334
  have hLp3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3 := by
    rw [l1_eq_L₁Of]
    exact S14.Lp3_F4
  set P := pCoreOf 2 (l1 T L V) with hP
  have hle : P ⊔ Subgroup.zpowers x' ≤ l1 T L V :=
    sup_le (pCoreOf_le 2 _) (Subgroup.zpowers_le.mpr hx'L)
  have hmul := Subgroup.relIndex_mul_relIndex P (P ⊔ Subgroup.zpowers x') (l1 T L V)
    le_sup_left hle
  rw [hLp3] at hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ hmul) with h | h
  · exfalso
    have hx : x' ∈ P := Subgroup.relIndex_eq_one.mp h
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x'))
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (l1 T L V)) ⟨x', hx⟩
    have hk' : x' ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact hx'1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hx'3) (orderOf_dvd_of_pow_eq_one hk')))
  · rw [h] at hmul
    have h1 : (P ⊔ Subgroup.zpowers x').relIndex (l1 T L V) = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1

theorem l1_le_closure_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    l1 T L V ≤ Subgroup.closure {x | x ∈ l1 T L V ∧ orderOf x = 3} := by
  obtain ⟨V₂, _, S14⟩ := D.exists_set14_F4 h1222 h1332 h1334
  rw [l1_eq_L₁Of]
  refine C.l1_le_of_cube_F4 S14 fun y hyL hy3 => ?_
  by_cases hy1 : y = 1
  · rw [hy1]
    exact one_mem _
  · exact Subgroup.subset_closure ⟨hyL, orderOf_eq_prime hy3 hy1⟩

theorem exists_commute_F4 (h1332 : Stmt13_3_2_F4) {y : G} (hy : y ∈ a114Y z z') (hy3 : y ^ 3 = 1) :
    ∃ x' ∈ l1 T L V, x' ^ 3 = 1 ∧ x' ≠ 1 ∧ y * x' = x' * y := by
  obtain ⟨x, hxY, -, hx3, -⟩ := D.exists_x
  have h3 : 3 ∣ Nat.card ↥(lY T L V z') := by
    have := orderOf_dvd_natCard (⟨x, hxY⟩ : ↥(lY T L V z'))
    rwa [Subgroup.orderOf_mk, hx3] at this
  obtain ⟨ω, hω, hω3, hω1, hyω⟩ :=
    C.exists_comm_of_normalizes h3 (D.a114Y_le_normalizer_lY_F4 h1332 hy) hy3
  exact ⟨ω, lY_le_l1 hω, hω3, hω1, hyω⟩

end IData

end CFSG.Quasithin.H13.L32A.L2
