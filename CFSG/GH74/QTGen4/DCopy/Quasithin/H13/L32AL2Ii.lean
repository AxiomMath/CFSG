module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2Ih
public import CFSG.Quasithin.EmptyFaithful.SzN17Aut
public import CFSG.Quasithin.H13.L32AL2Ig

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

theorem autOn_l1_le_sup_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {x' : G} (hx'L : x' ∈ l1 T L V) (hx'3 : x' ^ 3 = 1) (hx'1 : x' ≠ 1) :
    autOn (l1 T L V) (vI T L V z z') ≤ autOn (pCoreOf 2 (l1 T L V)) (vI T L V z z') ⊔
      Subgroup.zpowers (conjAct (vI T L V z z')
        ⟨x', iI_le_normalizer_vI T L V z z' (l1_le_iI hx'L)⟩) := by
  have hIW := iI_le_normalizer_vI T L V z z'
  have hle := D.l1_le_sup_F4 h1222 h1332 h1334 hx'L hx'3 hx'1
  have hzN : Subgroup.zpowers x' ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V) : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_pCoreOf 2 _ hx'L)
  intro φ hφ
  obtain ⟨⟨g, hgN⟩, hgL, rfl⟩ := Setup.mem_autOn_iff.mp hφ
  obtain ⟨q, hq, w, hw, hqw⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hzN).1 (hle hgL)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hqN : q ∈ Subgroup.normalizer (vI T L V z z' : Set G) :=
    hIW (l1_le_iI (pCoreOf_le 2 _ hq))
  have hx'N : x' ∈ Subgroup.normalizer (vI T L V z z' : Set G) := hIW (l1_le_iI hx'L)
  have e : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (vI T L V z z' : Set G))) =
      ⟨q, hqN⟩ * ⟨x', hx'N⟩ ^ n := Subtype.ext (by simpa using hqw)
  rw [e, map_mul, map_zpow]
  exact mul_mem (Subgroup.mem_sup_left (A1b.conjAct_mem_autOn hqN hq))
    (Subgroup.mem_sup_right (zpow_mem (Subgroup.mem_zpowers _) n))

theorem odd_mem_normalizer_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {K : Subgroup (MulAut ↥(vI T L V z z'))} (hK : GoodK K)
    (hKI : K ≤ autOn (iI T L V z z') (vI T L V z z'))
    (hK3 : ∀ u ∈ autOn (iI T L V z z') (vI T L V z z'), u ^ 3 = 1 →
      u ∈ Subgroup.normalizer (K : Set _))
    (hSyl : IsSylowTwoOf (autOn T (vI T L V z z') ⊓ K) K) {y : G} (hy : y ∈ a114Y z z')
    (ho : Odd (orderOf y)) :
    conjAct (vI T L V z z') ⟨y, iI_le_normalizer_vI T L V z z' (a114Y_le_iI hy)⟩ ∈
      Subgroup.normalizer (autOn (l1 T L V) (vI T L V z z') : Set (MulAut ↥(vI T L V z z'))) := by
  have hIW := iI_le_normalizer_vI T L V z z'
  have hVc : IsMulCommutative ↥(vI T L V z z') := (D.vI_spec_F4 h1222 h1332 h1334).2.1.1
  set Ip := autOn (iI T L V z z') (vI T L V z z') with hIp
  set Λ := autOn (l1 T L V) (vI T L V z z') with hΛ
  set Θ := autOn T (vI T L V z z') with hΘ
  set Qp := autOn (pCoreOf 2 (l1 T L V)) (vI T L V z z') with hQp
  set C := Ip ⊓ Subgroup.centralizer (K : Set (MulAut ↥(vI T L V z z'))) with hC
  have hy3 := D.pow_three_of_odd hy ho
  have hyN : y ∈ Subgroup.normalizer ((vI T L V z z') : Set G) := hIW (a114Y_le_iI hy)
  by_cases hy1 : y = 1
  · have e : (⟨y, hyN⟩ : ↥(Subgroup.normalizer ((vI T L V z z') : Set G))) = 1 := Subtype.ext hy1
    rw [e, map_one]
    exact one_mem _
  obtain ⟨x', hx'L, hx'3, hx'1, hyx'⟩ := D.exists_commute_F4 h1332 hy hy3
  have hx'N : x' ∈ Subgroup.normalizer ((vI T L V z z') : Set G) := hIW (l1_le_iI hx'L)
  set xp := conjAct (vI T L V z z') ⟨x', hx'N⟩ with hxp
  set yp := conjAct (vI T L V z z') ⟨y, hyN⟩ with hyp

  have hX := D.isQuotientOfSQTKTC_autOn_F4 h1222 h1332 h1334
  have hSylT : IsSylowTwoOf Θ Ip := D.isSylowTwoOf_autOn_T
  have hΘ2 : IsPGroup 2 Θ := hSylT.2.1
  have hKC : K ⊓ C = ⊥ := hK.inf_eq_bot inf_le_right
  have hcomm : ∀ a ∈ K, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ha
  have h3C : ∀ b ∈ C, ∀ b' ∈ C, b ^ 3 = 1 → b' ^ 3 = 1 → b * b' = b' * b →
      b = 1 ∨ b' ∈ Subgroup.zpowers b := by
    intro b hb b' hb' hb3 hb'3 hc
    let : CommGroup ↥(vI T L V z z') := IsMulCommutative.instCommGroup
    exact hK.three_centralizer hKI hX hb.1 hb'.1 hb.2 hb'.2 hb3 hb'3 hc
  have hΘΛ : Θ ≤ Subgroup.normalizer (Λ : Set (MulAut ↥(vI T L V z z'))) :=
    le_normalizer_of_conj (InternalSec.autOn_normal_of (Setting147.T_le_N_l1_F4 D.S h1332))
  have hQΘ : Qp ≤ Θ := InternalSec.autOn_le_autOn_of_le (D.pCoreOf_l1_le_T_F4 h1332)
  have hQΛ : Qp ≤ Λ := InternalSec.autOn_le_autOn_of_le (pCoreOf_le 2 _)
  have hQ2 : IsPGroup 2 Qp := hΘ2.to_le hQΘ
  have hΛI : Λ ≤ Ip := InternalSec.autOn_le_autOn_of_le l1_le_iI
  have hΛQ : Λ ≤ Subgroup.normalizer (Qp : Set (MulAut ↥(vI T L V z z'))) :=
    le_normalizer_of_conj (InternalSec.autOn_normal_of (le_normalizer_pCoreOf 2 _))

  have hl1eq : l1 T L V = Subgroup.closure {x | x ∈ l1 T L V ∧ orderOf x = 3} :=
    le_antisymm (D.l1_le_closure_F4 h1222 h1332 h1334)
      ((Subgroup.closure_le _).mpr fun x hx => hx.1)
  have hΛ3 : Λ ≤ Subgroup.closure {u | u ∈ Λ ∧ u ^ 3 = 1} := by
    rw [hΛ, SzN17.autOn_closure_orderThree hl1eq (l1_le_iI.trans hIW)]
    refine Subgroup.closure_mono fun u hu => ⟨Subgroup.subset_closure hu, ?_⟩
    rw [← hu.2]
    exact pow_orderOf_eq_one u
  have hΛKC : Λ ≤ K ⊔ C := hΛ3.trans ((Subgroup.closure_le _).mpr fun u hu =>
    hK.mem_sup hKI (hΛI hu.1) (hK3 _ (hΛI hu.1) hu.2) hu.2)

  have hxΛ : xp ∈ Λ := A1b.conjAct_mem_autOn hx'N hx'L
  have hyI : yp ∈ Ip := A1b.conjAct_mem_autOn hyN (a114Y_le_iI hy)
  have hx3 : xp ^ 3 = 1 := by
    rw [hxp, ← map_pow]
    have : (⟨x', hx'N⟩ : ↥(Subgroup.normalizer ((vI T L V z z') : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx'3)
    rw [this, map_one]
  have hy3' : yp ^ 3 = 1 := by
    rw [hyp, ← map_pow]
    have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer ((vI T L V z z') : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hxy : xp * yp = yp * xp := by
    rw [hxp, hyp, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hyx'.symm)
  exact mem_normalizer_of_commute hKC hcomm hK.three h3C hΘ2 hSyl hΘΛ hQ2 hQΘ hQΛ hxΛ
    (hΛQ hxΛ) (D.autOn_l1_le_sup_F4 h1222 h1332 h1334 hx'L hx'3 hx'1) hΛ3 hΛKC hx3
    (hK.mem_sup hKI hyI (hK3 _ hyI hy3') hy3') hy3' hxy

theorem false_of_goodK_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {K : Subgroup (MulAut ↥(vI T L V z z'))} (hK : GoodK K)
    (hKI : K ≤ autOn (iI T L V z z') (vI T L V z z'))
    (hK3 : ∀ u ∈ autOn (iI T L V z z') (vI T L V z z'), u ^ 3 = 1 →
      u ∈ Subgroup.normalizer (K : Set _))
    (hSyl : IsSylowTwoOf (autOn T (vI T L V z z') ⊓ K) K) : False := by
  have hIW := iI_le_normalizer_vI T L V z z'
  set Λ := autOn (l1 T L V) (vI T L V z z') with hΛ

  set Nt : Subgroup G :=
    ((Subgroup.normalizer (Λ : Set (MulAut ↥(vI T L V z z')))).comap
      (conjAct (vI T L V z z'))).map (Subgroup.normalizer ((vI T L V z z') : Set G)).subtype
    with hNt
  have hmem : ∀ {g : G} (hg : g ∈ Subgroup.normalizer ((vI T L V z z') : Set G)),
      conjAct (vI T L V z z') ⟨g, hg⟩ ∈ Subgroup.normalizer (Λ : Set (MulAut ↥(vI T L V z z'))) →
        g ∈ Nt :=
    fun hg h => ⟨⟨_, hg⟩, h, rfl⟩
  have hl1 : l1 T L V ≤ Nt := fun g hg =>
    hmem (hIW (l1_le_iI hg)) (Subgroup.le_normalizer (A1b.conjAct_mem_autOn _ hg))
  have hT : T ≤ Nt := fun g hg => hmem (hIW (T_le_iI hg))
    (le_normalizer_of_conj (InternalSec.autOn_normal_of (Setting147.T_le_N_l1_F4 D.S h1332))
      (A1b.conjAct_mem_autOn _ hg))
  have hY : a114Y z z' ≤ Nt := by
    refine D.a114Y_le_sup.trans (sup_le ?_ (D.hTY.trans hT))
    rw [oTwoUpper, Subgroup.closure_le]
    rintro y ⟨hy, ho⟩
    exact hmem _ (D.odd_mem_normalizer_F4 h1222 h1332 h1334 hK hKI hK3 hSyl hy ho)
  have hI : iI T L V z z' ≤ Nt := sup_le (sup_le hl1 hT) hY
  refine D.false_of_le_normalizer_F4 h1222 h1332 h1334 fun φ hφ => ?_
  obtain ⟨⟨g, hgN⟩, hgI, rfl⟩ := Setup.mem_autOn_iff.mp hφ
  obtain ⟨⟨g', hg'N⟩, hg', hgg'⟩ := hI hgI
  have e : (⟨g, hgN⟩ : ↥(Subgroup.normalizer ((vI T L V z z') : Set G))) = ⟨g', hg'N⟩ :=
    Subtype.ext hgg'.symm
  rw [e]
  exact hg'

end IData

end CFSG.Quasithin.H13.L32A.L2
