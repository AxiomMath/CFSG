module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem18Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7One

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

open Lem18

theorem stmt12_2_18_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3)
    (h1216 : Stmt12_2_16_F4) (h1217 : Stmt12_2_17_F4) (hrank : Lem12218TwoRank_F4) : Stmt12_2_18_F4 := by
  intro G _ _ T L V hH hNE H hHs hVO
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, hab, -⟩ := hall V hH.irrPlus

  have hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    simpa using congrArg Subtype.val (sq_eq_one_of_hyp1223 hH hred ⟨v, hv⟩)
  have hs : ∀ x ∈ V, x * x = 1 := fun x hx => by rw [← pow_two]; exact hV2 x hx
  have hVe : CFSG.IsElementaryAbelian 2 V := SteinbergBM.isElementaryAbelian_two_of hc hs

  have hZV := Lem7.omegaOneCenter_inf_ne_bot hH.sylow.1 hVT hTV hH.irrPlus.2.1 hV2
  obtain ⟨⟨z, hzZ, hzV⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZV
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hCV : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.centralizer_le (t := (V : Set G)) (Set.singleton_subset_iff.mpr hzV)).trans
      (hNE z hzV hz1)
  have hCZ : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G) :=
    (Subgroup.centralizer_le (t := (quasithinOmegaOneCenter T : Set G))
      (Set.singleton_subset_iff.mpr hzZ)).trans (hNE z hzV hz1)

  have h1226 := stmt12_2_6_of_F4 h1222 h323
  obtain ⟨-, hCTV, hQC, hCker⟩ := stmt12_2_7_one_F4 h331 h1222 h1226 hH hCZ hHs
  have hmin := Lem7.minParabolic_F4 h331 hH hHs
  have hQN : pCoreOf 2 H ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    (kerIn_le (hCker (hQC hx))).2
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hTH : T ≤ H := hHs.1.1

  have hW : ¬ weakClosureW0 T V ≤ pCoreOf 2 H := fun hWQ =>
    hHs.2.1 ((hHQ.trans (normalizer_le_normalizer_weakClosureW0 hWQ hQT)).trans
      (h1217 G T L V hH hNE).2.2)
  obtain ⟨g, hgT, hgQ⟩ : ∃ g : G, conjSub g V ≤ T ∧ ¬ conjSub g V ≤ pCoreOf 2 H := by
    by_contra hcon
    apply hW
    refine iSup₂_le fun g hg => ?_
    by_contra h
    exact hcon ⟨g, hg, h⟩
  have hA2 : IsPGroup 2 ↥(conjSub g V) := hH.sylow.1.to_le hgT

  have hAQ : conjSub g V ⊓ pCoreOf 2 H ≠ ⊥ := by
    intro hbot
    have hAC : conjSub g V ⊓ Subgroup.centralizer (VZ T H : Set G) = ⊥ := by
      rw [eq_bot_iff, ← hbot]
      intro x hx
      refine ⟨hx.1, ?_⟩
      rw [← hCTV]
      exact ⟨hgT hx.1, hx.2⟩
    have hcA : ∀ x ∈ conjSub g V, ∀ y ∈ conjSub g V, x * y = y * x := by
      intro x hx y hy
      rw [mem_conjSub] at hx hy
      have := hc _ hx _ hy
      calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
        _ = y * x := by group
    have hsA : ∀ x ∈ conjSub g V, x ^ 2 = 1 := by
      intro x hx
      rw [mem_conjSub] at hx
      have := hV2 _ hx
      rw [pow_two] at this ⊢
      calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hE : IsElemAbelian 2 (conjSub g V) :=
      ⟨⟨⟨fun a b => Subtype.ext (hcA a a.2 b b.2)⟩⟩, hsA⟩
    have h4 := hrank G T L V H hH hCZ hHs (conjSub g V) (hgT.trans hTH) hE hAC
    have hcard : Nat.card ↥(conjSub g V) = Nat.card ↥V :=
      Nat.card_congr (Subgroup.equivMapOfInjective V (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv.symm
    rw [hcard] at h4
    exact not_card_le_four hH hred h4

  have hcent : ∀ h ∈ H, conjSub h (conjSub g V) ≤ Subgroup.centralizer (V : Set G) := by
    intro h hh
    have hconj : CFSG.conjugate V (h * g)⁻¹ = conjSub h (conjSub g V) := by
      rw [← conjSub_mul h g]
      show conjSub (h * g)⁻¹⁻¹ V = conjSub (h * g) V
      rw [inv_inv]
    rw [← hconj]
    by_cases hVV : CFSG.conjugate V (h * g)⁻¹ = V
    · rw [hVV]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hc y hy x hx
    obtain ⟨-, hb⟩ := SteinbergBM.nq_elementary_TI_pair_commutation hVe
      (fun x => (h1216 G T L V hH hNE x).symm) hVV
    have h2 : IsPGroup 2 ↥(V ⊔ CFSG.conjugate V (h * g)⁻¹) := by
      refine (F7.isPGroup_conjSub (g := h) hH.sylow.1).to_le (sup_le ?_ ?_)
      · intro v hv
        rw [mem_conjSub]
        apply hQT
        have := (Subgroup.mem_normalizer_iff.mp (hHQ (H.inv_mem hh)) v).mp (hVO hv)
        rwa [inv_inv] at this
      · rw [hconj]
        exact conjSub_mono h hgT
    have hN : CFSG.conjugate V (h * g)⁻¹ ⊓ Subgroup.normalizer (V : Set G) ≠ ⊥ := by
      rw [hconj]
      intro hbot
      apply hAQ
      rw [eq_bot_iff]
      intro x hx
      have hx' : h * x * h⁻¹ ∈ conjSub h (conjSub g V) ⊓ Subgroup.normalizer (V : Set G) :=
        ⟨mul_mem_conjSub hx.1, hQN ((Subgroup.mem_normalizer_iff.mp (hHQ hh) x).mp hx.2)⟩
      rw [hbot, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      have e : x = h⁻¹ * (h * x * h⁻¹) * h := by group
      rw [e, hx']
      group
    have hcomm := hb h2 hN
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    exact Subgroup.le_centralizer_iff.mp hcomm

  set Y : Subgroup G := ⨆ (h : G) (_ : h ∈ H), conjSub h (conjSub g V) with hY
  have hYH : Y ≤ H := by
    rw [hY]
    refine iSup₂_le fun h hh x hx => ?_
    rw [mem_conjSub] at hx
    have e : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hh ((hgT.trans hTH) hx)) (H.inv_mem hh)
  have hYC : Y ≤ Subgroup.centralizer (V : Set G) := by
    rw [hY]
    exact iSup₂_le hcent
  have hYk : ∀ k ∈ H, conjSub k Y ≤ Y := by
    intro k hk
    rw [hY, conjSub_iSup]
    refine iSup_le fun h => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hh => ?_
    rw [← conjSub_mul k h]
    exact le_iSup₂_of_le (k * h) (H.mul_mem hk hh) le_rfl
  have hYn : H ≤ Subgroup.normalizer (Y : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hYk k hk (mul_mem_conjSub hy)
    · intro hy
      have := hYk k⁻¹ (H.inv_mem hk) (mul_mem_conjSub hy)
      simpa [mul_assoc] using this
  have hAY : conjSub g V ≤ Y := by
    rw [hY]
    exact le_iSup₂_of_le (1 : G) H.one_mem (conjSub_one _).ge
  have hYJ : Y ≤ kerIn (H ⊓ Subgroup.normalizer (L : Set G)) H :=
    le_kerIn_of_le_normalizer (le_inf hYH (hYC.trans hCV)) hYn
  exact hgQ (hmin.le_pCoreOf_of_isPGroup_of_le_kerIn hA2 (hAY.trans hYJ))

end CFSG.Quasithin.H13
