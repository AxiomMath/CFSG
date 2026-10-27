module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem17
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem stmt12_2_17_of_F4
    (h1216 : Stmt12_2_16_F4) (h1222 : Stmt12_2_2_F4) (h323 : Stmt3_2_3) :
    Stmt12_2_17_F4 := by
  intro G _ _ T L V hH hNE
  have hTIV := h1216 G T L V hH hNE
  have hTI : ∀ y : G, conjSub y V = V ∨ V ⊓ conjSub y V = ⊥ := fun y => by
    have := hTIV y⁻¹
    rwa [conjugate_eq_conjSub_inv, inv_inv] at this
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, hab, -⟩ := hall V hH.irrPlus
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hs : ∀ x ∈ V, x * x = 1 := fun x hx => by
    have := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨x, hVLT hx⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hx)
    rw [← pow_two]
    simpa using congrArg Subtype.val h2

  have hL0 := hH.conjClosure_eq
  have hV0 : conjClosure V T = V := conjClosure_eq_self_of_normalizes hTV
  have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G) := by
    have := (stmt3_2_2_eight_proved G T L V hH.fsu).2.2
    rwa [hL0, hV0] at this

  have hW : weakClosureW0 T V ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    refine iSup₂_le fun g hg => le_inf hg ?_
    exact conjSub_le_centralizer_of_le_normalizer hc hs hTI (hg.trans hTV)
  refine ⟨hW, hQ.symm, ?_⟩

  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hWQ : weakClosureW0 T V ≤ Q := by rw [hQ]; exact hW
  have hQT : Q ≤ T := by rw [hQ]; exact inf_le_left
  have hconj : ∀ x ∈ Subgroup.normalizer (Q : Set G),
      conjSub x (weakClosureW0 T V) ≤ weakClosureW0 T V := by
    intro x hx
    rw [weakClosureW0, conjSub_iSup]
    refine iSup_le fun g => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hg => ?_
    rw [← conjSub_mul]
    have hle : conjSub (x * g) V ≤ T := by
      rw [conjSub_mul]
      have h1 : conjSub g V ≤ Q := (conjSub_le_weakClosureW0 hg).trans hWQ
      refine (conjSub_mono x h1).trans (le_trans ?_ hQT)
      intro y hy
      rw [mem_conjSub] at hy
      have := (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * y * x)).mp hy
      simpa [mul_assoc] using this
    exact conjSub_le_weakClosureW0 hle
  have hNQ : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (weakClosureW0 T V : Set G) := by
    intro x hx
    have h1 := hconj x hx
    have h2 := hconj x⁻¹ (inv_mem hx)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      exact h1 (mul_mem_conjSub hw)
    · intro hw
      have := h2 (mul_mem_conjSub hw)
      simpa [mul_assoc] using this

  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (L ⊔ T) |>.trans' Subgroup.le_normalizer
  have h2W : IsPGroup 2 ↥(weakClosureW0 T V) :=
    (CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hH.sylow).elim fun S hS =>
      (hS ▸ S.isPGroup').to_le (hWQ.trans hQT)
  have hW1 : weakClosureW0 T V ≠ ⊥ := by
    intro h
    apply hH.irrPlus.2.1
    rw [eq_bot_iff, ← h]
    have := conjSub_le_weakClosureW0 (T := T) (V := V) (g := 1) (by rw [conjSub_one]; exact hVT)
    rwa [conjSub_one] at this
  obtain ⟨M', hM', hWM'⟩ :=
    CFSG.Quasithin.exists_maxTwoLocal_ge (L := Subgroup.normalizer (weakClosureW0 T V : Set G))
      ⟨weakClosureW0 T V, hW1, h2W, rfl⟩
  obtain ⟨-, ⟨-, huniq⟩, -⟩ :=
    h323 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful hH.quasisimple
  rw [hL0] at huniq
  have hM'eq := huniq M' hM' ((hLTQ.trans hNQ).trans hWM')
  rw [← hM'eq]
  exact hWM'

end CFSG.Quasithin.H13
