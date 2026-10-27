module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BD1Fixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BConjCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BHRank

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.Monster.B.GSide CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.CTIB


theorem t2D_mem_Ehat : t2D ∈ Ehat := by
  refine Ehat.mul_mem cQ_mem_Ehat ?_
  have h7 : (vPlus : Fin 8 → ZMod 2) 7 = 0 := by decide
  have hΨ : Psi vPlus = PhiD vPlus := by rw [Psi, h7, ZMod.val_zero, pow_zero, mul_one]
  rw [hΨ]
  exact B7_le_Ehat (PhiD_mem_B7 vPlus)

theorem t2D_ne_one_xhat : t2D ≠ 1 ∧ t2D ≠ xhat :=
  ⟨fun h => t2D_not_mem_A8 (h ▸ A8.one_mem), fun h => t2D_not_mem_A8 (h ▸ xhat_mem_A8_e0)⟩

theorem thirtyTwo_le_card_conj_of_fixes_T9S
    (n : ↥(Subgroup.centralizer ({t2DS} : Set Shat))) (hn : (n : Shat) * n = t2DS)
    (hfix : ∀ x ∈ T9S, (n : Shat) * x * (n : Shat)⁻¹ = x) :
    32 ≤ Nat.card {y : ↥(Subgroup.centralizer ({t2DS} : Set Shat)) // IsConj n y} := by
  have hxT : xhatS ∈ T9S := mem_T9S.2 (A8_le_T9 xhat_mem_A8_e0)
  have hnx : (n : Shat) * xhatS = xhatS * n := by
    have h := hfix xhatS hxT
    rwa [mul_inv_eq_iff_eq_mul] at h
  have hnC : (n : Shat) ∈ Subgroup.centralizer ({xhatS} : Set Shat) :=
    mem_centralizer_singleton_iff.2 hnx
  have hnJ : ((n : Shat) : Dfull) ∈ Jhat := mem_centralizer_xhatS.1 hnC
  have hnn : ((n : Shat) : Dfull) * ((n : Shat) : Dfull) = t2D := congrArg Subtype.val hn
  have ht2J : t2D ∈ Jhat := Ehat_le_Jhat t2D_mem_Ehat
  set k : Kstab v0 := jhatToKv0 ⟨((n : Shat) : Dfull), hnJ⟩ with hk
  have hk2 : k * k = 1 := by
    rw [hk, ← map_mul]
    have h : (⟨((n : Shat) : Dfull), hnJ⟩ * ⟨((n : Shat) : Dfull), hnJ⟩ : Jhat) = ⟨t2D, ht2J⟩ :=
      Subtype.ext hnn
    rw [h]
    exact jhatToKv0_eq_one_of_mem_Ehat ht2J t2D_mem_Ehat
  have hk1 : k ≠ 1 := by
    intro h
    have hker : (⟨((n : Shat) : Dfull), hnJ⟩ : Jhat) ∈ jhatToKv0.ker := MonoidHom.mem_ker.2 h
    rw [ker_jhatToKv0, Subgroup.mem_subgroupOf] at hker
    rcases Ehat_sq_mem hker with h1 | h1
    · exact t2D_ne_one_xhat.1 (hnn.symm.trans h1)
    · exact t2D_ne_one_xhat.2 (hnn.symm.trans h1)
  have hrank := six_le_finrank_range_wAct_sub_one k hk2 hk1
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  have hnE : ∀ e ∈ QhatS, (n : Shat) * e * (n : Shat)⁻¹ ∈ QhatS := fun e he =>
    conj_mem_QhatS hnC he
  let ψ : ↥QhatS → Wv v0 := fun e => psiW ⟨((e : Shat) : Dfull), mem_QhatS.1 e.2⟩
  have hψ : ∀ e e' : ↥QhatS, ψ (e * e') = ψ e + ψ e' := fun e e' =>
    psiW_mul ⟨((e : Shat) : Dfull), mem_QhatS.1 e.2⟩ ⟨((e' : Shat) : Dfull), mem_QhatS.1 e'.2⟩
  have hsurj : Function.Surjective ψ := fun w => by
    obtain ⟨e, he⟩ := psiW_surjective w
    exact ⟨⟨⟨e.1, Ehat_le_Shat e.2⟩, mem_QhatS.2 e.2⟩, he⟩
  have hT : ∀ e : ↥QhatS, ψ ⟨(n : Shat) * e * (n : Shat)⁻¹, hnE e e.2⟩ = wAct v0 k (ψ e) := by
    intro e
    have hg : ((n : Shat) : Dfull)⁻¹ ∈ Jhat := Jhat.inv_mem hnJ
    have h1 := psiW_conj hg (mem_QhatS.1 e.2)
    have h2 : jhatToKv0 ⟨((n : Shat) : Dfull)⁻¹, hg⟩ = k := by
      have h3 : (⟨((n : Shat) : Dfull)⁻¹, hg⟩ : Jhat) = (⟨((n : Shat) : Dfull), hnJ⟩ : Jhat)⁻¹ :=
        rfl
      rw [h3, map_inv, ← hk, hkinv]
    rw [h2] at h1
    refine Eq.trans (congrArg psiW (Subtype.ext ?_)) h1
    show ((n : Shat) : Dfull) * ((e : Shat) : Dfull) * ((n : Shat) : Dfull)⁻¹ =
      ((n : Shat) : Dfull)⁻¹⁻¹ * ((e : Shat) : Dfull) * ((n : Shat) : Dfull)⁻¹
    rw [inv_inv]
  let t₀E : Ehat := ⟨t2D, t2D_mem_Ehat⟩
  let l : Wv v0 →ₗ[ZMod 2] ZMod 2 := (LinearMap.flip bV) (psiW t₀E)
  have hl : ∀ e : ↥QhatS, l (ψ e) = 0 → (e : Shat) * t2DS = t2DS * e := by
    intro e he0
    have hcomm := Ehat_comm ⟨((e : Shat) : Dfull), mem_QhatS.1 e.2⟩ t₀E
    have hb : bV (psiW ⟨((e : Shat) : Dfull), mem_QhatS.1 e.2⟩) (psiW t₀E) = 0 := he0
    have hxpow : xhat ^ (bV (psiW ⟨((e : Shat) : Dfull), mem_QhatS.1 e.2⟩) (psiW t₀E)).val =
        1 := by rw [hb, ZMod.val_zero, pow_zero]
    rw [hxpow] at hcomm
    exact Subtype.ext (hcomm.trans (mul_one _))
  have h := two_pow_le_card_conj_of_hyperplane (H := Shat) (W := Wv v0) QhatS t2DS (n : Shat) n.2
    hnE ψ hψ hsurj (wAct v0 k) hT l hl hrank
  exact le_trans (le_of_eq (by norm_num)) h

theorem rootClassLarge_t2DS : RootClassLarge t2DS := by
  intro n hn
  by_contra h
  have hle : Nat.card {y : ↥(Subgroup.centralizer ({t2DS} : Set Shat)) // IsConj n y} ≤ 4 := by
    omega
  have h32 := thirtyTwo_le_card_conj_of_fixes_T9S n hn (fixes_T9S_of_few_conjugates n hle)
  omega

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
