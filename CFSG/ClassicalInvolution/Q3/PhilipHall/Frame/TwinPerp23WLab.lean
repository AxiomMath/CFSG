module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Lab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23WAE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement




namespace W

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.AE5

section Lab

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_not_mem_finset (α : Finset (Fin 5)) (h : α.card = 4) : ∃ p, p ∉ α := by
  by_contra hc
  push Not at hc
  have : α = Finset.univ := Finset.eq_univ_of_forall hc
  rw [this] at h
  simp at h

theorem mem_C_H_of_mem_coreLayer {x : G} (hx : x ∈ coreLayer Ω c) :
    ∃ hC : x ∈ Subgroup.centralizer ({c} : Set G),
      (⟨x, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a.2, ha⟩

theorem chiLayer_perm_mem (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hgen : TC.Thin.pSpan (TwinDisc.secFam Ω c) = ⊤) (I : TC.Thin.AEIdent (TwinDisc.secFam Ω c) 5)
    {J T : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hT : IsSylow2In T J)
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G)) {α : Finset (Fin 5)} {h : α.card = 4} {b : Bool}
    (hlab : ((TwinDisc.secImg Ω c J).subgroupOf (TC.Thin.pSpan (TwinDisc.secFam Ω c))).map I.φ =
      AE.memBar α h b) {p : Fin 5} (hp : p ∉ α) :
    ∀ τ ∈ T, ∃ hL : τ ∈ coreLayer Ω c, V4m p (chiLayer Ω c hgen I ⟨τ, hL⟩) := by
  intro τ hτ
  have hTs : IsSylow2In T (TwinADescent.coreAt c J) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hJ.2).mpr ⟨hT, hTc⟩
  have hτcore : τ ∈ TwinADescent.coreAt c J := hTs.1 hτ
  have hC : τ ∈ Subgroup.centralizer ({c} : Set G) := TwinADescent.coreAt_le_centralizer c J hτcore
  have hH0 : (⟨τ, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.mem_subgroupOf.mpr hτcore
  have hH : (⟨τ, hC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c := le_coreHull hJ hH0
  have hL : τ ∈ coreLayer Ω c := mem_coreLayer_of hC hH
  refine ⟨hL, ?_⟩
  rw [chiLayer_apply hgen I hC hH hL]
  have hy : (QuotientGroup.mk (⟨⟨τ, hC⟩, hH⟩ : ↥(coreHull Ω c)) :
      ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈ TwinDisc.secImg Ω c J :=
    ⟨⟨⟨τ, hC⟩, hH⟩, Subgroup.mem_subgroupOf.mpr hH0, rfl⟩
  have hmem := I.mem_map (TwinDisc.secImg_mem_secFam hJ) hy
  rw [hlab] at hmem
  obtain ⟨w, hw, hwe⟩ := hmem
  have : I.φ ⟨QuotientGroup.mk (⟨⟨τ, hC⟩, hH⟩ : ↥(coreHull Ω c)),
      TwinDisc.mem_pSpan_of_top hgen _⟩ = mkQ 5 w := hwe.symm
  rw [this]
  show V4m p w.perm
  exact perm_memAt hp hw

theorem chiLayer_exists_perm (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hgen : TC.Thin.pSpan (TwinDisc.secFam Ω c) = ⊤) (I : TC.Thin.AEIdent (TwinDisc.secFam Ω c) 5)
    {J T : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) (hT : IsSylow2In T J)
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G))
    (hA : IsPGroup 2 ↥(TwinDisc.secImg Ω c J)) {α : Finset (Fin 5)} {h : α.card = 4} {b : Bool}
    (hlab : ((TwinDisc.secImg Ω c J).subgroupOf (TC.Thin.pSpan (TwinDisc.secFam Ω c))).map I.φ =
      AE.memBar α h b) {p : Fin 5} (hp : p ∉ α) :
    ∀ σ : Equiv.Perm (Fin 5), V4m p σ →
      ∃ τ ∈ T, ∃ hL : τ ∈ coreLayer Ω c, chiLayer Ω c hgen I ⟨τ, hL⟩ = σ := by
  intro σ hσ
  obtain ⟨w, hw, hwσ⟩ := exists_memAt_perm h b hp hσ
  have hmem : mkQ 5 w ∈ ((TwinDisc.secImg Ω c J).subgroupOf
      (TC.Thin.pSpan (TwinDisc.secFam Ω c))).map I.φ := by
    rw [hlab]
    exact ⟨w, hw, rfl⟩
  obtain ⟨y', hy', hy'e⟩ := hmem
  have hyJ : (y' : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈
      TwinDisc.secImg Ω c J := Subgroup.mem_subgroupOf.mp hy'
  obtain ⟨τ, hτ, hC, hH, hτe⟩ := exists_mem_sylow_of_mem_secImg hΩ hc2 hJ hT hTc hA hyJ
  have hL : τ ∈ coreLayer Ω c := mem_coreLayer_of hC hH
  refine ⟨τ, hτ, hL, ?_⟩
  rw [chiLayer_apply hgen I hC hH hL]
  have : (⟨QuotientGroup.mk (⟨⟨τ, hC⟩, hH⟩ : ↥(coreHull Ω c)),
      TwinDisc.mem_pSpan_of_top hgen _⟩ : ↥(TC.Thin.pSpan (TwinDisc.secFam Ω c))) = y' :=
    Subtype.ext hτe
  rw [this, hy'e]
  show w.perm = σ
  exact hwσ

theorem chiLayer_fix_of_commutes (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      (TwinDisc.secFam Ω c))
    (I : TC.Thin.AEIdent (TwinDisc.secFam Ω c) 5)
    {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) {t : G} (ht : IsUniqueInvolution J t)
    {α : Finset (Fin 5)} {h : α.card = 4} {b : Bool}
    (hlab : ((TwinDisc.secImg Ω c J).subgroupOf (TC.Thin.pSpan (TwinDisc.secFam Ω c))).map I.φ =
      AE.memBar α h b) {p : Fin 5} (hp : p ∉ α)
    {x : G} (hx : x ∈ coreLayer Ω c) (hxt : x * t = t * x) :
    chiLayer Ω c (hgen_of hS) I ⟨x, hx⟩ p = p := by
  obtain ⟨htC, htY, hu⟩ := isUniqueInvolution_secImg hΩ hc2 hJ ht
  obtain ⟨hC, hH⟩ := mem_C_H_of_mem_coreLayer hx
  have hcomm : (⟨⟨x, hC⟩, hH⟩ : ↥(coreHull Ω c)) * ⟨⟨t, htC⟩, htY⟩ =
      ⟨⟨t, htC⟩, htY⟩ * ⟨⟨x, hC⟩, hH⟩ := Subtype.ext (Subtype.ext hxt)
  rw [chiLayer_apply (hgen_of hS) I hC hH hx]
  have hz := AEIdent.map_eq_zBar I (by norm_num) (TwinDisc.secImg_mem_secFam hJ)
    (members_card8 (by norm_num) hS I _ (TwinDisc.secImg_mem_secFam hJ)) hlab hu
  apply permQ_fix_of_comm_zBar h hp
  rw [← hz]
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (congrArg QuotientGroup.mk hcomm)

theorem exists_pow_mem_oddCoreOf_of_chi_eq_one (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hS : Q8Section (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      (TwinDisc.secFam Ω c))
    (I : TC.Thin.AEIdent (TwinDisc.secFam Ω c) 5) {x : G} (hx : x ∈ coreLayer Ω c)
    (h1 : chiLayer Ω c (hgen_of hS) I ⟨x, hx⟩ = 1) :
    ∃ j : ℕ, x ^ 2 ^ j ∈ oddCoreOf (coreLayer Ω c) := by
  obtain ⟨hC, hH⟩ := mem_C_H_of_mem_coreLayer hx
  rw [chiLayer_apply (hgen_of hS) I hC hH hx] at h1
  set y : ↥(TC.Thin.pSpan (TwinDisc.secFam Ω c)) :=
    ⟨QuotientGroup.mk (⟨⟨x, hC⟩, hH⟩ : ↥(coreHull Ω c)), TwinDisc.mem_pSpan_of_top (hgen_of hS) _⟩ with hy
  have hker : I.φ y ∈ (TC.Thin.permQ 5).ker := h1
  have hsq : I.φ y * I.φ y = 1 := mul_self_of_mem_ker_permQ hker
  have hyy : y * y ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact hsq
  obtain ⟨k, hk⟩ := ker_pGroupN hS I ⟨y * y, hyy⟩
  have hk' : (y * y) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨k + 1, ?_⟩
  have h2 : y ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul, pow_two]
    exact hk'
  have hmk : (QuotientGroup.mk ((⟨⟨x, hC⟩, hH⟩ : ↥(coreHull Ω c)) ^ 2 ^ (k + 1)) :
      ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) = 1 := by
    rw [QuotientGroup.mk_pow]
    have := congrArg Subtype.val h2
    simpa [hy] using this
  have hn := (QuotientGroup.eq_one_iff _).mp hmk
  have := mem_oddCoreOf_coreLayer hΩ hc2 hn
  simpa using this

end Lab

end W

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
