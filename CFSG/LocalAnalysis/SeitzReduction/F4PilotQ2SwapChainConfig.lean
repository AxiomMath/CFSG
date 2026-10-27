module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainSylow
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2SwapChainConfigNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

abbrev v1220 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 2, 0]
abbrev v0121 : Fin (Tag.rank .F4) → ℤ := ![0, 1, 2, 1]
abbrev v1221 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 2, 1]
abbrev v1242 : Fin (Tag.rank .F4) → ℤ := ![1, 2, 4, 2]

section Helpers

theorem map_wRep_le_rootSL2 (ω : List ℕ) {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    {H : Subgroup (adjointGroup .F4 K)} (h : H ≤ rootSL2 K γ) :
    H.map (MulAut.conj (wRep K ω)).toMonoidHom ≤ rootSL2 K (wordAct ω γ) := by
  rw [← map_wRep_rootSL2 ω hγ]
  exact Subgroup.map_mono h

theorem map_graph_le_rootSL2 {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    {H : Subgroup (adjointGroup .F4 K)} (h : H ≤ rootSL2 K γ) :
    H.map (graphAutF4 K).toMonoidHom ≤ rootSL2 K (psiF4 γ) := by
  rw [← map_graphAutF4_rootSL2 hγ]
  exact Subgroup.map_mono h

theorem map_conj_eq_of_le_B2Levi {c : adjointGroup .F4 K}
    (hc : c ∈ centralizer (B2Levi K : Set (adjointGroup .F4 K)))
    {H : Subgroup (adjointGroup .F4 K)} (h : H ≤ B2Levi K) :
    H.map (MulAut.conj c).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c * y = y * c := (mem_centralizer_iff.1 hc y (h hy)).symm
    change c * y * c⁻¹ ∈ H
    rw [e, mul_inv_cancel_right]
    exact hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    have e : c * x = x * c := (mem_centralizer_iff.1 hc x (h hx)).symm
    change c * x * c⁻¹ = x
    rw [e, mul_inv_cancel_right]

theorem card_map_mulAut (ψ : MulAut (adjointGroup .F4 K)) (H : Subgroup (adjointGroup .F4 K)) :
    Nat.card (H.map ψ.toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective ψ.injective

theorem levi_singleton_eq (i : Fin (Tag.rank .F4)) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} =
      (Adjoint.f4Datum K).rootGroup (Pi.single i 1) ⊔
        (Adjoint.f4Datum K).rootGroup (-Pi.single i 1) := by
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  rfl

theorem rootGroups_map_wRep (ω : List ℕ) {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) :
    ((Adjoint.f4Datum K).rootGroup β ⊔ (Adjoint.f4Datum K).rootGroup (-β)).map
        (MulAut.conj (wRep K ω)).toMonoidHom =
      (Adjoint.f4Datum K).rootGroup (wordAct ω β) ⊔
        (Adjoint.f4Datum K).rootGroup (-wordAct ω β) := by
  rw [Subgroup.map_sup, map_wRep_rootGroup ω hβ, map_wRep_rootGroup ω (IsRoot.neg hβ),
    wordAct_neg]

theorem rootGroups_le_B2Levi {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ b2LeviRoots)
    (hβ' : -β ∈ b2LeviRoots) :
    (Adjoint.f4Datum K).rootGroup β ⊔ (Adjoint.f4Datum K).rootGroup (-β) ≤ B2Levi K :=
  sup_le (rootGroup_le_B2Levi hβ) (rootGroup_le_B2Levi hβ')

theorem map_graphAutF4_B2Levi : (B2Levi K).map (graphAutF4 K).toMonoidHom = B2Levi K := by
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (adjointGroup .F4 K) := inferInstance
  have hle : (B2Levi K).map (graphAutF4 K).toMonoidHom ≤ B2Levi K := by
    rw [Subgroup.map_le_iff_le_comap, B2Levi_eq_iSup_rootGroup]
    refine iSup₂_le fun γ hγ => ?_
    rw [← Subgroup.map_le_iff_le_comap, map_graphAutF4_rootGroup (mem_b2LeviRoots.1 hγ).1,
      ← B2Levi_eq_iSup_rootGroup]
    have hl := mem_b2List_of_mem_b2LeviRoots hγ
    have key : ∀ v ∈ b2List, psiF4 v ∈ rootFinset .F4 ∧ psiF4 v 0 = 0 ∧ psiF4 v 3 = 0 := by
      decide +kernel
    obtain ⟨h1, h2, h3⟩ := key γ hl
    exact rootGroup_le_B2Levi (mem_b2LeviRoots_of_check h1 h2 h3)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_map_mulAut])

end Helpers

section Std

theorem map_wRep_X₀_eq (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3) (ω : List ℕ)
    (hω : wordAct ω rootR = rootR) :
    X₀.map (MulAut.conj (wRep K ω)).toMonoidHom = X₀ := by
  refine eq_of_le_rootSL2 hK isRoot_rootR ?_ hXr (by rw [card_map_mulAut, hX₀]) hX₀
  have := map_wRep_le_rootSL2 ω isRoot_rootR hXr
  rwa [hω] at this

theorem map_wRep_graph_X₀_eq (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3) (ω : List ℕ)
    (hω : wordAct ω rootS = rootS) :
    (X₀.map (graphAutF4 K).toMonoidHom).map (MulAut.conj (wRep K ω)).toMonoidHom =
      X₀.map (graphAutF4 K).toMonoidHom := by
  have h1 : X₀.map (graphAutF4 K).toMonoidHom ≤ rootSL2 K rootS := by
    have := map_graph_le_rootSL2 isRoot_rootR hXr
    rwa [psiF4_rootR] at this
  refine eq_of_le_rootSL2 hK isRoot_rootS ?_ h1 (by rw [card_map_mulAut, card_map_mulAut, hX₀])
    (by rw [card_map_mulAut, hX₀])
  have := map_wRep_le_rootSL2 ω isRoot_rootS h1
  rwa [hω] at this

theorem map_conj_inv_map_conj_self (c : adjointGroup .F4 K) (H : Subgroup (adjointGroup .F4 K)) :
    (H.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    change c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ ∈ H
    have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
    rw [e]
    exact hy
  · intro hx
    refine ⟨c * x * c⁻¹, ⟨x, hx, rfl⟩, ?_⟩
    change c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x
    group

theorem map_wRep_w0_std (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3) :
    (X₀ ⊔ stdX K).map (MulAut.conj (wRep K [0, 1, 2, 1, 0])).toMonoidHom = X₀ ⊔ stdX K := by
  have hcX : Nat.card (stdX K) = 3 := card_stdX
  have hXP : stdX K ≤ rootSL2 K root0122 := stdX_le_rootSL2
  have h1 : X₀.map (MulAut.conj (wRep K [0, 1, 2, 1, 0])).toMonoidHom = stdX K := by
    refine eq_of_le_rootSL2 hK isRoot_root0122 ?_ hXP (by rw [card_map_mulAut, hX₀]) hcX
    have := map_wRep_le_rootSL2 [0, 1, 2, 1, 0] isRoot_rootR hXr
    rwa [show wordAct [0, 1, 2, 1, 0] rootR = root0122 by decide +kernel] at this
  have h2 : (stdX K).map (MulAut.conj (wRep K [0, 1, 2, 1, 0])).toMonoidHom = X₀ := by
    refine eq_of_le_rootSL2 hK isRoot_rootR ?_ hXr (by rw [card_map_mulAut, hcX]) hX₀
    have := map_wRep_le_rootSL2 [0, 1, 2, 1, 0] isRoot_root0122 hXP
    rwa [show wordAct [0, 1, 2, 1, 0] root0122 = rootR by decide +kernel] at this
  rw [Subgroup.map_sup, h1, h2, sup_comm]

theorem map_wRep_w0S_graph_std (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXr : X₀ ≤ rootSL2 K rootR) (hX₀ : Nat.card X₀ = 3) :
    ((X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom).map
        (MulAut.conj (wRep K [3, 2, 1, 2, 3])).toMonoidHom =
      (X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom := by
  have hcX : Nat.card (stdX K) = 3 := card_stdX
  have hXP : stdX K ≤ rootSL2 K root0122 := stdX_le_rootSL2
  have hS : X₀.map (graphAutF4 K).toMonoidHom ≤ rootSL2 K rootS := by
    have := map_graph_le_rootSL2 isRoot_rootR hXr
    rwa [psiF4_rootR] at this
  have hE : (stdX K).map (graphAutF4 K).toMonoidHom ≤ rootSL2 K v1110 := by
    have := map_graph_le_rootSL2 isRoot_root0122 hXP
    rwa [show psiF4 root0122 = v1110 by decide +kernel] at this
  have hrE : IsRoot .F4 v1110 := mem_rootFinset.1 (by decide +kernel)
  have h1 : (X₀.map (graphAutF4 K).toMonoidHom).map
      (MulAut.conj (wRep K [3, 2, 1, 2, 3])).toMonoidHom =
        (stdX K).map (graphAutF4 K).toMonoidHom := by
    refine eq_of_le_rootSL2 hK hrE ?_ hE (by rw [card_map_mulAut, card_map_mulAut, hX₀])
      (by rw [card_map_mulAut, hcX])
    have := map_wRep_le_rootSL2 [3, 2, 1, 2, 3] isRoot_rootS hS
    rwa [show wordAct [3, 2, 1, 2, 3] rootS = v1110 by decide +kernel] at this
  have h2 : ((stdX K).map (graphAutF4 K).toMonoidHom).map
      (MulAut.conj (wRep K [3, 2, 1, 2, 3])).toMonoidHom = X₀.map (graphAutF4 K).toMonoidHom := by
    refine eq_of_le_rootSL2 hK isRoot_rootS ?_ hS (by rw [card_map_mulAut, card_map_mulAut, hcX])
      (by rw [card_map_mulAut, hX₀])
    have := map_wRep_le_rootSL2 [3, 2, 1, 2, 3] hrE hE
    rwa [show wordAct [3, 2, 1, 2, 3] v1110 = rootS by decide +kernel] at this
  rw [Subgroup.map_sup, Subgroup.map_sup, h1, h2, sup_comm]

end Std

section Region

theorem single_mem_b2LeviRoots {i : Fin (Tag.rank .F4)} (h0 : i ≠ 0) (h3 : i ≠ 3) :
    (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ b2LeviRoots ∧
      (-Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) ∈ b2LeviRoots := by
  refine ⟨mem_b2LeviRoots.2 ⟨isRoot_single .F4 i, ?_, ?_⟩,
    mem_b2LeviRoots.2 ⟨isRoot_neg_single .F4 i, ?_, ?_⟩⟩
  · simp [Ne.symm h0]
  · simp [Ne.symm h3]
  · simp [Ne.symm h0]
  · simp [Ne.symm h3]

theorem levi_le_B2Levi {i : Fin (Tag.rank .F4)} (h0 : i ≠ 0) (h3 : i ≠ 3) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} ≤ B2Levi K := by
  rw [levi_singleton_eq]
  exact rootGroups_le_B2Levi (single_mem_b2LeviRoots h0 h3).1 (single_mem_b2LeviRoots h0 h3).2

theorem levi_le_map_wRep_B2Levi (ω : List ℕ) {i : Fin (Tag.rank .F4)}
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ b2LeviRoots) (hβ' : -β ∈ b2LeviRoots)
    (hω : wordAct ω β = Pi.single i 1) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} ≤
      (B2Levi K).map (MulAut.conj (wRep K ω)).toMonoidHom := by
  rw [levi_singleton_eq]
  exact rootGroups_le_map_wRep_B2Levi ω hβ hβ' hω

theorem levi_eq_map_wRep (ω : List ℕ) {i j : Fin (Tag.rank .F4)}
    (hω : wordAct ω (Pi.single j 1) = Pi.single i 1) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} =
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {j}).map
        (MulAut.conj (wRep K ω)).toMonoidHom := by
  rw [levi_singleton_eq, levi_singleton_eq, rootGroups_map_wRep ω (isRoot_single .F4 j), hω]

end Region

section Chains

variable {X₀ : Subgroup (adjointGroup .F4 K)} {c : adjointGroup .F4 K}

theorem transGen_levi_one (hK : Nat.card K = 2) (hXr : X₀ ≤ rootSL2 K rootR)
    (hX₀ : Nat.card X₀ = 3) (hcB : c ∈ centralizer (B2Levi K : Set (adjointGroup .F4 K)))
    (hc : ((X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      X₀ ⊔ stdX K) :
    Relation.TransGen (TwoModelEdge X₀ (stdX K) (stdB K)
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1})) 1 (graphAutF4 K) := by
  have hB : stdB K = B2Levi K := stdB_eq_B2Levi
  rw [hB]
  set Wh := MulAut.conj (wRep K [3]) with hWh
  set Ww := MulAut.conj (wRep K [0, 1, 2, 1, 0]) with hWw
  set Ci := MulAut.conj c⁻¹ with hCi
  have hTw : (X₀ ⊔ stdX K).map Ww.toMonoidHom = X₀ ⊔ stdX K := map_wRep_w0_std hK hXr hX₀
  have hXh : X₀.map Wh.toMonoidHom = X₀ := map_wRep_X₀_eq hK hXr hX₀ [3] (by decide +kernel)
  have hTCi : (X₀ ⊔ stdX K).map Ci.toMonoidHom = (X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom :=
    calc (X₀ ⊔ stdX K).map Ci.toMonoidHom = (((X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom).map
          (MulAut.conj c).toMonoidHom).map Ci.toMonoidHom := by rw [hc]
      _ = (X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom := map_conj_inv_map_conj_self c _
  have hcB' : c⁻¹ ∈ centralizer (B2Levi K : Set (adjointGroup .F4 K)) := inv_mem hcB
  obtain ⟨hb, hb'⟩ := single_mem_b2LeviRoots (i := (1 : Fin (Tag.rank .F4))) (by decide) (by decide)
  have hAB := levi_le_B2Levi (K := K) (i := (1 : Fin (Tag.rank .F4))) (by decide) (by decide)
  have hAh : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1} ≤
      (B2Levi K).map Wh.toMonoidHom :=
    levi_le_map_wRep_B2Levi [3] (i := 1) (β := Pi.single 1 1) hb hb' (by decide +kernel)
  have hAw : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1} ≤
      (B2Levi K).map Ww.toMonoidHom :=
    levi_le_map_wRep_B2Levi [0, 1, 2, 1, 0] (i := 1) (β := Pi.single 1 1) hb hb'
      (by decide +kernel)
  have hAhw : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1} ≤
      (B2Levi K).map (Wh * Ww).toMonoidHom := by
    rw [map_mulAut_mul, levi_eq_map_wRep (K := K) [3] (i := 1) (j := 1) (by decide +kernel)]
    exact Subgroup.map_mono hAw
  have hXe : X₀.map (Wh * Ww).toMonoidHom ≤ B2Levi K := by
    rw [map_mulAut_mul]
    have h1 := map_wRep_le_rootSL2 (K := K) [0, 1, 2, 1, 0] isRoot_rootR hXr
    rw [show wordAct [0, 1, 2, 1, 0] rootR = root0122 by decide +kernel] at h1
    have h2 := map_wRep_le_rootSL2 (K := K) [3] isRoot_root0122 h1
    rw [show wordAct [3] root0122 = v0120 by decide +kernel] at h2
    exact h2.trans (rootSL2_le_B2Levi (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl))
  refine Relation.TransGen.head (b := Wh * Ww) ?_
    (Relation.TransGen.head (b := Ci * Wh) ?_ (Relation.TransGen.single ?_))
  · refine ⟨Wh, Wh * Ww, by rw [hXh, map_mulAut_one], rfl, ?_, hAh, hAhw⟩
    rw [map_mulAut_mul, hTw]
  · refine ⟨Ci * (Wh * Ww), Ci * Wh, ?_, rfl, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul, map_conj_eq_of_le_B2Levi hcB' hXe]
    · rw [map_mulAut_mul, map_mulAut_mul, map_mulAut_mul, hTw]
    · rw [map_mulAut_mul, ← map_conj_eq_of_le_B2Levi hcB' hAB]
      exact Subgroup.map_mono hAhw
    · rw [map_mulAut_mul, ← map_conj_eq_of_le_B2Levi hcB' hAB]
      exact Subgroup.map_mono hAh
  · refine ⟨Ci, graphAutF4 K, ?_, rfl, hTCi, ?_, ?_⟩
    · rw [map_mulAut_mul, hXh]
    · rw [map_conj_eq_of_le_B2Levi hcB' le_rfl]
      exact hAB
    · rw [map_graphAutF4_B2Levi]
      exact hAB

theorem transGen_levi_two (hK : Nat.card K = 2) (hXr : X₀ ≤ rootSL2 K rootR)
    (hX₀ : Nat.card X₀ = 3) (hcB : c ∈ centralizer (B2Levi K : Set (adjointGroup .F4 K)))
    (hc : ((X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      X₀ ⊔ stdX K) :
    Relation.TransGen (TwoModelEdge X₀ (stdX K) (stdB K)
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2})) 1 (graphAutF4 K) := by
  have hB : stdB K = B2Levi K := stdB_eq_B2Levi
  rw [hB]
  set W0 := MulAut.conj (wRep K [0]) with hW0
  set WS := MulAut.conj (wRep K [3, 2, 1, 2, 3]) with hWS
  set C := MulAut.conj c with hC
  set φ := graphAutF4 K with hφ
  have hTS : ((X₀ ⊔ stdX K).map φ.toMonoidHom).map WS.toMonoidHom =
      (X₀ ⊔ stdX K).map φ.toMonoidHom :=
    map_wRep_w0S_graph_std hK hXr hX₀
  have hX0 : (X₀.map φ.toMonoidHom).map W0.toMonoidHom = X₀.map φ.toMonoidHom :=
    map_wRep_graph_X₀_eq hK hXr hX₀ [0] (by decide +kernel)
  obtain ⟨hb, hb'⟩ := single_mem_b2LeviRoots (i := (2 : Fin (Tag.rank .F4))) (by decide) (by decide)
  have hAB := levi_le_B2Levi (K := K) (i := (2 : Fin (Tag.rank .F4))) (by decide) (by decide)
  have hA0 : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2} ≤
      (B2Levi K).map W0.toMonoidHom :=
    levi_le_map_wRep_B2Levi [0] (i := 2) (β := Pi.single 2 1) hb hb' (by decide +kernel)
  have hAS : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2} ≤
      (B2Levi K).map WS.toMonoidHom :=
    levi_le_map_wRep_B2Levi [3, 2, 1, 2, 3] (i := 2) (β := Pi.single 2 1) hb hb'
      (by decide +kernel)
  have hA0S : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2} ≤
      ((B2Levi K).map WS.toMonoidHom).map W0.toMonoidHom := by
    rw [levi_eq_map_wRep (K := K) [0] (i := 2) (j := 2) (by decide +kernel)]
    exact Subgroup.map_mono hAS
  have hXe : ((X₀.map φ.toMonoidHom).map WS.toMonoidHom).map W0.toMonoidHom ≤ B2Levi K := by
    have h1 := map_graph_le_rootSL2 (K := K) isRoot_rootR hXr
    rw [psiF4_rootR] at h1
    have h2 := map_wRep_le_rootSL2 (K := K) [3, 2, 1, 2, 3] isRoot_rootS h1
    rw [show wordAct [3, 2, 1, 2, 3] rootS = v1110 by decide +kernel] at h2
    have h3 := map_wRep_le_rootSL2 (K := K) [0] (mem_rootFinset.1 (by decide +kernel)) h2
    rw [show wordAct [0] v1110 = v0110 by decide +kernel] at h3
    exact h3.trans (rootSL2_le_B2Levi (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl))
  refine Relation.TransGen.head (b := C * φ) ?_
    (Relation.TransGen.head (b := C * (W0 * (WS * φ))) ?_ (Relation.TransGen.single ?_))
  · refine ⟨1, C * φ, rfl, rfl, ?_, ?_, ?_⟩
    · rw [map_mulAut_one, map_mulAut_mul, hc]
    · rw [map_mulAut_one]
      exact hAB
    · rw [map_mulAut_mul, hφ, map_graphAutF4_B2Levi, map_conj_eq_of_le_B2Levi hcB le_rfl]
      exact hAB
  · refine ⟨C * (W0 * φ), C * (W0 * (WS * φ)), ?_, rfl, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul, map_mulAut_mul, hX0, map_mulAut_mul]
    · rw [map_mulAut_mul, map_mulAut_mul, map_mulAut_mul, map_mulAut_mul, map_mulAut_mul, hTS]
    · rw [map_mulAut_mul, map_mulAut_mul, hφ, map_graphAutF4_B2Levi,
        ← map_conj_eq_of_le_B2Levi hcB hAB]
      exact Subgroup.map_mono hA0
    · rw [map_mulAut_mul, map_mulAut_mul, map_mulAut_mul, hφ, map_graphAutF4_B2Levi,
        ← map_conj_eq_of_le_B2Levi hcB hAB]
      exact Subgroup.map_mono hA0S
  · refine ⟨W0 * (WS * φ), W0 * φ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul C, map_mulAut_mul W0, map_mulAut_mul WS,
        map_conj_eq_of_le_B2Levi hcB hXe]
    · rw [map_mulAut_mul, hX0]
    · rw [map_mulAut_mul, map_mulAut_mul, map_mulAut_mul, hTS]
    · rw [map_mulAut_mul, map_mulAut_mul, hφ, map_graphAutF4_B2Levi]
      exact hA0S
    · rw [map_mulAut_mul, hφ, map_graphAutF4_B2Levi]
      exact hA0

theorem transGen_levi_zero (hK : Nat.card K = 2) (hXr : X₀ ≤ rootSL2 K rootR)
    (hX₀ : Nat.card X₀ = 3) (hcB : c ∈ centralizer (B2Levi K : Set (adjointGroup .F4 K)))
    (hc : ((X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      X₀ ⊔ stdX K) :
    Relation.TransGen (TwoModelEdge X₀ (stdX K) (stdB K)
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0}))
      (MulAut.conj (wRep K [0, 1, 2, 3]) * MulAut.conj (wRep K [0, 1, 2, 1, 0]))
      (graphAutF4 K) := by
  have hB : stdB K = B2Levi K := stdB_eq_B2Levi
  rw [hB]
  set Wh := MulAut.conj (wRep K [3]) with hWh
  set Ww := MulAut.conj (wRep K [0, 1, 2, 1, 0]) with hWw
  set Wu := MulAut.conj (wRep K [0, 1, 2, 3]) with hWu
  set Wd := MulAut.conj (wRep K [0, 1]) with hWd
  set Ci := MulAut.conj c⁻¹ with hCi
  have hTw : (X₀ ⊔ stdX K).map Ww.toMonoidHom = X₀ ⊔ stdX K := map_wRep_w0_std hK hXr hX₀
  have hXh : X₀.map Wh.toMonoidHom = X₀ := map_wRep_X₀_eq hK hXr hX₀ [3] (by decide +kernel)
  have hXd : (X₀.map (graphAutF4 K).toMonoidHom).map Wd.toMonoidHom =
      X₀.map (graphAutF4 K).toMonoidHom :=
    map_wRep_graph_X₀_eq hK hXr hX₀ [0, 1] (by decide +kernel)
  have hTCi : (X₀ ⊔ stdX K).map Ci.toMonoidHom = (X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom :=
    calc (X₀ ⊔ stdX K).map Ci.toMonoidHom = (((X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom).map
          (MulAut.conj c).toMonoidHom).map Ci.toMonoidHom := by rw [hc]
      _ = (X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom := map_conj_inv_map_conj_self c _
  have hcB' : c⁻¹ ∈ centralizer (B2Levi K : Set (adjointGroup .F4 K)) := inv_mem hcB
  obtain ⟨hb, hb'⟩ := single_mem_b2LeviRoots (i := (1 : Fin (Tag.rank .F4))) (by decide) (by decide)
  have hAB := levi_le_B2Levi (K := K) (i := (1 : Fin (Tag.rank .F4))) (by decide) (by decide)
  have hAh : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1} ≤
      (B2Levi K).map Wh.toMonoidHom :=
    levi_le_map_wRep_B2Levi [3] (i := 1) (β := Pi.single 1 1) hb hb' (by decide +kernel)
  have hAw : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1} ≤
      (B2Levi K).map Ww.toMonoidHom :=
    levi_le_map_wRep_B2Levi [0, 1, 2, 1, 0] (i := 1) (β := Pi.single 1 1) hb hb'
      (by decide +kernel)
  have hAhw : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1} ≤
      ((B2Levi K).map Ww.toMonoidHom).map Wh.toMonoidHom := by
    rw [levi_eq_map_wRep (K := K) [3] (i := 1) (j := 1) (by decide +kernel)]
    exact Subgroup.map_mono hAw
  have hu : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} =
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1}).map Wu.toMonoidHom :=
    levi_eq_map_wRep (K := K) [0, 1, 2, 3] (i := 0) (j := 1) (by decide +kernel)
  have hd : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {0} =
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {1}).map Wd.toMonoidHom :=
    levi_eq_map_wRep (K := K) [0, 1] (i := 0) (j := 1) (by decide +kernel)
  have hXe : X₀.map (Wh * Ww).toMonoidHom ≤ B2Levi K := by
    rw [map_mulAut_mul]
    have h1 := map_wRep_le_rootSL2 (K := K) [0, 1, 2, 1, 0] isRoot_rootR hXr
    rw [show wordAct [0, 1, 2, 1, 0] rootR = root0122 by decide +kernel] at h1
    have h2 := map_wRep_le_rootSL2 (K := K) [3] isRoot_root0122 h1
    rw [show wordAct [3] root0122 = v0120 by decide +kernel] at h2
    exact h2.trans (rootSL2_le_B2Levi (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl))
  have hr1220 : IsRoot .F4 v1220 := mem_rootFinset.1 (by decide +kernel)
  have hr0120 : IsRoot .F4 v0120 := mem_rootFinset.1 (by decide +kernel)
  refine Relation.TransGen.head (b := Wu) ?_
    (Relation.TransGen.head (b := Wd * Ci) ?_ (Relation.TransGen.single ?_))
  · refine ⟨Wu * Ww, Wu, rfl, rfl, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul, hTw]
    · rw [map_mulAut_mul, hu]
      exact Subgroup.map_mono hAw
    · rw [hu]
      exact Subgroup.map_mono hAB
  · refine ⟨Wd * (Ci * (Wh * Ww)), Wd * (Ci * Wh), ?_, ?_, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul Wd, map_mulAut_mul Ci, map_conj_eq_of_le_B2Levi hcB' hXe]
      have hcX : Nat.card X₀ = 3 := hX₀
      refine eq_of_le_rootSL2 hK hr1220 ?_ ?_ (by rw [card_map_mulAut, card_map_mulAut, hX₀])
        (by rw [card_map_mulAut, hX₀])
      · have h1 := map_wRep_le_rootSL2 (K := K) [0, 1] hr0120
          (show X₀.map (Wh * Ww).toMonoidHom ≤ rootSL2 K v0120 by
            rw [map_mulAut_mul]
            have h1 := map_wRep_le_rootSL2 (K := K) [0, 1, 2, 1, 0] isRoot_rootR hXr
            rw [show wordAct [0, 1, 2, 1, 0] rootR = root0122 by decide +kernel] at h1
            have h2 := map_wRep_le_rootSL2 (K := K) [3] isRoot_root0122 h1
            rwa [show wordAct [3] root0122 = v0120 by decide +kernel] at h2)
        rwa [show wordAct [0, 1] v0120 = v1220 by decide +kernel] at h1
      · have h1 := map_wRep_le_rootSL2 (K := K) [0, 1, 2, 3] isRoot_rootR hXr
        rwa [show wordAct [0, 1, 2, 3] rootR = v1220 by decide +kernel] at h1
    · rw [map_mulAut_mul Wd, map_mulAut_mul Ci, hXh, map_mulAut_mul]
    · rw [map_mulAut_mul Wd, map_mulAut_mul Ci, map_mulAut_mul Wh, hTw, map_mulAut_mul Wd,
        map_mulAut_mul Ci]
    · rw [map_mulAut_mul Wd, map_mulAut_mul Ci, map_mulAut_mul Wh, hd]
      refine Subgroup.map_mono ?_
      rw [← map_conj_eq_of_le_B2Levi hcB' hAB]
      exact Subgroup.map_mono hAhw
    · rw [map_mulAut_mul Wd, map_mulAut_mul Ci, hd]
      refine Subgroup.map_mono ?_
      rw [← map_conj_eq_of_le_B2Levi hcB' hAB]
      exact Subgroup.map_mono hAh
  · refine ⟨Wd * Ci, Wd * graphAutF4 K, rfl, ?_, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul, hXd]
    · rw [map_mulAut_mul, map_mulAut_mul, hTCi]
    · rw [map_mulAut_mul, map_conj_eq_of_le_B2Levi hcB' le_rfl, hd]
      exact Subgroup.map_mono hAB
    · rw [map_mulAut_mul, map_graphAutF4_B2Levi, hd]
      exact Subgroup.map_mono hAB

theorem transGen_levi_three_aux (hK : Nat.card K = 2) (hXr : X₀ ≤ rootSL2 K rootR)
    (hX₀ : Nat.card X₀ = 3) (hcB : c ∈ centralizer (B2Levi K : Set (adjointGroup .F4 K)))
    (hc : ((X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom).map (MulAut.conj c).toMonoidHom =
      X₀ ⊔ stdX K) :
    Relation.TransGen (TwoModelEdge X₀ (stdX K) (stdB K)
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3})) 1
      (MulAut.conj (wRep K [0, 1, 2, 3]) * MulAut.conj (wRep K [0, 1, 2, 1, 0])) := by
  have hB : stdB K = B2Levi K := stdB_eq_B2Levi
  rw [hB]
  set W0 := MulAut.conj (wRep K [0]) with hW0
  set WS := MulAut.conj (wRep K [3, 2, 1, 2, 3]) with hWS
  set Ww := MulAut.conj (wRep K [0, 1, 2, 1, 0]) with hWw
  set Wu := MulAut.conj (wRep K [0, 1, 2, 3]) with hWu
  set W1 := MulAut.conj (wRep K [3, 2]) with hW1
  set Wv := MulAut.conj (wRep K [3, 2, 1, 0]) with hWv
  set Wf := MulAut.conj (wRep K [0, 3, 2, 1]) with hWf
  set C := MulAut.conj c with hC
  set φ := graphAutF4 K with hφ
  have hTS : ((X₀ ⊔ stdX K).map φ.toMonoidHom).map WS.toMonoidHom =
      (X₀ ⊔ stdX K).map φ.toMonoidHom :=
    map_wRep_w0S_graph_std hK hXr hX₀
  have hX0 : (X₀.map φ.toMonoidHom).map W0.toMonoidHom = X₀.map φ.toMonoidHom :=
    map_wRep_graph_X₀_eq hK hXr hX₀ [0] (by decide +kernel)
  have hX1 : X₀.map W1.toMonoidHom = X₀ := map_wRep_X₀_eq hK hXr hX₀ [3, 2] (by decide +kernel)
  obtain ⟨hb, hb'⟩ := single_mem_b2LeviRoots (i := (2 : Fin (Tag.rank .F4))) (by decide) (by decide)
  have hAB := levi_le_B2Levi (K := K) (i := (2 : Fin (Tag.rank .F4))) (by decide) (by decide)
  have hA0 : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2} ≤
      (B2Levi K).map W0.toMonoidHom :=
    levi_le_map_wRep_B2Levi [0] (i := 2) (β := Pi.single 2 1) hb hb' (by decide +kernel)
  have hAS : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2} ≤
      (B2Levi K).map WS.toMonoidHom :=
    levi_le_map_wRep_B2Levi [3, 2, 1, 2, 3] (i := 2) (β := Pi.single 2 1) hb hb'
      (by decide +kernel)
  have hA0S : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2} ≤
      ((B2Levi K).map WS.toMonoidHom).map W0.toMonoidHom := by
    rw [levi_eq_map_wRep (K := K) [0] (i := 2) (j := 2) (by decide +kernel)]
    exact Subgroup.map_mono hAS
  have h1 : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} =
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2}).map W1.toMonoidHom :=
    levi_eq_map_wRep (K := K) [3, 2] (i := 3) (j := 2) (by decide +kernel)
  have hv : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} =
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2}).map Wv.toMonoidHom :=
    levi_eq_map_wRep (K := K) [3, 2, 1, 0] (i := 3) (j := 2) (by decide +kernel)
  have hf : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {3} =
      (CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {2}).map Wf.toMonoidHom :=
    levi_eq_map_wRep (K := K) [0, 3, 2, 1] (i := 3) (j := 2) (by decide +kernel)
  have hS : X₀.map φ.toMonoidHom ≤ rootSL2 K rootS := by
    have := map_graph_le_rootSL2 (K := K) isRoot_rootR hXr
    rwa [psiF4_rootR] at this
  have hr1110 : IsRoot .F4 v1110 := mem_rootFinset.1 (by decide +kernel)
  have hr0110 : IsRoot .F4 v0110 := mem_rootFinset.1 (by decide +kernel)
  have hE3 : ((X₀.map φ.toMonoidHom).map WS.toMonoidHom).map W0.toMonoidHom ≤
      rootSL2 K v0110 := by
    have h2 := map_wRep_le_rootSL2 (K := K) [3, 2, 1, 2, 3] isRoot_rootS hS
    rw [show wordAct [3, 2, 1, 2, 3] rootS = v1110 by decide +kernel] at h2
    have h3 := map_wRep_le_rootSL2 (K := K) [0] hr1110 h2
    rwa [show wordAct [0] v1110 = v0110 by decide +kernel] at h3
  have hXe : ((X₀.map φ.toMonoidHom).map WS.toMonoidHom).map W0.toMonoidHom ≤ B2Levi K :=
    hE3.trans (rootSL2_le_B2Levi (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl))
  have hcard : ∀ ψ ψ' : MulAut (adjointGroup .F4 K),
      Nat.card ((X₀.map ψ.toMonoidHom).map ψ'.toMonoidHom) = 3 := fun ψ ψ' => by
    rw [card_map_mulAut, card_map_mulAut, hX₀]
  have hcard3 : ∀ ψ ψ' ψ'' : MulAut (adjointGroup .F4 K),
      Nat.card (((X₀.map ψ.toMonoidHom).map ψ'.toMonoidHom).map ψ''.toMonoidHom) = 3 :=
    fun ψ ψ' ψ'' => by rw [card_map_mulAut, hcard]
  refine Relation.TransGen.head (b := W1 * (C * φ)) ?_
    (Relation.TransGen.head (b := W1 * (C * (W0 * (WS * φ)))) ?_
    (Relation.TransGen.head (b := Wv * (WS * φ)) ?_
    (Relation.TransGen.head (b := Wf * (C * (W0 * φ))) ?_ (Relation.TransGen.single ?_))))
  ·
    refine ⟨W1, W1 * (C * φ), by rw [hX1, map_mulAut_one], rfl, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul W1, map_mulAut_mul C, hc]
    · rw [h1]
      exact Subgroup.map_mono hAB
    · rw [map_mulAut_mul W1, map_mulAut_mul C, hφ, map_graphAutF4_B2Levi,
        map_conj_eq_of_le_B2Levi hcB le_rfl, h1]
      exact Subgroup.map_mono hAB
  ·
    refine ⟨W1 * (C * (W0 * φ)), W1 * (C * (W0 * (WS * φ))), ?_, rfl, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul W1, map_mulAut_mul C, map_mulAut_mul W0, hX0, map_mulAut_mul W1,
        map_mulAut_mul C]
    · rw [map_mulAut_mul W1, map_mulAut_mul C, map_mulAut_mul W0, map_mulAut_mul W1,
        map_mulAut_mul C, map_mulAut_mul W0, map_mulAut_mul WS, hTS]
    · rw [map_mulAut_mul W1, map_mulAut_mul C, map_mulAut_mul W0, hφ, map_graphAutF4_B2Levi, h1]
      refine Subgroup.map_mono ?_
      rw [← map_conj_eq_of_le_B2Levi hcB hAB]
      exact Subgroup.map_mono hA0
    · rw [map_mulAut_mul W1, map_mulAut_mul C, map_mulAut_mul W0, map_mulAut_mul WS, hφ,
        map_graphAutF4_B2Levi, h1]
      refine Subgroup.map_mono ?_
      rw [← map_conj_eq_of_le_B2Levi hcB hAB]
      exact Subgroup.map_mono hA0S
  ·
    refine ⟨Wv * φ, Wv * (WS * φ), ?_, rfl, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul W1, map_mulAut_mul C, map_mulAut_mul W0, map_mulAut_mul WS,
        map_conj_eq_of_le_B2Levi hcB hXe, map_mulAut_mul Wv]
      refine eq_of_le_rootSL2 hK (mem_rootFinset.1 (by decide +kernel) : IsRoot .F4 v0121) ?_ ?_
        (hcard _ _) (hcard3 _ _ _ |>.trans rfl |> fun h => by rw [card_map_mulAut]; exact h)
      · have h2 := map_wRep_le_rootSL2 (K := K) [3, 2, 1, 0] isRoot_rootS hS
        rwa [show wordAct [3, 2, 1, 0] rootS = v0121 by decide +kernel] at h2
      · have h2 := map_wRep_le_rootSL2 (K := K) [3, 2] hr0110 hE3
        rwa [show wordAct [3, 2] v0110 = v0121 by decide +kernel] at h2
    · rw [map_mulAut_mul Wv, map_mulAut_mul Wv, map_mulAut_mul WS, hTS]
    · rw [map_mulAut_mul Wv, hφ, map_graphAutF4_B2Levi, hv]
      exact Subgroup.map_mono hAB
    · rw [map_mulAut_mul Wv, map_mulAut_mul WS, hφ, map_graphAutF4_B2Levi, hv]
      exact Subgroup.map_mono hAS
  ·
    refine ⟨Wf * (C * (W0 * (WS * φ))), Wf * (C * (W0 * φ)), ?_, rfl, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul Wf, map_mulAut_mul C, map_mulAut_mul W0, map_mulAut_mul WS,
        map_conj_eq_of_le_B2Levi hcB hXe, map_mulAut_mul Wv, map_mulAut_mul WS]
      refine eq_of_le_rootSL2 hK (mem_rootFinset.1 (by decide +kernel) : IsRoot .F4 v1221) ?_ ?_
        (by rw [card_map_mulAut, hcard3]) (by rw [card_map_mulAut, hcard])
      · have h2 := map_wRep_le_rootSL2 (K := K) [0, 3, 2, 1] hr0110 hE3
        rwa [show wordAct [0, 3, 2, 1] v0110 = v1221 by decide +kernel] at h2
      · have h2 := map_wRep_le_rootSL2 (K := K) [3, 2, 1, 2, 3] isRoot_rootS hS
        rw [show wordAct [3, 2, 1, 2, 3] rootS = v1110 by decide +kernel] at h2
        have h3 := map_wRep_le_rootSL2 (K := K) [3, 2, 1, 0] hr1110 h2
        rwa [show wordAct [3, 2, 1, 0] v1110 = v1221 by decide +kernel] at h3
    · rw [map_mulAut_mul Wf, map_mulAut_mul C, map_mulAut_mul W0, map_mulAut_mul WS, hTS,
        map_mulAut_mul Wf, map_mulAut_mul C, map_mulAut_mul W0]
    · rw [map_mulAut_mul Wf, map_mulAut_mul C, map_mulAut_mul W0, map_mulAut_mul WS, hφ,
        map_graphAutF4_B2Levi, hf]
      refine Subgroup.map_mono ?_
      rw [← map_conj_eq_of_le_B2Levi hcB hAB]
      exact Subgroup.map_mono hA0S
    · rw [map_mulAut_mul Wf, map_mulAut_mul C, map_mulAut_mul W0, hφ, map_graphAutF4_B2Levi, hf]
      refine Subgroup.map_mono ?_
      rw [← map_conj_eq_of_le_B2Levi hcB hAB]
      exact Subgroup.map_mono hA0
  ·
    refine ⟨Wf * (C * φ), Wf, ?_, ?_, ?_, ?_, ?_⟩
    · rw [map_mulAut_mul Wf, map_mulAut_mul C, map_mulAut_mul Wf, map_mulAut_mul C,
        map_mulAut_mul W0, hX0]
    · rw [map_mulAut_mul Wu]
      refine eq_of_le_rootSL2 hK (mem_rootFinset.1 (by decide +kernel) : IsRoot .F4 v1242) ?_ ?_
        (by rw [card_map_mulAut, hX₀]) (hcard _ _)
      · have h2 := map_wRep_le_rootSL2 (K := K) [0, 3, 2, 1] isRoot_rootR hXr
        rwa [show wordAct [0, 3, 2, 1] rootR = v1242 by decide +kernel] at h2
      · have h2 := map_wRep_le_rootSL2 (K := K) [0, 1, 2, 1, 0] isRoot_rootR hXr
        rw [show wordAct [0, 1, 2, 1, 0] rootR = root0122 by decide +kernel] at h2
        have h3 := map_wRep_le_rootSL2 (K := K) [0, 1, 2, 3] isRoot_root0122 h2
        rwa [show wordAct [0, 1, 2, 3] root0122 = v1242 by decide +kernel] at h3
    · rw [map_mulAut_mul Wf, map_mulAut_mul C, hc]
    · rw [map_mulAut_mul Wf, map_mulAut_mul C, hφ, map_graphAutF4_B2Levi,
        map_conj_eq_of_le_B2Levi hcB le_rfl, hf]
      exact Subgroup.map_mono hAB
    · rw [hf]
      exact Subgroup.map_mono hAB

end Chains

section Assembly

theorem twoModelEdge_symm {X₀ xPP bPP A : Subgroup (adjointGroup .F4 K)}
    {ψ ψ' : MulAut (adjointGroup .F4 K)} (h : TwoModelEdge X₀ xPP bPP A ψ ψ') :
    TwoModelEdge X₀ xPP bPP A ψ' ψ := by
  obtain ⟨ψ₁, ψ₂, h1, h2, hT, hA1, hA2⟩ := h
  exact ⟨ψ₂, ψ₁, h2, h1, hT.symm, hA2, hA1⟩

theorem transGen_swap_of_symm {α : Type*} {r : α → α → Prop} (hr : ∀ x y, r x y → r y x)
    {a b : α} (h : Relation.TransGen r a b) : Relation.TransGen r b a := by
  induction h with
  | single h => exact Relation.TransGen.single (hr _ _ h)
  | tail _ hbc ih => exact Relation.TransGen.head (hr _ _ hbc) ih

theorem levi_le_map_C3Levi_W (i : Fin (Tag.rank .F4)) (j : Fin (Tag.rank .F4)) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (hj : j ≠ 0)
    (hij : wordAct [0, 1, 2, 3] (wordAct [0, 1, 2, 1, 0] (s • Pi.single j 1)) = Pi.single i 1) :
    CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup {i} ≤
      (C3Levi K).map (MulAut.conj (wRep K [0, 1, 2, 3]) *
        MulAut.conj (wRep K [0, 1, 2, 1, 0])).toMonoidHom := by
  have hβ : IsRoot .F4 (s • Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) := by
    rcases hs with rfl | rfl
    · rw [one_smul]
      exact isRoot_single .F4 j
    · rw [neg_one_smul]
      exact isRoot_neg_single .F4 j
  have hβ' : IsRoot .F4 (wordAct [0, 1, 2, 1, 0] (s • Pi.single j 1)) := by
    rw [← wordW_smul_eq_wordAct]
    exact IsRoot.smul hβ _
  have hC : ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ → γ 0 = 0 →
      (Adjoint.f4Datum K).rootGroup γ ≤ C3Levi K := fun γ hγ h0 =>
    rootGroup_le_C3Levi ⟨hγ, h0⟩
  have h0 : (s • Pi.single j 1 : Fin (Tag.rank .F4) → ℤ) 0 = 0 := by
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
  rw [levi_singleton_eq, map_mulAut_mul, ← hij, ← rootGroups_map_wRep _ hβ',
    ← rootGroups_map_wRep _ hβ]
  refine Subgroup.map_mono (Subgroup.map_mono (sup_le (hC _ hβ h0) (hC _ (IsRoot.neg hβ) ?_)))
  rw [Pi.neg_apply, h0, neg_zero]

theorem twoChainModelInput_holds : TwoChainModelInput := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀
  have hXr : X₀ ≤ rootSL2 K rootR := by
    rw [rootSL2_rootR, ← highestRootRankOne_eq_rootSL2R]
    exact hXJ
  obtain ⟨c, hcB12, hc⟩ := exists_conj_std hK hXJ hcyc hX₀
  have hcB : c ∈ centralizer (B2Levi K : Set (adjointGroup .F4 K)) :=
    B12_le_centralizer_B2Levi hcB12
  refine ⟨stdX K, stdB K, twoStdPairFacts_std K hK,
    transGen_levi_one hK hXr hX₀ hcB hc, transGen_levi_two hK hXr hX₀ hcB hc,
    MulAut.conj (wRep K [0, 1, 2, 3]) * MulAut.conj (wRep K [0, 1, 2, 1, 0]), ?_, ?_,
    transGen_levi_zero hK hXr hX₀ hcB hc,
    transGen_swap_of_symm (fun _ _ => twoModelEdge_symm)
      (transGen_levi_three_aux hK hXr hX₀ hcB hc)⟩
  · exact levi_le_map_C3Levi_W 0 1 1 (Or.inl rfl) (by decide) (by decide +kernel)
  · exact levi_le_map_C3Levi_W 3 3 (-1) (Or.inr rfl) (by decide) (by decide +kernel)

end Assembly

end CFSG.SeitzReduction.F4Pilot
