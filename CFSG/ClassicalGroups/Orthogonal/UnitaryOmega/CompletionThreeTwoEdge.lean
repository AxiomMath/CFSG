module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeTwoRho
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.QTwoTransporter

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {ω : K} (hω : IsTraceNormOne E ω)
  {H : Type} [Group H] {t : Equiv.Perm (Fin 4) →* H} {κ : normOmega E 3 →* H}

private theorem qTwoYCast_mem_normBlock_zero_one_two :
    qTwoYCast E hω ∈ normBlock E 4 {0, 1, 2} := by
  have hmem : qTwoYCast E hω ∈ (normOmegaCast E (Nat.le_succ 3)).range :=
    ⟨qTwoY E hω, rfl⟩
  have hset : (Finset.univ.erase (Fin.last 3) : Finset (Fin 4)) = {0, 1, 2} := by decide
  rw [qTwoYCast, range_normOmegaCast_succ E 3, hset] at hmem
  exact hmem

private noncomputable def edgeF : spinGroup (quadPlus 5 F) →* normOmega E 4 :=
  (MulAut.conj (qTwoYCast E hω)).toMonoidHom.comp (qTwoLambda E hω).symm.toMonoidHom

private theorem edgeF_apply (x : spinGroup (quadPlus 5 F)) :
    edgeF E hω x =
      qTwoYCast E hω * (qTwoLambda E hω).symm x * (qTwoYCast E hω)⁻¹ := by
  simp only [edgeF, MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]

private noncomputable abbrev edgeIncl (j : Fin 5) (hj : j ∈ ({1, 2} : Finset (Fin 5))) :
    rankOne (plusRootGroup 5 F (by norm_num)) j →*
      levi (plusRootGroup 5 F (by norm_num)) {1, 2} :=
  Subgroup.inclusion (rankOne_le_levi (plusRootGroup 5 F (by norm_num)) hj)

private noncomputable def edgeC (t : Equiv.Perm (Fin 4) →* H) (κ : normOmega E 3 →* H) : H :=
  deletionPhiThree E t κ {0, 1, 2} (by decide)
    ⟨qTwoYCast E hω, qTwoYCast_mem_normBlock_zero_one_two E hω⟩

private theorem edgeC_eq_kappa
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y) :
    edgeC E hω t κ = κ (qTwoY E hω) := by
  rw [edgeC]
  exact deletionPhiThree_normOmegaCast (E := E) (t := t) (κ := κ) hT1 hC
    (S := {0, 1, 2}) (by decide) (by decide) (qTwoY E hω)
    (qTwoYCast_mem_normBlock_zero_one_two E hω)

private theorem levi_le_comap_edgeF :
    levi (plusRootGroup 5 F (by norm_num)) {1, 2} ≤
      (normBlock E 4 {0, 1, 3}).comap (edgeF E hω) := by
  classical
  have h35 : 3 ≤ 5 := by norm_num
  refine iSup₂_le fun j hj => ?_
  rw [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · intro x hx
    rw [Subgroup.mem_comap]
    have hf : edgeF E hω x = (qTwoLambda E hω).symm x := by
      rw [edgeF_apply]
      have hcomm := commute_qTwoYCast_map_rankOne_one (E := E) (hω := hω)
        ((qTwoLambda E hω).symm x) (Subgroup.mem_map_of_mem _ hx)
      rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hf]
    exact normBlock_mono E 4 (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 3})
      (map_rankOne_le_normBlock_zero_one E hω (by decide)
        (Subgroup.mem_map_of_mem _ hx))
  · intro x hx
    have h2 : rankOne (plusRootGroup 5 F h35) 2 ≤
        (normBlock E 4 {0, 1, 3}).comap (edgeF E hω) := by
      rw [rankOne_plusRootGroup_eq_sup (n := 5) h35 (2 : Fin 5)]
      refine sup_le ?_ ?_
      · rintro _ ⟨c, rfl⟩
        rw [Subgroup.mem_comap]
        obtain ⟨g₁, hg₁, g₂, hg₂, hfac, hcomm, hconj⟩ :=
          exists_factor_rootD_two (E := E) (hω := hω) (Multiplicative.toAdd c)
        rw [show Multiplicative.ofAdd (Multiplicative.toAdd c) = c from ofAdd_toAdd c] at hfac
        have hf : edgeF E hω (rootD F h35 (2 : Fin 5) c) =
            g₁ * (qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹) := by
          rw [edgeF_apply, hfac, ← mul_assoc, hcomm.eq]
          simp only [mul_assoc]
        rw [hf]
        exact mul_mem (normBlock_mono E 4 (by decide : ({3} : Finset (Fin 4)) ⊆ {0, 1, 3})
          hg₁) (normBlock_mono E 4 (by decide : ({0} : Finset (Fin 4)) ⊆ {0, 1, 3}) hconj)
      · rintro _ ⟨c, rfl⟩
        rw [Subgroup.mem_comap]
        obtain ⟨g₁, hg₁, g₂, hg₂, hfac, hcomm, hconj⟩ :=
          exists_factor_negRootD_two (E := E) (hω := hω) (Multiplicative.toAdd c)
        rw [show Multiplicative.ofAdd (Multiplicative.toAdd c) = c from ofAdd_toAdd c] at hfac
        have hf : edgeF E hω (negRootD F h35 (2 : Fin 5) c) =
            g₁ * (qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹) := by
          rw [edgeF_apply, hfac, ← mul_assoc, hcomm.eq]
          simp only [mul_assoc]
        rw [hf]
        exact mul_mem (normBlock_mono E 4 (by decide : ({3} : Finset (Fin 4)) ⊆ {0, 1, 3})
          hg₁) (normBlock_mono E 4 (by decide : ({0} : Finset (Fin 4)) ⊆ {0, 1, 3}) hconj)
    exact h2 hx

private noncomputable def edgePsi (t : Equiv.Perm (Fin 4) →* H) (κ : normOmega E 3 →* H) :
    levi (plusRootGroup 5 F (by norm_num)) {1, 2} →* H :=
  (MulAut.conj (edgeC E hω t κ)⁻¹).toMonoidHom.comp
    ((deletionPhiThree E t κ {0, 1, 3} (by decide)).comp
      (((edgeF E hω).comp (levi (plusRootGroup 5 F (by norm_num)) {1, 2}).subtype).codRestrict
        (normBlock E 4 {0, 1, 3}) (fun x => levi_le_comap_edgeF E hω x.2)))

private theorem edgePsi_apply (x : levi (plusRootGroup 5 F (by norm_num)) {1, 2}) :
    edgePsi E hω t κ x = (edgeC E hω t κ)⁻¹ *
      deletionPhiThree E t κ {0, 1, 3} (by decide)
        ⟨edgeF E hω x, levi_le_comap_edgeF E hω x.2⟩ * edgeC E hω t κ := by
  simp [edgePsi]
  exact congrArg _ (Subtype.ext rfl)

private theorem edgePhi013_factor
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {g₁ g₂ : normOmega E 4} (hg₁ : g₁ ∈ normBlock E 4 {3})
    (hg₂ : g₂ ∈ normBlock E 4 {2})
    (hconj : qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹ ∈ normBlock E 4 {0})
    (hP : g₁ * (qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹) ∈ normBlock E 4 {0, 1, 3}) :
    deletionPhiThree E t κ {0, 1, 3} (by decide)
        ⟨g₁ * (qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹), hP⟩ =
      deletionPhiThree E t κ {3} (by decide) ⟨g₁, hg₁⟩ *
        (edgeC E hω t κ * deletionPhiThree E t κ {2} (by decide) ⟨g₂, hg₂⟩ *
          (edgeC E hω t κ)⁻¹) := by
  classical
  have hg₂Q : g₂ ∈ normBlock E 4 {0, 1, 2} :=
    normBlock_mono E 4 (by decide : ({2} : Finset (Fin 4)) ⊆ {0, 1, 2}) hg₂
  have huQ : qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹ ∈ normBlock E 4 {0, 1, 2} :=
    normBlock_mono E 4 (by decide : ({0} : Finset (Fin 4)) ⊆ {0, 1, 2}) hconj
  have hu : deletionPhiThree E t κ {0, 1, 3} (by decide)
        ⟨qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹,
          normBlock_mono E 4 (by decide : ({0} : Finset (Fin 4)) ⊆ {0, 1, 3}) hconj⟩ =
      edgeC E hω t κ * deletionPhiThree E t κ {2} (by decide) ⟨g₂, hg₂⟩ *
        (edgeC E hω t κ)⁻¹ := by
    rw [deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC
      (R := {0}) (S := {0, 1, 3}) (by decide) (by decide) (by decide) hconj]
    rw [← deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC
      (R := {0}) (S := {0, 1, 2}) (by decide) (by decide) (by decide) hconj]
    have harg : (⟨qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹, huQ⟩ :
        ↥(normBlock E 4 {0, 1, 2})) =
        ⟨qTwoYCast E hω, qTwoYCast_mem_normBlock_zero_one_two E hω⟩ *
          ⟨g₂, hg₂Q⟩ *
          ⟨qTwoYCast E hω, qTwoYCast_mem_normBlock_zero_one_two E hω⟩⁻¹ :=
      Subtype.ext rfl
    rw [harg]
    simp only [map_mul, map_inv, edgeC]
    rw [deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC
      (R := {2}) (S := {0, 1, 2}) (by decide) (by decide) (by decide) hg₂]
  have hsplit : (⟨g₁ * (qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹), hP⟩ :
      ↥(normBlock E 4 {0, 1, 3})) =
      ⟨g₁, normBlock_mono E 4 (by decide : ({3} : Finset (Fin 4)) ⊆ {0, 1, 3}) hg₁⟩ *
        ⟨qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹,
          normBlock_mono E 4 (by decide : ({0} : Finset (Fin 4)) ⊆ {0, 1, 3}) hconj⟩ :=
    Subtype.ext rfl
  rw [hsplit, map_mul]
  rw [deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC
      (R := {3}) (S := {0, 1, 3}) (by decide) (by decide) (by decide) hg₁, hu]

private theorem phi23_of_eq_mul
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {v g₁ g₂ : normOmega E 4} (hv : v ∈ normBlock E 4 {2, 3})
    (hg₁ : g₁ ∈ normBlock E 4 {3}) (hg₂ : g₂ ∈ normBlock E 4 {2}) (h : v = g₁ * g₂) :
    deletionPhiThree E t κ {2, 3} (by decide) ⟨v, hv⟩ =
      deletionPhiThree E t κ {3} (by decide) ⟨g₁, hg₁⟩ *
        deletionPhiThree E t κ {2} (by decide) ⟨g₂, hg₂⟩ := by
  subst h
  have harg : (⟨g₁ * g₂, hv⟩ : ↥(normBlock E 4 {2, 3})) =
      ⟨g₁, normBlock_mono E 4 (by decide : ({3} : Finset (Fin 4)) ⊆ {2, 3}) hg₁⟩ *
        ⟨g₂, normBlock_mono E 4 (by decide : ({2} : Finset (Fin 4)) ⊆ {2, 3}) hg₂⟩ :=
    Subtype.ext rfl
  rw [harg, map_mul]
  rw [deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC
      (R := {3}) (S := {2, 3}) (by decide) (by decide) (by decide) hg₁,
    deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC
      (R := {2}) (S := {2, 3}) (by decide) (by decide) (by decide) hg₂]

private theorem edgePsi_eq_of_factor
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (hR2 : ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ a) (t (Equiv.swap 2 3) * κ b * (t (Equiv.swap 2 3))⁻¹))
    (x : rankOne (plusRootGroup 5 F (by norm_num)) 2)
    {g₁ g₂ : normOmega E 4}
    (hg₁ : g₁ ∈ normBlock E 4 {3}) (hg₂ : g₂ ∈ normBlock E 4 {2})
    (hfac : (qTwoLambda E hω).symm x = g₁ * g₂)
    (hcomm : Commute (qTwoYCast E hω) g₁)
    (hconj : qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹ ∈ normBlock E 4 {0}) :
    edgePsi E hω t κ (edgeIncl 2 (by decide) x) =
      qTwoRho E hω t κ 2 x := by
  classical
  obtain ⟨b, hb, hb_eq⟩ :=
    exists_deletionPhiThree_singleton_three (E := E) (t := t) (κ := κ) hT1 hC hg₁
  have hcΦ : Commute (edgeC E hω t κ)
      (deletionPhiThree E t κ {3} (by decide) ⟨g₁, hg₁⟩) := by
    rw [edgeC_eq_kappa (E := E) (hω := hω) (t := t) (κ := κ) hT1 hC, hb_eq]
    exact hR2 (qTwoY E hω) (qTwoY_mem_normPureBlock E hω) b hb
  have hcΦ' : (edgeC E hω t κ)⁻¹ *
      deletionPhiThree E t κ {3} (by decide) ⟨g₁, hg₁⟩ * edgeC E hω t κ =
      deletionPhiThree E t κ {3} (by decide) ⟨g₁, hg₁⟩ := by
    rw [hcΦ.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hRHS : qTwoRho E hω t κ 2 x =
      deletionPhiThree E t κ {3} (by decide) ⟨g₁, hg₁⟩ *
        deletionPhiThree E t κ {2} (by decide) ⟨g₂, hg₂⟩ := by
    rw [qTwoRho_of_two_le (E := E) (hω := hω) (t := t) (κ := κ) (k := 2) (by decide) x]
    exact phi23_of_eq_mul (E := E) (t := t) (κ := κ) hT1 hC _ hg₁ hg₂ hfac
  have hf : edgeF E hω (edgeIncl 2 (by decide) x) =
      g₁ * (qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹) := by
    rw [edgeF_apply, Subgroup.coe_inclusion, hfac, ← mul_assoc, hcomm.eq]
    simp only [mul_assoc]
  have hP : g₁ * (qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹) ∈ normBlock E 4 {0, 1, 3} :=
    mul_mem (normBlock_mono E 4 (by decide : ({3} : Finset (Fin 4)) ⊆ {0, 1, 3}) hg₁)
      (normBlock_mono E 4 (by decide : ({0} : Finset (Fin 4)) ⊆ {0, 1, 3}) hconj)
  rw [hRHS, edgePsi_apply]
  have hsub : (⟨edgeF E hω (Subgroup.inclusion
      (rankOne_le_levi (plusRootGroup 5 F (by norm_num)) (j := 2)
        (J := ({1, 2} : Finset (Fin 5))) (by decide)) x),
      levi_le_comap_edgeF E hω (Subgroup.inclusion
        (rankOne_le_levi (plusRootGroup 5 F (by norm_num)) (j := 2)
          (J := ({1, 2} : Finset (Fin 5))) (by decide)) x).2⟩ :
        ↥(normBlock E 4 {0, 1, 3})) =
      ⟨g₁ * (qTwoYCast E hω * g₂ * (qTwoYCast E hω)⁻¹), hP⟩ := by
    apply Subtype.ext
    exact hf
  rw [hsub, edgePhi013_factor (E := E) (hω := hω) (t := t) (κ := κ) hT1 hC
    hg₁ hg₂ hconj hP]
  rw [show (edgeC E hω t κ)⁻¹ *
      (deletionPhiThree E t κ {3} (by decide) ⟨g₁, hg₁⟩ *
        (edgeC E hω t κ * deletionPhiThree E t κ {2} (by decide) ⟨g₂, hg₂⟩ *
          (edgeC E hω t κ)⁻¹)) * edgeC E hω t κ =
      ((edgeC E hω t κ)⁻¹ * deletionPhiThree E t κ {3} (by decide) ⟨g₁, hg₁⟩ *
        edgeC E hω t κ) * deletionPhiThree E t κ {2} (by decide) ⟨g₂, hg₂⟩ from by group]
  rw [hcΦ']

private theorem rootD_two_mem_rankOne (c : Multiplicative F) :
    rootD F (by norm_num) (2 : Fin 5) c ∈
      rankOne (plusRootGroup 5 F (by norm_num)) 2 := by
  rw [rankOne_plusRootGroup_eq_sup (n := 5) (by norm_num) (2 : Fin 5)]
  exact Subgroup.mem_sup_left ⟨c, rfl⟩

private theorem negRootD_two_mem_rankOne (c : Multiplicative F) :
    negRootD F (by norm_num) (2 : Fin 5) c ∈
      rankOne (plusRootGroup 5 F (by norm_num)) 2 := by
  rw [rankOne_plusRootGroup_eq_sup (n := 5) (by norm_num) (2 : Fin 5)]
  exact Subgroup.mem_sup_right ⟨c, rfl⟩

private theorem edgePsi_rootD_two
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (hR2 : ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ a) (t (Equiv.swap 2 3) * κ b * (t (Equiv.swap 2 3))⁻¹))
    (c : Multiplicative F) :
    edgePsi E hω t κ (edgeIncl 2 (by decide)
        (⟨rootD F (by norm_num) (2 : Fin 5) c, rootD_two_mem_rankOne c⟩ :
            rankOne (plusRootGroup 5 F (by norm_num)) 2)) =
      qTwoRho E hω t κ 2
        (⟨rootD F (by norm_num) (2 : Fin 5) c, rootD_two_mem_rankOne c⟩ :
            rankOne (plusRootGroup 5 F (by norm_num)) 2) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hfac, hcomm, hconj⟩ :=
    exists_factor_rootD_two (E := E) (hω := hω) (Multiplicative.toAdd c)
  rw [show Multiplicative.ofAdd (Multiplicative.toAdd c) = c from ofAdd_toAdd c] at hfac
  exact edgePsi_eq_of_factor (E := E) (hω := hω) (t := t) (κ := κ) hT1 hC hR2
    (x := ⟨rootD F (by norm_num) (2 : Fin 5) c, rootD_two_mem_rankOne c⟩)
    hg₁ hg₂ hfac hcomm hconj

private theorem edgePsi_negRootD_two
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (hR2 : ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ a) (t (Equiv.swap 2 3) * κ b * (t (Equiv.swap 2 3))⁻¹))
    (c : Multiplicative F) :
    edgePsi E hω t κ (edgeIncl 2 (by decide)
        (⟨negRootD F (by norm_num) (2 : Fin 5) c, negRootD_two_mem_rankOne c⟩ :
            rankOne (plusRootGroup 5 F (by norm_num)) 2)) =
      qTwoRho E hω t κ 2
        (⟨negRootD F (by norm_num) (2 : Fin 5) c, negRootD_two_mem_rankOne c⟩ :
            rankOne (plusRootGroup 5 F (by norm_num)) 2) := by
  obtain ⟨g₁, hg₁, g₂, hg₂, hfac, hcomm, hconj⟩ :=
    exists_factor_negRootD_two (E := E) (hω := hω) (Multiplicative.toAdd c)
  rw [show Multiplicative.ofAdd (Multiplicative.toAdd c) = c from ofAdd_toAdd c] at hfac
  exact edgePsi_eq_of_factor (E := E) (hω := hω) (t := t) (κ := κ) hT1 hC hR2
    (x := ⟨negRootD F (by norm_num) (2 : Fin 5) c, negRootD_two_mem_rankOne c⟩)
    hg₁ hg₂ hfac hcomm hconj

private theorem edgePsi_two
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (hR2 : ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ a) (t (Equiv.swap 2 3) * κ b * (t (Equiv.swap 2 3))⁻¹))
    (x : rankOne (plusRootGroup 5 F (by norm_num)) 2) :
    edgePsi E hω t κ (edgeIncl 2 (by decide) x) =
      qTwoRho E hω t κ 2 x := by
  classical
  let f : rankOne (plusRootGroup 5 F (by norm_num)) 2 →* H :=
    (edgePsi E hω t κ).comp (edgeIncl 2 (by decide))
  let g : rankOne (plusRootGroup 5 F (by norm_num)) 2 →* H := qTwoRho E hω t κ 2
  have hgen : rankOne (plusRootGroup 5 F (by norm_num)) 2 ≤
      (MonoidHom.eqLocus f g).map
        (rankOne (plusRootGroup 5 F (by norm_num)) 2).subtype := by
    conv_lhs => rw [rankOne_plusRootGroup_eq_sup (n := 5) (by norm_num) (2 : Fin 5)]
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      exact ⟨⟨rootD F (by norm_num) (2 : Fin 5) c, rootD_two_mem_rankOne c⟩,
        edgePsi_rootD_two (E := E) (hω := hω) (t := t) (κ := κ) hT1 hC hR2 c, rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact ⟨⟨negRootD F (by norm_num) (2 : Fin 5) c, negRootD_two_mem_rankOne c⟩,
        edgePsi_negRootD_two (E := E) (hω := hω) (t := t) (κ := κ) hT1 hC hR2 c, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hgen x.2
  rw [← Subtype.ext hzx]
  exact hz

private theorem edgePsi_one
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (x : rankOne (plusRootGroup 5 F (by norm_num)) 1) :
    edgePsi E hω t κ (edgeIncl 1 (by decide) x) =
      qTwoRho E hω t κ 1 x := by
  classical
  have hj1 : ((1 : Fin 5) : ℕ) < 2 := by decide
  have hcomm := commute_qTwoYCast_map_rankOne_one (E := E) (hω := hω)
    ((qTwoLambda E hω).symm x) (Subgroup.mem_map_of_mem _ x.2)
  have hf : edgeF E hω (edgeIncl 1 (by decide) x) =
      (qTwoLambda E hω).symm x := by
    rw [edgeF_apply, Subgroup.coe_inclusion, hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hg01 : (qTwoLambda E hω).symm x ∈ normBlock E 4 {0, 1} :=
    map_rankOne_le_normBlock_zero_one E hω hj1 (Subgroup.mem_map_of_mem _ x.2)
  have hcommC : Commute (edgeC E hω t κ)
      (deletionPhiThree E t κ {0, 1} (by decide)
        ⟨(qTwoLambda E hω).symm x, hg01⟩) := by
    have hsub : Commute
        (⟨qTwoYCast E hω, qTwoYCast_mem_normBlock_zero_one_two E hω⟩ :
          ↥(normBlock E 4 {0, 1, 2}))
        ⟨(qTwoLambda E hω).symm x, normBlock_mono E 4
          (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2}) hg01⟩ :=
      Subtype.ext hcomm.eq
    have hone : Commute (edgeC E hω t κ)
        (deletionPhiThree E t κ {0, 1, 2} (by decide)
          ⟨(qTwoLambda E hω).symm x, normBlock_mono E 4
            (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 2}) hg01⟩) :=
      hsub.map (deletionPhiThree E t κ {0, 1, 2} (by decide))
    rw [← deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC
      (R := {0, 1}) (S := {0, 1, 2}) (by decide) (by decide) (by decide) hg01]
    exact hone
  have hcΦ' : (edgeC E hω t κ)⁻¹ *
      deletionPhiThree E t κ {0, 1} (by decide) ⟨(qTwoLambda E hω).symm x, hg01⟩ *
        edgeC E hω t κ =
      deletionPhiThree E t κ {0, 1} (by decide) ⟨(qTwoLambda E hω).symm x, hg01⟩ := by
    rw [hcommC.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  rw [qTwoRho_of_lt_two (E := E) (hω := hω) (t := t) (κ := κ) (k := 1) hj1 x,
    edgePsi_apply]
  have hsub : (⟨edgeF E hω (Subgroup.inclusion
      (rankOne_le_levi (plusRootGroup 5 F (by norm_num)) (j := 1)
        (J := ({1, 2} : Finset (Fin 5))) (by decide)) x),
      levi_le_comap_edgeF E hω (Subgroup.inclusion
        (rankOne_le_levi (plusRootGroup 5 F (by norm_num)) (j := 1)
          (J := ({1, 2} : Finset (Fin 5))) (by decide)) x).2⟩ :
        ↥(normBlock E 4 {0, 1, 3})) =
      ⟨(qTwoLambda E hω).symm x, normBlock_mono E 4
        (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 3}) hg01⟩ := by
    apply Subtype.ext
    exact hf
  rw [hsub]
  rw [show deletionPhiThree E t κ {0, 1, 3} (by decide)
      ⟨(qTwoLambda E hω).symm x, normBlock_mono E 4
        (by decide : ({0, 1} : Finset (Fin 4)) ⊆ {0, 1, 3}) hg01⟩ =
      deletionPhiThree E t κ {0, 1} (by decide) ⟨(qTwoLambda E hω).symm x, hg01⟩ from
    deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC
      (R := {0, 1}) (S := {0, 1, 3}) (by decide) (by decide) (by decide) hg01]
  exact hcΦ'

theorem exists_levi_hom_one_two
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (hR2 : ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ a) (t (Equiv.swap 2 3) * κ b * (t (Equiv.swap 2 3))⁻¹)) :
    ∃ ψ : levi (plusRootGroup 5 F (by norm_num)) {1, 2} →* H,
      ∀ j (hj : j ∈ ({1, 2} : Finset (Fin 5)))
        (x : rankOne (plusRootGroup 5 F (by norm_num)) j),
        ψ (Subgroup.inclusion (rankOne_le_levi _ hj) x) = qTwoRho E hω t κ j x := by
  refine ⟨edgePsi E hω t κ, ?_⟩
  intro j hj x
  rw [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact edgePsi_one (E := E) (hω := hω) (t := t) (κ := κ) hT1 hC x
  · exact edgePsi_two (E := E) (hω := hω) (t := t) (κ := κ) hT1 hC hR2 x

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
