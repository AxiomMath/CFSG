module

public import CFSG.LargeExtraspecial.AS35ESixEleven
public import CFSG.LargeExtraspecial.AS35DSixThreeE
public import CFSG.LargeExtraspecial.AS35EBender
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTheorem
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open
open scoped commutatorElement

namespace S14

@[expose] def AschbacherFiveNineTwoStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.SixFiveConcl →
    ∀ t ∈ S.DSet, ∀ c : G, c * (S.z * t) = S.z * t * c →
      c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = t

end S14

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem mem_DSet_of_mem_BSet_of_commute (hS : S.SixFourConcl)
    (h681 : ∀ s ∈ S.DSet, ∀ h : G, h * S.z * h⁻¹ ∈ S.DSet →
      s * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * s → s ≠ h * S.z * h⁻¹ → s ∈ S.DAt h)
    {b : G} (hb : b ∈ S.BSet) (hbz : b * S.z = S.z * b) (hne : b ≠ S.z) : b ∈ S.DSet := by
  obtain ⟨k, hk, hbk⟩ := hb
  rw [DAt_one] at hk
  have hzk : S.z ∈ S.DAt k := S.z_mem_DAt hS hk rfl
  have h1 : k⁻¹ * b * k ∈ S.DSet := S.mem_DAt.mp hbk
  have h2 : k⁻¹ * S.z * k⁻¹⁻¹ ∈ S.DSet := by
    rw [inv_inv]
    exact S.mem_DAt.mp hzk
  have hcomm : k⁻¹ * b * k * (k⁻¹ * S.z * k⁻¹⁻¹) = k⁻¹ * S.z * k⁻¹⁻¹ * (k⁻¹ * b * k) := by
    rw [inv_inv]
    calc k⁻¹ * b * k * (k⁻¹ * S.z * k) = k⁻¹ * (b * S.z) * k := by group
      _ = k⁻¹ * (S.z * b) * k := by rw [hbz]
      _ = k⁻¹ * S.z * k * (k⁻¹ * b * k) := by group
  have hne' : k⁻¹ * b * k ≠ k⁻¹ * S.z * k⁻¹⁻¹ := by
    rw [inv_inv]
    intro h
    apply hne
    calc b = k * (k⁻¹ * b * k) * k⁻¹ := by group
      _ = S.z := by rw [h]; group
  have h3 := S.conj_mem_DAt_mul (c := k) (h681 _ h1 k⁻¹ h2 hcomm hne')
  rwa [mul_inv_cancel, DAt_one, show k * (k⁻¹ * b * k) * k⁻¹ = b by group] at h3

theorem centralizer_le_BStab_of_mem_DSet (hS : S.SixFourConcl)
    (h69 : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g ⊆ S.BSet) (hzB : S.z ∈ S.BSet)
    {t : G} (ht : t ∈ S.DSet)
    (h59t : ∀ c : G, c * (S.z * t) = S.z * t * c → c * S.z * c⁻¹ = S.z ∨ c * S.z * c⁻¹ = t) :
    centralizer ({S.z * t} : Set G) ≤ S.BStab := by
  intro c hc
  rw [S.mem_BStab_iff hS h69 hzB]
  rcases h59t c (mem_centralizer_singleton_iff.mp hc) with h | h
  · rw [h]
    exact hzB
  · rw [h]
    exact S.DSet_subset_BSet hS ht

end Setting

namespace S14

open CFSG.ComponentClassification.AschbacherStrongEmbedding in
theorem aschbacherSixElevenStmt_of_fusion
    (h1 : AschbacherSixElevenFusionStmt)
    (h681 : AschbacherSixEightOneStmt) (h592 : AschbacherFiveNineTwoStmt) :
    AschbacherSixElevenStmt := by
  intro G _ _ S ih hS h65 h69 h610
  have hS4 := hS.sixFour
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS4 hS.hSet_nonempty
  have hzB : S.z ∈ S.BSet := by
    have := S.self_mem_BAt hS4 ⟨t, ht⟩ 1
    simpa using this
  have h69' : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g ⊆ S.BSet := fun g hg => (h69 g hg).le
  have hmem : ∀ x, x ∈ S.BStab ↔ x * S.z * x⁻¹ ∈ S.BSet := fun x =>
    S.mem_BStab_iff hS4 h69' hzB
  have hCent : ∀ t' : G, IsConj S.z t' → S.z * t' = t' * S.z → t' ≠ S.z →
      centralizer ({S.z * t'} : Set G) ≤ S.BStab := by
    intro t' htc htz hne
    have htM : t' ∈ S.M := S.mem_M_iff.mpr htz.symm
    obtain ⟨g, rfl⟩ := isConj_iff.mp htc
    have htX : g * S.z * g⁻¹ ∈ S.BStab := by
      rw [hmem, S.conj_z_of_mem_M htM]
      exact hzB
    have htB := h1 G S ih hS h65 h69 h610 g htX
    have htD := S.mem_DSet_of_mem_BSet_of_commute hS4 (h681 G S ih hS h65) htB htz.symm hne
    exact S.centralizer_le_BStab_of_mem_DSet hS4 h69' hzB htD (h592 G S hS h65 _ htD)
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨g₀, hg₀⟩ := hcon
  have hX : S.BStab ≠ ⊤ := fun h => hg₀ ((hmem g₀).mp (h ▸ mem_top g₀))
  have hzX : S.z ∈ S.BStab := (hmem S.z).mpr (by rwa [show S.z * S.z * S.z⁻¹ = S.z by group])
  have hBX : ∀ b ∈ S.BSet, b ∈ S.BStab := by
    intro b hb
    obtain ⟨c, rfl⟩ : ∃ c : G, c * S.z * c⁻¹ = b := by
      obtain ⟨k, -, hbk⟩ := hb
      exact S.exists_conj_of_mem_DAt hbk
    have hc : c ∈ S.BStab := (hmem c).mpr hb
    exact mul_mem (mul_mem hc hzX) (inv_mem hc)
  have huniq : ∀ g : G,
      S.z ∈ CFSG.BenderSuzuki.PFchapter1section1.rightConjugate S.BStab g ↔ g ∈ S.BStab := by
    intro g
    simp only [CFSG.BenderSuzuki.PFchapter1section1.rightConjugate, Subgroup.conjBy]
    constructor
    · rintro ⟨y, hy, hyz⟩
      have hy' : y = g * S.z * g⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hyz
        rw [← hyz]
        group
      rw [hy'] at hy
      exact (hmem g).mpr (h1 G S ih hS h65 h69 h610 g hy)
    · intro hg
      refine ⟨g * S.z * g⁻¹, hBX _ ((hmem g).mp hg), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  have hCPC : CentralProductCentralizer S.BStab S.z := by
    refine ⟨?_, ?_⟩
    · obtain ⟨P, hQP, hPM⟩ := S.exists_sylow_le_M
      refine ⟨P, hQP S.z_mem_QG, ?_⟩
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (S.mem_M_iff.mp (hPM y.2))
    · rintro t' ⟨g, rfl⟩ hc hne
      refine hCent _ (isConj_iff.mpr ⟨g⁻¹, ?_⟩) hc hne
      simp only [CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem, inv_inv]
  have h33 := (theorem_3_3 CFSG.ShultStronglyClosedTI.not_minimalInvolutionPointLocalFailure
    CFSG.ComponentClassification.AschbacherStrongEmbedding.benderDoubleCoverRigidity S.BStab S.z
    S.orderOf_z hX huniq).2.1 hCPC
  have h2r := S.two_le_twoRank hS4 ht
  rcases h33 with h1' | ⟨u, -, -, -, -, hSE, -⟩
  · have heq : CFSG.Open.twoRank S.zGen =
        CFSG.Open.twoRank (CFSG.ShultStronglyClosedTI.involutionPointHull S.z) := by
      rw [S.zGen_eq_involutionPointHull]
    exact absurd (h2r.trans (heq.trans_le h1')) (by norm_num)
  · rw [← S.zGen_eq_involutionPointHull, S.commutator_zGen_eq hS.simple hS.centralizer_eq] at hSE
    have := hS.simple
    obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht
    have htL : t ∈ S.zGen := hh ▸ S.conj_mem_zGen h
    have htM := S.mem_M_of_mem_ESet hS4 ht.1
    have htt : t * t = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
    have htz := S.ne_z_of_mem_ESet ht.1
    have hsolv := Asc77.isSolvable_centralizer_of_stronglyEmbedded hSE
      (a := ⟨S.z, S.z_mem_zGen⟩) (b := ⟨t, htL⟩)
      (Subtype.ext (by simp [pow_two, S.z_mul_z])) (Subtype.ext (by simp [pow_two, htt]))
      (fun h' => S.z_ne_one (congrArg Subtype.val h'))
      (fun h' => by
        have h3 : t = 1 := congrArg Subtype.val h'
        apply S.z_ne_one
        calc S.z = h⁻¹ * (h * S.z * h⁻¹) * h := by group
          _ = 1 := by rw [hh, h3]; group)
      (Subtype.ext (S.mem_M_iff.mp htM).symm)
      (fun h' => htz (congrArg Subtype.val h').symm)
      (x := ⟨S.z, S.z_mem_zGen⟩) (by rw [Subgroup.orderOf_mk, S.orderOf_z])
    exact S.not_isSolvable_M h65 (S.isSolvable_M_of hS.sup_eq_top hsolv)

@[expose] def AschbacherSixElevenFusionCoreStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), AschbacherBelow (Nat.card G) →
    S.SixHyp → S.SixFiveConcl →
    (∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g = S.BSet) →
    (∀ a ∈ S.BSet, ∀ b ∈ S.BSet, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)) →
    ∀ (hQX : S.QG ≤ S.BStab) (hMX : ∀ m ∈ S.M, ∀ y ∈ S.BStab, m * y * m⁻¹ ∈ S.BStab),
      S.BStab ≠ ⊤ → (S.restrict S.BStab hQX hMX).AschTwo →
        ∀ g : G, g * S.z * g⁻¹ ∈ S.BStab → g * S.z * g⁻¹ ∈ S.BSet

theorem aschbacherSixElevenFusionStmt_of_core (h : AschbacherSixElevenFusionCoreStmt) :
    AschbacherSixElevenFusionStmt := by
  intro G _ _ S ih hS h65 h69 h610 g hg
  have hS4 := hS.sixFour
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS4 hS.hSet_nonempty
  have hzB : S.z ∈ S.BSet := by
    have := S.self_mem_BAt hS4 ⟨t, ht⟩ 1
    simpa using this
  have h69' : ∀ g : G, g * S.z * g⁻¹ ∈ S.BSet → S.BAt g ⊆ S.BSet := fun g hg => (h69 g hg).le
  have hmem : ∀ x, x ∈ S.BStab ↔ x * S.z * x⁻¹ ∈ S.BSet := fun x =>
    S.mem_BStab_iff hS4 h69' hzB
  have hMX : S.M ≤ S.BStab := fun m hm => (hmem m).mpr (by rw [S.conj_z_of_mem_M hm]; exact hzB)
  have hQX : S.QG ≤ S.BStab := S.QG_le_M.trans hMX
  have hMX' : ∀ m ∈ S.M, ∀ y ∈ S.BStab, m * y * m⁻¹ ∈ S.BStab := fun m hm y hy =>
    mul_mem (mul_mem (hMX hm) hy) (inv_mem (hMX hm))
  by_cases hXtop : S.BStab = ⊤
  · exact (hmem g).mp (hXtop ▸ mem_top g)
  have hlt : Nat.card S.BStab < Nat.card G := by
    by_contra hle
    exact hXtop (Subgroup.eq_top_of_le_card _ (not_lt.mp hle))
  have hn := hS.three_le_width
  have hT := ih S.BStab hlt (S.restrict S.BStab hQX hMX')
    (by rw [S.restrict_width]; omega)
  refine h G S ih hS h65 h69 h610 hQX hMX' hXtop ?_ g hg
  rcases hT with h1 | h2 | ⟨t₁, ht₁Q, ht₁2, ht₁⟩ | ⟨g₁, hg₁Q, hg₁ne⟩
  ·
    exfalso
    obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet ht
    have hhM : h ∉ S.M := fun hM => S.ne_z_of_mem_ESet ht.1 (hh ▸ S.conj_z_of_mem_M hM)
    apply S.Qa_not_le_M hhM
    intro y hy
    have hyt : y * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * y := by
      rw [Setting.Qa_eq_map] at hy
      obtain ⟨q, hq, rfl⟩ := hy
      have := S.z_comm_QG hq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc h * q * h⁻¹ * (h * S.z * h⁻¹) = h * (q * S.z) * h⁻¹ := by group
        _ = h * (S.z * q) * h⁻¹ := by rw [this]
        _ = h * S.z * h⁻¹ * (h * q * h⁻¹) := by group
    have hyX : y ∈ S.BStab := by
      rw [hmem]
      refine ⟨h, by rw [Setting.DAt_one, hh]; exact ht, ?_⟩
      exact S.conj_mem_DAt_of_commute hyt (S.z_mem_DAt hS4 ht hh)
    have h3 := mem_center_iff.mp h1 ⟨y, hyX⟩
    rw [S.mem_M_iff]
    exact congrArg Subtype.val h3
  · exact h2
  · exact absurd (S.zInOTwo_restrict _ hQX hMX' (hS.zInOTwo _
      ((S.mem_restrict_QG _ hQX hMX').mp ht₁Q) (by rw [Subgroup.orderOf_coe]; exact ht₁2))) ht₁
  · exact absurd (Subtype.ext (hS.weak _ ((S.mem_restrict_QG _ hQX hMX').mp hg₁Q))) hg₁ne

end S14

end CFSG.LargeExtraspecial
