module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

omit [Finite H] in
theorem S_le_M : elemBaumannIn 2 R ≤ M := (elemBaumannIn_le 2 R).trans h.le_M

theorem exists_P (i : Fin r) :
    ∃ P : Subgroup H, elemBaumannIn 2 R ≤ P ∧ P ≤ h.Yi i ⊔ elemBaumannIn 2 R ∧ ¬ P ≤ M ∧
      ∀ Y : Subgroup H, elemBaumannIn 2 R ≤ Y → Y < P → Y ≤ M := by
  let 𝒮 : Set (Subgroup H) := {P | elemBaumannIn 2 R ≤ P ∧ P ≤ h.Yi i ⊔ elemBaumannIn 2 R ∧ ¬ P ≤ M}
  have hne : 𝒮.Nonempty := ⟨h.Yi i ⊔ elemBaumannIn 2 R, le_sup_right, le_rfl, fun hle =>
    h.Yi_not_le_M i (le_sup_left.trans hle)⟩
  obtain ⟨P, hP, hmin⟩ := wellFounded_lt.has_min 𝒮 hne
  refine ⟨P, hP.1, hP.2.1, hP.2.2, fun Y hSY hYP => ?_⟩
  by_contra hYM
  exact hmin Y ⟨hSY, hYP.le.trans hP.2.1, hYM⟩ hYP

theorem S_ne_bot : elemBaumannIn 2 R ≠ ⊥ := by
  obtain ⟨t, ht⟩ := h.exists_t
  intro hb
  have hR1 : R ≠ ⊥ := fun hb' => h.nonnormal (by rw [hb']; exact Subgroup.normal_bot)
  have hJne : thompsonJ R ≠ ⊥ := thompsonJ_ne_bot h.sylow.2.1 hR1
  exact hJne (le_bot_iff.mp (hb ▸ thompsonJ_le_baumann))

theorem charTwo_NS (hchar : CharTwo (⊤ : Subgroup H)) :
    CharTwo (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) :=
  CharTwo.of_normal hchar le_top (h.NS_normal.subgroupOf _)

theorem Q0_le_S : blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ≤
    elemBaumannIn 2 R := by
  obtain ⟨t, hTC⟩ := internal_S3_wreath_transfer h
  exact hTC.syl_S.pCoreOf_le

structure IsSelected (i : Fin r) (P : Subgroup H) : Prop where
  S_le : elemBaumannIn 2 R ≤ P
  P_le : P ≤ h.Yi i ⊔ elemBaumannIn 2 R
  not_le_M : ¬ P ≤ M
  minimal : ∀ Y : Subgroup H, elemBaumannIn 2 R ≤ Y → Y < P → Y ≤ M

variable {h} {i : Fin r} {P : Subgroup H} (hP : h.IsSelected i P)

include hP

omit [Finite H] in
theorem IsSelected.S_lt : elemBaumannIn 2 R < P :=
  lt_of_le_of_ne hP.S_le fun e => hP.not_le_M (e ▸ h.S_le_M)

omit [Finite H] in
theorem IsSelected.PM_lt : P ⊓ M < P :=
  lt_of_le_of_ne inf_le_left fun e => hP.not_le_M (e ▸ inf_le_right)

omit [Finite H] in
theorem IsSelected.max : ∀ Y : Subgroup H, elemBaumannIn 2 R ≤ Y → Y < P → Y ≤ P ⊓ M :=
  fun Y hY hYP => le_inf hYP.le (hP.minimal Y hY hYP)

omit [Finite H] in
theorem IsSelected.sup_R : P ⊔ R = ⊤ := by
  by_contra hne
  have hlt : P ⊔ R < ⊤ := lt_top_iff_ne_top.mpr hne
  exact hP.not_le_M (le_sup_left.trans (h.M_max _ le_sup_right hlt))

theorem IsSelected.not_le_normalizer :
    ¬ P ≤ Subgroup.normalizer ((elemBaumannIn 2 R : Subgroup H) : Set H) := by
  intro hPn
  have hSR : elemBaumannIn 2 R ≤ R := elemBaumannIn_le 2 R
  have hchar := characteristic_elemBaumannIn R
  have hRn : R ≤ Subgroup.normalizer ((elemBaumannIn 2 R : Subgroup H) : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSR).mp inferInstance
  have hSn : (elemBaumannIn 2 R).Normal := by
    refine Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp ?_)
    rw [← hP.sup_R]
    exact sup_le hPn hRn
  have hS2 : IsPGroup 2 (elemBaumannIn 2 R) := h.sylow.isPGroup.to_le hSR
  have hSQ : elemBaumannIn 2 R ≤ CFSG.pCore 2 H := le_sSup ⟨hSn, hS2⟩
  apply h.J_not_le_centralizer
  exact ((thompsonJ_le_baumann (R := R)).trans hSQ).trans h.frattini.2.2.1

theorem IsSelected.noChar_P (hnoChar : NoCharNormal R ⊤) : NoCharNormal (elemBaumannIn 2 R) P :=
  NoCharNormal.of_sup_eq_top (elemBaumannIn_le 2 R) (characteristic_elemBaumannIn R) hP.sup_R
    hnoChar

omit [Finite H] in
theorem IsSelected.P_le_NS : P ≤ oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R :=
  hP.P_le.trans (sup_le ((h.Yi_le_N i).trans le_sup_left) le_sup_right)

theorem IsSelected.sylow_P : IsSylowTwoOf (elemBaumannIn 2 R) P := by
  obtain ⟨t, hTC⟩ := internal_S3_wreath_transfer h
  have hS := hTC.syl_S
  refine ⟨hP.S_le, hS.2.1, ?_⟩
  intro hdvd
  apply hS.2.2
  have h1 := Subgroup.relIndex_mul_relIndex (elemBaumannIn 2 R) P _ hP.S_le hP.P_le_NS
  show 2 ∣ (elemBaumannIn 2 R).relIndex _
  rw [← h1]
  exact Dvd.dvd.mul_right hdvd _

theorem IsSelected.charTwo_P (hchar : CharTwo (⊤ : Subgroup H)) : CharTwo P := by
  have hNS := h.charTwo_NS hchar
  have hQ0S := h.Q0_le_S
  have hPNS := hP.P_le_NS
  have hQP : blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ≤ P :=
    hQ0S.trans hP.S_le
  have hnormal : ((blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).subgroupOf
      P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr (hPNS.trans (le_normalizer_blockQ _))
  have hQ0P : blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ≤
      CFSG.Open.pCoreOf 2 P :=
    CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hQP hnormal
      (isPGroup_blockQ _)
  rintro x ⟨hxP, hxc⟩
  have hx : x ∈ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer ((blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) :
        Subgroup H) : Set H) :=
    ⟨hPNS hxP, Subgroup.centralizer_le (by exact_mod_cast hQ0P) hxc⟩
  exact hQ0P (hNS hx)

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
