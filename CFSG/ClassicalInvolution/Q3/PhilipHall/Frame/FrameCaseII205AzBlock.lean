module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205HRow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf19Thm3A
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf42U3Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205HComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205HU33
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4 CFSG.Open
open scoped commutatorElement

section Quat

theorem exists_q8_hom_of_involution {Y : Type} [Group Y] {R₀ : Subgroup Y}
    (ψ : ↥R₀ ≃* QuaternionGroup 2) {ζ : Y} (hζR : ζ ∈ R₀) (hζ2 : ζ * ζ = 1) (hζ1 : ζ ≠ 1) :
    ∃ ι : QuaternionGroup 2 →* Y, (∀ q, ι q ∈ R₀) ∧ ι (QuaternionGroup.a 2) = ζ := by
  have hquat : ∀ q : QuaternionGroup 2, q * q = 1 → q ≠ 1 → q = QuaternionGroup.a 2 := by
    decide
  have hsq : ψ ⟨ζ, hζR⟩ * ψ ⟨ζ, hζR⟩ = 1 := by
    rw [← map_mul]
    have : (⟨ζ, hζR⟩ : ↥R₀) * ⟨ζ, hζR⟩ = 1 := Subtype.ext hζ2
    rw [this, map_one]
  have hne : ψ ⟨ζ, hζR⟩ ≠ 1 := by
    intro h
    apply hζ1
    have : (⟨ζ, hζR⟩ : ↥R₀) = 1 := ψ.injective (h.trans (map_one ψ).symm)
    exact congrArg Subtype.val this
  have hψ2 : ψ ⟨ζ, hζR⟩ = QuaternionGroup.a 2 := hquat _ hsq hne
  refine ⟨R₀.subtype.comp ψ.symm.toMonoidHom, fun q => (ψ.symm q).2, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
  rw [← hψ2, MulEquiv.symm_apply_apply]

end Quat

section Moved

theorem component_le_of_moved {Z : Type} [Group Z] [Finite Z] {T : Subgroup Z}
    (hT : T.IsSubnormal) {ζ : Z} (hζ : ζ ∈ T) {L : Subgroup Z} (hL : CFSG.IsComponent L)
    (hmov : ∃ y ∈ L, ζ * y ≠ y * ζ) : L ≤ T := by
  rcases CFSG.LocalCores.component_subnormal_subgroup hL hT with h | h
  · exact h
  · exfalso
    obtain ⟨y, hy, hne⟩ := hmov
    have h1 : ⁅y, ζ⁆ ∈ ⁅L, T⁆ := Subgroup.commutator_mem_commutator hy hζ
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hne h1.symm

end Moved


theorem hyp51_of_rows_block (hU : TL4.OuterFixedOddFree .PSU 3)
    (hM12 : TwinCentRes.ModelFactM12)
    (hM12fin : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12))
    (hM12nab : ∃ x y : CFSG.Blueprint.NativeSporadic.M12, x * y ≠ y * x)
    {Z Y : Type} [Group Z] [Finite Z] [Group Y] [Finite Y] {Ω : Set (Subgroup Y)}
    {P : Subgroup Y} (hrows : Thm3A.Thm3RowsA Ω P) {T : Subgroup Z}
    (F : ↥T →* (↥P ⧸ classicalInvolutionOddCore ↥P)) (hFs : Function.Surjective F)
    (hK : Odd (Nat.card F.ker)) {ζ : Z} (hζT : ζ ∈ T) {ζP : Y} (hζP : ζP ∈ P)
    (hFz : F ⟨ζ, hζT⟩ = QuotientGroup.mk' (classicalInvolutionOddCore ↥P) ⟨ζP, hζP⟩)
    (hq : ∃ ι : QuaternionGroup 2 →* Y, (∀ q, ι q ∈ P) ∧ ι (QuaternionGroup.a 2) = ζP)
    (hmoved : ∀ L : Subgroup Z, CFSG.IsComponent L → (∃ y ∈ L, ζ * y ≠ y * ζ) → L ≤ T) :
    (∀ L₁ L₂ : Subgroup Z, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, ζ * y ≠ y * ζ) → (∃ y ∈ L₂, ζ * y ≠ y * ζ) → L₁ = L₂) ∧
    (∀ L : Subgroup Z, CFSG.IsComponent L → (∃ y ∈ L, ζ * y ≠ y * ζ) → Q3NM.AutOddFree ↥L) := by
  rcases hrows with hU3 | hM12' | hL3 | hW
  ·
    obtain ⟨N, hNn, hidx, hlie⟩ := hU3
    obtain ⟨hsimpN, hnabN⟩ := u33_isSimpleGroup hlie
    haveI : N.Normal := hNn
    haveI : IsSimpleGroup N := hsimpN
    have hsolv : Group.IsSolvable (SecQuot P ⧸ N) :=
      isSolvable_of_card_two_pow (n := 1)
        (by rw [← Subgroup.index_eq_card, hidx]; norm_num)
    obtain ⟨U', O'⟩ := component_eq_and_autOddFree F hFs hK hnabN (frameU33_autOddFree hU hlie)
    exact transfer_uniq_odd _ hmoved U' O'
  ·
    obtain ⟨e⟩ := hM12'
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M12) := hM12.1
    haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M12) := hM12fin
    haveI hsimpS : IsSimpleGroup (SecQuot P) := e.isSimpleGroup
    have hAOS : Q3NM.AutOddFree (SecQuot P) := Q3NM.AutOddFree.of_mulEquiv e.symm hM12.2
    have hnabS := exists_noncomm_of_mulEquiv e hM12nab
    have hnabT : ∃ x y : ↥(⊤ : Subgroup (SecQuot P)), x * y ≠ y * x :=
      exists_noncomm_of_mulEquiv Subgroup.topEquiv hnabS
    haveI hsimpT : IsSimpleGroup ↥(⊤ : Subgroup (SecQuot P)) :=
      Subgroup.topEquiv.isSimpleGroup
    have hsolv : Group.IsSolvable (SecQuot P ⧸ (⊤ : Subgroup (SecQuot P))) :=
      isSolvable_of_card_two_pow (n := 0)
        (by rw [← Subgroup.index_eq_card, Subgroup.index_top]; norm_num)
    have hAOT : Q3NM.AutOddFree ↥(⊤ : Subgroup (SecQuot P)) :=
      Q3NM.AutOddFree.of_mulEquiv Subgroup.topEquiv.symm hAOS
    obtain ⟨U', O'⟩ := component_eq_and_autOddFree F hFs hK hnabT hAOT
    exact transfer_uniq_odd _ hmoved U' O'
  ·
    obtain ⟨E, hEn, -, hEcard, ⟨eL⟩⟩ := hL3
    haveI : E.Normal := hEn
    have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
    obtain ⟨ι, hιP, hιa⟩ := hq
    let Φq : QuaternionGroup 2 →* SecQuot P :=
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥P)).comp (ι.codRestrict P hιP)
    have hΦa : Φq (QuaternionGroup.a 2) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥P) ⟨ζP, hζP⟩ := by
      simp only [Φq, MonoidHom.comp_apply]
      congr 1
      exact Subtype.ext hιa
    have hFzE : F ⟨ζ, hζT⟩ ∈ E := by
      rw [hFz, ← hΦa]
      exact mem_of_q8_hom Φq eL
    have nomoved : ∀ L : Subgroup Z, CFSG.IsComponent L → (∃ y ∈ L, ζ * y ≠ y * ζ) → False := by
      intro L hL hm
      have hLT := hmoved L hL hm
      obtain ⟨y, hy, hne⟩ := hm
      have hyT := hLT hy
      have hc := centralizes_of_preimage F hFs hK hEp
        (CFSG.LocalCores.component_overgroup hL hLT) hFzE
        (x := (⟨y, hyT⟩ : ↥T)) (Subgroup.mem_subgroupOf.mpr hy)
      exact hne (congrArg Subtype.val hc)
    exact ⟨fun L₁ L₂ h₁ _ m₁ _ => (nomoved L₁ h₁ m₁).elim,
      fun L hL hm => (nomoved L hL hm).elim⟩
  ·
    obtain ⟨W₀, hWn, hWeq, ⟨eW⟩⟩ := hW
    haveI : W₀.Normal := hWn
    have hWp : IsPGroup 2 W₀ :=
      isPGroup_of_mem_WSet (by rw [hWeq]; exact Set.mem_singleton _)
    haveI : Group.IsSolvable (DihedralGroup 6) := CFSG.Walter.isSolvable_dihedralGroup' 6
    haveI : Group.IsSolvable (SecQuot P ⧸ W₀) :=
      Group.isSolvable_of_surjective (f := eW.symm.toMonoidHom) eW.symm.surjective
    have nomoved : ∀ L : Subgroup Z, CFSG.IsComponent L → (∃ y ∈ L, ζ * y ≠ y * ζ) → False := by
      intro L hL hm
      have hLT := hmoved L hL hm
      exact no_component_of_pgroup F hK hWp (CFSG.LocalCores.component_overgroup hL hLT) |>.elim
    exact ⟨fun L₁ L₂ h₁ _ m₁ _ => (nomoved L₁ h₁ m₁).elim,
      fun L hL hm => (nomoved L hL hm).elim⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
