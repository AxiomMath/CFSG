module

public import CFSG.ClassicalInvolution.Q3.Q3VF4Main
public import CFSG.ClassicalInvolution.Q3.Q3VCollFast
public import CFSG.ClassicalInvolution.Q3.Q3VCollCert
public import CFSG.ClassicalInvolution.Q3.Q3TWCollCert

set_option linter.unusedSectionVars false

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blk spBlock)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  iSup_subgroupOf_eq_top)
open CFSG.ClassicalInvolution.Q3.Q3Z CFSG.ClassicalInvolution.Q3.Q3TW
open scoped MatrixGroups

section Restrict

variable {F : Type} [Field F] {G : Type} [Group G] {U : Fin 4 → Subgroup G}

theorem f4Frame_rho_mem (fr : F4Frame F U) (k : Fin 4) (A : SL(2, F)) :
    fr.ρ k A ∈ ⨆ j, U j := by
  have h : fr.ρ k A ∈ U k := (fr.ρ_range k) ▸ ⟨A, rfl⟩
  exact le_iSup U k h

theorem f4Frame_psiL_mem (fr : F4Frame F U) (A : SL(3, F)) :
    fr.ψL A ∈ ⨆ j, U j := by
  have h : fr.ψL.range ≤ ⨆ j, U j := by
    rw [range_eq_sup_of_blocks fr.ψL_zero fr.ψL_one, fr.ρ_range, fr.ρ_range]
    exact sup_le (le_iSup U 0) (le_iSup U 1)
  exact h ⟨A, rfl⟩

theorem f4Frame_psiR_mem (fr : F4Frame F U) (A : SL(3, F)) :
    fr.ψR A ∈ ⨆ j, U j := by
  have h : fr.ψR.range ≤ ⨆ j, U j := by
    rw [range_eq_sup_of_blocks fr.ψR_zero fr.ψR_one, fr.ρ_range, fr.ρ_range]
    exact sup_le (le_iSup U 3) (le_iSup U 2)
  exact h ⟨A, rfl⟩

theorem f4Frame_psi4_mem (fr : F4Frame F U) (A : StatedSp 2 F) :
    fr.ψ4 A ∈ ⨆ j, U j := by
  have h : fr.ψ4.range ≤ ⨆ j, U j := by
    rw [range_eq_sup_of_spBlocks fr.ψ4_short fr.ψ4_long, fr.ρ_range, fr.ρ_range]
    exact sup_le (le_iSup U 2) (le_iSup U 1)
  exact h ⟨A, rfl⟩

@[expose] noncomputable def F4Frame.restrict (fr : F4Frame F U) :
    F4Frame F (fun k => (U k).subgroupOf (⨆ j, U j)) where
  ρ k := (fr.ρ k).codRestrict (⨆ j, U j) (f4Frame_rho_mem fr k)
  ρ_inj k := fun _ _ h => fr.ρ_inj k (congrArg Subtype.val h)
  ρ_range k := by
    rw [← fr.ρ_range k]
    refine (MonoidHom.subgroupOf_range_eq_of_le (fr.ρ k) fun x hx => ?_).symm
    obtain ⟨A, rfl⟩ := hx
    exact f4Frame_rho_mem fr k A
  ψL := fr.ψL.codRestrict (⨆ j, U j) (f4Frame_psiL_mem fr)
  ψL_zero := MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun fr.ψL_zero A)
  ψL_one := MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun fr.ψL_one A)
  ψR := fr.ψR.codRestrict (⨆ j, U j) (f4Frame_psiR_mem fr)
  ψR_zero := MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun fr.ψR_zero A)
  ψR_one := MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun fr.ψR_one A)
  ψ4 := fr.ψ4.codRestrict (⨆ j, U j) (f4Frame_psi4_mem fr)
  ψ4_long := MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun fr.ψ4_long A)
  ψ4_short := MonoidHom.ext fun A => Subtype.ext (DFunLike.congr_fun fr.ψ4_short A)

end Restrict

section Recognition


theorem weakCT3_f4_subgroup_of_frame {G : Type} [Group G] (U : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (fr : F4Frame3 U) :
    ∃ Ψ : (adjointGroup .F4 (GaloisField 3 1)) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .F4 0 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨Ψ', hsurj, hker, hqs, -, hlie, hblk⟩ := weakCT3_f4_of_frame
    (fun k => (U k).subgroupOf (⨆ j, U j)) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy)) fr.restrict
  refine ⟨(⨆ j, U j).subtype.comp Ψ', ?_, ?_, hqs, hlie, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro k
    rw [← Subgroup.map_map (f := Ψ') (g := (⨆ j, U j).subtype), hblk k,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_iSup U k)]

theorem weakCT3_f4 (hC6 : V6Collapse) (hC3 : B3Collapse) {X : Type} [Group X]
    (U : Fin 4 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U 1) (U 2)) :
    ∃ Ψ : (adjointGroup .F4 (GaloisField 3 1)) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (adjointGroup .F4 (GaloisField 3 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .F4 0 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨fr⟩ := exists_f4Frame3 U hcomm hC6 hC3 (hpair 0 1 (by decide) (by decide))
    (hpair 2 3 (by decide) (by decide)) hsp
  exact weakCT3_f4_of_frame U hgen hcomm fr

theorem weakCT3_f4_subgroup (hC6 : V6Collapse) (hC3 : B3Collapse) {G : Type} [Group G]
    (U : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U 1) (U 2)) :
    ∃ Ψ : (adjointGroup .F4 (GaloisField 3 1)) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .F4 0 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨fr⟩ := exists_f4Frame3 U hcomm hC6 hC3 (hpair 0 1 (by decide) (by decide))
    (hpair 2 3 (by decide) (by decide)) hsp
  exact weakCT3_f4_subgroup_of_frame U hcomm fr

@[expose] def WeakCT3F4Hyp : Prop :=
  ∀ {X : Type} [Group X] (U : Fin 4 → Subgroup X),
    (∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) →
    (∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j)) →
    (∃ W, SymplecticBlockStandardPair (GaloisField 3 1) W (U 1) (U 2)) →
    ∃ Ψ : (adjointGroup .F4 (GaloisField 3 1)) →* X, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧ IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .F4 0 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.f4Datum (GaloisField 3 1)).rootGroup k).map Ψ =
        U k

theorem weakCT3F4Hyp_of_collapse (hC6 : V6Collapse) (hC3 : B3Collapse) : WeakCT3F4Hyp := by
  intro X _ U hcomm hpair hsp
  exact weakCT3_f4_subgroup hC6 hC3 U hcomm hpair hsp

theorem weakCT3F4Hyp_of_check (h6 : V6CollapseCheckFast) (h3 : B3CollapseCheck) : WeakCT3F4Hyp :=
  weakCT3F4Hyp_of_collapse (v6Collapse_of_checkFast h6) (b3Collapse_of_check h3)

theorem weakCT3F4Hyp_proved :
    WeakCT3F4Hyp :=
  weakCT3F4Hyp_of_collapse v6Collapse_proved b3Collapse_proved

end Recognition

end CFSG.ClassicalInvolution.Q3.Q3V
