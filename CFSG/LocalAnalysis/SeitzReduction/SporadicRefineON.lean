module

public import CFSG.Sporadic.ONOddCore.FullGroup
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification (PSL3Four.F4 PSL3Four.frob PSL3Four.frob_apply)

theorem frob_ne_one : PSL3Four.frob ≠ 1 := by
  intro h
  have hall : ∀ x : PSL3Four.F4, x = 0 ∨ x = 1 := by
    intro x
    have hx : x ^ 2 = x := by
      rw [← PSL3Four.frob_apply, h]
      rfl
    have h0 : x * (x - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_two, hx, sub_self]
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact .inl h1
    · exact .inr (sub_eq_zero.1 h1)
  classical
  have hinj : Function.Injective fun x : PSL3Four.F4 => decide (x = 1) := by
    intro x y hxy
    rcases hall x with rfl | rfl <;> rcases hall y with rfl | rfl <;> simp_all
  have h4 := Nat.card_le_card_of_injective _ hinj
  rw [card_F4, Nat.card_eq_fintype_card, Fintype.card_bool] at h4
  norm_num at h4

section ON


theorem onPv_outer_false_of_fix_sylow {α : MulAut Pv}
    (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hα2 : α * α = 1) (hz : α zP = zP)
    {T : Subgroup Pv} (hT : Nat.card T = 512) (hfix : ∀ x ∈ T, α x = x)
    (hTz : ∀ x ∈ T, x * zP = zP * x) : False := by
  obtain ⟨hker, -, hrest⟩ := ctuc_on_outer_local_quotient_is_graph_or_field
  obtain ⟨-, hL, -, A, hcases⟩ := hrest α hout hz
  obtain ⟨γ, hγform, hc⟩ : ∃ γ : MulAut (LinearFlag.projectiveSL 3 PSL3Four.F4),
      (γ = conjAut 3 PSL3Four.F4 A * dualAut 3 PSL3Four.F4 ∨
        γ = conjAut 3 PSL3Four.F4 A * fieldAut 3 PSL3Four.F4 PSL3Four.frob) ∧
      ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
          ((α ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
        lToS a' = γ (lToS a) := by
    rcases hcases with h | h
    · exact ⟨_, .inl rfl, h⟩
    · exact ⟨_, .inr rfl, h⟩
  have hk4 : Nat.card PSL3Four.F4 = 4 := by rw [card_F4]; norm_num
  have hγ2 : γ * γ = 1 := induced_sq hα2 hL hc
  have hγout : γ ∉ (MulAut.conj : LinearFlag.projectiveSL 3 PSL3Four.F4 →*
      MulAut (LinearFlag.projectiveSL 3 PSL3Four.F4)).range := by
    intro h
    rcases hγform with rfl | rfl
    · have := RankThree.PartTwo.KFacts.L34.eq_of_conjAut_mul_mem_range hk4 PSL3Four.frob_apply
        A 1 (ε := 1) le_rfl (by rwa [map_one, mul_one, pow_one])
      exact absurd this.2.1 (by norm_num)
    · have := RankThree.PartTwo.KFacts.L34.eq_of_conjAut_mul_mem_range hk4 PSL3Four.frob_apply
        A PSL3Four.frob (ε := 0) (by norm_num) (by rwa [pow_zero, mul_one])
      exact frob_ne_one this.1
  have hcardγ : Nat.card (autFixed γ) = 168 ∨ Nat.card (autFixed γ) = 60 ∨
      Nat.card (autFixed γ) = 72 := by
    rcases RankThree.PartTwo.KFacts.L34.involution_cases_card hk4 PSL3Four.frob_apply hγ2 with
      h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hγout
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  set T' : Subgroup (Equiv.Perm (Fin N)) := T.map Pv.subtype with hT'
  have hT'card : Nat.card T' = 512 := by
    rw [hT', Subgroup.card_map_of_injective Pv.subtype_injective, hT]
  have hT'M : T' ≤ onM := by
    rintro _ ⟨x, hx, rfl⟩
    have hxc : x ∈ Subgroup.centralizer ({zP} : Set Pv) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hTz x hx)
    rw [Sporadic.ONOddCore.centralizer_zP] at hxc
    exact mem_Mv.1 hxc
  have hr1 := Subgroup.relIndex_mul_card T' onM
  have hr2 := Subgroup.relIndex_mul_card onL onM
  have hr3 := Subgroup.relIndex_mul_card (T' ⊓ onL) onM
  rw [inf_eq_left.2 hT'M, hT'card, card_onM] at hr1
  rw [inf_eq_left.2 onL_le_M, card_onL, card_onM] at hr2
  rw [inf_eq_left.2 (inf_le_left.trans hT'M), card_onM] at hr3
  have hle := Subgroup.relIndex_inf_le (H := T') (K := onL) (L := onM)
  have hI256 : 256 ≤ Nat.card ↥(T' ⊓ onL) := by
    have h315 : T'.relIndex onM = 315 := by linarith
    have h2 : onL.relIndex onM = 2 := by linarith
    rw [h315, h2] at hle
    have hpos : 0 < Nat.card ↥(T' ⊓ onL) := Nat.card_pos
    nlinarith
  have hIdvd : Nat.card ↥(T' ⊓ onL) ∣ 512 :=
    hT'card ▸ Subgroup.card_dvd_of_le inf_le_left
  set U : Subgroup onL := T'.subgroupOf onL with hU
  have hUcard : Nat.card U = Nat.card ↥(T' ⊓ onL) := by
    rw [← Subgroup.card_map_of_injective onL.subtype_injective, hU,
      Subgroup.subgroupOf_map_subtype]
  set f : U →* LinearFlag.projectiveSL 3 PSL3Four.F4 := lToS.comp U.subtype with hf
  have hrange : f.range = U.map lToS := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerf : Nat.card f.ker ≤ 4 := by
    have hle' : f.ker.map U.subtype ≤ lToS.ker := by
      rintro _ ⟨u, hu, rfl⟩
      exact hu
    have h1 := Subgroup.card_le_of_le hle'
    rw [Subgroup.card_map_of_injective U.subtype_injective, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe onQ_le_L).toEquiv, card_onQ] at h1
    exact h1
  have hkr := Subgroup.card_ker_mul_card_range f
  rw [hrange, hUcard] at hkr
  have hV64 : 64 ≤ Nat.card ↥(U.map lToS) := by
    have hpos : 0 < Nat.card ↥(U.map lToS) := Nat.card_pos
    nlinarith
  have hVdvd : Nat.card ↥(U.map lToS) ∣ 512 :=
    (Subgroup.card_map_dvd (f := lToS) U).trans (hUcard ▸ hIdvd)
  have hV64dvd : 64 ∣ Nat.card ↥(U.map lToS) := by
    obtain ⟨k, hk, hkV⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card ↥(U.map lToS) ∣ 2 ^ 9 by simpa using hVdvd)
    rw [hkV] at hV64 ⊢
    have h6 : 6 ≤ k := by
      by_contra h
      have : 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (show (64 : ℕ) = 2 ^ 6 by norm_num) ▸ pow_dvd_pow 2 h6
  have hVfix : U.map lToS ≤ autFixed γ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_autFixed]
    have hu' : (u : Equiv.Perm (Fin N)) ∈ T' := Subgroup.mem_subgroupOf.1 hu
    obtain ⟨x, hxT, hxu⟩ := hu'
    refine (hc u u ?_).symm
    have hx' : (⟨(u : Equiv.Perm (Fin N)), onM_le (onL_le_M u.2)⟩ : Pv) = x :=
      Subtype.ext hxu.symm
    rw [hx', hfix x hxT]
    exact hxu.symm
  have hdvd := (hV64dvd.trans (Subgroup.card_dvd_of_le hVfix))
  rcases hcardγ with h | h | h <;> rw [h] at hdvd <;> norm_num at hdvd

end ON

section ONTransport


theorem on_outer_false_of_fix_two_subgroup {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.ON) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {T₀ : Subgroup S}
    (hT₀ : Nat.card T₀ = 512) (hfix : ∀ x ∈ T₀, σ x = x) : False := by
  set f : S ≃* Pv := e.trans onEquivPv
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  set α₀ := MulAut.congr f σ with hα₀
  have hα₀2 : α₀ * α₀ = 1 := Sporadic.FischerOddCore.congr_mul_self f σ hσ2
  have hα₀out : α₀ ∉ (MulAut.conj : Pv →* MulAut Pv).range :=
    fun h => hout ((Sporadic.FischerOddCore.congr_mem_inner_iff f σ).1 h)
  set T₁ : Subgroup Pv := T₀.map f.toMonoidHom with hT₁def
  have hT₁ : Nat.card T₁ = 512 := by
    rw [hT₁def, Subgroup.card_map_of_injective f.injective, hT₀]
  have hfix₁ : ∀ x ∈ T₁, α₀ x = x := by
    rintro _ ⟨y, hy, rfl⟩
    show f (σ (f.symm (f y))) = f y
    rw [MulEquiv.symm_apply_apply, hfix y hy]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 T₁ := IsPGroup.of_card (n := 9) (by rw [hT₁]; norm_num)
  have : Nontrivial T₁ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hT₁]
    norm_num
  have hZnt : Nontrivial (center T₁) := hp.center_nontrivial
  have hZp : IsPGroup 2 (center T₁) := hp.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk1 : 1 ≤ k := by
    by_contra h
    have : Nat.card (center T₁) = 1 := by rw [hk, show k = 0 by omega, pow_zero]
    exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' this
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center T₁) 2
    (by rw [hk]; exact dvd_pow_self 2 (by omega))
  set a : Pv := ((c : T₁) : Pv) with hadef
  have ha : orderOf a = 2 := by
    rw [hadef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have haT : a ∈ T₁ := (c : T₁).2
  have hacomm : ∀ x ∈ T₁, x * a = a * x := fun x hx =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 c.2 ⟨x, hx⟩)
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate (a : Equiv.Perm (Fin N)) a.2
    (by rw [Subgroup.orderOf_coe]; exact ha)
  set gP : Pv := ⟨g, hg⟩
  have hgaP : a = gP * zP * gP⁻¹ := Subtype.ext hga
  set α : MulAut Pv := (MulAut.conj gP)⁻¹ * α₀ * MulAut.conj gP with hαdef
  have hαapp : ∀ x, α x = gP⁻¹ * α₀ (gP * x * gP⁻¹) * gP := fun x => by
    rw [hαdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hz : α zP = zP := by
    rw [hαapp, ← hgaP, hfix₁ a haT, hgaP]
    group
  have hα2 : α * α = 1 := by
    rw [hαdef, show (MulAut.conj gP)⁻¹ * α₀ * MulAut.conj gP * ((MulAut.conj gP)⁻¹ * α₀ *
      MulAut.conj gP) = (MulAut.conj gP)⁻¹ * (α₀ * α₀) * MulAut.conj gP by group, hα₀2]
    group
  have hαout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range := by
    rintro ⟨y, hy⟩
    apply hα₀out
    refine ⟨gP * y * gP⁻¹, ?_⟩
    have h1 : α₀ = MulAut.conj gP * α * (MulAut.conj gP)⁻¹ := by
      rw [hαdef]
      group
    rw [h1, ← hy, map_mul, map_mul, map_inv]
  set T : Subgroup Pv := T₁.map (MulAut.conj gP⁻¹).toMonoidHom with hTdef
  have hT : Nat.card T = 512 := by
    rw [hTdef, Subgroup.card_map_of_injective (MulAut.conj gP⁻¹).injective, hT₁]
  have hfixT : ∀ x ∈ T, α x = x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hαapp, show gP * (gP⁻¹ * y * gP) * gP⁻¹ = y by group, hfix₁ y hy]
  have hTz : ∀ x ∈ T, x * zP = zP * x := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h1 := hacomm y hy
    rw [hgaP] at h1
    calc gP⁻¹ * y * gP * zP = gP⁻¹ * (y * (gP * zP * gP⁻¹)) * gP := by group
      _ = gP⁻¹ * ((gP * zP * gP⁻¹) * y) * gP := by rw [h1]
      _ = zP * (gP⁻¹ * y * gP) := by group
  exact onPv_outer_false_of_fix_sylow hαout hα2 hz hT hfixT hTz

theorem on_outer_false_of_lieModel {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.ON) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hDm : LieModel D .PSp 3 2 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDc : Nat.card D = 1451520 := by
    rw [F4Pilot.card_of_lieModel_PSp_three_two hDm]
    norm_num
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 9) (G := D)
    (by rw [hDc]; norm_num)
  set T₀ : Subgroup S := (K.map D.subtype).map (fixedSubgroup σ).subtype with hT₀def
  have hT₀ : Nat.card T₀ = 512 := by
    rw [hT₀def, Subgroup.card_map_of_injective (fixedSubgroup σ).subtype_injective,
      Subgroup.card_map_of_injective D.subtype_injective, hK]
    norm_num
  refine on_outer_false_of_fix_two_subgroup e hσ hout hT₀ fun x hx => ?_
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

end ONTransport

end CFSG.SeitzReduction.SporadicRefine
