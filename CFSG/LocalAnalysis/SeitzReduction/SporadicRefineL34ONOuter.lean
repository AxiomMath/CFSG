module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineON
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ONOuterCent
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34SuzOuter

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

section ONLocal


theorem onPv_outer_exists_of_fix_card_sixtyfour {α : MulAut Pv}
    (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hα2 : α * α = 1) (hz : α zP = zP)
    {T : Subgroup Pv} (hT : Nat.card T = 64) (hfix : ∀ x ∈ T, α x = x)
    (hTz : ∀ x ∈ T, x * zP = zP * x) :
    ∃ q ∈ T, orderOf q = 4 ∧ ∃ W : Subgroup Pv, W ≤ T ∧ Nat.card W = 32 ∧
      ∀ w ∈ W, w * q = q * w := by
  obtain ⟨hker, -, hrest⟩ := ctuc_on_outer_local_quotient_is_graph_or_field
  obtain ⟨-, hL, -, A, hcases⟩ := hrest α hout hz
  obtain ⟨γ, hγform, hc⟩ :
      ∃ γ : MulAut (LinearFlag.projectiveSL 3 ComponentClassification.PSL3Four.F4),
      (γ = conjAut 3 ComponentClassification.PSL3Four.F4 A *
          dualAut 3 ComponentClassification.PSL3Four.F4 ∨
        γ = conjAut 3 ComponentClassification.PSL3Four.F4 A *
          fieldAut 3 ComponentClassification.PSL3Four.F4 ComponentClassification.PSL3Four.frob) ∧
      ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
          ((α ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
        lToS a' = γ (lToS a) := by
    rcases hcases with h | h
    · exact ⟨_, .inl rfl, h⟩
    · exact ⟨_, .inr rfl, h⟩
  have hk4 : Nat.card ComponentClassification.PSL3Four.F4 = 4 := by
    rw [card_F4]
    norm_num
  have hγ2 : γ * γ = 1 := induced_sq hα2 hL hc
  have hγout : γ ∉ (MulAut.conj : LinearFlag.projectiveSL 3 ComponentClassification.PSL3Four.F4 →*
      MulAut (LinearFlag.projectiveSL 3 ComponentClassification.PSL3Four.F4)).range := by
    intro h
    rcases hγform with rfl | rfl
    · have := RankThree.PartTwo.KFacts.L34.eq_of_conjAut_mul_mem_range hk4
        ComponentClassification.PSL3Four.frob_apply A 1 (ε := 1) le_rfl
        (by rwa [map_one, mul_one, pow_one])
      exact absurd this.2.1 (by norm_num)
    · have := RankThree.PartTwo.KFacts.L34.eq_of_conjAut_mul_mem_range hk4
        ComponentClassification.PSL3Four.frob_apply A ComponentClassification.PSL3Four.frob
        (ε := 0) (by norm_num) (by rwa [pow_zero, mul_one])
      exact frob_ne_one this.1
  have hcardγ : Nat.card (autFixed γ) = 168 ∨ Nat.card (autFixed γ) = 60 ∨
      Nat.card (autFixed γ) = 72 := by
    rcases RankThree.PartTwo.KFacts.L34.involution_cases_card hk4
        ComponentClassification.PSL3Four.frob_apply hγ2 with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hγout
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  set T' : Subgroup (Equiv.Perm (Fin N)) := T.map Pv.subtype with hT'
  have hT'card : Nat.card T' = 64 := by
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
  have hI32 : 32 ≤ Nat.card ↥(T' ⊓ onL) := by
    have h2520 : T'.relIndex onM = 2520 := by linarith
    have h2 : onL.relIndex onM = 2 := by linarith
    rw [h2520, h2] at hle
    have hpos : 0 < Nat.card ↥(T' ⊓ onL) := Nat.card_pos
    nlinarith
  have hIdvd : Nat.card ↥(T' ⊓ onL) ∣ 64 :=
    hT'card ▸ Subgroup.card_dvd_of_le inf_le_left
  set U : Subgroup onL := T'.subgroupOf onL with hU
  have hUcard : Nat.card U = Nat.card ↥(T' ⊓ onL) := by
    rw [← Subgroup.card_map_of_injective onL.subtype_injective, hU,
      Subgroup.subgroupOf_map_subtype]
  set f : U →* LinearFlag.projectiveSL 3 ComponentClassification.PSL3Four.F4 :=
    lToS.comp U.subtype with hf
  have hrange : f.range = U.map lToS := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hkerle : f.ker.map U.subtype ≤ lToS.ker := by
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  have hQcard : Nat.card lToS.ker = 4 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe onQ_le_L).toEquiv, card_onQ]
  have hkerf : Nat.card f.ker ≤ 4 := by
    have h1 := Subgroup.card_le_of_le hkerle
    rwa [Subgroup.card_map_of_injective U.subtype_injective, hQcard] at h1
  have hkr := Subgroup.card_ker_mul_card_range f
  rw [hrange, hUcard] at hkr
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
  have hVdvd64 : Nat.card ↥(U.map lToS) ∣ 64 :=
    (Subgroup.card_map_dvd (f := lToS) U).trans (hUcard ▸ hIdvd)
  have hV8 : Nat.card ↥(U.map lToS) ≤ 8 := by
    have hfixd := Subgroup.card_dvd_of_le hVfix
    have hg : Nat.card ↥(U.map lToS) ∣ 8 := by
      rcases hcardγ with h | h | h <;> rw [h] at hfixd
      · exact (Nat.dvd_gcd hVdvd64 hfixd).trans (by norm_num)
      · exact (Nat.dvd_gcd hVdvd64 hfixd).trans (by norm_num)
      · exact (Nat.dvd_gcd hVdvd64 hfixd).trans (by norm_num)
    exact Nat.le_of_dvd (by norm_num) hg
  have hker4 : Nat.card f.ker = 4 := by
    have h1 : Nat.card f.ker * Nat.card ↥(U.map lToS) ≤ Nat.card f.ker * 8 :=
      Nat.mul_le_mul_left _ hV8
    omega
  have hI : Nat.card ↥(T' ⊓ onL) = 32 := by
    have h1 : Nat.card f.ker * Nat.card ↥(U.map lToS) ≤ 4 * 8 := Nat.mul_le_mul hkerf hV8
    omega
  have hkerQ : f.ker.map U.subtype = lToS.ker := by
    refine Subgroup.eq_of_le_of_card_ge hkerle ?_
    rw [Subgroup.card_map_of_injective U.subtype_injective, hker4, hQcard]
  have hqL : onq ∈ onL := onq_mem_L
  have hqT' : onq ∈ T' := by
    have hq : (⟨onq, hqL⟩ : onL) ∈ lToS.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_zpowers onq
    rw [← hkerQ] at hq
    obtain ⟨u, -, hu⟩ := hq
    have hu' : (u : onL) = ⟨onq, hqL⟩ := hu
    have hmem : (u : onL) ∈ U := u.2
    rw [hu'] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  obtain ⟨q, hqT, hqq⟩ := hqT'
  refine ⟨q, hqT, ?_, T ⊓ onL.comap Pv.subtype, inf_le_left, ?_, ?_⟩
  · rw [← orderOf_injective Pv.subtype Pv.subtype_injective q]
    exact hqq ▸ orderOf_onq
  · have hmap : (T ⊓ onL.comap Pv.subtype).map Pv.subtype = T' ⊓ onL := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, (Subgroup.mem_inf.1 hx).1, rfl⟩, (Subgroup.mem_inf.1 hx).2⟩
      · rintro ⟨⟨x, hx, rfl⟩, hy⟩
        exact ⟨x, Subgroup.mem_inf.2 ⟨hx, hy⟩, rfl⟩
    rw [← Subgroup.card_map_of_injective Pv.subtype_injective, hmap, hI]
  · intro w hw
    apply Subtype.ext
    have hwL : (w : Equiv.Perm (Fin N)) ∈ onL := (Subgroup.mem_inf.1 hw).2
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (onL_le_centralizer_q hwL)
    simp only [Subgroup.coe_mul]
    rw [show ((q : Pv) : Equiv.Perm (Fin N)) = onq from hqq]
    exact h1

end ONLocal

section ONTransport


theorem on_outer_exists_of_fix_card_sixtyfour {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.ON) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {T₀ : Subgroup S}
    (hT₀ : Nat.card T₀ = 64) (hfix : ∀ x ∈ T₀, σ x = x) :
    ∃ q ∈ T₀, orderOf q = 4 ∧ ∃ W : Subgroup S, W ≤ T₀ ∧ Nat.card W = 32 ∧
      ∀ w ∈ W, w * q = q * w := by
  set f : S ≃* Pv := e.trans onEquivPv
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  set α₀ := MulAut.congr f σ with hα₀
  have hα₀2 : α₀ * α₀ = 1 := Sporadic.FischerOddCore.congr_mul_self f σ hσ2
  have hα₀out : α₀ ∉ (MulAut.conj : Pv →* MulAut Pv).range :=
    fun h => hout ((Sporadic.FischerOddCore.congr_mem_inner_iff f σ).1 h)
  set T₁ : Subgroup Pv := T₀.map f.toMonoidHom with hT₁def
  have hT₁ : Nat.card T₁ = 64 := by
    rw [hT₁def, Subgroup.card_map_of_injective f.injective, hT₀]
  have hfix₁ : ∀ x ∈ T₁, α₀ x = x := by
    rintro _ ⟨y, hy, rfl⟩
    show f (σ (f.symm (f y))) = f y
    rw [MulEquiv.symm_apply_apply, hfix y hy]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 T₁ := IsPGroup.of_card (n := 6) (by rw [hT₁]; norm_num)
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
  have hT : Nat.card T = 64 := by
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
  obtain ⟨q, hqT, hqo, W, hWT, hWcard, hWq⟩ :=
    onPv_outer_exists_of_fix_card_sixtyfour hαout hα2 hz hT hfixT hTz
  set φ : Pv ≃* S := (MulAut.conj gP).trans f.symm with hφ
  have hφT : ∀ x ∈ T, φ x ∈ T₀ := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    simp only [hφ, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show gP * (gP⁻¹ * f t * gP) * gP⁻¹ = f t by group, MulEquiv.symm_apply_apply]
    exact ht
  refine ⟨φ q, hφT q hqT, by rw [MulEquiv.orderOf_eq, hqo], W.map φ.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hφT w (hWT hw)
  · rw [Subgroup.card_map_of_injective φ.injective, hWcard]
  · rintro _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hWq w hw]

theorem on_outer_not_lieModel_psl_three_two {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.ON) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hfree : FixedCentralizerTwoFree σ D) : ¬ LieModel (D ⧸ center D) .PSL 3 2 2 := by
  intro hDm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Nat.card (D ⧸ center D) = 20160 := by
    rw [LinearPilot.card_of_lieModel_PSL_two hDm]
    decide
  have hDcard : Nat.card D = 20160 * Nat.card (center D) := by
    rw [← hq]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 6) (G := D)
    (by rw [hDcard]; exact Dvd.dvd.mul_right (by norm_num) _)
  have hKp : IsPGroup 2 K := IsPGroup.of_card hK
  have hKZ : K ⊓ center D = ⊥ := inf_center_eq_bot_of_twoFree hfree hKp
  set ι : K →* S := (fixedSubgroup σ).subtype.comp (D.subtype.comp K.subtype) with hι
  have hιinj : Function.Injective ι :=
    (fixedSubgroup σ).subtype_injective.comp (D.subtype_injective.comp K.subtype_injective)
  have hT₀card : Nat.card ι.range = 64 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hιinj, Subgroup.card_top, hK]
    norm_num
  have hfix : ∀ x ∈ ι.range, σ x = x := by
    rintro _ ⟨k, rfl⟩
    exact ((k : D) : fixedSubgroup σ).2
  obtain ⟨q, hqT, hqo, W, hWT, hWcard, hWq⟩ :=
    on_outer_exists_of_fix_card_sixtyfour e hσ hout hT₀card hfix
  obtain ⟨qK, rfl⟩ := hqT
  set W' : Subgroup K := W.comap ι with hW'
  have hW'card : Nat.card W' = 32 := by
    rw [← Subgroup.card_map_of_injective hιinj, hW', Subgroup.map_comap_eq_self hWT, hWcard]
  have hqKo : orderOf qK = 4 := by rw [← orderOf_injective ι hιinj, hqo]
  have hW'q : ∀ w ∈ W', w * qK = qK * w := fun w hw =>
    hιinj (by rw [map_mul, map_mul]; exact hWq _ hw)
  set ψ : K →* D ⧸ center D := (QuotientGroup.mk' (center D)).comp K.subtype with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : (k : D) ∈ center D := by
      have h0 : (QuotientGroup.mk' (center D)) (k : D) = 1 := hk
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
    have h2 : (k : D) ∈ K ⊓ center D := mem_inf.mpr ⟨k.2, h1⟩
    rw [hKZ, mem_bot] at h2
    exact Subtype.ext h2
  have hxo : orderOf (ψ qK) = 4 := by rw [orderOf_injective ψ hψinj, hqKo]
  have hle : W'.map ψ ≤ centralizer {ψ qK} := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hW'q w hw]
  have h32 : 32 ≤ Nat.card (centralizer ({ψ qK} : Set (D ⧸ center D))) := by
    have h1 := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective hψinj, hW'card] at h1
  have h16 := card_centralizer_le_of_orderOf_four hDm hxo
  omega

end ONTransport

end CFSG.SeitzReduction.SporadicRefine
