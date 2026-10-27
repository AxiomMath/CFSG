module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineON

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification (PSL3Four.F4 PSL3Four.frob PSL3Four.frob_apply)

theorem card_autFixed_dvd_card_eqLocus {L X : Type*} [Group L] [Group X] [Finite L]
    (f : L →* X) (hf : Function.Surjective f) (hQ : ∀ a ∈ f.ker, ∀ b : L, a * b = b * a)
    (β : L →* L) (γ : MulAut X) (hc : ∀ a : L, f (β a) = γ (f a)) :
    Nat.card (autFixed γ) ∣ Nat.card (MonoidHom.eqLocus β (MonoidHom.id L)) := by
  classical
  set P : Subgroup L := (autFixed γ).comap f with hP
  have hval : ∀ a : P, (a : L)⁻¹ * β a ∈ f.ker := by
    intro a
    have ha : f a ∈ autFixed γ := a.2
    rw [mem_autFixed] at ha
    rw [MonoidHom.mem_ker, map_mul, map_inv, hc, ha, inv_mul_cancel]
  let φ : P →* L :=
    { toFun := fun a => (a : L)⁻¹ * β a
      map_one' := by simp
      map_mul' := fun a b => by
        have h1 := hQ _ (hval a) (b : L)⁻¹
        change ((a : L) * b)⁻¹ * β ((a : L) * b) = (a : L)⁻¹ * β a * ((b : L)⁻¹ * β b)
        rw [map_mul, mul_inv_rev]
        calc (b : L)⁻¹ * (a : L)⁻¹ * (β a * β b) = (b : L)⁻¹ * ((a : L)⁻¹ * β a) * β b := by
              group
          _ = (a : L)⁻¹ * β a * (b : L)⁻¹ * β b := by rw [← h1]
          _ = (a : L)⁻¹ * β a * ((b : L)⁻¹ * β b) := by group }
  have hφ : ∀ a : P, φ a = (a : L)⁻¹ * β a := fun _ => rfl
  have hrange : φ.range ≤ f.ker := by
    rintro _ ⟨a, rfl⟩
    exact hval a
  have hrdvd : Nat.card φ.range ∣ Nat.card f.ker := card_dvd_of_le hrange
  have hEP : MonoidHom.eqLocus β (MonoidHom.id L) ≤ P := by
    intro a ha
    have ha' : β a = a := ha
    show f a ∈ autFixed γ
    rw [mem_autFixed, ← hc, ha']
  have hker : φ.ker.map P.subtype = MonoidHom.eqLocus β (MonoidHom.id L) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ] at ha
      show β a = a
      have : (a : L)⁻¹ * β a = 1 := ha
      calc β a = (a : L) * ((a : L)⁻¹ * β a) := by group
        _ = a := by rw [this, mul_one]
    · intro hx
      refine ⟨⟨x, hEP hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hφ]
      have : β x = x := hx
      change x⁻¹ * β x = 1
      rw [this, inv_mul_cancel]
  have hkercard : Nat.card φ.ker = Nat.card (MonoidHom.eqLocus β (MonoidHom.id L)) := by
    rw [← hker, card_map_of_injective P.subtype_injective]
  set fP : P →* X := f.comp P.subtype with hfP
  have hfPrange : fP.range = autFixed γ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hx
      obtain ⟨a, rfl⟩ := hf x
      exact ⟨⟨a, hx⟩, rfl⟩
  have hfPker : Nat.card fP.ker = Nat.card f.ker := by
    have hle : f.ker ≤ P := by
      intro a ha
      show f a ∈ autFixed γ
      rw [MonoidHom.mem_ker] at ha
      rw [ha]
      exact one_mem _
    have : fP.ker.map P.subtype = f.ker := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hx
        exact ⟨⟨x, hle hx⟩, hx, rfl⟩
    rw [← this, card_map_of_injective P.subtype_injective]
  have h1 := Subgroup.card_ker_mul_card_range fP
  rw [hfPrange, hfPker] at h1
  have h2 := Subgroup.card_ker_mul_card_range φ
  rw [hkercard] at h2
  obtain ⟨k, hk⟩ := hrdvd
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  refine ⟨k, ?_⟩
  have h3 : Nat.card (MonoidHom.eqLocus β (MonoidHom.id L)) * Nat.card φ.range =
      Nat.card (autFixed γ) * k * Nat.card φ.range := by
    rw [h2, ← h1, hk]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h3

section Pv


theorem onPv_outer_card_dvd_of_fix_z {α : MulAut Pv}
    (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hα2 : α * α = 1) (hz : α zP = zP) :
    168 ∣ Nat.card ↥(fixedSubgroup α ⊓ centralizer {zP}) ∨
      60 ∣ Nat.card ↥(fixedSubgroup α ⊓ centralizer {zP}) ∨
      72 ∣ Nat.card ↥(fixedSubgroup α ⊓ centralizer {zP}) := by
  obtain ⟨hker, hsurj, hrest⟩ := ctuc_on_outer_local_quotient_is_graph_or_field
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
      exact SporadicRefine.frob_ne_one this.1
  have hcardγ : Nat.card (autFixed γ) = 168 ∨ Nat.card (autFixed γ) = 60 ∨
      Nat.card (autFixed γ) = 72 := by
    rcases RankThree.PartTwo.KFacts.L34.involution_cases_card hk4 PSL3Four.frob_apply hγ2 with
      h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd h hγout
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  let β : onL →* onL :=
    { toFun := fun a => ⟨((α ⟨a, onL_le a.2⟩ : Pv) : Equiv.Perm (Fin N)), (hL _).2 a.2⟩
      map_one' := by
        apply Subtype.ext
        change ((α 1 : Pv) : Equiv.Perm (Fin N)) = 1
        rw [map_one]
        rfl
      map_mul' := fun a b => by
        apply Subtype.ext
        change ((α (⟨a, onL_le a.2⟩ * ⟨b, onL_le b.2⟩) : Pv) : Equiv.Perm (Fin N)) = _
        rw [map_mul]
        rfl }
  have hβ : ∀ a : onL, ((β a : onL) : Equiv.Perm (Fin N)) =
      ((α ⟨a, onL_le a.2⟩ : Pv) : Equiv.Perm (Fin N)) := fun _ => rfl
  have hcβ : ∀ a : onL, lToS (β a) = γ (lToS a) := fun a => hc a (β a) (hβ a)
  have hQc : ∀ a ∈ lToS.ker, ∀ b : onL, a * b = b * a := by
    intro a ha b
    rw [hker] at ha
    have ha' : (a : Equiv.Perm (Fin N)) ∈ onQ := ha
    have h := Subgroup.mem_centralizer_iff.1 (onQ_le_centralizer_L ha') (b : Equiv.Perm (Fin N))
      b.2
    exact Subtype.ext h.symm
  have hdvd1 := card_autFixed_dvd_card_eqLocus lToS hsurj hQc β γ hcβ
  set E := MonoidHom.eqLocus β (MonoidHom.id onL) with hE
  let ι : E →* ↥(fixedSubgroup α ⊓ centralizer {zP}) :=
    { toFun := fun a => ⟨⟨((a : onL) : Equiv.Perm (Fin N)), onL_le (a : onL).2⟩, by
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have ha : β a = a := a.2
          show α _ = _
          apply Subtype.ext
          rw [← hβ, ha]
          rfl
        · rw [mem_centralizer_zP_iff]
          exact onL_le_M (a : onL).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro a b h
    have h1 := congrArg (fun x : ↥(fixedSubgroup α ⊓ centralizer {zP}) =>
      ((x : Pv) : Equiv.Perm (Fin N))) h
    exact Subtype.ext (Subtype.ext h1)
  have hdvd2 := Subgroup.card_dvd_of_injective ι hι
  rcases hcardγ with h | h | h
  · exact .inl (h ▸ hdvd1.trans hdvd2)
  · exact .inr (.inl (h ▸ hdvd1.trans hdvd2))
  · exact .inr (.inr (h ▸ hdvd1.trans hdvd2))

theorem onPv_outer_card_dvd {α : MulAut Pv}
    (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hα2 : α * α = 1) {a : Pv}
    (ha : orderOf a = 2) (hαa : α a = a) :
    168 ∣ Nat.card ↥(fixedSubgroup α ⊓ centralizer {a}) ∨
      60 ∣ Nat.card ↥(fixedSubgroup α ⊓ centralizer {a}) ∨
      72 ∣ Nat.card ↥(fixedSubgroup α ⊓ centralizer {a}) := by
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate (a : Equiv.Perm (Fin N)) a.2
    (by rw [Subgroup.orderOf_coe]; exact ha)
  set gP : Pv := ⟨g, hg⟩
  set φ : Pv ≃* Pv := MulAut.conj gP⁻¹
  have hφa : φ a = zP := by
    apply Subtype.ext
    show (g⁻¹ * (a : Equiv.Perm (Fin N)) * g⁻¹⁻¹) = onz
    rw [hga]
    group
  set γ := MulAut.congr φ α with hγ
  have hz : γ zP = zP := by
    rw [← hφa, hγ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hαa]
  have hγ2 : γ * γ = 1 := by
    rw [hγ, ← map_mul, hα2, map_one]
  have h := onPv_outer_card_dvd_of_fix_z (not_inner_congr hout φ) hγ2 hz
  have e1 := fixedCentCongr φ α a
  rw [hφa] at e1
  rw [Nat.card_congr e1.toEquiv]
  exact h

end Pv

section Transport


theorem on_outer_transport_data {S : Type} [Group S] (e : S ≃* NativeSporadic.ON)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {t : S} (ht : orderOf t = 2) (hσt : σ t = t) :
    MulAut.congr (e.trans onEquivPv) σ ∉ (MulAut.conj : Pv →* MulAut Pv).range ∧
      MulAut.congr (e.trans onEquivPv) σ * MulAut.congr (e.trans onEquivPv) σ = 1 ∧
      orderOf ((e.trans onEquivPv) t) = 2 ∧
      MulAut.congr (e.trans onEquivPv) σ ((e.trans onEquivPv) t) = (e.trans onEquivPv) t := by
  set ψ : S ≃* Pv := e.trans onEquivPv
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  refine ⟨fun h => hout ((Sporadic.FischerOddCore.congr_mem_inner_iff ψ σ).1 h),
    Sporadic.FischerOddCore.congr_mul_self ψ σ hσ2, by rw [MulEquiv.orderOf_eq, ht], ?_⟩
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    hσt]

theorem on_outer_card_dvd {S : Type} [Group S] (e : S ≃* NativeSporadic.ON) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {t : S}
    (ht : orderOf t = 2) (hσt : σ t = t) :
    168 ∣ Nat.card ↥(fixedSubgroup σ ⊓ centralizer {t}) ∨
      60 ∣ Nat.card ↥(fixedSubgroup σ ⊓ centralizer {t}) ∨
      72 ∣ Nat.card ↥(fixedSubgroup σ ⊓ centralizer {t}) := by
  obtain ⟨h1, h2, h3, h4⟩ := on_outer_transport_data e hσ hout ht hσt
  rw [Nat.card_congr (fixedCentCongr (e.trans onEquivPv) σ t).toEquiv]
  exact onPv_outer_card_dvd h1 h2 h3 h4

theorem on_outer_oddCore_eq_bot {S : Type} [Group S] (e : S ≃* NativeSporadic.ON)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {t : S} (ht : orderOf t = 2) (hσt : σ t = t) :
    CFSG.oddCore ↥(fixedSubgroup σ ⊓ centralizer {t}) = ⊥ := by
  obtain ⟨h1, h2, h3, h4⟩ := on_outer_transport_data e hσ hout ht hσt
  exact ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
    (fixedCentCongr (e.trans onEquivPv) σ t).symm (oddCore_fixed_centralizer h1 h2 h3 h4)

end Transport

end CFSG.SeitzReduction.RankOne
