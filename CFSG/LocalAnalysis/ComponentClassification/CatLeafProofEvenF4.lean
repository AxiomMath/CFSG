module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenG2
public import CFSG.LieType.Ree.LargeReeModelSchreier

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : center B = ⊥) : center A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ center B := (MulEquivClass.apply_mem_center_iff e).2 hx
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.2 (e.injective (hx'.trans (map_one e).symm))

variable {F : Type} [Field F]

theorem even_F4_outer_fixed
    [Finite F] [CharP F ReeTag.F4.prime] {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (β : MulAut (adjointGroup .F4 F)) (hβ2 : β ^ 2 = 1) (hβo : β ∉ inner (adjointGroup .F4 F)) :
    (∃ e : ℕ, 1 ≤ e ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ e ∧
        Nonempty (fixedSubgroup β ≃* adjointGroup .F4 k)) ∨
      ∃ m : ℕ, f = 2 * m + 1 ∧ Nonempty (fixedSubgroup β ≃* reeFixed ReeTag.F4 F m) := by
  have : CharP F 2 := ‹CharP F ReeTag.F4.prime›
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨ψ, hψ, heven, hodd, -⟩ := even_F4_all_outer_involutions_canonical hf F hF β hβ2 hβo
  set ψ₀ : MulAut (adjointGroup .F4 F) := ψ
  set γ : MulAut (adjointGroup .F4 F) := ReeTag.F4.finiteExceptionalAut F ^ f with hγdef
  have hc : MulAut.congr ψ₀ β = γ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ₀ β = ψ₀ * β * ψ₀⁻¹).trans hψ
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' f
  · left
    have hn1 : 1 ≤ n := by omega
    have hF' : Nat.card F = 2 ^ (2 * n) := by rw [hF, hn]
    set δ := iterateFrobenius F 2 n
    have hδc : ∀ c, δ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
    set σ := ExcSelector.ringEquivOfFinite δ
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by rw [ExcSelector.ringEquivOfFinite_apply, hδc]
    have hk := ExcSelector.card_fixSubfield_of_pow hn1 hF' hσ
    have hγ : ∀ u, (γ u : ModGL .F4 F) =
        Units.map (entrywiseHom σ.toRingHom) (u : ModGL .F4 F) := fun u => by
      rw [ExcSelector.toRingHom_ringEquivOfFinite]
      exact (heven n hn).2 δ hδc u
    have hfix := ExcSelector.fixedSubgroup_eq_fixedFieldImage_even (τ := .F4) (Or.inr (Or.inl rfl))
      hchar σ hγ
    have hJC : fixedFieldImage .F4 σ ≤ adjointGroup .F4 F := fun x hx =>
      (fixedFieldImage_le hx).1
    have hβψ : fixedSubgroup (MulAut.congr ψ₀ β) =
        (fixedFieldImage .F4 σ).subgroupOf (adjointGroup .F4 F) :=
      (congrArg fixedSubgroup hc).trans hfix
    exact ⟨n, hn1, fixSubfield σ, inferInstance, inferInstance, hk,
      ⟨(fixedSubgroupCongrEquiv ψ₀ β).trans ((MulEquiv.subgroupCongr hβψ).trans
        ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ).symm))⟩⟩
  · right
    have hβψ : fixedSubgroup (MulAut.congr ψ₀ β) = reeFixed ReeTag.F4 F n :=
      (congrArg fixedSubgroup (hc.trans (hodd n hn).1)).trans
        (ExcSelector.fixedSubgroup_finiteReeAut n)
    exact ⟨n, hn, ⟨(fixedSubgroupCongrEquiv ψ₀ β).trans (MulEquiv.subgroupCongr hβψ)⟩⟩

theorem lieModel_F4_of_mulEquiv
    {G : Type} [Group G] {k : Type} [Field k] [Finite k] {e : ℕ} (he : 1 ≤ e)
    (hk : Nat.card k = 2 ^ e) (E : G ≃* adjointGroup .F4 k) :
    StatedLieAdmissible .F4 0 2 e ∧ LieModel G .F4 0 2 e :=
  ⟨⟨Nat.prime_two, he, rfl⟩, Or.inr (Or.inl ⟨rfl, by decide,
    ⟨⟨Nat.prime_two, he, rfl⟩, untwistedChevalleyModel_of_mulEquiv hk E⟩⟩)⟩

theorem lieModel_twistedF4_of_mulEquiv
    {G : Type} [Group G] [Finite F] [CharP F ReeTag.F4.prime] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) (E : G ≃* reeFixed ReeTag.F4 F m) :
    StatedLieAdmissible .twistedF4 0 2 (2 * m + 1) ∧ LieModel G .twistedF4 0 2 (2 * m + 1) := by
  have hadm : StatedLieAdmissible .twistedF4 0 2 (2 * m + 1) :=
    ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩
  obtain ⟨iso⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma (K := F) (a := m) hm hF
  have hfx : reeFixedGroup .F4 F reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ m else 2 ^ (m + 1)) = ReeTag.F4.reeGamma F m :=
    (ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.F4) (K := F) (a := m)).symm
  let eC : DerivedCentralQuotient (reeFixedGroup .F4 F reeF4Perm
      (fun i => if i ∈ reeF4Long then 2 ^ m else 2 ^ (m + 1))) ≃*
      DerivedCentralQuotient (ReeTag.F4.reeGamma F m) :=
    QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (by rw [hfx]; rfl))
      (Subgroup.map_center_eq _)
  have hR : ReeTitsModel G .twistedF4 2 (2 * m + 1) :=
    ⟨hadm, m, rfl, F, inferInstance, inferInstance, hF,
      ⟨(E.trans (ReeTag.reeFixedEquivReeGamma F m)).trans (iso.symm.trans eC.symm)⟩⟩
  exact ⟨hadm, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))⟩

theorem lieModel_tits_of_isPComponent
    [Finite F] [CharP F ReeTag.F4.prime] (hF : Nat.card F = 2) {X : Type} [Group X]
    [Finite X] (Ψ : X ≃* reeFixed ReeTag.F4 F 0) {P : Subgroup X} (hP : IsPComponent 2 P) :
    StatedLieAdmissible .Tits 0 2 1 ∧ LieModel (P ⧸ Open.fusionZStar P) .Tits 0 2 1 := by
  have : Finite (ModGL ReeTag.F4.tag F) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag F) := Subtype.finite
  set W := reeFixed ReeTag.F4 F 0 with hW
  have hD : IsSimpleGroup (commutator ↥W) := ExcSelector.isSimpleGroup_commutator_reeFixed_tits hF
  have hPeq := eq_commutator_of_isPComponent hD
    (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ hP)
  have hH : reeFixedGroup .F4 F reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1)) =
      W.map (adjointGroup ReeTag.F4.tag F).subtype :=
    reeFixedGroup_eq_map_reeFixed ReeTag.F4 F 0
  set H := reeFixedGroup .F4 F reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ 0 else 2 ^ (0 + 1))
  have hHc : ⁅H, H⁆ = ⁅W, W⁆.map (adjointGroup ReeTag.F4.tag F).subtype := by
    rw [hH, Subgroup.map_commutator]
    rfl
  let EY : commutator ↥W ≃* ↥⁅H, H⁆ := (commutatorSubtypeEquiv W).trans
    ((⁅W, W⁆.equivMapOfInjective _ (adjointGroup ReeTag.F4.tag F).subtype_injective).trans
      (MulEquiv.subgroupCongr hHc.symm))
  have hZD : center (commutator ↥W) = ⊥ := ExcSelector.center_eq_bot_of_isSimpleGroup' (by
    obtain ⟨x, hx, y, hy, hxy⟩ := (LieType.Simplicity.titsData F hF).nonabelian
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩)
  have hZY : center ↥⁅H, H⁆ = ⊥ := center_eq_bot_of_mulEquiv EY.symm hZD
  obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    ((P.equivMapOfInjective Ψ.toMonoidHom Ψ.injective).trans (MulEquiv.subgroupCongr hPeq))
  have hadm : StatedLieAdmissible .Tits 0 2 1 := ⟨Nat.prime_two, le_refl 1, rfl, rfl, rfl⟩
  have hR : ReeTitsModel (P ⧸ Open.fusionZStar P) .Tits 2 1 :=
    ⟨hadm, 0, rfl, F, inferInstance, inferInstance, hF.trans (pow_one 2).symm,
      ⟨(E.trans EY).trans
        ((QuotientGroup.quotientMulEquivOfEq hZY).trans QuotientGroup.quotientBot).symm⟩⟩
  exact ⟨hadm, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))⟩

theorem evenOuterFamilyInput_F4
    : EvenOuterFamilyInput .F4 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .F4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hu
  have : Finite (ModGL .F4 F) := finite_modGL
  have : Finite (ModGL ReeTag.F4.tag F) := finite_modGL
  have : Finite ↥(adjointGroup ReeTag.F4.tag F) := Subtype.finite
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .F4 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  have : CharP F 2 := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hF
  have : CharP F ReeTag.F4.prime := ‹CharP F 2›
  rcases even_F4_outer_fixed hf hF β hβ2 hβo with ⟨e', he', k, _, _, hk, ⟨Φ⟩⟩ | ⟨m, hfm, ⟨Φ⟩⟩
  · have : Finite (ModGL .F4 k) := finite_modGL
    have := (ExcSelector.adjointGroup_F4_even he' hk).1
    obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
      ((fixedSubgroupCongrEquiv e α).trans Φ) hP
    exact Or.inl ⟨.F4, 0, e', lieModel_F4_of_mulEquiv he' hk E⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have hF2 : Nat.card F = 2 := by rw [hF, hfm]; rfl
      exact Or.inl ⟨.Tits, 0, 1, lieModel_tits_of_isPComponent hF2
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP⟩
    · have hF' : Nat.card F = 2 ^ (2 * m + 1) := hfm ▸ hF
      have := (ExcSelector.reeFixed_F4_simple_not_smallType hm1 hF').1
      obtain ⟨E⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
        ((fixedSubgroupCongrEquiv e α).trans Φ) hP
      exact Or.inl ⟨.twistedF4, 0, 2 * m + 1, lieModel_twistedF4_of_mulEquiv hm1 hF' E⟩

end CFSG.ComponentClassification.CatLeafProof
