module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBTypeInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieDatum

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

@[expose] def BurgoyneE7FieldQuatInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p e : ℕ), p.Prime → p ≠ 2 → 1 ≤ e →
    Nat.card K = (p ^ e) ^ 2 → ∀ δ : K ≃+* K, (∀ c, δ c = c ^ (p ^ e)) →
    ∀ (α : MulAut (adjointGroup .E7 K)) (g : adjointGroup .E7 K) (a : Fin Tag.E7.rank → Kˣ),
      (∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 a *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL .E7 K) * (rootDiagUnit .E7 a)⁻¹ *
          (g : ModGL .E7 K)⁻¹) → orderOf α = 2 →
      QuatComponentForm (fixedSubgroup α)

theorem false_of_L2_of_quat {S : Type} [Group S] [Finite S] {v : MulAut S}
    (hq : ∀ L : Subgroup (autFixed v), IsPComponent 2 L → IsQuasisimple L)
    (hQ : QuatComponentForm (autFixed v)) {R : Subgroup S} (hRv : R ≤ autFixed v)
    (hRc : IsPComponent 2 (R.subgroupOf (autFixed v))) {p₁ n₁ : ℕ} [Fact p₁.Prime]
    (hp₁2 : p₁ ≠ 2) (hn₁ : 0 < n₁) (N : Subgroup R) [N.Normal] (hN : Odd (Nat.card N))
    (e : R ⧸ N ≃* PSL(2, GaloisField p₁ n₁)) : False := by
  have hLc : IsComponent (R.subgroupOf (autFixed v)) :=
    ⟨hq _ hRc, by obtain ⟨_, _, h, _⟩ := hRc; exact h⟩
  obtain ⟨H, ⟨eH⟩⟩ := hQ _ hLc
  let eR : R.subgroupOf (autFixed v) ≃* R := Subgroup.subgroupOfEquivOfLe hRv
  set H' : Subgroup R := H.map eR.toMonoidHom with hH'
  let eH' : H' ≃* QuaternionGroup 2 := (H.equivMapOfInjective _ eR.injective).symm.trans eH
  let ψ : H' →* PSL(2, GaloisField p₁ n₁) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' N).comp H'.subtype)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have hN' : (h : R) ∈ N := by
      have h1 : QuotientGroup.mk' N (h : R) = 1 := by
        have := congrArg e.symm hh
        simpa [ψ] using this
      exact (QuotientGroup.eq_one_iff _).1 h1
    have h8 : orderOf h ∣ 8 := by
      have := orderOf_dvd_natCard (eH' h)
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card, MulEquiv.orderOf_eq] at this
      exact this
    have hodd : orderOf (⟨(h : R), hN'⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hodd
    have h1 : orderOf h = 1 := by
      have hco : Nat.Coprime (orderOf h) 2 := by
        rw [Nat.coprime_two_right]
        exact Odd.of_dvd_nat hN hodd
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 3 hco) h8
    rw [orderOf_eq_one_iff] at h1
    rw [h1]
    exact Subgroup.one_mem _
  have hF : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p₁ n₁)) :=
    ⟨p₁, n₁, Fact.out, Nat.Prime.odd_of_ne_two Fact.out hp₁2, hn₁,
      GaloisField.card p₁ n₁ (by omega)⟩
  exact false_of_quaternion_of_hasDihedralSylowTwo
    (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model _ hF) ψ.range
    ((MonoidHom.ofInjective hψ).symm.trans eH')


theorem burgoynePropBE7S_of_fieldQuat (hfq : BurgoyneE7FieldQuatInput) : BurgoynePropBE7S := by
  intro S _ _ n p f hp2 hL v hv2 R hRv hRc p₁ n₁ _ hp₁2 hn₁ N _ hN ⟨e⟩
  have hm := GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL
  have hp : p.Prime := hm.1.1
  obtain ⟨F, _, _, hF, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .E7
    (hm.2 : UntwistedChevalleyModel S .E7 (p ^ f))
  have hFodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  let α : MulAut (adjointGroup .E7 F) := θ.symm.trans (v.trans θ)
  have hα : ∀ x, α (θ x) = θ (v x) := fun x => by
    change θ (v (θ.symm (θ x))) = θ (v x)
    rw [MulEquiv.symm_apply_apply]
  have hαo : orderOf α = 2 := by
    have : α = MulAut.congr θ v := MulEquiv.ext fun _ => rfl
    rw [this, MulEquiv.orderOf_eq, hv2]
  have hα2 : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hmap : (autFixed v).map θ.toMonoidHom = fixedSubgroup α := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change α (θ x) = θ x
      rw [hα]
      exact congrArg θ hx
    · intro hy
      refine ⟨θ.symm y, ?_, by simp⟩
      change v (θ.symm y) = θ.symm y
      apply θ.injective
      rw [← hα, MulEquiv.apply_symm_apply]
      exact hy
  let Φ : autFixed v ≃* fixedSubgroup α :=
    ((autFixed v).equivMapOfInjective θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hq : ∀ L : Subgroup (autFixed v), IsPComponent 2 L → IsQuasisimple L := by
    intro L hL
    have hL' := ((CFSG.LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 2
      Nat.prime_two Φ).1 L).1 hL
    exact LocalCores.isQuasisimple_of_mulEquiv (L.equivMapOfInjective _ Φ.injective).symm
      (LieType.AlgebraicGroups.odd_E7_all_involution_fixed_p_components F hFodd α hα2 2
        Nat.prime_two _ hL')
  have hQ : QuatComponentForm (fixedSubgroup α) := by
    rcases LieType.AlgebraicGroups.odd_E7_involution_inner_or_quadratic hFodd hα2 with ⟨g, a, hga⟩ |
      ⟨p', e', hp', he', hFc, δ, hδ, g, a, hga⟩
    · exact oddExcInnerDiagQuatForm_E7 F p f hp hp2 hF α g a hga hαo
    · have hp'2 : p' ≠ 2 := by
        rintro rfl
        rw [hFc] at hFodd
        exact (Nat.not_odd_iff_even.2 ((Nat.even_pow.2 ⟨even_two, by omega⟩).pow_of_ne_zero
          two_ne_zero)) hFodd
      exact hfq F p' e' hp' hp'2 he' hFc δ hδ α g a hga hαo
  exact false_of_L2_of_quat hq (quatComponentForm_of_mulEquiv Φ hQ) hRv hRc hp₁2 hn₁ N hN e

end CFSG.ComponentClassification.Burgoyne
