module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBCover
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSp4Lift

public section

namespace CFSG.ComponentClassification.CatFactsL4U4.BurgD

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne
open CFSG.ComponentClassification.Burgoyne.PSL CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.UnbalancingLocal
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def negOneSL : SL(4, F) :=
  ⟨-1, by rw [det_neg, det_one, Fintype.card_fin]; norm_num⟩

theorem coe_negOneSL : ((negOneSL : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = -1 := rfl

theorem exists_sl4_transport {J : Type} [Group J] [Finite J] {K : Subgroup J} [K.Normal]
    {t : J} {Y : Subgroup J} {c : K ⧸ pPrimeCore 2 K} (hH : PropBHyp J K t Y c) [Finite F]
    (hF : ringChar F ≠ 2)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* projectiveSL 4 F)
    {A : GL (Fin 4) F} (hA : socleAction θ ((rhoZ K).rangeRestrict t) = conjAut 4 F A)
    {H : GL (Fin 4) F} {J₀ : Finset (Fin 4)} {μ : Fˣ}
    (hHA : H * A * H⁻¹ = GeneralLinearGroup.scalar (Fin 4) μ * signGL F J₀) :
    ∃ (e : SL(4, F) ≃* (K ⧸ pPrimeCore 2 K)) (ψ' : (rhoZ K).range →* MulAut (projectiveSL 4 F)),
      Function.Injective ψ' ∧
      (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range ≤ ψ'.range ∧
      ψ' ((rhoZ K).rangeRestrict t) = conjAut 4 F (signGL F J₀) ∧ e negOneSL = c ∧
      ∀ j : J, descendAut 4 F (MulAut.congr e.symm (phiO K j)) =
        ψ' ((rhoZ K).rangeRestrict j) := by
  obtain ⟨hq, hM4, -, -, -, s, hs2, -, -, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2, -⟩ := id hH
  have hII : PropBHypII (K ⧸ pPrimeCore 2 K) c := ⟨s, hs2, Q, hQs, hQc, hQiso, hcZ, hcQ, hc2⟩
  obtain ⟨hsimple, hnab, -, -, -⟩ := hM4
  set ψ := socleAction θ with hψdef
  have hψ := socleAction_injective hsimple hnab θ
  have hInn : (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  obtain ⟨hψ', hInn'⟩ := conj_embedding hψ hInn (conjAut 4 F H)
  set ψ' := (MulAut.conj (conjAut 4 F H)).toMonoidHom.comp ψ with hψ'def
  have hψ't : ψ' ((rhoZ K).rangeRestrict t) = conjAut 4 F (signGL F J₀) := by
    change conjAut 4 F H * ψ _ * (conjAut 4 F H)⁻¹ = _
    rw [hA, ← map_inv, ← map_mul, ← map_mul, hHA, map_mul, conjAut_scalar, one_mul]
  have hInnN := conj_range_normal (T := projectiveSL 4 F)
  have hpre : ∀ x, ψ' x ∈ (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range ↔
      ψ x ∈ (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range := by
    intro x
    change conjAut 4 F H * ψ x * (conjAut 4 F H)⁻¹ ∈ _ ↔ _
    constructor
    · intro h
      have := hInnN.conj_mem _ h (conjAut 4 F H)⁻¹
      rwa [inv_inv, show (conjAut 4 F H)⁻¹ * (conjAut 4 F H * ψ x * (conjAut 4 F H)⁻¹) *
        conjAut 4 F H = ψ x by group] at this
    · intro h
      exact hInnN.conj_mem _ h _
  have hsocle : ∀ x : (rhoZ K).range, x ∈ GeneralizedFitting.subgroup (rhoZ K).range ↔
      ψ' x ∈ (MulAut.conj : projectiveSL 4 F →* MulAut (projectiveSL 4 F)).range :=
    fun x => by rw [hpre, mem_socle_iff hsimple hnab θ]
  set β : SL(4, F) →* (rhoZ K).range :=
    factorHom hψ' (conjProj 4 F) (fun g => hInn' ⟨_, rfl⟩) with hβ
  have hrange := liftHom_range_eq K hq hsimple hnab
  have hβr : β.range = (liftHom K).range := by
    rw [hrange]
    ext x
    rw [hsocle]
    constructor
    · rintro ⟨g, rfl⟩
      rw [factorHom_spec]
      exact ⟨_, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨g, rfl⟩ := proj_surjective 4 F y
      refine ⟨g, hψ' ?_⟩
      rw [factorHom_spec]
      exact hy
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* SL(4, F)),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : SL(4, F) →* E, ∀ x, π (s x) = x := by
    intro E _ _ π hπ hker h2
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.sl_central_two_extension_splitting 3 hF hπ hker h2
    exact ⟨s, hs⟩
  obtain ⟨α, hαβ, hαs, -⟩ := exists_cover K hsplit hq hβr
  have hcα : α negOneSL = c := (burgoynePropBSL4CoverInput F hF _ α hαs c hII negOneSL rfl).symm
  have key : ∀ y : SL(4, F), MulAut.conj (proj 4 F y) = ψ' (liftHom K (α y)) := fun y => by
    rw [hαβ, factorHom_spec]
    rfl
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hαinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [mem_bot]
    have hpg : proj 4 F g = 1 := by
      apply hinj
      rw [map_one, key g, hg, map_one, map_one]
    obtain ⟨r, hr4, hr⟩ := mem_scalars.1 (proj_eq_one_iff.1 hpg)
    have hr4' : ((r : F) ^ 2 - 1) * ((r : F) ^ 2 + 1) = 0 := by
      have := congrArg Units.val hr4
      rw [Units.val_pow_eq_pow_val, Units.val_one] at this
      linear_combination this
    rcases mul_eq_zero.1 hr4' with h1 | h1
    · have h1' : ((r : F) - 1) * ((r : F) + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h1' with h3 | h3
      · apply Subtype.ext
        rw [hr, sub_eq_zero.1 h3, map_one, Matrix.SpecialLinearGroup.coe_one]
      · exfalso
        apply hc1
        have hgn : g = negOneSL := by
          apply Subtype.ext
          rw [hr, eq_neg_of_add_eq_zero_left h3, coe_negOneSL, map_neg, map_one]
        rw [← hcα, ← hgn, hg]
    · exfalso
      apply hc1
      have hgg : g * g = negOneSL := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, hr, coe_negOneSL, ← map_mul, ← pow_two,
          eq_neg_of_add_eq_zero_left h1, map_neg, map_one]
      rw [← hcα, ← hgg, map_mul, hg, mul_one]
  set e : SL(4, F) ≃* (K ⧸ pPrimeCore 2 K) := MulEquiv.ofBijective α ⟨hαinj, hαs⟩ with he
  have heα : ∀ g, e g = α g := fun g => rfl
  refine ⟨e, ψ', hψ', hInn', hψ't, hcα, fun j => ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective 4 F x
  rw [descendAut_proj]
  apply hinj
  change MulAut.conj (proj 4 F (e.symm (phiO K j (e g)))) =
    MulAut.conj (ψ' ((rhoZ K).rangeRestrict j) (proj 4 F g))
  rw [key, ← mul_conj_mul_inv, key, ← heα, e.apply_symm_apply, heα, liftHom_conj, map_mul,
    map_mul, map_inv]

end CFSG.ComponentClassification.CatFactsL4U4.BurgD
