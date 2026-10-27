module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3GJModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap510

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
open scoped commutatorElement

theorem hasOrderThreeLift_of_comp_fixSub_one {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) {S : Subgroup Y} (hS : GLAPComponent 3 (fixSub (1 : MulAut Y)) S)
    (hO : GLAPPrimeCore 3 ↥S = ⊥) {s : Y} (hsS : s ∈ S) (hlift : HasOrderThreeLift Y s) :
    HasOrderThreeLift (barOf 3 S) (QuotientGroup.mk (⟨s, hsS⟩ : ↥S)) := by
  rw [fixSub_one] at hS
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup Y) :=
    isQuasisimple_open_of_mulEquiv Subgroup.topEquiv hY
  have hST : S = ⊤ := eq_of_isSubnormal_of_quasisimple hq hS.2.1 (glaPComponent_perfect hS)
    (glaPComponent_ne_bot hS)
  subst hST
  have h1 := hasOrderThreeLift_of_mulEquiv (Subgroup.topEquiv (G := Y)).symm hlift
  have h2 := hasOrderThreeLift_of_mulEquiv (barEquivOfCore hO) h1
  have : (barEquivOfCore hO) ((Subgroup.topEquiv (G := Y)).symm s) =
      QuotientGroup.mk (⟨s, hsS⟩ : ↥(⊤ : Subgroup Y)) := by
    rw [barEquivOfCore_apply]
    rfl
  rwa [this] at h2

theorem hasOrderThreeLift_of_comp_fixSub {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) {α : MulAut Y} (h3 : α ^ 3 = 1) (hf : IsFieldAutThree α)
    {S : Subgroup Y} (hS : GLAPComponent 3 (fixSub α) S) (hO : GLAPPrimeCore 3 ↥S = ⊥) {s : Y}
    (hsS : s ∈ S) (hs1 : s ≠ 1) (hlift : HasOrderThreeLift Y s) :
    HasOrderThreeLift (barOf 3 S) (QuotientGroup.mk (⟨s, hsS⟩ : ↥S)) := by
  by_cases hα : α = 1
  · subst hα
    exact hasOrderThreeLift_of_comp_fixSub_one hY hS hO hsS hlift
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨π, p, f, K, _, hK, hq, hq2, e, yh, hyh, hey⟩ := exists_model_of_hasOrderThreeLift hY hlift
  obtain ⟨σ, hσ, x, hx, e₂, hc, hconj⟩ := l3gj_exists_frobModel hY hK hq2 e h3 hf hα
  obtain ⟨d⟩ := exists_frobData hK hσ
  have hq₀ := d.modThree hq
  have hKfin := hK.finite
  have hK₀fin := d.hP.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  let pm : ↥(slPi π 3 (p ^ f) K) →* ↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K) := QuotientGroup.mk' _
  have hsurj : Function.Surjective pm := QuotientGroup.mk'_surjective _
  have hker : ∀ c, pm c = 1 → c ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := fun c h => (QuotientGroup.eq_one_iff c).1 h
  have hcm : ∀ g, pm (frobSL hK σ g) = centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ) (pm g) := fun g => rfl
  have hmapker : Nat.Coprime 3 (Nat.card ↥(fixSub α ⊓ e₂.toMonoidHom.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e₂.injective, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right _
  have hfix : fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ)) = (fixSub α).map e₂.toMonoidHom := by
    rw [← hc]
    exact fixSub_congr e₂ α
  have hS' : GLAPComponent 3 (fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ))) (S.map e₂.toMonoidHom) := by
    rw [hfix]
    exact glaPComponent_map hp e₂.toMonoidHom hmapker hS
  set S' : Subgroup (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) := S.map e₂.toMonoidHom with hS'def
  set Sp : Subgroup (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)) := (fixSub (frobSL hK σ)).map pm with hSp
  have hSp_le : S' ≤ Sp := by
    calc S' = ⁅S', S'⁆ := (glaPComponent_perfect hS').symm
      _ ≤ ⁅fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ)), fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ))⁆ :=
        Subgroup.commutator_mono hS'.1 hS'.1
      _ ≤ Sp := fixSub_commutator_le_map hsurj hker hcm
  have hSp_fix : Sp ≤ fixSub (centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_fixSub, ← hcm u, mem_fixSub.1 hu]
  let θ : ↥(slPi π 3 (p ^ d.f₀) d.K₀) →* ↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K) := pm.comp d.incl
  have hrange : θ.range = Sp := by
    rw [MonoidHom.range_comp, ← d.fixSub_eq]
  have hker' : θ.ker = Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) := by
    ext s0
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : d.incl s0 ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := hker _ h
      rw [← d.map_center_incl hq] at h1
      obtain ⟨z, hz, hzs⟩ := h1
      rwa [← d.incl_injective hzs]
    · intro h
      apply (QuotientGroup.eq_one_iff _).2
      rw [← d.map_center_incl hq]
      exact ⟨s0, h, rfl⟩
  have hSS' : S' = Sp := by
    by_cases hπ2 : π = false ∧ p ^ d.f₀ = 2
    · exfalso
      obtain ⟨hπf, h2⟩ := hπ2
      have hsolv : Group.IsSolvable ↥(slPi π 3 (p ^ d.f₀) d.K₀) := by
        subst hπf
        exact (isSolvable_slPi_false_two d.hP h2).1
      have hsolvr : Group.IsSolvable ↥θ.range := Group.isSolvable_of_surjective (f := θ.rangeRestrict)
        θ.rangeRestrict_surjective
      rw [hrange] at hsolvr
      have hsolvS : Group.IsSolvable ↥S' :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hSp_le)
      have hperf : Group.IsPerfect ↥S' := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hS')
      have hnt : Nontrivial ↥S' := (Subgroup.nontrivial_iff_ne_bot _).2 (glaPComponent_ne_bot hS')
      exact Group.IsPerfect.not_isSolvable ↥S' hsolvS
    · have hne : π = false → p ^ d.f₀ ≠ 2 := fun h h2 => hπ2 ⟨h, h2⟩
      have hS₀q : CFSG.Open.IsQuasisimple ↥(slPi π 3 (p ^ d.f₀) d.K₀) := isQuasisimple_slPi d.hP hne
      let e1 : ↥(slPi π 3 (p ^ d.f₀) d.K₀) ⧸ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) ≃* ↥Sp :=
        (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
          ((QuotientGroup.quotientKerEquivRange θ).trans (MulEquiv.subgroupCongr hrange))
      have hSpq : CFSG.Open.IsQuasisimple ↥Sp :=
        isQuasisimple_open_of_mulEquiv e1.symm (isQuasisimple_quotient_center hS₀q)
      have hsn : IsSubnormal S' Sp := isSubnormal_of_le_of_le hS'.2.1 hSp_le hSp_fix
      exact eq_of_isSubnormal_of_quasisimple hSpq hsn (glaPComponent_perfect hS')
        (glaPComponent_ne_bot hS')
  have hmem : ∀ t : ↥(slPi π 3 (p ^ d.f₀) d.K₀), e₂.symm (θ t) ∈ S := by
    intro t
    have : θ t ∈ S' := by rw [hSS', ← hrange]; exact ⟨t, rfl⟩
    obtain ⟨z, hz, hzt⟩ := this
    have : e₂.symm (θ t) = z := by rw [← hzt]; exact e₂.symm_apply_apply z
    rw [this]; exact hz
  let ψ1 : ↥(slPi π 3 (p ^ d.f₀) d.K₀) →* ↥S :=
    ((e₂.symm.toMonoidHom).comp θ).codRestrict S hmem
  let Ψ : ↥(slPi π 3 (p ^ d.f₀) d.K₀) →* barOf 3 S :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)).comp ψ1
  have hΨ : ∀ t, Ψ t = QuotientGroup.mk (⟨e₂.symm (θ t), hmem t⟩ : ↥S) := fun t => rfl
  have hΨsurj : Function.Surjective Ψ := by
    intro w
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientGroup.mk_surjective w
    have : e₂ z ∈ Sp := by rw [← hSS']; exact ⟨z, hz, rfl⟩
    rw [← hrange] at this
    obtain ⟨t, ht⟩ := this
    refine ⟨t, ?_⟩
    rw [hΨ]
    congr 1
    apply Subtype.ext
    show e₂.symm (θ t) = z
    rw [show θ t = e₂ z from ht]
    exact e₂.symm_apply_apply z
  have hΨker : ∀ t, Ψ t = 1 → t ∈ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) := by
    intro t ht
    rw [hΨ, QuotientGroup.eq_one_iff, hO, Subgroup.mem_bot] at ht
    have h1 : e₂.symm (θ t) = 1 := congrArg Subtype.val ht
    have h2 : θ t = 1 := by
      have := congrArg e₂ h1
      simpa using this
    rw [← hker']
    exact h2
  have hΨcen : ∀ t ∈ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀), Ψ t = 1 := by
    intro t ht
    rw [← hker'] at ht
    have h2 : θ t = 1 := ht
    rw [hΨ, QuotientGroup.eq_one_iff, hO, Subgroup.mem_bot]
    apply Subtype.ext
    show e₂.symm (θ t) = 1
    rw [h2]
    exact map_one _
  let Λ : ↥(slPi π 3 (p ^ d.f₀) d.K₀) ⧸ Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀) ≃*
      barOf 3 S :=
    MulEquiv.ofBijective
      (QuotientGroup.lift (Subgroup.center ↥(slPi π 3 (p ^ d.f₀) d.K₀)) Ψ hΨcen)
      ⟨by
        intro a b
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            intro hab
            have h1 : Ψ a = Ψ b := hab
            rw [QuotientGroup.eq]
            apply hΨker
            rw [map_mul, map_inv, h1, inv_mul_cancel],
        by
          intro w
          obtain ⟨t, ht⟩ := hΨsurj w
          exact ⟨QuotientGroup.mk t, ht⟩⟩
  let tl : ↥(slPi π 3 (p ^ f) K) := (conjSL' hπ hx).symm yh
  have htl : (tl : GL (Fin 3) K) = x * yh * x⁻¹ := rfl
  have hord : orderOf tl = 3 := by
    have := orderOf_injective (conjSL' hπ hx).symm.toMonoidHom (conjSL' hπ hx).symm.injective yh
    rw [hyh] at this
    exact this
  have hes : e₂ s = QuotientGroup.mk tl := hconj s yh tl hey htl
  have hsSp : e₂ s ∈ Sp := by rw [← hSS']; exact ⟨s, hsS, rfl⟩
  obtain ⟨u, hu, hus⟩ := hsSp
  obtain ⟨t₀, rfl⟩ := (d.fixSub_eq ▸ hu : u ∈ d.incl.range)
  have hθt₀ : θ t₀ = e₂ s := hus
  have hcen : (d.incl t₀)⁻¹ * tl ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
    apply hker
    rw [map_mul, map_inv]
    have h1 : pm (d.incl t₀) = pm tl := hus.trans hes
    rw [h1, inv_mul_cancel]
  set z : ↥(slPi π 3 (p ^ f) K) := (d.incl t₀)⁻¹ * tl with hz
  have hz3 : z ^ 3 = 1 := pow_three_of_mem_center hK hq hcen
  have hzc : Commute tl z⁻¹ := Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hcen) tl
  have hu3 : (d.incl t₀) ^ 3 = 1 := by
    have h1 : d.incl t₀ = tl * z⁻¹ := by rw [hz]; group
    rw [h1, hzc.mul_pow, inv_pow, hz3, inv_one, mul_one]
    have := pow_orderOf_eq_one tl
    rwa [hord] at this
  have ht₀3 : t₀ ^ 3 = 1 := by
    apply d.incl_injective
    rw [map_pow, map_one]
    exact hu3
  have ht₀1 : t₀ ≠ 1 := by
    rintro rfl
    apply hs1
    have : e₂ s = 1 := by rw [← hθt₀]; exact map_one _
    exact e₂.injective (by rw [this, map_one])
  have ht₀ord : orderOf t₀ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨hp⟩
    exact orderOf_eq_prime ht₀3 ht₀1
  refine hasOrderThreeLift_of_model d.hP hq₀ Λ.symm ht₀ord ?_
  rw [MulEquiv.symm_apply_eq]
  refine Eq.symm ?_
  show Ψ t₀ = _
  rw [hΨ]
  congr 1
  apply Subtype.ext
  show e₂.symm (θ t₀) = s
  rw [hθt₀]
  exact e₂.symm_apply_apply s

end CFSG.HardMathSupport.Solomon.Coordinator
