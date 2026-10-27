module

public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.Generic.Induction
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverChevalley
import CFSG.Adapters.TauCetiLieModels
import CFSG.LieType.SeitzGeneration.ExcPlaneModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal TauCeti


@[expose] def EvenTag : StatedLieTag → Prop
  | .PSL | .PSU | .PSp | .POmegaPlus | .F4 | .E6 | .E7 | .E8 | .twistedE6 => True
  | _ => False

theorem EvenTag.isFundTag {t : StatedLieTag} (h : EvenTag t) :
    CFSG.ClassicalInvolution.Generic.IsFundTag t := by
  cases t <;> first | trivial | exact h.elim

theorem EvenTag.isFundTag' {t : StatedLieTag} (h : EvenTag t) :
    CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
  cases t <;> first | trivial | exact h.elim

theorem modelUniv_eq {t : StatedLieTag} (ht : EvenTag t) (n p f : ℕ) (hp : p.Prime) :
    CFSG.ClassicalInvolution.Generic.modelUniv t n p f hp = lieUniversal t n p f hp := by
  cases t <;> first | rfl | exact ht.elim

theorem modelUniv_eq' {t : StatedLieTag} (ht : EvenTag t) (n p f : ℕ) (hp : p.Prime) :
    CFSG.ClassicalInvolution.ModelFacts.modelUniv t n p f hp = lieUniversal t n p f hp := by
  cases t <;> first | rfl | exact ht.elim

section Unique

open CFSG.Adapters.RankTwoModelTransports
  (glCongr glCongr_statedScalars statedProjCongr glCongr_statedSL glCongr_statedSp glCongr_statedSU)
open CFSG.ClassicalInvolution.Upgrade (fieldIsoOfCard map_statedOmega statedQuadPlus_comp)

theorem statedClassicalModel_unique_even {X Y : Type} [Group X] [Group Y] {t : StatedLieTag}
    {n r e : ℕ} (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus)
    (hX : StatedClassicalModel X t n r e) (hY : StatedClassicalModel Y t n r e) :
    Nonempty (X ≃* Y) := by
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSL φ n)
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  · obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSU φ n (r ^ e))
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  · obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (glCongr_statedSp φ n)
      (glCongr_statedScalars φ)).trans e₂.symm)⟩
  · obtain ⟨-, K₁, _, _, hc₁, ⟨e₁⟩⟩ := hX
    obtain ⟨-, K₂, _, _, hc₂, ⟨e₂⟩⟩ := hY
    let φ := fieldIsoOfCard (hc₁.trans hc₂.symm)
    exact ⟨e₁.trans ((statedProjCongr (glCongr φ) (map_statedOmega φ (statedQuadPlus_comp φ))
      (glCongr_statedScalars φ)).trans e₂.symm)⟩

theorem lieModel_unique_even {X Y : Type} [Group X] [Group Y] {t : StatedLieTag} (ht : EvenTag t)
    {n f : ℕ} (hX : CFSG.Blueprint.LieModel X t n 2 f) (hY : CFSG.Blueprint.LieModel Y t n 2 f) :
    Nonempty (X ≃* Y) := by
  by_cases hcl : t ∈ classicalTags
  · have h4 : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus := by
      cases t <;> simp_all [EvenTag, classicalTags]
    exact statedClassicalModel_unique_even h4 (hX.statedClassicalModel hcl)
      (hY.statedClassicalModel hcl)
  · have hch : t ∈ chevalleyExceptionalTags := by
      cases t <;> simp_all [EvenTag, classicalTags, chevalleyExceptionalTags]
    exact CFSG.ClassicalInvolution.Upgrade.chevalleyExceptionalModel_unique
      (hX.chevalleyExceptionalModel hch) (hY.chevalleyExceptionalModel hch)

end Unique

theorem exists_cover_aux {U : LieUniversal} {t : StatedLieTag} (ht : EvenTag t) {n f : ℕ}
    (hq : CFSG.Open.IsQuasisimple U.K)
    (hY : CFSG.Blueprint.LieModel (U.K ⧸ Subgroup.center U.K) t n 2 f) {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X t n 2 f) :
    ∃ ψ₀ : U.K →* X, Function.Surjective ψ₀ ∧ ψ₀.ker ≤ Subgroup.center U.K ∧
      IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨E⟩ := lieModel_unique_even ht hY hX
  have hsimple : IsSimpleGroup (U.K ⧸ Subgroup.center U.K) := hq.2
  haveI := hsimple
  have hsimpleX : IsSimpleGroup X := MulEquiv.isSimpleGroup E.symm
  set ψ₀ : U.K →* X := E.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center U.K)) with hψ₀
  have hsurj : Function.Surjective ψ₀ := E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ₀.ker ≤ Subgroup.center U.K := fun k hk => by
    have h1 : E (QuotientGroup.mk' (Subgroup.center U.K) k) = 1 := hk
    rw [map_eq_one_iff _ E.injective] at h1
    exact (QuotientGroup.eq_one_iff k).1 h1
  refine ⟨ψ₀, hsurj, hker, hsimpleX, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have hcom : commutator U.K ≤ ψ₀.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (hcomm _ _)
  rw [hq.1] at hcom
  haveI := hsimpleX.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  obtain ⟨k, rfl⟩ := hsurj x
  exact hx (hcom (Subgroup.mem_top k))

theorem exists_cover_even {t : StatedLieTag} (ht : EvenTag t) {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X t n 2 f) :
    ∃ ψ₀ : (lieUniversal t n 2 f Nat.prime_two).K →* X, Function.Surjective ψ₀ ∧
      ψ₀.ker ≤ Subgroup.center (lieUniversal t n 2 f Nat.prime_two).K ∧
      IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨hq, hY⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n 2 f Nat.prime_two
    ht.isFundTag hadm
  have h := exists_cover_aux ht hq hY hX
  rwa [modelUniv_eq ht] at h

section CatModels

open CFSG.LieType.SeitzGeneration (Cat exists_field_pow exists_catEquiv_adjointGroup)
open CFSG.LieType.Chevalley CFSG.TauCetiBridge

@[expose] def EvenScope : LieTypeIndex → Prop
  | .A r q => q.p = 2 ∧ 2 ≤ r
  | .twistedA r q => q.p = 2 ∧ 3 ≤ r
  | .B _ q => q.p = 2
  | .D _ q => q.p = 2
  | .E6 q => q.p = 2
  | .E7 q => q.p = 2
  | .E8 q => q.p = 2
  | .F4 q => q.p = 2
  | .twistedE6 q => q.p = 2
  | _ => False

theorem blueprintLieModel_of_models {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : CFSG.Models.LieModel G t n p f) :
    CFSG.Blueprint.LieModel G t n p f := by
  refine Or.inl ⟨ht, ?_⟩
  rcases h.2 with h' | ⟨-, ⟨d', hd'v⟩, hd', -⟩
  · exact h'
  · exfalso
    simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> cases d' <;>
      simp [CFSG.Models.NamesTag] at hd'

theorem untwistedChevalleyModel_cat {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid) :
    UntwistedChevalleyModel (Cat ⟨c q, hv⟩) τ (q.p ^ q.exponent) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup hB q hv
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let eA : ↥(adjointGroup τ K) ≃* AdjointQuotient τ K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact ⟨K, inferInstance, inferInstance, by rw [hK, PrimePower.card_def], ⟨e.trans eA⟩⟩

theorem blueprintLieModel_cat_F4 {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid) :
    CFSG.Blueprint.LieModel (Cat ⟨.F4 q, hv⟩) .F4 0 q.p q.exponent :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedChevalleyModel_cat Even.chevalleyBridgesAll.f4 q hv⟩)

theorem blueprintLieModel_cat_E6 {q : PrimePower} (hv : (LieTypeIndex.E6 q).Valid) :
    CFSG.Blueprint.LieModel (Cat ⟨.E6 q, hv⟩) .E6 0 q.p q.exponent :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedChevalleyModel_cat Even.chevalleyBridgesAll.e6 q hv⟩)

theorem blueprintLieModel_cat_E7 {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid) :
    CFSG.Blueprint.LieModel (Cat ⟨.E7 q, hv⟩) .E7 0 q.p q.exponent :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedChevalleyModel_cat Even.chevalleyBridgesAll.e7 q hv⟩)

theorem blueprintLieModel_cat_E8 {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) :
    CFSG.Blueprint.LieModel (Cat ⟨.E8 q, hv⟩) .E8 0 q.p q.exponent :=
  Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩,
    untwistedChevalleyModel_cat Even.chevalleyBridgesAll.e8 q hv⟩)

theorem blueprintLieModel_cat_twistedE6 {q : PrimePower} (hv : (LieTypeIndex.twistedE6 q).Valid) :
    CFSG.Blueprint.LieModel (Cat ⟨.twistedE6 q, hv⟩) .twistedE6 0 q.p q.exponent := by
  obtain ⟨K, _, _, hK, -⟩ := exists_field_pow q (m := TwistTag.E6.order) TwistTag.E6.order_pos
  rw [PrimePower.card_def] at hK
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p q.exponent_pos K hK
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.twistedE6 q hv K (by rw [PrimePower.card_def]; exact hK)
    σ.toRingHom hσ'
  exact Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance,
    inferInstance, hK, σ.toRingHom, hσ'', ⟨φ.symm⟩⟩)

theorem exists_blueprintLieModel_of_scope (d : ValidLieTypeIndex) (hs : EvenScope d.1) :
    ∃ (t : StatedLieTag) (n f : ℕ), EvenTag t ∧ StatedLieAdmissible t n 2 f ∧
      ¬ (t = .PSL ∧ n = 2) ∧ ¬ (t = .PSU ∧ n = 3) ∧
      CFSG.Blueprint.LieModel (Cat d) t n 2 f := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    have hq2 : q.p = 2 := hs.1
    have h := CFSG.Models.lieModel_A r q hv (MulEquiv.refl (Cat ⟨.A r q, hv⟩))
    rw [hq2] at h
    have hb := blueprintLieModel_of_models (by simp [classicalTags]) h
    exact ⟨.PSL, r + 1, q.exponent, trivial, hb.admissible, by have := hs.2; simp; omega,
      by simp, hb⟩
  | twistedA r q =>
    have hq2 : q.p = 2 := hs.1
    have h := CFSG.Models.lieModel_twistedA r q hv (MulEquiv.refl (Cat ⟨.twistedA r q, hv⟩))
    have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := by
      simp [ValidLieTypeIndex.characteristic, hq2]
    have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent := by
      simp [ValidLieTypeIndex.fieldExponent]
    rw [hc, hf] at h
    have hb := blueprintLieModel_of_models (by simp [classicalTags]) h
    exact ⟨.PSU, r + 1, q.exponent, trivial, hb.admissible, by simp,
      by have := hs.2; simp; omega, hb⟩
  | B r q =>
    have hq2 : q.p = 2 := hs
    rcases CFSG.Models.lieModel_B r q hv (MulEquiv.refl (Cat ⟨.B r q, hv⟩)) with h | h
    · rw [hq2] at h
      have hb := blueprintLieModel_of_models (by simp [classicalTags]) h
      exact ⟨.PSp, r, q.exponent, trivial, hb.admissible, by simp, by simp, hb⟩
    · exfalso
      exact h.1.2.2.2 hq2
  | D r q =>
    have hq2 : q.p = 2 := hs
    have h := CFSG.Models.lieModel_D r q hv (MulEquiv.refl (Cat ⟨.D r q, hv⟩))
    rw [hq2] at h
    have hb := blueprintLieModel_of_models (by simp [classicalTags]) h
    exact ⟨.POmegaPlus, r, q.exponent, trivial, hb.admissible, by simp, by simp, hb⟩
  | E6 q =>
    have hq2 : q.p = 2 := hs
    have h := blueprintLieModel_cat_E6 hv
    rw [hq2] at h
    exact ⟨.E6, 0, q.exponent, trivial, h.admissible, by simp, by simp, h⟩
  | E7 q =>
    have hq2 : q.p = 2 := hs
    have h := blueprintLieModel_cat_E7 hv
    rw [hq2] at h
    exact ⟨.E7, 0, q.exponent, trivial, h.admissible, by simp, by simp, h⟩
  | E8 q =>
    have hq2 : q.p = 2 := hs
    have h := blueprintLieModel_cat_E8 hv
    rw [hq2] at h
    exact ⟨.E8, 0, q.exponent, trivial, h.admissible, by simp, by simp, h⟩
  | F4 q =>
    have hq2 : q.p = 2 := hs
    have h := blueprintLieModel_cat_F4 hv
    rw [hq2] at h
    exact ⟨.F4, 0, q.exponent, trivial, h.admissible, by simp, by simp, h⟩
  | twistedE6 q =>
    have hq2 : q.p = 2 := hs
    have h := blueprintLieModel_cat_twistedE6 hv
    rw [hq2] at h
    exact ⟨.twistedE6, 0, q.exponent, trivial, h.admissible, by simp, by simp, h⟩
  | C r q => exact hs.elim
  | twistedD r q => exact hs.elim
  | G2 q => exact hs.elim
  | trialityD4 q => exact hs.elim
  | suzuki m => exact hs.elim
  | reeG2 m => exact hs.elim
  | reeF4 m => exact hs.elim
  | tits => exact hs.elim

end CatModels

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
