module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutBeta
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAutBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Real

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.HSFLit.AutBeta
open Subgroup

variable {G : Type} [Group G]

section Make

variable {K : Subgroup G} (hK : ⁅K, K⁆ = K)
  {q : Jhat K →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S) (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
  (hqker : q.ker = center (Jhat K))

include hqsurj in
theorem real_unique {β : Jhat K ≃* Jhat K} {r r' : Equiv.Perm (Fin 42)} (hr : r ∈ R)
    (hr' : r' ∈ R) (h : ∀ e, q (β e) = r * q e * r⁻¹) (h' : ∀ e, q (β e) = r' * q e * r'⁻¹) :
    r = r' := by
  have hc : r⁻¹ * r' ∈ centralizer (S : Set (Equiv.Perm (Fin 42))) ⊓ R := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun s hs => ?_, R.mul_mem (R.inv_mem hr) hr'⟩
    obtain ⟨e, rfl⟩ := hqsurj s hs
    have := (h e).symm.trans (h' e)
    calc q e * (r⁻¹ * r') = r⁻¹ * (r * q e * r⁻¹) * r' := by group
      _ = r⁻¹ * (r' * q e * r'⁻¹) * r' := by rw [this]
      _ = r⁻¹ * r' * q e := by group
  rw [centralizer_S_inf_R, mem_bot, inv_mul_eq_one] at hc
  exact hc

include hqS hqsurj hqker in
theorem exists_r (g : ↥(normalizer (K : Set G))) :
    ∃ r ∈ R, ∀ e, q (betaHat K g.2 e) = r * q e * r⁻¹ :=
  exists_realization q hqS hqsurj (betaHat K g.2) fun e => by
    rw [hqker]
    exact mulEquiv_mem_center_iff _ e

@[expose] noncomputable def realOf : Real K where
  φ :=
    { toFun := fun g => (exists_r hqS hqsurj hqker g).choose⁻¹
      map_one' := by
        have h := exists_r hqS hqsurj hqker 1
        rw [inv_eq_one]
        exact real_unique hqsurj h.choose_spec.1 R.one_mem h.choose_spec.2 fun e => by
          rw [betaHat_eq_self K _ rfl]
          group
      map_mul' := fun g h => by
        have hg := exists_r hqS hqsurj hqker g
        have hh := exists_r hqS hqsurj hqker h
        have hgh := exists_r hqS hqsurj hqker (g * h)
        rw [← mul_inv_rev]
        congr 1
        refine real_unique hqsurj hgh.choose_spec.1
          (R.mul_mem hh.choose_spec.1 hg.choose_spec.1) hgh.choose_spec.2 fun e => ?_
        have e1 : betaHat K (g * h).2 e = betaHat K h.2 (betaHat K g.2 e) :=
          betaHat_mul K g.2 h.2 e
        rw [e1, hh.choose_spec.2, hg.choose_spec.2]
        group }
  mem_R g := R.inv_mem (exists_r hqS hqsurj hqker g).choose_spec.1
  ker_iff g := by
    have hr := exists_r hqS hqsurj hqker g
    show hr.choose⁻¹ = 1 ↔ _
    rw [inv_eq_one, ← betaHat_eq_id_iff K g.2]
    constructor
    · intro h1
      have hq : q.comp (betaHat K g.2).toMonoidHom = q.comp (MonoidHom.id _) := by
        refine MonoidHom.ext fun e => ?_
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply]
        rw [hr.choose_spec.2, h1]
        group
      have := hom_ext_of_central (commutator_jhat hK) q (hqker ▸ le_refl _) hq
      intro e
      exact DFunLike.congr_fun this e
    · intro h1
      exact real_unique hqsurj hr.choose_spec.1 R.one_mem hr.choose_spec.2 fun e => by
        rw [h1]
        group
  map_K k hk := by
    have hr := exists_r hqS hqsurj hqker ⟨k, le_normalizer hk⟩
    show hr.choose⁻¹ ∈ S
    have e1 : hr.choose = (q (jq K ⟨k, hk⟩))⁻¹ :=
      real_unique hqsurj hr.choose_spec.1 (R.inv_mem (S_le_R (hqS _))) hr.choose_spec.2
        fun e => by
          rw [betaHat_mem_K K hk e, map_mul, map_mul, map_inv]
          group
    rw [e1, inv_inv]
    exact hqS _
  onto_S s hs := by
    obtain ⟨e, rfl⟩ := hqsurj s hs
    obtain ⟨k, rfl⟩ := jq_surjective K e
    refine ⟨k, k.2, ?_⟩
    have hr := exists_r hqS hqsurj hqker ⟨k, le_normalizer k.2⟩
    show hr.choose⁻¹ = _
    have e1 : hr.choose = (q (jq K k))⁻¹ :=
      real_unique hqsurj hr.choose_spec.1 (R.inv_mem (S_le_R (hqS _))) hr.choose_spec.2
        fun e => by
          rw [betaHat_mem_K K k.2 e, map_mul, map_mul, map_inv]
          group
    rw [e1, inv_inv]

theorem realOf_phi {g : ↥(normalizer (K : Set G))} {r : Equiv.Perm (Fin 42)} (hr : r ∈ R)
    (h : ∀ e, q (betaHat K g.2 e) = r * q e * r⁻¹) :
    (realOf hK hqS hqsurj hqker).φ g = r⁻¹ := by
  have hr' := exists_r hqS hqsurj hqker g
  show hr'.choose⁻¹ = r⁻¹
  rw [real_unique hqsurj hr'.choose_spec.1 hr hr'.choose_spec.2 h]

end Make

variable [Finite G]

theorem exists_real {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hL : IsL34Type (K ⧸ Open.fusionZStar K)) : Nonempty (Real K) := by
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hL
  exact ⟨realOf hK hqS hqsurj hqker⟩

theorem exists_real_unitary {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hL : IsL34Type (K ⧸ Open.fusionZStar K)) {x : G} (hx : IsL34Unitary K x) :
    ∃ ρ : Real K, ρ.φ ⟨x, hx.1⟩ = r₄ := by
  obtain ⟨q, hqS, hqsurj, hqker, -, hβ⟩ := exists_unitary_realization hK hL hx
  have h4 : r₄⁻¹ = r₄ := inv_eq_of_mul_eq_one_right GrSLit.L34Facts.r₄_mul_self
  refine ⟨realOf hK hqS hqsurj hqker, ?_⟩
  have := realOf_phi hK hqS hqsurj hqker (g := ⟨x, hx.1⟩) r₄_mem_R hβ
  exact this.trans h4

end CFSG.ComponentClassification.HSFLit.AutL34
