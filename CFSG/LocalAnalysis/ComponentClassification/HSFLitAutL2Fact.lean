module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL2Model
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutBeta

public section

namespace CFSG.ComponentClassification.HSFLit.AutL2

open CFSG Subgroup Equiv CFSG.GH74.KGroups
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.HSFLit.AutBeta

variable {G : Type} [Group G] {J : Subgroup G} {n : ℕ} (M : AutModel (Jhat J) (Perm (Fin n)))

@[expose] noncomputable def rhoHom : ↥(normalizer (J : Set G)) →* Perm (Fin n) where
  toFun g := (rhoM M g.2)⁻¹
  map_one' := by rw [rhoM_one M _ rfl, inv_one]
  map_mul' g h := by
    show (rhoM M (mul_mem g.2 h.2))⁻¹ = _
    rw [rhoM_mul M g.2 h.2, mul_inv_rev]

theorem rhoHom_apply (g : ↥(normalizer (J : Set G))) : rhoHom M g = (rhoM M g.2)⁻¹ := rfl

theorem rhoHom_eq_one_iff (g : ↥(normalizer (J : Set G))) :
    rhoHom M g = 1 ↔ (g : G) ∈ coreActionKernel J := by
  rw [rhoHom_apply, inv_eq_one, ← betaHat_eq_id_iff J g.2]
  constructor
  · exact rhoM_eq_one M g.2
  · intro h
    have h1 : betaHat J g.2 = 1 := MulEquiv.ext h
    rw [rhoM, h1, map_one]
    rfl

variable [Finite G]

theorem l2UnbalancingAutFact :
    L2UnbalancingAutFact := by
  intro G _ _ a x J R htri hL hR2
  obtain ⟨-, hxo, -, -, -, hxJ, hDJ⟩ := htri
  have hx2 : x * x = 1 := by rw [← pow_two, ← hxo, pow_orderOf_eq_one]
  have hset : {y | ∃ j ∈ J, ∃ d ∈ ({x} : Set G), y = j⁻¹ * d⁻¹ * j * d} =
      {y | ∃ j ∈ J, y = j⁻¹ * x⁻¹ * j * x} := by
    ext y
    simp
  have hxJ' : closure {y | ∃ j ∈ J, ∃ d ∈ ({x} : Set G), y = j⁻¹ * d⁻¹ * j * d} = J := by
    rw [hset]
    exact hxJ
  have hxN : x ∈ normalizer (J : Set G) := mem_normalizer_of_closure hxJ' (Set.mem_singleton x)
  obtain ⟨n, M, hF, hidx⟩ := exists_l2Model' hL
  obtain ⟨hρ2, hρ1, hρP⟩ := rhoM_outer M hF hxN hx2 hxJ' hDJ fun d hd => (mem_inf.mp hd).1
  have hrA := rhoM_mem M hxN
  have hsq : ∀ w ∈ M.A, w * rhoM M hxN = rhoM M hxN * w → (∃ k : ℕ, w ^ 2 ^ k = 1) →
      w * w = 1 := fun w hw hwr ⟨k, hk⟩ =>
    hF.outer2 _ hrA hρ2 hρ1 hρP w hw hwr (hF.two w hw k hk)
  constructor
  · intro hRle
    have hRN : R ≤ normalizer (J : Set G) := fun g hg => (mem_inf.1 (hRle hg)).1
    set X := (R.subgroupOf (normalizer (J : Set G))).map (rhoHom M)
    have hX : ∀ w ∈ X, w ∈ M.A ∧ w * rhoM M hxN = rhoM M hxN * w ∧ w * w = 1 := by
      intro w hw
      obtain ⟨g, hg, rfl⟩ := mem_map.1 hw
      have hgx : (g : G) * x = x * g :=
        mem_centralizer_singleton_iff.1 (mem_inf.1 (hRle (mem_subgroupOf.1 hg))).2
      have hc := rhoM_comm M g.2 hxN hgx
      have hA : rhoHom M g ∈ M.A := M.A.inv_mem (rhoM_mem M g.2)
      have hc' : rhoHom M g * rhoM M hxN = rhoM M hxN * rhoHom M g := by
        rw [rhoHom_apply]
        calc (rhoM M g.2)⁻¹ * rhoM M hxN =
            (rhoM M g.2)⁻¹ * (rhoM M hxN * rhoM M g.2) * (rhoM M g.2)⁻¹ := by group
          _ = (rhoM M g.2)⁻¹ * (rhoM M g.2 * rhoM M hxN) * (rhoM M g.2)⁻¹ := by rw [hc]
          _ = rhoM M hxN * (rhoM M g.2)⁻¹ := by group
      obtain ⟨k, hk⟩ := hR2 ⟨g, mem_subgroupOf.1 hg⟩
      have hk' : rhoHom M g ^ 2 ^ k = 1 := by
        rw [← map_pow]
        have : g ^ 2 ^ k = 1 := Subtype.ext (by
          have := congrArg Subtype.val hk
          simpa using this)
        rw [this, map_one]
      exact ⟨hA, hc', hsq _ hA hc' ⟨k, hk'⟩⟩
    refine ⟨fun y hy => ?_, ?_⟩
    · have h1 := (hX _ (mem_map_of_mem _ (mem_subgroupOf.2 (show ((⟨y, hRN hy⟩ :
        ↥(normalizer (J : Set G))) : G) ∈ R from hy)))).2.2
      rw [← map_mul] at h1
      exact (rhoHom_eq_one_iff M _).1 h1
    · rw [card_eq_of_hom (rhoHom M) (rhoHom_eq_one_iff M) hRN]
      apply Nat.mul_le_mul_right
      have hXA : X ≤ M.A := fun w hw => (hX w hw).1
      have h1 : Nat.card X ≤ 2 * Nat.card ↥(M.P ⊓ X) := card_le_two_mul_inf hF.le hidx hXA
      have h2 := card_le_two_of_inv hF hrA hρ2 hρ1 hρP (X := M.P ⊓ X) inf_le_left
        (fun w hw => (hX w (mem_inf.1 hw).2).2.2) fun w hw => (hX w (mem_inf.1 hw).2).2.1
      show Nat.card X ≤ 4
      omega
  · intro hRle
    have hRJ : R ≤ J := fun g hg => (mem_inf.1 (hRle hg)).1
    let χ : ↥R →* Perm (Fin n) :=
      ((M.P.subtype.comp M.e.toMonoidHom).comp (jq J)).comp (inclusion hRJ)
    have hχ : Function.Injective χ := by
      intro u v h
      have h1 : M.e (jq J ⟨u, hRJ u.2⟩) = M.e (jq J ⟨v, hRJ v.2⟩) := Subtype.ext h
      exact Subtype.ext (eq_of_jq_eq hRJ hR2 u.2 v.2 (M.e.injective h1))
    have hY : ∀ w ∈ χ.range, w ∈ M.P ∧ w * rhoM M hxN = rhoM M hxN * w := by
      rintro _ ⟨u, rfl⟩
      refine ⟨(M.e (jq J ⟨u, hRJ u.2⟩)).2, ?_⟩
      have hux : (u : G) * x = x * u := mem_centralizer_singleton_iff.1 (mem_inf.1 (hRle u.2)).2
      have hfix : betaHat J hxN (jq J ⟨u, hRJ u.2⟩) = jq J ⟨u, hRJ u.2⟩ := by
        rw [betaHat_jq]
        congr 1
        apply Subtype.ext
        rw [coe_conjJ]
        calc x⁻¹ * u * x = x⁻¹ * (u * x) := by group
          _ = x⁻¹ * (x * u) := by rw [hux]
          _ = u := by group
      have h1 := rhoM_spec M hxN (jq J ⟨u, hRJ u.2⟩)
      rw [hfix] at h1
      show ((M.e (jq J ⟨u, hRJ u.2⟩) : M.P) : Perm (Fin n)) * rhoM M hxN =
        rhoM M hxN * (M.e (jq J ⟨u, hRJ u.2⟩) : Perm (Fin n))
      calc ((M.e (jq J ⟨u, hRJ u.2⟩) : M.P) : Perm (Fin n)) * rhoM M hxN =
          rhoM M hxN * (M.e (jq J ⟨u, hRJ u.2⟩) : Perm (Fin n)) * (rhoM M hxN)⁻¹ *
            rhoM M hxN := by rw [← h1]
        _ = rhoM M hxN * (M.e (jq J ⟨u, hRJ u.2⟩) : Perm (Fin n)) := by group
    have hY2 : ∀ w ∈ χ.range, w * w = 1 := by
      rintro _ ⟨u, rfl⟩
      obtain ⟨k, hk⟩ := hR2 u
      exact hsq _ (hF.le (hY _ ⟨u, rfl⟩).1) (hY _ ⟨u, rfl⟩).2
        ⟨k, by rw [← map_pow, hk, map_one]⟩
    have h1 := card_le_two_of_inv hF hrA hρ2 hρ1 hρP (X := χ.range) (fun w hw => (hY w hw).1)
      hY2 fun w hw => (hY w hw).2
    have h2 : Nat.card R = Nat.card χ.range := by
      rw [← Nat.card_range_of_injective hχ]
      rfl
    rw [h2]
    exact h1

end CFSG.ComponentClassification.HSFLit.AutL2
