
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowPositionBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G] {J P : Subgroup G}

theorem exists_sylow_standard
    [Finite G] (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    (hP : IsSylowTwoIn P J) :
    ∃ (q : Jhat J →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat J), (∀ e, q e ∈ S) ∧
      (∀ s ∈ S, ∃ e, q e = s) ∧ q.ker = center (Jhat J) ∧ (∀ e ∈ q.ker, e ^ 3 = 1 → e = 1) ∧
      q.comp l = sigma ∧ Function.Surjective l ∧
      ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e := by
  obtain ⟨q, hqS, hqsurj, hqker, h3⟩ := exists_jq hL
  obtain ⟨g, hgS, hg⟩ := exists_conj_sylow_image hP hqS hqsurj
  obtain ⟨hS', hsurj', hker'⟩ := conj_jq hqS hqsurj (R.inv_mem (S_le_R hgS))
  set q' := (MulAut.conj g⁻¹).toMonoidHom.comp q with hq'
  have hq'e : ∀ e, q' e = g⁻¹ * q e * g := fun e => by simp [hq']
  have hker'' : q'.ker = center (Jhat J) := by rw [hker', hqker]
  obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hJ) q' hS' hsurj' (hker'' ▸ le_refl _)
  refine ⟨q', l, hS', hsurj', hker'', by rw [hker']; exact h3, hl, hls, fun e => ?_⟩
  rw [hq'e]
  constructor
  · intro he
    obtain ⟨-, p, hpP, hpJ, hpe⟩ := (hg _).2 he
    have hz : (jq J ⟨p, hpJ⟩)⁻¹ * e ∈ center (Jhat J) := by
      rw [← hqker, MonoidHom.mem_ker, map_mul, map_inv, hpe, inv_mul_cancel]
    obtain ⟨p', hp'P, hp'J, hp'e⟩ := exists_mem_of_mem_center hP hz
    refine ⟨p * p', P.mul_mem hpP hp'P, J.mul_mem hpJ hp'J, ?_⟩
    have e1 : (⟨p * p', J.mul_mem hpJ hp'J⟩ : J) = ⟨p, hpJ⟩ * ⟨p', hp'J⟩ := rfl
    rw [e1, map_mul, hp'e]
    group
  · rintro ⟨p, hpP, hpJ, rfl⟩
    exact (hg _).1 ⟨hqS _, p, hpP, hpJ, rfl⟩

variable {hPJ : P ≤ J}

variable {q : Jhat J →* Equiv.Perm (Fin 42)}

end CFSG.ComponentClassification.GrSLit.L34Facts
