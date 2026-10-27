
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandardBase

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem not_isCyclic_of_card {K : Type*} [Group K] (h16 : Nat.card K = 16)
    (h4 : ∀ z : K, z ^ 4 = 1) : ¬ IsCyclic K := by
  intro hc
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [h16]; norm_num)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  have ho : orderOf g = 16 := by
    rw [← h16]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  have hd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one (h4 g)
  rw [ho] at hd
  exact absurd hd (by norm_num)

theorem exists_kerOmega {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)}
    (hcen : q.ker ≤ center E) : ∃ K : Subgroup E, ∀ z, z ∈ K ↔ z ∈ q.ker ∧ z * z = 1 := by
  refine ⟨{ carrier := {z | z ∈ q.ker ∧ z * z = 1}
            one_mem' := ⟨one_mem _, mul_one 1⟩
            mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, ?_⟩
            inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ },
    fun z => Iff.rfl⟩
  have hab := mem_center_iff.mp (hcen hb.1) a
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← hab]
    _ = a * a * (b * b) := by group
    _ = 1 := by rw [ha.2, hb.2, one_mul]

variable {G : Type} [Group G] [Finite G]

theorem card_center_jhat (J : Subgroup G) :
    Nat.card (center (Jhat J)) * Nat.card (oddIn J) = Nat.card (zStarIn J) := by
  have h1 : Nat.card (zStarIn J) = Nat.card (Open.fusionZStar ↥J) := by
    rw [zStarIn, Subgroup.card_map_of_injective Subtype.val_injective]
  have h2 : Nat.card (oddIn J) = Nat.card (pPrimeCore 2 ↥J) := by
    rw [oddIn, Subgroup.card_map_of_injective Subtype.val_injective]
  rw [h1, h2, GrS4.fusionZStar_eq_comap_pPrimeCore,
    card_comap_eq (jq J) _ (fun e _ => jq_surjective J e), QuotientGroup.ker_mk']

end CFSG.ComponentClassification.GrSLit.L34Facts
