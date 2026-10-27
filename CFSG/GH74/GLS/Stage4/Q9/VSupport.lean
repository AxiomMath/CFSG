module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup CFSG.RankThreeEvenClassification.Helpers

section Klein

variable {G : Type*} [Group G]

private theorem mem_closure_pair_iff {z u : G} (hz : z * z = 1) (hu : u * u = 1) (hzu : z * u = u * z)
    (x : G) : x ∈ closure ({z, u} : Set G) ↔ x = 1 ∨ x = z ∨ x = u ∨ x = z * u := by
  have e1 : z * (z * u) = u := by rw [← mul_assoc, hz, one_mul]
  have e2 : z * u * z = u := by rw [hzu, mul_assoc, hz, mul_one]
  have e3 : u * (z * u) = z := by rw [hzu, ← mul_assoc, hu, one_mul]
  have e4 : z * u * u = z := by rw [mul_assoc, hu, mul_one]
  have e5 : z * u * (z * u) = 1 := by rw [mul_assoc, e3, hz]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hzui : (z * u)⁻¹ = z * u := by rw [mul_inv_rev, hzi, hui, hzu]
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h'] <;>
        simp [hz, hu, e1, e2, e3, e4, e5, hzu.symm]
    | inv x _ hx =>
      rcases hx with h | h | h | h <;> rw [h] <;> simp [hzi, hui, hzui]
  · rintro (h | h | h | h) <;> rw [h]
    · exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private theorem mul_self_eq_one_of_orderOf_eq_two {z : G} (hz : orderOf z = 2) : z * z = 1 := by
  rw [← pow_two, ← hz]
  exact pow_orderOf_eq_one z

private theorem ne_one_of_orderOf_eq_two {z : G} (hz : orderOf z = 2) : z ≠ 1 := by
  rintro rfl
  simp at hz

private theorem card_closure_pair {z u : G} (hz : orderOf z = 2) (hu : orderOf u = 2) (hzu : z * u = u * z)
    (hne : z ≠ u) : Nat.card (closure ({z, u} : Set G)) = 2 ^ 2 := by
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz
  have hu2 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two hz
  have hu1 : u ≠ 1 := ne_one_of_orderOf_eq_two hu
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hset : ((closure ({z, u} : Set G) : Subgroup G) : Set G) = {1, z, u, z * u} := by
    ext x
    simp only [SetLike.mem_coe, mem_closure_pair_iff hz2 hu2 hzu x, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have hcard : Nat.card (closure ({z, u} : Set G)) =
      Set.ncard ((closure ({z, u} : Set G) : Subgroup G) : Set G) := Nat.card_coe_set_eq _
  have h1 : (1 : G) ∉ ({z, u, z * u} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨hz1.symm, hu1.symm, fun h => hne ?_⟩
    exact hzi.symm.trans (eq_inv_of_mul_eq_one_right h.symm).symm
  have h2 : z ∉ ({u, z * u} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, fun h => hu1 (mul_eq_left.mp h.symm)⟩
  have h3 : u ≠ z * u := fun h => hz1 (mul_eq_right.mp h.symm)
  rw [hcard, hset, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]
  norm_num

private theorem sq_eq_one_of_mem_closure_pair {z u : G} (hz : orderOf z = 2) (hu : orderOf u = 2)
    (hzu : z * u = u * z) (x : closure ({z, u} : Set G)) : x ^ 2 = 1 := by
  have hz2 := mul_self_eq_one_of_orderOf_eq_two hz
  have hu2 := mul_self_eq_one_of_orderOf_eq_two hu
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have hu2' : u ^ 2 = 1 := by rw [pow_two]; exact hu2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  rcases (mem_closure_pair_iff hz2 hu2 hzu x).mp x.2 with h | h | h | h <;> rw [h]
  · exact one_pow 2
  · exact hz2'
  · exact hu2'
  · rw [Commute.mul_pow hzu, hz2', hu2', one_mul]

private theorem eq_of_ne_one_of_mem_closure_pair {z u : G} (hz : orderOf z = 2) (hu : orderOf u = 2)
    (hzu : z * u = u * z) (x : closure ({z, u} : Set G)) (hx : x ≠ 1) :
    (x : G) = z ∨ (x : G) = u ∨ (x : G) = z * u := by
  rcases (mem_closure_pair_iff (mul_self_eq_one_of_orderOf_eq_two hz)
    (mul_self_eq_one_of_orderOf_eq_two hu) hzu x).mp x.2 with h | h | h | h
  · exact absurd (Subtype.ext h) hx
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem closure_pair_le_normalizer {z u : G} (hz : orderOf z = 2) (hu : orderOf u = 2)
    (hzu : z * u = u * z) (O : Subgroup G) (hOz : ∀ o ∈ O, z * o * z⁻¹ ∈ O)
    (hOu : ∀ o ∈ O, u * o * u⁻¹ ∈ O) : closure ({z, u} : Set G) ≤ normalizer (O : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx o ho
  rcases (mem_closure_pair_iff (mul_self_eq_one_of_orderOf_eq_two hz)
    (mul_self_eq_one_of_orderOf_eq_two hu) hzu x).mp hx with h | h | h | h <;> rw [h]
  · simpa using ho
  · exact hOz o ho
  · exact hOu o ho
  · simpa [mul_assoc] using hOz _ (hOu o ho)

end Klein

theorem odd_generation {G : Type*} [Group G] [Finite G] {z u : G} (hz : orderOf z = 2)
    (hu : orderOf u = 2) (hzu : z * u = u * z) (hne : z ≠ u) (O : Subgroup G)
    (hodd : Odd (Nat.card O)) (hOz : ∀ o ∈ O, z * o * z⁻¹ ∈ O) (hOu : ∀ o ∈ O, u * o * u⁻¹ ∈ O) :
    O = (O ⊓ Subgroup.centralizer ({z} : Set G)) ⊔ (O ⊓ Subgroup.centralizer ({u} : Set G)) ⊔
      (O ⊓ Subgroup.centralizer ({z * u} : Set G)) := by
  have hgen := coprime_centralizer_generation_of_plane 2 Nat.prime_two
    (closure ({z, u} : Set G)) O (sq_eq_one_of_mem_closure_pair hz hu hzu)
    (card_closure_pair hz hu hzu hne) hodd.not_two_dvd_nat
    (closure_pair_le_normalizer hz hu hzu O hOz hOu)
  refine le_antisymm (hgen.le.trans (iSup₂_le fun x hx => ?_))
    (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
  rcases eq_of_ne_one_of_mem_closure_pair hz hu hzu x hx with h | h | h
  · rw [h]
    exact le_sup_of_le_left le_sup_left
  · rw [h]
    exact le_sup_of_le_left le_sup_right
  · rw [h]
    exact le_sup_right

theorem odd_prime_support {G : Type*} [Group G] [Finite G] {z u : G} (hz : orderOf z = 2)
    (hu : orderOf u = 2) (hzu : z * u = u * z) (hne : z ≠ u) (O : Subgroup G)
    (hodd : Odd (Nat.card O)) (hOz : ∀ o ∈ O, z * o * z⁻¹ ∈ O) (hOu : ∀ o ∈ O, u * o * u⁻¹ ∈ O)
    (π : ℕ → Prop)
    (hπ : ∀ v ∈ ({z, u, z * u} : Set G), ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ↥(O ⊓ Subgroup.centralizer ({v} : Set G)) → π r) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card O → π r := by
  intro r hr hrO
  by_contra hπr
  have : Fact r.Prime := ⟨hr⟩
  have hcompl : ¬ 2 ∣ Nat.card O := hodd.not_two_dvd_nat
  obtain ⟨S, hS⟩ := exists_normalized_sylow_in_prime_complement_subgroup 2 Nat.prime_two
    (closure ({z, u} : Set G)) O (IsPGroup.of_card (card_closure_pair hz hu hzu hne)) hcompl
    (closure_pair_le_normalizer hz hu hzu O hOz hOu) r hr
  have hRO : (S : Subgroup O).map O.subtype ≤ O := Subgroup.map_subtype_le _
  have hRp : IsPGroup r ((S : Subgroup O).map O.subtype) := S.isPGroup'.map O.subtype
  have hRcompl : ¬ 2 ∣ Nat.card ((S : Subgroup O).map O.subtype) :=
    fun h => hcompl (h.trans (Subgroup.card_dvd_of_le hRO))
  have hgen := coprime_centralizer_generation_of_plane 2 Nat.prime_two
    (closure ({z, u} : Set G)) ((S : Subgroup O).map O.subtype)
    (sq_eq_one_of_mem_closure_pair hz hu hzu) (card_closure_pair hz hu hzu hne) hRcompl hS
  have hbot : (S : Subgroup O).map O.subtype = ⊥ := by
    refine eq_bot_iff.mpr (hgen.le.trans (iSup₂_le fun x hx => ?_))
    have hv : (x : G) ∈ ({z, u, z * u} : Set G) := by
      rcases eq_of_ne_one_of_mem_closure_pair hz hu hzu x hx with h | h | h <;> simp [h]
    have hCp : IsPGroup r ↥((S : Subgroup O).map O.subtype ⊓
        centralizer ({(x : G)} : Set G)) := hRp.to_le inf_le_left
    obtain ⟨n, hn⟩ := hCp.exists_card_eq
    rcases n with _ | n
    · exact (eq_bot_of_card_eq _ (by simpa using hn)).le
    · exfalso
      have hdvd : r ∣ Nat.card ↥(O ⊓ centralizer ({(x : G)} : Set G)) := by
        refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le (inf_le_inf_right _ hRO))
        rw [hn]
        exact dvd_pow_self r (Nat.succ_ne_zero n)
      exact hπr (hπ _ hv r hr hdvd)
  exact S.ne_bot_of_dvd_card hrO
    ((Subgroup.map_eq_bot_iff_of_injective _ O.subtype_injective).mp hbot)

end CFSG.GH74.GLS.Stage4.Q9
