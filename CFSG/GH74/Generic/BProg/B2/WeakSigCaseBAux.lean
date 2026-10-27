module

public import CFSG.GH74.Generic.BProg.B2.WeakSigGen

public section

namespace CFSG.GH74.Generic.BProg.B2.WeakSigCaseB

open CFSG Subgroup CFSG.GH74.Generic.BProg.B2.WeakSigGen

section Conj
variable {Y : Type} [Group Y]

theorem mem_conjugate_iff {L : Subgroup Y} {g y : Y} : y ∈ conjugate L g ↔ g * y * g⁻¹ ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simpa [mul_assoc] using hl
  · intro h
    exact ⟨g * y * g⁻¹, h, by simp [mul_assoc]⟩

theorem conjugate_conjugate (L : Subgroup Y) (a b : Y) :
    conjugate (conjugate L a) b = conjugate L (a * b) := by
  ext y
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff]
  have : a * (b * y * b⁻¹) * a⁻¹ = a * b * y * (a * b)⁻¹ := by group
  rw [this]

theorem conjugate_eq_self_iff {L : Subgroup Y} {g : Y} :
    conjugate L g = L ↔ g ∈ normalizer (L : Set Y) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h y
    rw [← mem_conjugate_iff, h]
  · intro h
    ext y
    rw [mem_conjugate_iff, ← h y]

theorem conjugate_one (L : Subgroup Y) : conjugate L 1 = L := by
  ext y; rw [mem_conjugate_iff]; simp

theorem isComponent_conjugate {L : Subgroup Y} (hL : IsComponent L) (g : Y) :
    IsComponent (conjugate L g) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) hL

theorem commute_of_ne [Finite Y] {L L' : Subgroup Y} (hL : IsComponent L) (hL' : IsComponent L')
    (hne : L ≠ L') : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := by
  have h := (CFSG.LocalCores.distinct_components_commute hL hL').resolve_left hne
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm

end Conj

section Rank
variable {Y : Type} [Group Y] [Finite Y]

theorem sup_zpowers_rank {D E₀ : Subgroup Y} {s' : Y} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hE₀ : E₀ ≤ D) (hs' : s' ∈ D) (hns : s' ∉ E₀) :
    E₀ ⊔ Subgroup.zpowers s' ≤ D ∧
      pRank 2 ↥E₀ + 1 ≤ pRank 2 ↥(E₀ ⊔ Subgroup.zpowers s') := by
  obtain ⟨hab, hsq⟩ := forall_of_isElementaryAbelian hD
  have hle : E₀ ⊔ Subgroup.zpowers s' ≤ D := sup_le hE₀ ((Subgroup.zpowers_le).mpr hs')
  refine ⟨hle, ?_⟩
  set E : Subgroup Y := E₀ ⊔ Subgroup.zpowers s' with hE
  have h1 : CFSG.IsElementaryAbelian 2 ↥E₀ :=
    isElementaryAbelian_of_forall (fun u hu v hv => hab u (hE₀ hu) v (hE₀ hv))
      (fun u hu => hsq u (hE₀ hu))
  have h2 : CFSG.IsElementaryAbelian 2 ↥E :=
    isElementaryAbelian_of_forall (fun u hu v hv => hab u (hle hu) v (hle hv))
      (fun u hu => hsq u (hle hu))
  have hlt : Nat.card ↥E₀ < Nat.card ↥E := by
    by_contra hcon
    have heq : E₀ = E := Subgroup.eq_of_le_of_card_ge le_sup_left (not_lt.mp hcon)
    exact hns (heq ▸ (le_sup_right : Subgroup.zpowers s' ≤ E) (Subgroup.mem_zpowers s'))
  have hdvd : Nat.card ↥E₀ ∣ Nat.card ↥E := Subgroup.card_dvd_of_le le_sup_left
  obtain ⟨m, hm⟩ := hdvd
  have hpos : 0 < Nat.card ↥E₀ := Nat.card_pos
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · simp at hm; omega
    · simp at hm; omega
    · omega
  have e1 := card_eq_two_pow_pRank h1
  have e2 := card_eq_two_pow_pRank h2
  have : 2 ^ (pRank 2 ↥E₀ + 1) ≤ 2 ^ pRank 2 ↥E := by
    rw [pow_succ, ← e1, ← e2, hm]
    nlinarith
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

end Rank

section Orbit
variable {Y : Type} [Group Y]

theorem card_D_eq {D L : Subgroup Y} {s : Y} (hsD : s ∈ D) (hs : s ∉ normalizer (L : Set Y))
    (hO : ∀ d ∈ D, d ∈ normalizer (L : Set Y) ∨ d * s ∈ normalizer (L : Set Y)) :
    Nat.card ↥D = 2 * Nat.card ↥(D ⊓ normalizer (L : Set Y)) := by
  set D₀ : Subgroup Y := D ⊓ normalizer (L : Set Y) with hD₀
  have hle : D₀ ≤ D := inf_le_left
  have hidx : (D₀.subgroupOf D).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsD⟩, fun b => ?_⟩
    have hbs : (b : Y) * s ∈ D := D.mul_mem b.2 hsD
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, hD₀, Subgroup.mem_inf, b.2, hbs, true_and]
    by_cases hb : (b : Y) ∈ normalizer (L : Set Y)
    · have : (b : Y) * s ∉ normalizer (L : Set Y) := fun h => hs (by
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h
        simpa using this)
      simp [hb, this]
    · have := (hO b b.2).resolve_left hb
      simp [hb, this]
  have h1 := Subgroup.card_mul_index (D₀.subgroupOf D)
  rw [hidx] at h1
  have h2 : Nat.card ↥(D₀.subgroupOf D) = Nat.card ↥D₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2] at h1
  omega

theorem rank_D₀ [Finite Y] {D L : Subgroup Y} {s : Y} (hD : CFSG.IsElementaryAbelian 2 ↥D)
    (hsD : s ∈ D) (hs : s ∉ normalizer (L : Set Y))
    (hO : ∀ d ∈ D, d ∈ normalizer (L : Set Y) ∨ d * s ∈ normalizer (L : Set Y)) :
    CFSG.IsElementaryAbelian 2 ↥(D ⊓ normalizer (L : Set Y)) ∧
      pRank 2 ↥D = pRank 2 ↥(D ⊓ normalizer (L : Set Y)) + 1 := by
  obtain ⟨hab, hsq⟩ := forall_of_isElementaryAbelian hD
  have h1 : CFSG.IsElementaryAbelian 2 ↥(D ⊓ normalizer (L : Set Y)) :=
    isElementaryAbelian_of_forall (fun u hu v hv => hab u hu.1 v hv.1) (fun u hu => hsq u hu.1)
  refine ⟨h1, ?_⟩
  have hc := card_D_eq hsD hs hO
  rw [card_eq_two_pow_pRank hD, card_eq_two_pow_pRank h1, ← pow_succ'] at hc
  exact Nat.pow_right_injective le_rfl hc

end Orbit

end CFSG.GH74.Generic.BProg.B2.WeakSigCaseB
