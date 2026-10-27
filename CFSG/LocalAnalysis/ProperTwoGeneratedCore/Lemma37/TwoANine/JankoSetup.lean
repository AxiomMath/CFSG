module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoSetupFrame

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

namespace JankoFrame

variable {G : Type} [Group G] [Finite G] {z : G} (fr : JankoFrame G z)

theorem isSylowOf_S₁ (hz : orderOf z = 2) : IsSylowOf (centralizer (fr.P₁ : Set G)) 2 fr.S₁ :=
  isSylowOf_of_normalizer_le (W := centralizer ({z} : Set G)) (n := 4)
    (fr.S₁_le.trans fr.F_le_centralizer) (fr.normalizer_S₁_le hz) (by rw [fr.card_S₁]; norm_num)
    (by rw [fr.centralizer_P₁_eq, fr.card_centralizer_s₁]; norm_num)

theorem isSylowOf_D (hz : orderOf z = 2) : IsSylowOf (normalizer (fr.P₂ : Set G)) 2 fr.D :=
  isSylowOf_of_normalizer_le (W := centralizer ({z} : Set G)) (n := 3) fr.D_le_normalizer
    (fr.normalizer_D_le hz) (by rw [fr.card_D]; norm_num)
    (by rw [fr.card_normalizer_P₂]; norm_num)

theorem isSylowOf_V (hz : orderOf z = 2) : IsSylowOf (centralizer (fr.P₂ : Set G)) 2 fr.V := by
  have hVC : fr.V ≤ centralizer (fr.P₂ : Set G) := fr.D_inf_centralizer ▸ inf_le_right
  refine isSylowOf_of_forall_card_le hVC (fr.isPGroup_V hz) fun Q hQ hQC => ?_
  rw [← fr.D_inf_centralizer]
  exact card_le_card_inf_of_isSylowOf (fr.isSylowOf_D hz) (centralizer_le_normalizer _)
    (normalizer_le_normalizer_centralizer _) hQ hQC

theorem isSylowOf_z (hz : orderOf z = 2) :
    IsSylowOf (centralizer (fr.P₃ : Set G)) 2 (zpowers z) := by
  have hzP : zpowers z ≤ centralizer (fr.P₃ : Set G) := by
    rw [zpowers_le, fr.centralizer_P₃_eq, mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (fr.E_le fr.s₃_mem_E)).symm
  refine isSylowOf_of_normalizer_le (W := centralizer ({z} : Set G)) (n := 1) hzP
    (normalizer_le_centralizer_of_involution (mem_zpowers z) hz fun x hx hx2 =>
      (eq_one_or_eq_of_mem_zpowers hz hx).resolve_left (ne_one_of_orderOf_eq_two hx2))
    (by rw [Nat.card_zpowers, hz, pow_one])
    (by rw [fr.centralizer_P₃_eq, fr.card_centralizer_s₃]; norm_num)

theorem not_isConj_s₁_s₂ (hz : orderOf z = 2) : ¬ IsConj fr.s₁ fr.s₂ := fun h => by
  have h1 := card_le_of_isConj h (isPGroup_of_isSylowOf (fr.isSylowOf_S₁ hz))
    (fr.centralizer_P₁_eq ▸ fr.S₁_le.trans fr.F_le_centralizer)
    (fr.centralizer_P₂_eq ▸ fr.isSylowOf_V hz)
  rw [fr.card_S₁, fr.card_V hz] at h1
  norm_num at h1

theorem not_isConj_s₁_s₃ (hz : orderOf z = 2) : ¬ IsConj fr.s₁ fr.s₃ := fun h => by
  have h1 := card_le_of_isConj h (isPGroup_of_isSylowOf (fr.isSylowOf_S₁ hz))
    (fr.centralizer_P₁_eq ▸ fr.S₁_le.trans fr.F_le_centralizer)
    (fr.centralizer_P₃_eq ▸ fr.isSylowOf_z hz)
  rw [fr.card_S₁, Nat.card_zpowers, hz] at h1
  norm_num at h1

theorem not_isConj_s₂_s₃ (hz : orderOf z = 2) : ¬ IsConj fr.s₂ fr.s₃ := fun h => by
  have h1 := card_le_of_isConj h (fr.isPGroup_V hz)
    (fr.centralizer_P₂_eq ▸ fr.D_inf_centralizer ▸ inf_le_right)
    (fr.centralizer_P₃_eq ▸ fr.isSylowOf_z hz)
  rw [fr.card_V hz, Nat.card_zpowers, hz] at h1
  norm_num at h1

theorem normalizer_P₁_eq :
    normalizer (fr.P₁ : Set G) = centralizer (fr.P₁ : Set G) ⊔ zpowers fr.t := by
  have ht2 := mul_self_eq_one_of_orderOf_eq_two fr.orderOf_t
  have htinv : fr.t⁻¹ = fr.t := inv_eq_of_mul_eq_one_right ht2
  apply le_antisymm
  · intro n hn
    have hs : n * fr.s₁ * n⁻¹ ∈ zpowers fr.s₁ :=
      fr.P₁_eq ▸ (mem_normalizer_iff.mp hn _).mp (fr.P₁_eq ▸ mem_zpowers _)
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers fr.orderOf_s₁ hs with h | h | h
    · rw [mul_inv_eq_one, mul_eq_left] at h
      exact absurd fr.orderOf_s₁ (by rw [h, orderOf_one]; norm_num)
    · refine mem_sup_left ?_
      rw [fr.centralizer_P₁_eq, mem_centralizer_singleton_iff]
      calc n * fr.s₁ = n * fr.s₁ * n⁻¹ * n := by group
        _ = fr.s₁ * n := by rw [h]
    · have hnt : n * fr.t ∈ centralizer (fr.P₁ : Set G) := by
        rw [fr.centralizer_P₁_eq, mem_centralizer_singleton_iff]
        calc n * fr.t * fr.s₁ = n * (fr.t * fr.s₁ * fr.t⁻¹) * fr.t := by group
          _ = (n * fr.s₁ * n⁻¹)⁻¹ * (n * fr.t) := by rw [fr.t_mul_s₁]; group
          _ = fr.s₁ * (n * fr.t) := by rw [h, inv_inv]
      have : n = n * fr.t * fr.t := by rw [mul_assoc, ht2, mul_one]
      rw [this]
      exact mul_mem (mem_sup_left hnt) (mem_sup_right (mem_zpowers _))
  · refine sup_le (centralizer_le_normalizer _) ?_
    rw [zpowers_le, fr.P₁_eq]
    refine CFSG.Walter.J1.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow, fr.t_mul_s₁, inv_zpow']
    exact zpow_mem (mem_zpowers _) _

theorem exists_isConj_card_eq (hset : JankoSetting G z) {u : G} (hu : orderOf u = 2) {x : G}
    (hx : x ∈ centralizer ({u} : Set G)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ s ∈ ({fr.s₁, fr.s₂, fr.s₃} : Set G), IsConj x s ∧
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) =
        Nat.card (centralizer ({s} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (hset.isConj u hu)
  have hy : c * x * c⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [← hc, mem_centralizer_singleton_iff]
    calc c * x * c⁻¹ * (c * u * c⁻¹) = c * (x * u) * c⁻¹ := by group
      _ = c * (u * x) * c⁻¹ := by rw [mem_centralizer_singleton_iff.mp hx]
      _ = c * u * c⁻¹ * (c * x * c⁻¹) := by group
  have hy3 : (c * x * c⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hy1 : c * x * c⁻¹ ≠ 1 := fun h => hx1 (by rwa [mul_inv_eq_one, mul_eq_left] at h)
  obtain ⟨h, hh, hs⟩ := fr.exists_conj _ hy hy3 hy1
  have hhz : h * z * h⁻¹ = z := by rw [mem_centralizer_singleton_iff.mp hh, mul_inv_cancel_right]
  refine ⟨h * (c * x * c⁻¹) * h⁻¹, ?_, isConj_iff.mpr ⟨h * c, by group⟩, ?_⟩
  · rcases hs with hs | hs | hs <;> simp [hs]
  · rw [← card_centralizer_inf_conj c x u, hc, ← card_centralizer_inf_conj h (c * x * c⁻¹) z,
      hhz]

omit [Finite G] in
theorem eq_of_card_eq {s s' : G} (hs : s ∈ ({fr.s₁, fr.s₂, fr.s₃} : Set G))
    (hs' : s' ∈ ({fr.s₁, fr.s₂, fr.s₃} : Set G))
    (h : Nat.card (centralizer ({s} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) =
      Nat.card (centralizer ({s'} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G)) :
    s = s' := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hs'
  rcases hs with rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl
  all_goals first
    | rfl
    | (simp only [fr.card_centralizer_s₁, fr.card_centralizer_s₂, fr.card_centralizer_s₃] at h
       norm_num at h)

theorem eq_of_isConj (hz : orderOf z = 2) {s s' : G} (hs : s ∈ ({fr.s₁, fr.s₂, fr.s₃} : Set G))
    (hs' : s' ∈ ({fr.s₁, fr.s₂, fr.s₃} : Set G)) (h : IsConj s s') : s = s' := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hs'
  rcases hs with rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl
  all_goals first
    | rfl
    | exact absurd h (fr.not_isConj_s₁_s₂ hz)
    | exact absurd h (fr.not_isConj_s₁_s₃ hz)
    | exact absurd h (fr.not_isConj_s₂_s₃ hz)
    | exact absurd h.symm (fr.not_isConj_s₁_s₂ hz)
    | exact absurd h.symm (fr.not_isConj_s₁_s₃ hz)
    | exact absurd h.symm (fr.not_isConj_s₂_s₃ hz)

theorem isConj_iff_card_eq (hset : JankoSetting G z) {u : G} (hu : orderOf u = 2) {x : G}
    (hx : x ∈ centralizer ({u} : Set G)) (hx3 : x ^ 3 = 1) {s : G}
    (hs : s ∈ ({fr.s₁, fr.s₂, fr.s₃} : Set G)) :
    IsConj x s ↔
      Nat.card (centralizer ({x} : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G) =
        Nat.card (centralizer ({s} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  have hz := hset.orderOf_z
  have hs1 : s ≠ 1 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl <;> intro h
    · exact absurd fr.orderOf_s₁ (by rw [h, orderOf_one]; norm_num)
    · exact absurd fr.orderOf_s₂ (by rw [h, orderOf_one]; norm_num)
    · exact absurd fr.orderOf_s₃ (by rw [h, orderOf_one]; norm_num)
  constructor
  · intro h
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hs1 (isConj_one_right.mp h)
    obtain ⟨s', hs', hxs', hcard⟩ := fr.exists_isConj_card_eq hset hu hx hx3 hx1
    rw [hcard, fr.eq_of_isConj hz hs' hs (hxs'.symm.trans h)]
  · intro h
    by_cases hx1 : x = 1
    · exfalso
      have hH : Nat.card (centralizer ({u} : Set G)) = 362880 :=
        (hset.twoANine_centralizer u hu).card_eq
      have h1 : centralizer ({(1 : G)} : Set G) = ⊤ := by
        ext y
        simp [mem_centralizer_singleton_iff]
      rw [hx1, h1, top_inf_eq, hH] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · rw [fr.card_centralizer_s₁] at h
        norm_num at h
      · rw [fr.card_centralizer_s₂] at h
        norm_num at h
      · rw [fr.card_centralizer_s₃] at h
        norm_num at h
    · obtain ⟨s', hs', hxs', hcard⟩ := fr.exists_isConj_card_eq hset hu hx hx3 hx1
      rwa [fr.eq_of_card_eq hs hs' (h.symm.trans hcard)]

end JankoFrame

theorem jankoStep7 : JankoStep7 := by
  intro G _ _ z fr hset _
  have hz := hset.orderOf_z
  refine
    { isSylowOf_S₁ := fr.isSylowOf_S₁ hz
      isSylowOf_V := fr.isSylowOf_V hz
      isSylowOf_z := fr.isSylowOf_z hz
      not_isConj_s₁_s₂ := fr.not_isConj_s₁_s₂ hz
      not_isConj_s₁_s₃ := fr.not_isConj_s₁_s₃ hz
      not_isConj_s₂_s₃ := fr.not_isConj_s₂_s₃ hz
      normalizer_P₁ := fr.normalizer_P₁_eq
      card_centralizer_P₂_t := ?_
      isConj_of_mem_centralizer := fun u hu x hx hx3 hx1 => ?_
      isConj_s₁_iff := fun u hu x hx hx3 => ?_
      isConj_s₂_iff := fun u hu x hx hx3 => ?_
      isConj_s₃_iff := fun u hu x hx hx3 => ?_
      card_le_two := fun y hy B hB hB2 => ?_ }
  · rw [fr.centralizer_P₂_eq, ← fr.card_centralizer_s₂]
    exact (fr.isConj_iff_card_eq hset fr.orderOf_t fr.s₂_mem_centralizer_t fr.s₂_pow_three
      (by simp)).mp (IsConj.refl _)
  · obtain ⟨s, hs, hxs, -⟩ := fr.exists_isConj_card_eq hset hu hx hx3 hx1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact Or.inl hxs
    · exact Or.inr (Or.inl hxs)
    · exact Or.inr (Or.inr hxs)
  · rw [← fr.card_centralizer_s₁]
    exact fr.isConj_iff_card_eq hset hu hx hx3 (by simp)
  · rw [← fr.card_centralizer_s₂]
    exact fr.isConj_iff_card_eq hset hu hx hx3 (by simp)
  · rw [← fr.card_centralizer_s₃]
    exact fr.isConj_iff_card_eq hset hu hx hx3 (by simp)
  · have h := card_le_of_isConj hy hB2 hB (fr.centralizer_P₃_eq ▸ fr.isSylowOf_z hz)
    rwa [Nat.card_zpowers, hz] at h

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
