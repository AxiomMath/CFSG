module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def commSub (a : G) (T : Subgroup G) : Subgroup G := ⁅Subgroup.zpowers a, T⁆

section Basic

variable {T : Subgroup G} {a : G}

theorem elemAbelian_mul_comm {p : ℕ} (hT : IsElemAbelian p T) {x y : G} (hx : x ∈ T)
    (hy : y ∈ T) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hT hx hy

theorem conj_mem_of_mem_normalizer (hN : a ∈ Subgroup.normalizer (T : Set G)) {t : G}
    (ht : t ∈ T) : a * t * a⁻¹ ∈ T :=
  (Subgroup.mem_normalizer_iff.1 hN t).1 ht

theorem comm_mem_of_mem_normalizer (hN : a ∈ Subgroup.normalizer (T : Set G)) {t : G}
    (ht : t ∈ T) : ⁅a, t⁆ ∈ T := by
  rw [commutatorElement_def]
  exact T.mul_mem (conj_mem_of_mem_normalizer hN ht) (T.inv_mem ht)

theorem comm_mul_comm (hT : IsElemAbelian 2 T) (hN : a ∈ Subgroup.normalizer (T : Set G))
    {t s : G} (ht : t ∈ T) (hs : s ∈ T) : ⁅a, t * s⁆ = ⁅a, t⁆ * ⁅a, s⁆ := by
  have hu : ⁅a, s⁆ ∈ T := comm_mem_of_mem_normalizer hN hs
  have hcomm : t⁻¹ * ⁅a, s⁆ = ⁅a, s⁆ * t⁻¹ := elemAbelian_mul_comm hT (T.inv_mem ht) hu
  have h1 : ⁅a, t * s⁆ = (a * t * a⁻¹) * (⁅a, s⁆ * t⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h1, ← hcomm]
  simp only [commutatorElement_def]; group

theorem comm_sq_eq_one (hT : IsElemAbelian 2 T) (hN : a ∈ Subgroup.normalizer (T : Set G))
    {t : G} (ht : t ∈ T) : ⁅a, t⁆ ^ 2 = 1 := by
  have h := hT.2 _ (comm_mem_of_mem_normalizer hN ht)
  exact h

@[expose] def commHom (hT : IsElemAbelian 2 T) (hN : a ∈ Subgroup.normalizer (T : Set G)) :
    T →* G where
  toFun t := ⁅a, (t : G)⁆
  map_one' := by simp
  map_mul' t s := comm_mul_comm hT hN t.2 s.2

theorem commHom_apply (hT : IsElemAbelian 2 T) (hN : a ∈ Subgroup.normalizer (T : Set G))
    (t : T) : commHom hT hN t = ⁅a, (t : G)⁆ := rfl

theorem mem_commSub_iff (hT : IsElemAbelian 2 T) (ha : a ^ 2 = 1)
    (hN : a ∈ Subgroup.normalizer (T : Set G)) {c : G} :
    c ∈ commSub a T ↔ ∃ t ∈ T, c = ⁅a, t⁆ := by
  have hrange : (commHom hT hN).range = commSub a T := by
    apply le_antisymm
    · rintro c ⟨t, rfl⟩
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers a) t.2
    · rw [commSub, Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₁
      rw [zpow_eq_zpow_emod k (n := 2) (by simpa using ha)]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · rw [h]; simp
      · rw [h]; exact ⟨⟨g₂, hg₂⟩, by simp [commHom_apply]⟩
  rw [← hrange]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩

theorem commSub_le (hT : IsElemAbelian 2 T) (ha : a ^ 2 = 1)
    (hN : a ∈ Subgroup.normalizer (T : Set G)) :
    commSub a T ≤ T ⊓ Subgroup.centralizer ({a} : Set G) := by
  intro c hc
  obtain ⟨t, ht, rfl⟩ := (mem_commSub_iff hT ha hN).1 hc
  refine ⟨comm_mem_of_mem_normalizer hN ht, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  have ht' : x * t * x⁻¹ ∈ T := conj_mem_of_mem_normalizer hN ht
  have hsq : x * x = 1 := by simpa [pow_two] using ha
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hsq
  have e1 : x * (x * t * x⁻¹) * x⁻¹ = t := by
    have : x * (x * t * x⁻¹) * x⁻¹ = (x * x) * t * (x * x)⁻¹ := by group
    rw [this, hsq]; simp
  have hc1 : ⁅x, t⁆ = (x * t * x⁻¹) * t := by
    have := hT.2 t ht
    rw [commutatorElement_def, show t⁻¹ = t from inv_eq_of_mul_eq_one_right (by simpa [pow_two]
      using this)]
  have hc2 : x * ⁅x, t⁆ = ⁅x, t⁆ * x := by
    rw [hc1]
    have hct : t * (x * t * x⁻¹) = (x * t * x⁻¹) * t := elemAbelian_mul_comm hT ht ht'
    calc x * ((x * t * x⁻¹) * t) = (x * (x * t * x⁻¹) * x⁻¹) * (x * t * x⁻¹) * x := by
          simp only [mul_assoc]; group
      _ = t * (x * t * x⁻¹) * x := by rw [e1]
      _ = ((x * t * x⁻¹) * t) * x := by rw [hct]
  exact hc2

theorem card_commSub_mul_card_centralizer [Finite G] (hT : IsElemAbelian 2 T) (ha : a ^ 2 = 1)
    (hN : a ∈ Subgroup.normalizer (T : Set G)) :
    Nat.card ↥(commSub a T) * Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥T := by
  have hrange : (commHom hT hN).range = commSub a T := by
    ext c
    rw [mem_commSub_iff hT ha hN, MonoidHom.mem_range]
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨t, t.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, rfl⟩
  have hker : Nat.card (commHom hT hN).ker =
      Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) := by
    apply Nat.card_congr
    refine
      { toFun := fun t => ⟨(t.1 : G), t.1.2, ?_⟩
        invFun := fun c => ⟨⟨(c : G), c.2.1⟩, ?_⟩
        left_inv := fun t => rfl
        right_inv := fun c => rfl }
    · have := t.2
      rw [MonoidHom.mem_ker, commHom_apply, commutatorElement_def] at this
      refine Subgroup.mem_centralizer_iff.2 ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact this
    · rw [MonoidHom.mem_ker, commHom_apply, commutatorElement_def]
      have h := Subgroup.mem_centralizer_iff.1 c.2.2 a (Set.mem_singleton a)
      simp only [mul_inv_eq_one]
      rw [mul_inv_eq_iff_eq_mul]
      exact h
  rw [← hrange, ← hker, mul_comm]
  exact Subgroup.card_ker_mul_card_range (commHom hT hN)

theorem conj_orbit_eq (hT : IsElemAbelian 2 T) (ha : a ^ 2 = 1)
    (hN : a ∈ Subgroup.normalizer (T : Set G)) :
    {x | ∃ t ∈ T, x = t⁻¹ * a * t} = {x | ∃ c ∈ commSub a T, x = a * c} := by
  have hsq : a * a = 1 := by simpa [pow_two] using ha
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⁅a, t⁻¹⁆, (mem_commSub_iff hT ha hN).2 ⟨t⁻¹, T.inv_mem ht, rfl⟩, ?_⟩
    have : a * ⁅a, t⁻¹⁆ = (a * a) * t⁻¹ * a⁻¹ * t := by
      simp only [commutatorElement_def]; group
    rw [this, hsq, hinv]; group
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_commSub_iff hT ha hN).1 hc
    refine ⟨t⁻¹, T.inv_mem ht, ?_⟩
    have : a * ⁅a, t⁆ = (a * a) * t * a⁻¹ * t⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [this, hsq, hinv]; group

theorem card_commSub_eq_iff [Finite G] (hT : IsElemAbelian 2 T) (ha : a ^ 2 = 1)
    (hN : a ∈ Subgroup.normalizer (T : Set G)) :
    Nat.card ↥(commSub a T) = Nat.card ↥(T ⊓ Subgroup.centralizer ({a} : Set G)) ↔
      ∀ t ∈ T, (a * t) ^ 2 = 1 → ∃ s ∈ T, a * t = s⁻¹ * a * s := by
  have hsq : a * a = 1 := by simpa [pow_two] using ha
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hsq
  have hle := commSub_le hT ha hN
  have hinvol : ∀ t ∈ T, (a * t) ^ 2 = 1 ↔ t ∈ T ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro t ht
    have ht2 : t * t = 1 := by simpa [pow_two] using hT.2 t ht
    constructor
    · intro h
      refine ⟨ht, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h' : y * t * y * t = 1 := by simpa [pow_two, mul_assoc] using h
      have h3 : y * t * y⁻¹ = t⁻¹ := by
        rw [hinv]
        rw [eq_inv_iff_mul_eq_one]
        simpa [mul_assoc] using h'
      have h4 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      rw [h4] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3)
    · rintro ⟨-, hc⟩
      have hc' : a * t = t * a := Subgroup.mem_centralizer_iff.1 hc a (Set.mem_singleton a)
      calc (a * t) ^ 2 = a * t * (a * t) := pow_two _
        _ = a * (t * a) * t := by simp only [mul_assoc]
        _ = a * (a * t) * t := by rw [hc']
        _ = (a * a) * (t * t) := by simp only [mul_assoc]
        _ = 1 := by rw [hsq, ht2, mul_one]
  have hconj : ∀ t ∈ T, (∃ s ∈ T, a * t = s⁻¹ * a * s) ↔ t ∈ commSub a T := by
    intro t ht
    have hmem : a * t ∈ {x | ∃ s ∈ T, x = s⁻¹ * a * s} ↔
        a * t ∈ {x | ∃ c ∈ commSub a T, x = a * c} := by rw [conj_orbit_eq hT ha hN]
    constructor
    · rintro ⟨s, hs, h⟩
      obtain ⟨c, hc, h2⟩ := hmem.1 ⟨s, hs, h⟩
      rwa [mul_left_cancel h2]
    · intro h
      obtain ⟨s, hs, h2⟩ := hmem.2 ⟨t, h, rfl⟩
      exact ⟨s, hs, h2⟩
  have hiff : (T ⊓ Subgroup.centralizer ({a} : Set G) ≤ commSub a T) ↔
      ∀ t ∈ T, (a * t) ^ 2 = 1 → ∃ s ∈ T, a * t = s⁻¹ * a * s := by
    constructor
    · intro h t ht hsq'
      exact (hconj t ht).2 (h ((hinvol t ht).1 hsq'))
    · intro h t ht
      exact (hconj t ht.1).1 (h t ht.1 ((hinvol t ht.1).2 ht))
  rw [← hiff]
  constructor
  · intro hcard
    have := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    exact this ▸ le_rfl
  · intro hC
    rw [le_antisymm hle hC]

theorem comm_comm_of_mem (hT : IsElemAbelian 2 T) (hN : a ∈ Subgroup.normalizer (T : Set G))
    {t : G} (ht : t ∈ T) : ⁅t, a⁆ = ⁅a, t⁆ := by
  rw [← commutatorElement_inv]
  have h2 : ⁅a, t⁆ * ⁅a, t⁆ = 1 := by simpa [pow_two] using comm_sq_eq_one hT hN ht
  exact inv_eq_of_mul_eq_one_right h2

theorem commutator_eq_image_card [Finite G] {A : Subgroup G} {x : G} (hA : IsElemAbelian 2 A)
    (hx : x ^ 2 = 1) (hN : x ∈ Subgroup.normalizer (A : Set G)) :
    ((⁅A, Subgroup.zpowers x⁆ : Subgroup G) : Set G) = {c | ∃ a ∈ A, c = ⁅a, x⁆} ∧
      Nat.card ↥⁅A, Subgroup.zpowers x⁆ * Nat.card ↥(A ⊓ Subgroup.centralizer ({x} : Set G)) =
        Nat.card ↥A := by
  have hcomm : ⁅A, Subgroup.zpowers x⁆ = commSub x A := Subgroup.commutator_comm _ _
  refine ⟨?_, by rw [hcomm]; exact card_commSub_mul_card_centralizer hA hx hN⟩
  ext c
  rw [hcomm]
  change c ∈ commSub x A ↔ _
  rw [mem_commSub_iff hA hx hN]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (comm_comm_of_mem hA hN ht).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, comm_comm_of_mem hA hN ha⟩

end Basic

end CFSG.CGT.Timmesfeld75
