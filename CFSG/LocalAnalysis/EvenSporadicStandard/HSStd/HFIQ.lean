module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvOut

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Equiv Equiv.Perm Subgroup CFSG.EvenSporadicStandard.HSStd.HL34
  CFSG.EvenSporadicStandard.HSStd.HOv CFSG.ComponentClassification.OuterAutomorphisms

section Closure

variable {G : Type*} [Group G]

theorem isElemAbelian_closure {s : Set G} (hc : s.Pairwise Commute) (h2 : ∀ x ∈ s, x * x = 1) :
    CFSG.Open.IsElemAbelian 2 (closure s) := by
  have : IsMulCommutative (closure s) := isMulCommutative_closure hc
  refine ⟨inferInstance, fun g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx => rw [pow_two]; exact h2 x hx
  | one => exact one_pow 2
  | mul x y hx hy hx2 hy2 =>
    have hxy : Commute x y :=
      congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : closure s) ⟨y, hy⟩)
    rw [hxy.mul_pow, hx2, hy2, one_mul]
  | inv x hx hx2 => rw [inv_pow, hx2, inv_one]

theorem closure_pair_eq (x y : G) : closure ({x, y} : Set G) = zpowers x ⊔ zpowers y := by
  rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]

theorem closure_triple_eq (x y z : G) :
    closure ({x, y, z} : Set G) = zpowers x ⊔ closure ({y, z} : Set G) := by
  rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure]

theorem disjoint_zpowers_of_not_mem {t : G} (ht : orderOf t = 2) {K : Subgroup G} (h : t ∉ K) :
    Disjoint (zpowers t) K := by
  rw [Subgroup.disjoint_def]
  intro x hx hxK
  rcases eq_one_or_eq_of_mem_zpowers ht hx with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hxK) h

theorem zpowers_le_centralizer_of_commute {x y : G} (hc : x * y = y * x) :
    zpowers y ≤ centralizer ({x} : Set G) := by
  rw [zpowers_le]
  exact mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hc

theorem card_closure_pair [Finite G] {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxy : x ≠ y) (hc : x * y = y * x) : Nat.card (closure ({x, y} : Set G)) = 4 := by
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  rw [closure_pair_eq, card_zpowers_sup (zpowers_le_centralizer_of_commute hc)
    (disjoint_zpowers_of_not_mem hx (fun hmem => ?_)), hx, Nat.card_zpowers, hy]
  rcases eq_one_or_eq_of_mem_zpowers hy hmem with h | h
  · exact hx1 h
  · exact hxy h

theorem eq_of_mem_closure_pair {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hc : x * y = y * x) {g : G} (hg : g ∈ closure ({x, y} : Set G)) :
    g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  rw [closure_pair_eq] at hg
  obtain ⟨z, hz, k, hk, rfl⟩ := exists_mul_of_mem_sup (zpowers_le_centralizer_of_commute hc) hg
  rcases eq_one_or_eq_of_mem_zpowers hx hz with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers hy hk with rfl | rfl <;> simp

theorem card_closure_triple [Finite G] {t x y : G} (ht : orderOf t = 2) (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x ≠ y) (htx : t * x = x * t) (hty : t * y = y * t)
    (hxy' : x * y = y * x) (hind : t ∉ closure ({x, y} : Set G)) :
    Nat.card (closure ({t, x, y} : Set G)) = 8 := by
  have hle : closure ({x, y} : Set G) ≤ centralizer ({t} : Set G) := by
    rw [closure_pair_eq, sup_le_iff]
    exact ⟨zpowers_le_centralizer_of_commute htx, zpowers_le_centralizer_of_commute hty⟩
  rw [closure_triple_eq, card_zpowers_sup hle (disjoint_zpowers_of_not_mem ht hind), ht,
    card_closure_pair hx hy hxy hxy']

end Closure

section Normal

variable {D : Type*} [Group D] [Finite D]

theorem exists_elemAbelian_eight_of_mem_normal {t : D} (ht : orderOf t = 2)
    (e : Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (S : Subgroup D) [S.Normal] (h4 : 4 ∣ Nat.card S) (htS : t ∈ S) :
    ∃ E : Subgroup D, E ≤ S ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card ↥E = 8 := by
  obtain ⟨e⟩ := e
  obtain ⟨K, hC, hd, ⟨eK⟩⟩ := exists_complement ht e
  have hKC : K ≤ centralizer ({t} : Set D) := le_sup_right.trans hC.ge
  by_cases hsub : S ⊓ centralizer ({t} : Set D) ≤ zpowers t
  · exact (false_of_mem_of_inf_le ht S h4 htS hsub).elim
  obtain ⟨x, hxX, hxz⟩ := Set.not_subset.1 hsub
  have hxS : x ∈ S := (Subgroup.mem_inf.1 hxX).1
  have hxC : x ∈ centralizer ({t} : Set D) := (Subgroup.mem_inf.1 hxX).2
  obtain ⟨z, hz, k, hk, rfl⟩ := exists_mul_of_mem_sup hKC (hC ▸ hxC)
  have hzS : z ∈ S := by
    rcases eq_one_or_eq_of_mem_zpowers ht hz with h | h <;> rw [h]
    exacts [S.one_mem, htS]
  have hkS : k ∈ S := by
    have := S.mul_mem (S.inv_mem hzS) hxS
    simpa using this
  have hk1 : k ≠ 1 := fun h => hxz (by rw [h, mul_one]; exact hz)
  let N : Subgroup (Perm (Fin 5)) := (S.subgroupOf K).map eK.toMonoidHom
  have hNmem : ∀ σ ∈ N, ∃ m : D, ∃ hm : m ∈ K, m ∈ S ∧ eK ⟨m, hm⟩ = σ := by
    rintro _ ⟨⟨m, hm⟩, hmS, rfl⟩
    exact ⟨m, hm, hmS, rfl⟩
  have hNn : N.Normal := ⟨by
    intro n hn g
    obtain ⟨m, hm, hmS, rfl⟩ := hNmem n hn
    set κ' : K := eK.symm g with hκ'
    refine ⟨κ' * ⟨m, hm⟩ * κ'⁻¹, ?_, ?_⟩
    · show ((κ' : D) * m * (κ' : D)⁻¹) ∈ S
      exact Normal.conj_mem inferInstance m hmS _
    · show eK (κ' * ⟨m, hm⟩ * κ'⁻¹) = g * eK ⟨m, hm⟩ * g⁻¹
      rw [map_mul, map_mul, map_inv, hκ', MulEquiv.apply_symm_apply]⟩
  have hkN : eK ⟨k, hk⟩ ∈ N := ⟨⟨k, hk⟩, hkS, rfl⟩
  have hnt : Nontrivial N := ⟨⟨⟨_, hkN⟩, 1, fun h => hk1 (by
    have h1 : eK ⟨k, hk⟩ = 1 := congrArg Subtype.val h
    have := congrArg Subtype.val (eK.injective (h1.trans (map_one eK).symm))
    exact this)⟩⟩
  have hAN : alternatingGroup (Fin 5) ≤ N :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) hnt
  have hx₁A : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 5) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    rfl
  have hy₁A : (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) ∈ alternatingGroup (Fin 5) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    rfl
  obtain ⟨m₁, hm₁K, hm₁S, hm₁e⟩ := hNmem _ (hAN hx₁A)
  obtain ⟨m₂, hm₂K, hm₂S, hm₂e⟩ := hNmem _ (hAN hy₁A)
  have hsq1 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) * (Equiv.swap 0 1 * Equiv.swap 2 3) = 1 :=
    by decide
  have hsq2 : (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) * (Equiv.swap 0 2 * Equiv.swap 1 3) = 1 :=
    by decide
  have hne1 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ≠ 1 := by decide
  have hne2 : (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) ≠ 1 := by decide
  have hne12 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ≠ Equiv.swap 0 2 * Equiv.swap 1 3 := by
    decide
  have hcm : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) * (Equiv.swap 0 2 * Equiv.swap 1 3) =
      (Equiv.swap 0 2 * Equiv.swap 1 3) * (Equiv.swap 0 1 * Equiv.swap 2 3) := by decide
  have hm₁sq : m₁ * m₁ = 1 := by
    have h : eK (⟨m₁, hm₁K⟩ * ⟨m₁, hm₁K⟩) = eK 1 := by rw [map_mul, hm₁e, hsq1, map_one]
    exact congrArg Subtype.val (eK.injective h)
  have hm₂sq : m₂ * m₂ = 1 := by
    have h : eK (⟨m₂, hm₂K⟩ * ⟨m₂, hm₂K⟩) = eK 1 := by rw [map_mul, hm₂e, hsq2, map_one]
    exact congrArg Subtype.val (eK.injective h)
  have hm₁1 : m₁ ≠ 1 := fun h => by
    have h1 : eK ⟨m₁, hm₁K⟩ = 1 := by
      have : (⟨m₁, hm₁K⟩ : ↥K) = 1 := Subtype.ext h
      rw [this, map_one]
    rw [hm₁e] at h1
    exact hne1 h1
  have hm₂1 : m₂ ≠ 1 := fun h => by
    have h1 : eK ⟨m₂, hm₂K⟩ = 1 := by
      have : (⟨m₂, hm₂K⟩ : ↥K) = 1 := Subtype.ext h
      rw [this, map_one]
    rw [hm₂e] at h1
    exact hne2 h1
  have hm₁₂ : m₁ ≠ m₂ := fun h => by
    subst h
    exact hne12 (hm₁e.symm.trans hm₂e)
  have hcomm12 : m₁ * m₂ = m₂ * m₁ := by
    have h : eK (⟨m₁, hm₁K⟩ * ⟨m₂, hm₂K⟩) = eK (⟨m₂, hm₂K⟩ * ⟨m₁, hm₁K⟩) := by
      rw [map_mul, map_mul, hm₁e, hm₂e]
      exact hcm
    exact congrArg Subtype.val (eK.injective h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho₁ : orderOf m₁ = 2 := orderOf_eq_prime (by rwa [sq]) hm₁1
  have ho₂ : orderOf m₂ = 2 := orderOf_eq_prime (by rwa [sq]) hm₂1
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hct₁ : t * m₁ = m₁ * t := mem_centralizer_iff.1 (hKC hm₁K) t rfl
  have hct₂ : t * m₂ = m₂ * t := mem_centralizer_iff.1 (hKC hm₂K) t rfl
  have htK : t ∉ K := fun h => by
    have h1 : t ∈ zpowers t ⊓ K := ⟨mem_zpowers t, h⟩
    rw [disjoint_iff.1 hd, mem_bot] at h1
    rw [h1, orderOf_one] at ht
    omega
  have hpairK : closure ({m₁, m₂} : Set D) ≤ K := by
    rw [closure_le]
    intro u hu
    rcases hu with rfl | rfl
    · exact hm₁K
    · exact hm₂K
  refine ⟨closure ({t, m₁, m₂} : Set D), ?_, ?_, ?_⟩
  · rw [closure_le]
    intro u hu
    rcases hu with rfl | rfl | rfl
    · exact htS
    · exact hm₁S
    · exact hm₂S
  · refine isElemAbelian_closure ?_ ?_
    · intro u hu v hv huv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact absurd rfl huv
      · exact hct₁
      · exact hct₂
      · exact hct₁.symm
      · exact absurd rfl huv
      · exact hcomm12
      · exact hct₂.symm
      · exact hcomm12.symm
      · exact absurd rfl huv
    · intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact ht2
      · exact hm₁sq
      · exact hm₂sq
  · exact card_closure_triple ht ho₁ ho₂ hm₁₂ hct₁ hct₂ hcomm12 (fun h => htK (hpairK h))

theorem false_of_good_mem_of_rank {t : D} (ht : orderOf t = 2)
    (e : Nonempty (↥(centralizer ({t} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (S : Subgroup D) [S.Normal] (h4 : 4 ∣ Nat.card S)
    (hS : ∀ E : Subgroup ↥S, CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4) (htS : t ∈ S) :
    False := by
  obtain ⟨E, hES, hE, hcard⟩ := exists_elemAbelian_eight_of_mem_normal ht e S h4 htS
  have hE' : CFSG.Open.IsElemAbelian 2 (E.subgroupOf S) := by
    have := isElemAbelian_subgroupOf_inf S hE
    rwa [inf_eq_left.2 hES] at this
  have h1 := hS _ hE'
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv, hcard] at h1
  omega

theorem false_of_good_triple_of_normal
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥) {a b : D}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (ea : Nonempty (↥(centralizer ({a} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eb : Nonempty (↥(centralizer ({b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (eab : Nonempty (↥(centralizer ({a * b} : Set D)) ≃* Multiplicative (ZMod 2) × Perm (Fin 5)))
    (S : Subgroup D) [S.Normal] (h4 : 4 ∣ Nat.card S) (h240 : 240 < Nat.card S)
    (hS : ∀ E : Subgroup ↥S, CFSG.Open.IsElemAbelian 2 E → Nat.card E ≤ 4) (m : ℕ)
    (hm : Nat.card (Outer ↥S) ∣ m) (hm2 : ∀ k : ℕ, 2 ^ k ∣ m → 2 ^ k ≤ 2) : False := by
  have hC := centralizer_eq_bot_of_normal_of_card hZ ha ea S h4 h240
  have ha2 : a * a = 1 := by rw [← sq, ← ha]; exact pow_orderOf_eq_one a
  have hb2 : b * b = 1 := by rw [← sq, ← hb]; exact pow_orderOf_eq_one b
  have hab2 : orderOf (a * b) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · calc (a * b) ^ 2 = (a * b) * (a * b) := sq _
        _ = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hcomm]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · intro h
      exact hab ((inv_eq_of_mul_eq_one_right ha2).symm.trans (eq_inv_of_mul_eq_one_right h).symm)
  have hA4 : Nat.card (closure ({a, b} : Set D)) = 4 := card_closure_pair ha hb hab hcomm
  have hA2 : ∀ x ∈ closure ({a, b} : Set D), x * x = 1 := by
    intro x hx
    have hel : CFSG.Open.IsElemAbelian 2 (closure ({a, b} : Set D)) := by
      refine isElemAbelian_closure ?_ ?_
      · intro u hu v hv huv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact absurd rfl huv
        · exact hcomm
        · exact hcomm.symm
        · exact absurd rfl huv
      · intro u hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl
        · exact ha2
        · exact hb2
    simpa [pow_two] using hel.2 x hx
  have hAS : Nat.card ↥(closure ({a, b} : Set D) ⊓ S) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    rcases eq_of_mem_closure_pair ha hb hcomm hg.1 with rfl | rfl | rfl | rfl
    · rfl
    · exact (false_of_good_mem_of_rank ha ea S h4 hS hg.2).elim
    · exact (false_of_good_mem_of_rank hb eb S h4 hS hg.2).elim
    · exact (false_of_good_mem_of_rank hab2 eab S h4 hS hg.2).elim
  obtain ⟨r, hr, hrdvd, k, hk⟩ := exists_card_eq_mul_outer S hC hA2
  rw [hA4, hAS, one_mul] at hr
  have h2k : 2 ^ k ≤ 2 := hm2 k (hk ▸ hrdvd.trans hm)
  omega

end Normal

end CFSG.EvenSporadicStandard.HSStd.HFI
