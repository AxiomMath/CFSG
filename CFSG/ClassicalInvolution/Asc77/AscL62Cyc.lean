module

public import CFSG.ClassicalInvolution.Asc77.AscL62Pair

public section

namespace CFSG.ClassicalInvolution.Asc77.AscL62

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G]

theorem eq_zpowers_of_generator {A : Subgroup G} (g : ↥A) (hg : ∀ x : ↥A, x ∈ Subgroup.zpowers g) :
    A = Subgroup.zpowers (g : G) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  · exact Subgroup.zpowers_le.mpr g.2

theorem le_normalizer_of_commutes {A A' : Subgroup G} (h : Commutes A A') :
    A ≤ Subgroup.normalizer (A' : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : a * y * a⁻¹ = y := by rw [h a ha y hy]; group
    rwa [this]
  · intro hy
    have h0 : a⁻¹ * (a * y * a⁻¹) = (a * y * a⁻¹) * a⁻¹ := h a⁻¹ (A.inv_mem ha) _ hy
    have h1 : a⁻¹ * (a * y * a⁻¹) * a = a * y * a⁻¹ := by
      calc a⁻¹ * (a * y * a⁻¹) * a = (a⁻¹ * (a * y * a⁻¹)) * a := rfl
        _ = ((a * y * a⁻¹) * a⁻¹) * a := by rw [h0]
        _ = a * y * a⁻¹ := by group
    have h2 : a⁻¹ * (a * y * a⁻¹) * a = y := by group
    have h3 : y = a * y * a⁻¹ := h2.symm.trans h1
    rw [h3]
    exact hy

variable [Finite G]

theorem exists_orderOf_four_of_cyclic {A : Subgroup G} (hA : IsCyclic ↥A) (hA2 : IsPGroup 2 ↥A)
    (h4 : 4 ≤ Nat.card A) : ∃ u ∈ A, orderOf u = 4 := by
  obtain ⟨g, hg⟩ := hA.exists_generator
  have hgord : orderOf g = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm⟩ := hA2.exists_card_eq
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hn0 : 2 ^ (m - 2) ≠ 0 := by positivity
  have hdvd : 2 ^ (m - 2) ∣ orderOf g := by
    rw [hgord, hm]
    exact pow_dvd_pow 2 (by omega)
  have hord : orderOf (g ^ 2 ^ (m - 2)) = 4 := by
    rw [orderOf_pow_of_dvd hn0 hdvd, hgord, hm, Nat.pow_div (by omega : m - 2 ≤ m) (by norm_num)]
    have : m - (m - 2) = 2 := by omega
    rw [this]
  exact ⟨((g ^ 2 ^ (m - 2) : ↥A) : G), (g ^ 2 ^ (m - 2)).2, by rw [Subgroup.orderOf_coe, hord]⟩

theorem zpowers_eq_of_cyclic_of_orderOf_eq {C : Subgroup G} (hC : IsCyclic ↥C) {x y : G}
    (hx : x ∈ C) (hy : y ∈ C) (h : orderOf x = orderOf y) :
    Subgroup.zpowers x = Subgroup.zpowers y := by
  have key : Subgroup.zpowers (⟨x, hx⟩ : ↥C) = Subgroup.zpowers (⟨y, hy⟩ : ↥C) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact h
  have hmap := congrArg (Subgroup.map C.subtype) key
  rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap

theorem zpowers_eq_of_commute_of_orderOf_eq {R : Subgroup G} (hR : IsQuatSub R) {z : G}
    (hz : IsUniqueInvolution R z) {g g' : G} (hg : g ∈ R) (hg' : g' ∈ R) (hc : g * g' = g' * g)
    {k : ℕ} (hk : 2 ≤ k) (hgo : orderOf g = 2 ^ k) (hgo' : orderOf g' = 2 ^ k) :
    Subgroup.zpowers g = Subgroup.zpowers g' := by
  obtain ⟨C, hCR, hCc, hCcard, hCmem⟩ := hR.exists_cyclic_max
  by_cases hk3 : 3 ≤ k
  · have h4 : 4 < 2 ^ k := by
      calc 4 < 8 := by norm_num
        _ = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    exact zpowers_eq_of_cyclic_of_orderOf_eq hCc (hCmem g hg (by rw [hgo]; exact h4))
      (hCmem g' hg' (by rw [hgo']; exact h4)) (by rw [hgo, hgo'])
  · have hk2 : k = 2 := by omega
    subst hk2
    have hgo4 : orderOf g = 4 := by simpa using hgo
    have hgo4' : orderOf g' = 4 := by simpa using hgo'
    have hg4 : g ^ 4 = 1 := by rw [← hgo4]; exact pow_orderOf_eq_one g
    have hgsq : g * g ≠ 1 := by
      intro h1
      have h2 : g ^ 2 = 1 := by rw [pow_two]; exact h1
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hgo4] at this
      omega
    have hgsq' : g' * g' ≠ 1 := by
      intro h1
      have h2 : g' ^ 2 = 1 := by rw [pow_two]; exact h1
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hgo4'] at this
      omega
    by_cases hgC : g ∈ C <;> by_cases hg'C : g' ∈ C
    · exact zpowers_eq_of_cyclic_of_orderOf_eq hCc hgC hg'C (by rw [hgo4, hgo4'])
    · exfalso
      have h1 := conj_eq_inv_of_not_mem hR hz hCR hCc hCcard hg' hg'C hgC
      have h2 : g' * g * g'⁻¹ = g := by rw [← hc]; group
      rw [h2] at h1
      apply hgsq
      calc g * g = g * g⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel g
    · exfalso
      have h1 := conj_eq_inv_of_not_mem hR hz hCR hCc hCcard hg hgC hg'C
      have h2 : g * g' * g⁻¹ = g' := by rw [hc]; group
      rw [h2] at h1
      apply hgsq'
      calc g' * g' = g' * g'⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel g'
    · have hcC : g⁻¹ * g' ∈ C := inv_mul_mem_of_index_two hCR hCcard hg hg' hgC hg'C
      have h1 := conj_eq_inv_of_not_mem hR hz hCR hCc hCcard hg hgC hcC
      have h2 : g * (g⁻¹ * g') * g⁻¹ = g⁻¹ * g' := by
        calc g * (g⁻¹ * g') * g⁻¹ = g' * g⁻¹ := by group
          _ = g⁻¹ * g' := (show Commute g g' from hc).inv_left.eq.symm
      rw [h2] at h1
      have hcc : (g⁻¹ * g') * (g⁻¹ * g') = 1 := by
        calc (g⁻¹ * g') * (g⁻¹ * g') = (g⁻¹ * g') * (g⁻¹ * g')⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel _
      rcases hz.unique _ (hCR hcC) hcc with h3 | h3
      · have : g' = g := by
          have := congrArg (fun w => g * w) h3
          simpa using this
        rw [this]
      · have hgg : g * g = z := sq_eq_of_not_mem hR hz hCR hCc hCcard hg hgC
        have h4 : g * g' = 1 := by
          have h5 : g' = g * z := by
            have := congrArg (fun w => g * w) h3
            simpa using this
          rw [h5, ← hgg]
          calc g * (g * (g * g)) = g ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = 1 := hg4
        have h6 : g' = g⁻¹ := eq_inv_of_mul_eq_one_right h4
        rw [h6, Subgroup.zpowers_inv]

theorem eq_of_commutes_of_natCard_eq {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
    (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsUniqueInvolution K z) {A A' : Subgroup G} (hAK : A ≤ K) (hA'K : A' ≤ K)
    (hA : IsCyclic ↥A) (hA' : IsCyclic ↥A') (hA2 : IsPGroup 2 ↥A) (hA'2 : IsPGroup 2 ↥A')
    (h4 : 4 ≤ Nat.card A) (hcard : Nat.card A = Nat.card A') (hcomm : Commutes A A') :
    A = A' := by
  have hP : IsPGroup 2 ↥(A ⊔ A') :=
    hA2.to_sup_of_normal_right' hA'2 (le_normalizer_of_commutes hcomm)
  obtain ⟨R, hR, hPR⟩ := IsSylow2In.exists_ge hP (sup_le hAK hA'K)
  have hquat : IsQuatSub R := hΩ.isQuatSub_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hR)
  have hzR : z ∈ R :=
    mem_of_uniqueInvolution_of_pGroup hz hR.1 hR.2.1 (by have := hquat.eight_le; omega)
  have hzR' : IsUniqueInvolution R z := isUniqueInvolution_of_le hz hR.1 hzR
  obtain ⟨g, hg⟩ := hA.exists_generator
  obtain ⟨g', hg'⟩ := hA'.exists_generator
  have hAeq := eq_zpowers_of_generator g hg
  have hA'eq := eq_zpowers_of_generator g' hg'
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hgo : orderOf (g : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hk]
  have hgo' : orderOf (g' : G) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg', ← hcard, hk]
  rw [hAeq, hA'eq]
  exact zpowers_eq_of_commute_of_orderOf_eq hquat hzR' (hPR ((le_sup_left : A ≤ A ⊔ A') g.2))
    (hPR ((le_sup_right : A' ≤ A ⊔ A') g'.2)) (hcomm g g.2 g' g'.2) hk2 hgo hgo'

end CFSG.ClassicalInvolution.Asc77.AscL62
