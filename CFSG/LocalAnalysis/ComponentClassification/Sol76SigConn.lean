module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigThird

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

omit [Finite G] in
theorem orderOf_pow_orderOf_sq_eq_two {O : Subgroup G} (hO : Odd (Nat.card O)) {c : G}
    (hc2 : c ^ 2 ∈ O) (hcO : c ∉ O) : orderOf (c ^ orderOf (c ^ 2)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodd : Odd (orderOf (c ^ 2)) := Odd.of_dvd_nat hO (O.orderOf_dvd_natCard hc2)
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
  · intro h
    obtain ⟨k, hk⟩ := hmodd
    apply hcO
    have hc : c = (c ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      calc c = c ^ orderOf (c ^ 2) * c := by rw [h, one_mul]
        _ = c ^ (orderOf (c ^ 2) + 1) := (pow_succ c _).symm
        _ = c ^ (2 * (k + 1)) := by rw [hk]; congr 1
    rw [hc]
    exact pow_mem hc2 _

omit [Finite G] in
theorem exists_involution_commute_of_mul_sq_mem {O : Subgroup G} (hO : Odd (Nat.card O))
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : (a * b) ^ 2 ∈ O)
    (habO : a * b ∉ O) :
    ∃ w ∈ zpowers (a * b), orderOf w = 2 ∧ w * a = a * w ∧ w * b = b * w := by
  have hw2 := orderOf_pow_orderOf_sq_eq_two hO hab habO
  set d := a * b with hd
  set w := d ^ orderOf (d ^ 2) with hw
  have ha2 : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  have hb2 : b * b = 1 := by rw [← sq, ← hb, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by
    rw [← sq, ← hw2, pow_orderOf_eq_one])
  have hsa : a * d = d⁻¹ * a := by
    rw [hd, mul_inv_rev, hainv, hbinv, ← mul_assoc, ha2, one_mul, mul_assoc, ha2, mul_one]
  have hsb : b * d = d⁻¹ * b := by
    rw [hd, mul_inv_rev, hainv, hbinv, mul_assoc]
  have hpa : a * w = w * a := by
    have h := (show SemiconjBy a d d⁻¹ from hsa).pow_right (orderOf (d ^ 2))
    rw [inv_pow, ← hw, hwinv] at h
    exact h
  have hpb : b * w = w * b := by
    have h := (show SemiconjBy b d d⁻¹ from hsb).pow_right (orderOf (d ^ 2))
    rw [inv_pow, ← hw, hwinv] at h
    exact h
  exact ⟨w, pow_mem (mem_zpowers d) _, hw2, hpa.symm, hpb.symm⟩

theorem reachable_of_commute {X : Type*} [Group X] {s t : {x : X // orderOf x = 2}}
    (h : (s : X) * t = t * s) : (CFSG.Assembly.involutionGraph X).Reachable s t := by
  by_cases hst : s = t
  · subst hst
    exact SimpleGraph.Reachable.refl _
  · refine SimpleGraph.Adj.reachable ?_
    rw [CFSG.Assembly.involutionGraph, SimpleGraph.fromRel_adj]
    exact ⟨hst, Or.inl h⟩

theorem exists_involution_mem_inf_of_mem_coreActionKernel
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSQ : S ≤ coreActionKernel K) {z : G} (hzK : z ∈ K)
    (hz2 : orderOf z = 2) (hzQ : z ∈ coreActionKernel K) :
    ∃ u ∈ K ⊓ centralizer (S : Set G), orderOf u = 2 ∧ u ∈ coreActionKernel K := by
  have hO : Odd (Nat.card (oddCoreIn K)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  have hOQ : oddCoreIn K ≤ coreActionKernel K := GSThmB.oddCoreIn_le_coreActionKernel K
  have hzY : z ∈ ((K ⊓ centralizer (S : Set G) ⊔ oddCoreIn K : Subgroup G) : Set G) := by
    rw [inf_centralizer_sup_oddCoreIn_eq hS2 hSQ]
    exact hzK
  rw [coe_mul_of_left_le_normalizer_right _ _
    (inf_le_left.trans (le_normalizer_oddCoreIn K))] at hzY
  obtain ⟨c, hcY, o, hoO, hco⟩ := hzY
  have hz2' : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2'
  have hc : c = z * o⁻¹ := by rw [← hco, mul_inv_cancel_right]
  have hcQ : c ∈ coreActionKernel K := by
    rw [hc]
    exact mul_mem hzQ (inv_mem (hOQ hoO))
  have hc2 : c ^ 2 ∈ oddCoreIn K := by
    have hconj : z * o⁻¹ * z⁻¹ ∈ oddCoreIn K :=
      (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K hzK) o⁻¹).mp (inv_mem hoO)
    have he : c ^ 2 = z * o⁻¹ * z⁻¹ * o⁻¹ := by rw [sq, hc, hzinv]; group
    rw [he]
    exact mul_mem hconj (inv_mem hoO)
  have hcO : c ∉ oddCoreIn K := fun h => by
    have hzO : z ∈ oddCoreIn K := by rw [← hco]; exact mul_mem h hoO
    have hdvd := (oddCoreIn K).orderOf_dvd_natCard hzO
    rw [hz2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)
  exact ⟨c ^ orderOf (c ^ 2), pow_mem hcY _, orderOf_pow_orderOf_sq_eq_two hO hc2 hcO,
    pow_mem hcQ _⟩

theorem involutionGraph_preconnected_of_mem (hK : K ∈ kStarComponents N) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSQ : S ≤ coreActionKernel K) {u : G}
    (hu : u ∈ K ⊓ centralizer (S : Set G)) (hu2 : orderOf u = 2) (huQ : u ∈ coreActionKernel K) :
    (CFSG.Assembly.involutionGraph ↥(K ⊓ centralizer (S : Set G))).Preconnected := by
  classical
  have hO : Odd (Nat.card (oddCoreIn K)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  have hOQ : oddCoreIn K ≤ coreActionKernel K := GSThmB.oddCoreIn_le_coreActionKernel K
  have hnot : ∀ y : G, orderOf y = 2 → y ∉ oddCoreIn K := fun y hy hyO => by
    have hdvd := (oddCoreIn K).orderOf_dvd_natCard hyO
    rw [hy] at hdvd
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr hdvd)
  have hinv : ∀ y : G, orderOf y = 2 → y⁻¹ = y := fun y hy =>
    inv_eq_of_mul_eq_one_right (by rw [← sq, ← hy, pow_orderOf_eq_one])
  have hsq : ∀ t ∈ K, orderOf t = 2 → ∀ v : G, orderOf v = 2 → v ∈ coreActionKernel K →
      (t * v) ^ 2 ∈ oddCoreIn K := fun t htK ht2 v hv2 hvQ => by
    have h : t⁻¹ * v⁻¹ * t * v ∈ oddCoreIn K := (mem_coreActionKernel.mp hvQ).2 t htK
    rw [hinv t ht2, hinv v hv2] at h
    rw [sq, ← mul_assoc]
    exact h
  have vert : ∀ x : G, x ∈ K ⊓ centralizer (S : Set G) → orderOf x = 2 →
      ∃ v : {y : ↥(K ⊓ centralizer (S : Set G)) // orderOf y = 2}, (v.1 : G) = x :=
    fun x hx hx2 => ⟨⟨⟨x, hx⟩, by rw [Subgroup.orderOf_mk]; exact hx2⟩, rfl⟩
  have hcomm : ∀ v v' : {y : ↥(K ⊓ centralizer (S : Set G)) // orderOf y = 2},
      (v.1 : G) * (v'.1 : G) = (v'.1 : G) * (v.1 : G) →
        (CFSG.Assembly.involutionGraph ↥(K ⊓ centralizer (S : Set G))).Reachable v v' :=
    fun v v' h => reachable_of_commute (Subtype.ext h)
  have hjoin : ∀ v v' : {y : ↥(K ⊓ centralizer (S : Set G)) // orderOf y = 2},
      (v'.1 : G) ∈ coreActionKernel K → (v.1 : G) * (v'.1 : G) ∉ oddCoreIn K →
        (CFSG.Assembly.involutionGraph ↥(K ⊓ centralizer (S : Set G))).Reachable v v' := by
    intro v v' hv'Q hvv'
    have hv2 : orderOf (v.1 : G) = 2 := by rw [Subgroup.orderOf_coe]; exact v.2
    have hv'2 : orderOf (v'.1 : G) = 2 := by rw [Subgroup.orderOf_coe]; exact v'.2
    obtain ⟨w, hwz, hw2, hwv, hwv'⟩ := exists_involution_commute_of_mul_sq_mem hO hv2 hv'2
      (hsq _ (v.1.2).1 hv2 _ hv'2 hv'Q) hvv'
    have hwY : w ∈ K ⊓ centralizer (S : Set G) :=
      (zpowers_le.mpr (mul_mem v.1.2 v'.1.2)) hwz
    obtain ⟨w₀, hw₀⟩ := vert w hwY hw2
    exact (hcomm v w₀ (by rw [hw₀]; exact hwv.symm)).trans (hcomm w₀ v' (by rw [hw₀]; exact hwv'))
  have hrank := two_le_pRank_inf_centralizer hK hS2 hSQ
  obtain ⟨a, haY, ha2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hrank)
  obtain ⟨F, hFY, hF, -⟩ := exists_isKleinFour_mem hrank haY ha2
  obtain ⟨f₁, hf₁F, hf₁1⟩ := exists_mem_ne_one_of_isKleinFour hF
  obtain ⟨f₂, hf₂F, hf₂z⟩ := exists_not_mem_zpowers_of_isKleinFour hF hf₁F
  have hf₂1 : f₂ ≠ 1 := fun h => hf₂z (by rw [h]; exact one_mem _)
  have hs : ∃ s ∈ K ⊓ centralizer (S : Set G), orderOf s = 2 ∧ s * u ∉ oddCoreIn K := by
    by_cases h₁ : f₁ * u ∈ oddCoreIn K
    · by_cases h₂ : f₂ * u ∈ oddCoreIn K
      · exfalso
        have h12 : f₁ * f₂⁻¹ ∈ oddCoreIn K := by
          have := mul_mem h₁ (inv_mem h₂)
          rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left] at this
        have h121 : f₁ * f₂⁻¹ ≠ 1 := fun h' => hf₂z (by
          rw [mul_inv_eq_one] at h'
          rw [← h']
          exact mem_zpowers f₁)
        exact hnot _ (orderOf_eq_two_of_isKleinFour hF (mul_mem hf₁F (inv_mem hf₂F)) h121) h12
      · exact ⟨f₂, hFY hf₂F, orderOf_eq_two_of_isKleinFour hF hf₂F hf₂1, h₂⟩
    · exact ⟨f₁, hFY hf₁F, orderOf_eq_two_of_isKleinFour hF hf₁F hf₁1, h₁⟩
  obtain ⟨s, hsY, hs2, hsu⟩ := hs
  obtain ⟨u₀, hu₀⟩ := vert u hu hu2
  obtain ⟨s₀, hs₀⟩ := vert s hsY hs2
  have hsu₀ : (CFSG.Assembly.involutionGraph ↥(K ⊓ centralizer (S : Set G))).Reachable s₀ u₀ :=
    hjoin s₀ u₀ (by rw [hu₀]; exact huQ) (by rw [hs₀, hu₀]; exact hsu)
  have hreach : ∀ v : {y : ↥(K ⊓ centralizer (S : Set G)) // orderOf y = 2},
      (CFSG.Assembly.involutionGraph ↥(K ⊓ centralizer (S : Set G))).Reachable v u₀ := by
    intro v
    have hv2 : orderOf (v.1 : G) = 2 := by rw [Subgroup.orderOf_coe]; exact v.2
    by_cases htu : (v.1 : G) * u ∈ oddCoreIn K
    ·
      have hvQ : (v.1 : G) ∈ coreActionKernel K := by
        have hv : (v.1 : G) = ((v.1 : G) * u) * u := by
          rw [mul_assoc, ← sq, (Sig.sq_eq_one_of_orderOf_eq_two hu2),
            mul_one]
        rw [hv]
        exact mul_mem (hOQ htu) huQ
      have hsv : s * (v.1 : G) ∉ oddCoreIn K := fun h => hsu (by
        have := mul_mem h htu
        rwa [mul_assoc, ← mul_assoc (v.1 : G), ← sq,
          (Sig.sq_eq_one_of_orderOf_eq_two hv2), one_mul]
          at this)
      have hs₀v : (CFSG.Assembly.involutionGraph ↥(K ⊓ centralizer (S : Set G))).Reachable s₀ v :=
        hjoin s₀ v hvQ (by rw [hs₀]; exact hsv)
      exact hs₀v.symm.trans hsu₀
    · exact hjoin v u₀ (by rw [hu₀]; exact huQ) (by rw [hu₀]; exact htu)
  intro v v'
  exact (hreach v).trans (hreach v').symm

theorem involutionGraph_preconnected_of_central (hK : K ∈ kStarComponents N) {S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSQ : S ≤ coreActionKernel K) {z : G} (hzK : z ∈ K)
    (hz2 : orderOf z = 2) (hzQ : z ∈ coreActionKernel K) :
    (CFSG.Assembly.involutionGraph ↥(K ⊓ centralizer (S : Set G))).Preconnected := by
  obtain ⟨u, hu, hu2, huQ⟩ :=
    exists_involution_mem_inf_of_mem_coreActionKernel hS2 hSQ hzK hz2 hzQ
  exact involutionGraph_preconnected_of_mem hK hS2 hSQ hu hu2 huQ

end CFSG.ComponentClassification.Sol76.Sig
