module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Quotient

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

namespace PartC

theorem conj_mem_sup_of_involution (hc : PartC T Q P₁ e u) {n t : G}
    (hn : n ∈ Subgroup.normalizer (T : Set G)) (htT : t ∈ T) (ht : t * t = 1) (ht1 : t ≠ 1) :
    n * t * n⁻¹ ∈ Q ⊔ P₁ := by
  have hmem : n * t * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn t).mp htT
  refine hc.involution_mem _ hmem (orderOf_eq_prime ?_ ?_)
  · rw [pow_two, show n * t * n⁻¹ * (n * t * n⁻¹) = n * (t * t) * n⁻¹ by group, ht, mul_one,
      mul_inv_cancel]
  · intro h1
    apply ht1
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1

theorem exists_inv_mul_ne {R : Subgroup G} (φ : R ≃* QuaternionGroup 2) (he : e ∈ R)
    (he2 : orderOf e = 2) {x : G} (hx : x ∈ R) :
    ∃ b ∈ R, b ≠ 1 ∧ b ≠ e ∧ b⁻¹ * x ≠ 1 ∧ b⁻¹ * x ≠ e := by
  obtain ⟨a, ha, c, hc', haa, hcc, hca, hcae⟩ := quaternion_exists_pair φ he he2
  have hne : ∀ {b : G}, b * b = e → b ≠ 1 ∧ b ≠ e := fun {b} hb => by
    have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he2; exact absurd he2 (by decide)
    refine ⟨fun h => he1 (by rw [← hb, h, mul_one]), fun h => he1 ?_⟩
    have hee : e * e = 1 := by rw [← pow_two, ← he2, pow_orderOf_eq_one]
    rw [← hee, ← h, hb, h]
  by_cases hxa : x = a ∨ x = a * e
  · refine ⟨c, hc', (hne hcc).1, (hne hcc).2, fun h => ?_, fun h => ?_⟩
    · rw [inv_mul_eq_one] at h
      rcases hxa with rfl | rfl
      · exact hca h
      · exact hcae h
    · rw [inv_mul_eq_iff_eq_mul] at h
      have hee : e * e = 1 := by rw [← pow_two, ← he2, pow_orderOf_eq_one]
      have hc2 : c = x * e := by rw [h, mul_assoc, hee, mul_one]
      rcases hxa with rfl | rfl
      · exact hcae hc2
      · exact hca (by rw [hc2, mul_assoc, hee, mul_one])
  · push Not at hxa
    refine ⟨a, ha, (hne haa).1, (hne haa).2, fun h => hxa.1 ?_, fun h => hxa.2 ?_⟩
    · rw [inv_mul_eq_one] at h
      exact h.symm
    · rw [inv_mul_eq_iff_eq_mul] at h
      exact h

theorem conj_mem_sup_of_mem_normalizer (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2)
    {n : G} (hn : n ∈ Subgroup.normalizer (T : Set G)) {w : G} (hw : w ∈ Q ⊔ P₁) :
    n * w * n⁻¹ ∈ Q ⊔ P₁ := by
  obtain ⟨φQ⟩ := hc.quaternion
  have hee := hc.centralElt_mul_self
  have hne := hc.conj_centralElt n
  have hprod : ∀ t₁ t₂ : G, t₁ ∈ T → t₂ ∈ T → t₁ * t₁ = 1 → t₂ * t₂ = 1 → t₁ ≠ 1 → t₂ ≠ 1 →
      n * (t₁ * t₂ * e) * n⁻¹ ∈ Q ⊔ P₁ := by
    intro t₁ t₂ h1 h2 h11 h22 h1' h2'
    rw [show n * (t₁ * t₂ * e) * n⁻¹ = (n * t₁ * n⁻¹) * (n * t₂ * n⁻¹) * (n * e * n⁻¹) by group,
      hne]
    exact (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).mul_mem (hc.conj_mem_sup_of_involution hn h1 h11 h1')
      (hc.conj_mem_sup_of_involution hn h2 h22 h2')) (Subgroup.mem_sup_left hc.mem_left)
  have hZ : ∀ {z : G}, (z = 1 ∨ z = e) → n * z * n⁻¹ ∈ Q ⊔ P₁ := by
    rintro z (rfl | rfl)
    · rw [mul_one, mul_inv_cancel]
      exact (Q ⊔ P₁).one_mem
    · rw [hne]
      exact Subgroup.mem_sup_left hc.mem_left
  have hinv : ∀ q ∈ Q, ∀ p ∈ P₁, q ≠ 1 → q ≠ e → p ≠ 1 → p ≠ e →
      q * p * (q * p) = 1 ∧ q * p ≠ 1 := by
    intro q hq p hp hq1 hqe hp1 hpe
    have hqq := quaternion_mul_self_of_ne φQ hc.mem_left hc.order hq hq1 hqe
    have hpp := quaternion_mul_self_of_ne φ hc.mem_right hc.order hp hp1 hpe
    refine ⟨by rw [show q * p * (q * p) = q * (p * q) * p by group, ← hc.commute q hq p hp,
      show q * (q * p) * p = q * q * (p * p) by group, hqq, hpp, hee], fun h => ?_⟩
    have hqP : q ∈ P₁ := by
      rw [eq_inv_of_mul_eq_one_left h]
      exact P₁.inv_mem hp
    rcases hc.mem_inf q hq hqP with h' | h'
    exacts [hq1 h', hqe h']
  have hu1 := hc.self_ne
  obtain ⟨q₀, hq₀, hq₀1, hq₀e, -, -⟩ := exists_inv_mul_ne φQ hc.mem_left hc.order hc.mem_left
  have hQ : ∀ q ∈ Q, n * q * n⁻¹ ∈ Q ⊔ P₁ := by
    intro q hq
    by_cases hqZ : q = 1 ∨ q = e
    · exact hZ hqZ
    push Not at hqZ
    obtain ⟨a, ha, ha1, hae, hb1, hbe⟩ := exists_inv_mul_ne φQ hc.mem_left hc.order hq
    have h1 := hinv a ha u hc.self_mem ha1 hae hu1.1 hu1.2
    have h2 := hinv (a⁻¹ * q) (Q.mul_mem (Q.inv_mem ha) hq) u hc.self_mem hb1 hbe hu1.1 hu1.2
    have hq' : q = a * u * (a⁻¹ * q * u) * e := by
      rw [show a * u * (a⁻¹ * q * u) * e = a * (u * (a⁻¹ * q)) * (u * e) by group,
        ← hc.commute _ (Q.mul_mem (Q.inv_mem ha) hq) u hc.self_mem, ← hc.sq,
        show a * (a⁻¹ * q * u) * (u * (u * u)) = q * ((u * u) * (u * u)) by group, hc.sq, hee,
        mul_one]
    rw [hq']
    exact hprod _ _ (hc.sup_le (mul_mem_sup ha hc.self_mem))
      (hc.sup_le (mul_mem_sup (Q.mul_mem (Q.inv_mem ha) hq) hc.self_mem)) h1.1 h2.1 h1.2 h2.2
  have hP : ∀ p ∈ P₁, n * p * n⁻¹ ∈ Q ⊔ P₁ := by
    intro p hp
    by_cases hpZ : p = 1 ∨ p = e
    · exact hZ hpZ
    push Not at hpZ
    obtain ⟨a, ha, ha1, hae, hb1, hbe⟩ := exists_inv_mul_ne φ hc.mem_right hc.order hp
    have h1 := hinv q₀ hq₀ a ha hq₀1 hq₀e ha1 hae
    have h2 := hinv q₀ hq₀ (a⁻¹ * p) (P₁.mul_mem (P₁.inv_mem ha) hp) hq₀1 hq₀e hb1 hbe
    have hq₀q₀ := quaternion_mul_self_of_ne φQ hc.mem_left hc.order hq₀ hq₀1 hq₀e
    have hp' : p = q₀ * a * (q₀ * (a⁻¹ * p)) * e := by
      rw [show q₀ * a * (q₀ * (a⁻¹ * p)) * e = q₀ * (a * q₀) * (a⁻¹ * p) * e by group,
        ← hc.commute q₀ hq₀ a ha,
        show q₀ * (q₀ * a) * (a⁻¹ * p) * e = q₀ * q₀ * (p * e) by group,
        hq₀q₀, hc.commute_centralElt p, ← mul_assoc, hee, one_mul]
    rw [hp']
    exact hprod _ _ (hc.sup_le (mul_mem_sup hq₀ ha))
      (hc.sup_le (mul_mem_sup hq₀ (P₁.mul_mem (P₁.inv_mem ha) hp))) h1.1 h2.1 h1.2 h2.2
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp hw
  rw [show n * (q * p) * n⁻¹ = (n * q * n⁻¹) * (n * p * n⁻¹) by group]
  exact (Q ⊔ P₁).mul_mem (hQ q hq) (hP p hp)

theorem eq_or_eq_of_le_sup [Finite G] (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2)
    {R : Subgroup G} (hRW : R ≤ Q ⊔ P₁) (hR : Nat.card R = 8)
    (hRsq : ∀ r ∈ R, r ≠ 1 → r ≠ e → r * r = e) : R = P₁ ∨ R = Q := by
  obtain ⟨φQ⟩ := hc.quaternion
  have he1 := hc.centralElt_ne_one
  have hcard8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardP : Nat.card P₁ = 8 := by rw [Nat.card_congr φ.toEquiv, hcard8]
  have hcardQ : Nat.card Q = 8 := by rw [Nat.card_congr φQ.toEquiv, hcard8]
  have hsplit : ∀ r ∈ R, r ≠ 1 → r ≠ e → r ∈ P₁ ∨ r ∈ Q := by
    intro r hr hr1 hre
    have hrr := hRsq r hr hr1 hre
    obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp (hRW hr)
    have hsq : q * p * (q * p) = q * q * (p * p) := by
      rw [show q * p * (q * p) = q * (p * q) * p by group, ← hc.commute q hq p hp]
      group
    rcases quaternion_mul_self φQ hc.mem_left hc.order hq with hqq | hqq
    · left
      rcases quaternion_eq_of_mul_self φQ hc.mem_left hc.order hq hqq with rfl | rfl
      · rw [one_mul]
        exact hp
      · exact P₁.mul_mem hc.mem_right hp
    · right
      have hpp : p * p = 1 := by
        rw [hsq, hqq] at hrr
        calc p * p = e⁻¹ * (e * (p * p)) := by group
          _ = 1 := by rw [hrr, inv_mul_cancel]
      rcases hc.eq_of_mem_right_of_mul_self hp hpp with rfl | rfl
      · rw [mul_one]
        exact hq
      · exact Q.mul_mem hq hc.mem_left
  by_cases hA : R ≤ P₁
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hA (by rw [hcardP, hR]))
  right
  obtain ⟨r₂, hr₂R, hr₂P⟩ := Set.not_subset.mp hA
  have hr₂1 : r₂ ≠ 1 := fun h => hr₂P (h ▸ P₁.one_mem)
  have hr₂e : r₂ ≠ e := fun h => hr₂P (h ▸ hc.mem_right)
  have hr₂Q : r₂ ∈ Q := (hsplit r₂ hr₂R hr₂1 hr₂e).resolve_left hr₂P
  refine Subgroup.eq_of_le_of_card_ge (fun r hr => ?_) (by rw [hcardQ, hR])
  by_cases hrZ : r = 1 ∨ r = e
  · rcases hrZ with rfl | rfl
    exacts [Q.one_mem, hc.mem_left]
  push Not at hrZ
  rcases hsplit r hr hrZ.1 hrZ.2 with hrP | hrQ
  · exfalso
    have hrr := hRsq r hr hrZ.1 hrZ.2
    have hr₂r₂ := hRsq r₂ hr₂R hr₂1 hr₂e
    have hprod : r * r₂ * (r * r₂) = 1 := by
      rw [show r * r₂ * (r * r₂) = r * (r₂ * r) * r₂ by group, hc.commute r₂ hr₂Q r hrP,
        show r * (r * r₂) * r₂ = r * r * (r₂ * r₂) by group, hrr, hr₂r₂,
        hc.centralElt_mul_self]
    have h1 : r * r₂ ≠ 1 := fun h => hr₂P (by
      rw [eq_inv_of_mul_eq_one_right h]
      exact P₁.inv_mem hrP)
    have h2 : r * r₂ ≠ e := fun h => hr₂P (by
      rw [show r₂ = r⁻¹ * e by rw [← h]; group]
      exact P₁.mul_mem (P₁.inv_mem hrP) hc.mem_right)
    have := hRsq _ (R.mul_mem hr hr₂R) h1 h2
    rw [hprod] at this
    exact he1 this.symm
  · exact hrQ

end PartC

namespace CaseC3

theorem conj_self_of_mem (h : CaseC3 T Q P₁ e u y) {t : G} (ht : t ∈ T) :
    t * u * t⁻¹ = u ∨ t * u * t⁻¹ = u * e := by
  have hc := h.partC
  have hmem : t * u * t⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.mp (h.le_normalizer ht) u).mp (Subgroup.mem_zpowers u)
  have hne := hc.self_ne
  rcases hc.mem_zpowers_self hmem with h1 | h1 | h1 | h1
  · exfalso
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact hne.1 h1
  · exact Or.inl h1
  · exfalso
    rw [← hc.conj_centralElt t] at h1
    exact hne.2 (mul_left_cancel (mul_right_cancel h1))
  · exact Or.inr h1

theorem conj_self_mem (h : CaseC3 T Q P₁ e u y) {n : G}
    (hnT : n ∈ Subgroup.normalizer (T : Set G)) (hnP : n ∈ Subgroup.normalizer (P₁ : Set G)) :
    n * u * n⁻¹ = u ∨ n * u * n⁻¹ = u * e := by
  have hc := h.partC
  have hwP : n * u * n⁻¹ ∈ P₁ := (Subgroup.mem_normalizer_iff.mp hnP u).mp hc.self_mem
  have hy' : n⁻¹ * y * n ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnT) y).mp h.mem
    simpa using this
  have hfix : y * (n * u * n⁻¹) * y⁻¹ = n * u * n⁻¹ ∨
      y * (n * u * n⁻¹) * y⁻¹ = n * u * n⁻¹ * e := by
    have hconj : y * (n * u * n⁻¹) * y⁻¹ =
        n * ((n⁻¹ * y * n) * u * (n⁻¹ * y * n)⁻¹) * n⁻¹ := by group
    rcases h.conj_self_of_mem hy' with h1 | h1 <;> rw [hconj, h1]
    · exact Or.inl rfl
    · right
      rw [show n * (u * e) * n⁻¹ = n * u * (e * n⁻¹) by group, ← hc.commute_centralElt n⁻¹,
        ← mul_assoc]
  have hne := hc.self_ne
  rcases h.mem_of_conj_right hwP hfix with h1 | h1 | h1 | h1
  · exfalso
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact hne.1 h1
  · exfalso
    rw [← hc.conj_centralElt n] at h1
    exact hne.2 (mul_left_cancel (mul_right_cancel h1))
  · exact Or.inl h1
  · exact Or.inr h1

theorem mem_normalizer_zpowers [Finite G] (h : CaseC3 T Q P₁ e u y) {n : G}
    (hnT : n ∈ Subgroup.normalizer (T : Set G)) (hnP : n ∈ Subgroup.normalizer (P₁ : Set G)) :
    n ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  have hmem : n * u * n⁻¹ ∈ Subgroup.zpowers u := by
    rcases h.conj_self_mem hnT hnP with hw | hw <;> rw [hw]
    · exact Subgroup.mem_zpowers u
    · rw [← h.partC.sq]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers u)
        (Subgroup.mul_mem _ (Subgroup.mem_zpowers u) (Subgroup.mem_zpowers u))
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hmem k

theorem map_conj_eq_or_eq_of_conj_mem [Finite G] (h : CaseC3 T Q P₁ e u y) {x : G}
    (hxW : ∀ w ∈ Q ⊔ P₁, x * w * x⁻¹ ∈ Q ⊔ P₁) {R : Subgroup G} (hRW : R ≤ Q ⊔ P₁)
    (hR : Nat.card R = 8) (hRsq : ∀ r ∈ R, r ≠ 1 → r ≠ e → r * r = e) :
    R.map (MulAut.conj x).toMonoidHom = P₁ ∨ R.map (MulAut.conj x).toMonoidHom = Q := by
  have hc := h.partC
  obtain ⟨φ⟩ := h.quaternion_right
  refine hc.eq_or_eq_of_le_sup φ ?_ ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact hxW r (hRW hr)
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hR]
  · rintro _ ⟨r, hr, rfl⟩ h1 h2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1 h2 ⊢
    have hr1 : r ≠ 1 := fun h' => h1 (by rw [h', mul_one, mul_inv_cancel])
    have hre : r ≠ e := fun h' => h2 (by rw [h', hc.conj_centralElt])
    rw [show x * r * x⁻¹ * (x * r * x⁻¹) = x * (r * r) * x⁻¹ by group,
      hRsq r hr hr1 hre, hc.conj_centralElt]

theorem map_conj_eq_or_eq [Finite G] (h : CaseC3 T Q P₁ e u y) {x : G}
    (hxT : x ∈ Subgroup.normalizer (T : Set G)) {R : Subgroup G} (hRW : R ≤ Q ⊔ P₁)
    (hR : Nat.card R = 8) (hRsq : ∀ r ∈ R, r ≠ 1 → r ≠ e → r * r = e) :
    R.map (MulAut.conj x).toMonoidHom = P₁ ∨ R.map (MulAut.conj x).toMonoidHom = Q :=
  h.map_conj_eq_or_eq_of_conj_mem (fun _ hw =>
    h.partC.conj_mem_sup_of_mem_normalizer h.quaternion_right.some hxT hw) hRW hR hRsq

theorem conj_swap [Finite G] (h : CaseC3 T Q P₁ e u y)
    (hmax : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers u : Set G),
      n ∈ Subgroup.normalizer (T : Set G) → (∃ k : ℕ, n ^ 2 ^ k = 1) → n ∈ T)
    {x : G} (hxT : x ∈ Subgroup.normalizer (T : Set G)) (hx : x ∉ T)
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    (∀ p ∈ P₁, x * p * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, x * q * x⁻¹ ∈ P₁) := by
  have hc := h.partC
  obtain ⟨φ⟩ := h.quaternion_right
  obtain ⟨φQ⟩ := hc.quaternion
  have hcard8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hmem : ∀ {R : Subgroup G} {g : G}, g ∈ R →
      x * g * x⁻¹ ∈ R.map (MulAut.conj x).toMonoidHom := fun {R g} hg =>
    ⟨g, hg, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hP := h.map_conj_eq_or_eq hxT (R := P₁) le_sup_right
    (by rw [Nat.card_congr φ.toEquiv, hcard8])
    (fun r hr h1 h2 => quaternion_mul_self_of_ne φ hc.mem_right hc.order hr h1 h2)
  have hQ := h.map_conj_eq_or_eq hxT (R := Q) le_sup_left
    (by rw [Nat.card_congr φQ.toEquiv, hcard8])
    (fun r hr h1 h2 => quaternion_mul_self_of_ne φQ hc.mem_left hc.order hr h1 h2)
  have hPQ : P₁.map (MulAut.conj x).toMonoidHom = Q := by
    refine hP.resolve_left fun hP' => hx ?_
    have hxP : x ∈ Subgroup.normalizer (P₁ : Set G) :=
      mem_normalizer_of_conj_mem fun p hp => hP' ▸ hmem hp
    exact hmax x (h.mem_normalizer_zpowers hxT hxP) hxT hx2
  have hQP : Q.map (MulAut.conj x).toMonoidHom = P₁ := by
    refine hQ.resolve_right fun hQ' => ?_
    have huQ : x * u * x⁻¹ ∈ Q := hPQ ▸ hmem hc.self_mem
    rw [← hQ'] at huQ
    obtain ⟨q, hq, hqu⟩ := huQ
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqu
    have hqu' : q = u := mul_left_cancel (mul_right_cancel hqu)
    rcases hc.mem_inf u (hqu' ▸ hq) hc.self_mem with h1 | h1
    exacts [hc.self_ne.1 h1, hc.self_ne.2 h1]
  exact ⟨fun p hp => hPQ ▸ hmem hp, fun q hq => hQP ▸ hmem hq⟩

end CaseC3

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
