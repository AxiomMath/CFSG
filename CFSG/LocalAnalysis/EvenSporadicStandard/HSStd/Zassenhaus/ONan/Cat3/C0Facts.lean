module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3Defs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup

private lemma cycleType_five_cases {σ : Equiv.Perm (Fin 5)} :
    σ.cycleType = 0 ∨ σ.cycleType = {2} ∨ σ.cycleType = {3} ∨
    σ.cycleType = {4} ∨ σ.cycleType = {5} ∨ σ.cycleType = {2, 2} ∨
    σ.cycleType = {2, 3} := by
  have h2 : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => σ.two_le_of_mem_cycleType hn
  have hsum : σ.cycleType.sum ≤ 5 := by simpa using σ.sum_cycleType_le
  have hcard : σ.cycleType.card ≤ 2 := by
    have h := Multiset.card_nsmul_le_sum (s := σ.cycleType) (a := 2) h2
    simp only [nsmul_eq_mul] at h
    simp only [Nat.cast_id] at h
    omega
  interval_cases hc : σ.cycleType.card
  · rw [Multiset.card_eq_zero.mp hc]; decide
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hc
    rw [ha] at h2 hsum
    have ha2 : 2 ≤ a := h2 a (Multiset.mem_singleton_self a)
    have ha5 : a ≤ 5 := by simpa using hsum
    rw [ha]
    interval_cases a <;> decide
  · obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp hc
    rw [hxy] at h2 hsum
    have hx2 : 2 ≤ x := h2 x (by simp)
    have hy2 : 2 ≤ y := h2 y (by simp)
    have hsum2 : x + y ≤ 5 := by simpa using hsum
    have hx : x = 2 ∨ x = 3 := by omega
    have hy : y = 2 ∨ y = 3 := by omega
    rw [hxy]
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · decide
    · decide
    · decide
    · exfalso; omega

private lemma perm_five_order_lcm_mem (σ : Equiv.Perm (Fin 5)) :
    orderOf σ ∈ ({1,2,3,4,5,6} : Finset ℕ) := by
  rw [← Equiv.Perm.lcm_cycleType]
  have h2 : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => σ.two_le_of_mem_cycleType hn
  have hsum : σ.cycleType.sum ≤ 5 := by simpa using σ.sum_cycleType_le
  have hcard : σ.cycleType.card ≤ 2 := by
    have h := Multiset.card_nsmul_le_sum (s := σ.cycleType) (a := 2) h2
    simp only [nsmul_eq_mul] at h
    simp only [Nat.cast_id] at h
    omega
  interval_cases hc : σ.cycleType.card
  · rw [Multiset.card_eq_zero.mp hc]; decide
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hc
    rw [ha] at h2 hsum
    have ha2 : 2 ≤ a := h2 a (Multiset.mem_singleton_self a)
    have ha5 : a ≤ 5 := by simpa using hsum
    rw [ha]
    interval_cases a <;> decide
  · obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp hc
    rw [hxy] at h2 hsum
    have hx2 : 2 ≤ x := h2 x (by simp)
    have hy2 : 2 ≤ y := h2 y (by simp)
    have hsum2 : x + y ≤ 5 := by simpa using hsum
    have hx3 : x ≤ 3 := by omega
    have hy3 : y ≤ 3 := by omega
    rw [hxy]
    interval_cases x <;> interval_cases y <;> decide

private lemma perm_five_centralizer_le_six {σ : Equiv.Perm (Fin 5)} (hσ : 3 ≤ orderOf σ) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 5)))) ≤ 6 := by
  rcases cycleType_five_cases (σ := σ) with h | h | h | h | h | h | h
  · rw [← Equiv.Perm.lcm_cycleType, h] at hσ; norm_num at hσ
  · rw [← Equiv.Perm.lcm_cycleType, h] at hσ; norm_num at hσ
  · rw [Equiv.Perm.nat_card_centralizer, h]; norm_num
  · rw [Equiv.Perm.nat_card_centralizer, h]; norm_num
  · rw [Equiv.Perm.nat_card_centralizer, h]; norm_num
  · rw [← Equiv.Perm.lcm_cycleType, h] at hσ; norm_num at hσ
  · rw [Equiv.Perm.nat_card_centralizer, h]; norm_num

private lemma centralizer_doubleTransposition_not_comm {τ : Equiv.Perm (Fin 5)}
    (hτ : τ.cycleType = {2, 2}) :
    ∃ u v : Equiv.Perm (Fin 5),
      u ∈ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 5))) ∧
      v ∈ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 5))) ∧ u * v ≠ v * u := by
  let τ₀ : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3
  let u₀ : Equiv.Perm (Fin 5) := Equiv.swap 0 1
  let v₀ : Equiv.Perm (Fin 5) := Equiv.swap 0 2 * Equiv.swap 1 3
  have hτ₀ : τ₀.cycleType = {2, 2} :=
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup (x := 0) (y := 1) (z := 2) (t := 3) (by decide)
  have hu₀ : u₀ * τ₀ = τ₀ * u₀ := by decide
  have hv₀ : v₀ * τ₀ = τ₀ * v₀ := by decide
  have huv₀ : u₀ * v₀ ≠ v₀ * u₀ := by decide
  have hconj : IsConj τ₀ τ :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [hτ₀, hτ])
  rw [isConj_iff] at hconj
  obtain ⟨g, hg⟩ := hconj
  refine ⟨g * u₀ * g⁻¹, g * v₀ * g⁻¹, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    calc g * u₀ * g⁻¹ * (g * τ₀ * g⁻¹)
        = g * (u₀ * τ₀) * g⁻¹ := by group
      _ = g * (τ₀ * u₀) * g⁻¹ := by rw [hu₀]
      _ = g * τ₀ * g⁻¹ * (g * u₀ * g⁻¹) := by group
  · rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    calc g * v₀ * g⁻¹ * (g * τ₀ * g⁻¹)
        = g * (v₀ * τ₀) * g⁻¹ := by group
      _ = g * (τ₀ * v₀) * g⁻¹ := by rw [hv₀]
      _ = g * τ₀ * g⁻¹ * (g * v₀ * g⁻¹) := by group
  · intro h
    apply huv₀
    have h2 := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using h2

private theorem perm_five_abelian_card_le_six {A : Subgroup (Equiv.Perm (Fin 5))}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A ≤ 6 := by
  by_cases hbig : ∃ σ ∈ A, 3 ≤ orderOf σ
  · obtain ⟨σ, hσA, hσ⟩ := hbig
    have hAle : A ≤ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 5))) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hA a ha σ hσA
    exact (Nat.card_le_card_of_injective (Subgroup.inclusion hAle)
      (Subgroup.inclusion_injective hAle)).trans (perm_five_centralizer_le_six hσ)
  · push Not at hbig
    by_cases hbot : A = ⊥
    · rw [hbot]; simp
    · have hex : ∃ τ ∈ A, τ ≠ 1 := by
        by_contra h
        apply hbot
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        by_contra hx1
        exact h ⟨x, hx, hx1⟩
      obtain ⟨τ, hτA, hτne⟩ := hex
      have hτ2 : orderOf τ = 2 := by
        have hle := hbig τ hτA
        have hne : orderOf τ ≠ 1 := fun h => hτne (orderOf_eq_one_iff.mp h)
        have hpos := orderOf_pos τ
        omega
      have hAle : A ≤ Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 5))) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hA a ha τ hτA
      rcases cycleType_five_cases (σ := τ) with h | h | h | h | h | h | h
      · rw [← Equiv.Perm.lcm_cycleType, h] at hτ2
        exact absurd hτ2 (by decide)
      · have hcard : Nat.card (Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 5)))) = 12 := by
          rw [Equiv.Perm.nat_card_centralizer, h]; norm_num
        have hdvd : Nat.card A ∣ 12 := by
          rw [← hcard]; exact Subgroup.card_dvd_of_le hAle
        by_contra hnot
        simp only [not_le] at hnot
        have h3 : 3 ∣ Nat.card A := by
          have h12 : Nat.card A ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
          interval_cases hAc : Nat.card A <;> first | (norm_num at hdvd; done) | norm_num
        obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 h3
        have hco : orderOf (a : Equiv.Perm (Fin 5)) = 3 := by
          rw [Subgroup.orderOf_coe, ha]
        have := hbig (a : Equiv.Perm (Fin 5)) a.2
        omega
      · rw [← Equiv.Perm.lcm_cycleType, h] at hτ2
        exact absurd hτ2 (by decide)
      · rw [← Equiv.Perm.lcm_cycleType, h] at hτ2
        exact absurd hτ2 (by decide)
      · rw [← Equiv.Perm.lcm_cycleType, h] at hτ2
        exact absurd hτ2 (by decide)
      · have hcard : Nat.card (Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 5)))) = 8 := by
          rw [Equiv.Perm.nat_card_centralizer, h]; norm_num
        have hdvd : Nat.card A ∣ 8 := by
          rw [← hcard]; exact Subgroup.card_dvd_of_le hAle
        by_contra hnot
        simp only [not_le] at hnot
        have h8 : Nat.card A = 8 := by
          have hle : Nat.card A ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
          interval_cases hAc : Nat.card A <;> first | (norm_num at hdvd; done) | rfl
        have heq : A = Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin 5))) := by
          apply Subgroup.eq_of_le_of_card_ge hAle
          rw [h8, hcard]
        obtain ⟨u, v, hu, hv, huv⟩ := centralizer_doubleTransposition_not_comm h
        exact huv (hA u (by rw [heq]; exact hu) v (by rw [heq]; exact hv))
      · rw [← Equiv.Perm.lcm_cycleType, h] at hτ2
        exact absurd hτ2 (by decide)

private lemma lcm_three_mem {m a : ℕ}
    (hm : m ∈ ({1,2,3,4,5,6} : Finset ℕ)) (ha : a ∣ 3) :
    Nat.lcm a m ∈ ({1,2,3,4,5,6,12,15} : Finset ℕ) := by
  have ha' : a = 1 ∨ a = 3 := (Nat.dvd_prime Nat.prime_three).mp ha
  rcases ha' with rfl | rfl <;> fin_cases hm <;> decide

private lemma natCard_multiplicative_zmod_three : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private lemma orderOf_multiplicative_zmod_three_dvd (a : Multiplicative (ZMod 3)) :
    orderOf a ∣ 3 := by
  have h : orderOf a ∣ Nat.card (Multiplicative (ZMod 3)) := orderOf_dvd_natCard a
  rwa [natCard_multiplicative_zmod_three] at h

private theorem prod_three_perm_abelian_card_le_18
    {B : Subgroup (Multiplicative (ZMod 3) × Equiv.Perm (Fin 5))}
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 18 := by
  let φ : B →* Equiv.Perm (Fin 5) := (MonoidHom.snd _ _).comp B.subtype
  have hker : Nat.card φ.ker ≤ 3 := by
    have hinj : Function.Injective
        (fun k : φ.ker =>
          (((k : B) : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)).1)) := by
      intro k₁ k₂ h
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext h ?_
      have h1 : ((k₁ : B) : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)).2 = 1 := by
        have hk := k₁.2
        rw [MonoidHom.mem_ker] at hk
        exact hk
      have h2 : ((k₂ : B) : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)).2 = 1 := by
        have hk := k₂.2
        rw [MonoidHom.mem_ker] at hk
        exact hk
      rw [h1, h2]
    calc Nat.card φ.ker ≤ Nat.card (Multiplicative (ZMod 3)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = 3 := natCard_multiplicative_zmod_three
  have hrange : Nat.card φ.range ≤ 6 := by
    apply perm_five_abelian_card_le_six
    intro a ha b hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    have hab : a' * b' = b' * a' :=
      Subtype.ext (hB (a' : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) a'.2
        (b' : Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) b'.2)
    rw [← map_mul, ← map_mul, hab]
  rw [← card_ker_mul_card_range φ]
  exact (Nat.mul_le_mul hker hrange).trans (by norm_num)

private lemma orderOf_finRotate_five : orderOf (finRotate 5) = 5 := by
  have hcyc : Equiv.Perm.IsCycle (finRotate 5) :=
    isCycle_finRotate_of_le (n := 5) (by norm_num)
  rw [hcyc.orderOf, support_finRotate_of_le (n := 5) (by norm_num)]
  simp

private lemma threeA5OrS5_elim {C : Type*} [Group C] {P : Prop} (h : ThreeA5OrS5 C)
    (hA : (C ≃* Multiplicative (ZMod 3) × ↥(alternatingGroup (Fin 5))) → P)
    (hS : (C ≃* Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) → P) : P :=
  h.elim (fun hn => hn.elim hA) (fun hn => hn.elim hS)

namespace ThreeA5OrS5

variable {C : Type*} [Group C]

theorem card (h : ThreeA5OrS5 C) : Nat.card C = 180 ∨ Nat.card C = 360 := by
  refine threeA5OrS5_elim h (fun e => ?_) (fun e => ?_)
  · left
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_multiplicative_zmod_three,
      nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card]
  · right
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, natCard_multiplicative_zmod_three, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card]

theorem orderOf_mem (h : ThreeA5OrS5 C) (g : C) :
    orderOf g ∈ ({1, 2, 3, 4, 5, 6, 12, 15} : Finset ℕ) := by
  refine threeA5OrS5_elim h (fun e => ?_) (fun e => ?_)
  · have h1 : orderOf (e g).1 ∣ 3 := orderOf_multiplicative_zmod_three_dvd (e g).1
    have h2 : orderOf (e g).2 ∈ ({1,2,3,4,5,6} : Finset ℕ) := by
      have := perm_five_order_lcm_mem ((e g).2 : Equiv.Perm (Fin 5))
      rwa [Subgroup.orderOf_coe] at this
    have ho : orderOf g = Nat.lcm (orderOf (e g).1) (orderOf (e g).2) := by
      rw [← e.orderOf_eq, Prod.orderOf]
    rw [ho]
    exact lcm_three_mem h2 h1
  · have h1 : orderOf (e g).1 ∣ 3 := orderOf_multiplicative_zmod_three_dvd (e g).1
    have h2 : orderOf (e g).2 ∈ ({1,2,3,4,5,6} : Finset ℕ) := perm_five_order_lcm_mem (e g).2
    have ho : orderOf g = Nat.lcm (orderOf (e g).1) (orderOf (e g).2) := by
      rw [← e.orderOf_eq, Prod.orderOf]
    rw [ho]
    exact lcm_three_mem h2 h1

theorem card_le_of_comm (h : ThreeA5OrS5 C) {B : Subgroup C}
    (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) : Nat.card B ≤ 18 := by
  refine threeA5OrS5_elim h (fun e => ?_) (fun e => ?_)
  · let incl : Multiplicative (ZMod 3) × ↥(alternatingGroup (Fin 5)) →*
        Multiplicative (ZMod 3) × Equiv.Perm (Fin 5) :=
      (MonoidHom.fst _ _).prod
        ((Subgroup.subtype (alternatingGroup (Fin 5))).comp (MonoidHom.snd _ _))
    have hincl : Function.Injective incl := by
      intro x y hxy
      change (x.1, (x.2 : Equiv.Perm (Fin 5))) =
        (y.1, (y.2 : Equiv.Perm (Fin 5))) at hxy
      exact Prod.ext (Prod.ext_iff.mp hxy).1 (Subtype.coe_injective (Prod.ext_iff.mp hxy).2)
    let φ : C →* Multiplicative (ZMod 3) × Equiv.Perm (Fin 5) := incl.comp e.toMonoidHom
    have hφ : Function.Injective φ := hincl.comp e.injective
    have hcard : Nat.card B = Nat.card (B.map φ) :=
      Nat.card_congr (Subgroup.equivMapOfInjective B φ hφ).toEquiv
    rw [hcard]
    exact prod_three_perm_abelian_card_le_18 (fun a ha b hb => by
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [← map_mul, ← map_mul, hB a' ha' b' hb'])
  · have hcard : Nat.card B = Nat.card (B.map e.toMonoidHom) :=
      Nat.card_congr (Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).toEquiv
    rw [hcard]
    exact prod_three_perm_abelian_card_le_18 (fun a ha b hb => by
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [← map_mul, ← map_mul, hB a' ha' b' hb'])

theorem exists_orderOf_eq_five (h : ThreeA5OrS5 C) : ∃ g : C, orderOf g = 5 := by
  refine threeA5OrS5_elim h (fun e => ?_) (fun e => ?_)
  · let σ' : ↥(alternatingGroup (Fin 5)) :=
      ⟨finRotate 5, Equiv.Perm.finRotate_bit1_mem_alternatingGroup (n := 2)⟩
    refine ⟨e.symm (1, σ'), ?_⟩
    have hσ : orderOf σ' = 5 := by
      rw [← Subgroup.orderOf_coe σ']
      exact orderOf_finRotate_five
    rw [e.symm.orderOf_eq, Prod.orderOf, orderOf_one, hσ]
    norm_num
  · refine ⟨e.symm (1, finRotate 5), ?_⟩
    rw [e.symm.orderOf_eq, Prod.orderOf, orderOf_one, orderOf_finRotate_five]
    norm_num

end ThreeA5OrS5

namespace Cat3

variable {L : Type*} [Group L] {x : L}

theorem orderOf_mem_of_commute (hx : ThreeA5OrS5 ↥(centralizer ({x} : Set L))) {y : L}
    (hy : y * x = x * y) : orderOf y ∈ ({1, 2, 3, 4, 5, 6, 12, 15} : Finset ℕ) := by
  let y' : ↥(centralizer ({x} : Set L)) :=
    ⟨y, (Subgroup.mem_centralizer_singleton_iff).mpr hy⟩
  have h := ThreeA5OrS5.orderOf_mem hx y'
  have hcoe : orderOf y = orderOf y' := Subgroup.orderOf_coe y'
  rw [hcoe]
  exact h

theorem card_le_of_comm (hx : ThreeA5OrS5 ↥(centralizer ({x} : Set L))) {B : Subgroup L}
    (hBx : ∀ b ∈ B, b * x = x * b) (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    Nat.card B ≤ 18 := by
  have hle : B ≤ Subgroup.centralizer ({x} : Set L) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hBx b hb
  let B' : Subgroup ↥(Subgroup.centralizer ({x} : Set L)) := B.subgroupOf _
  have hB' : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    apply Subtype.ext
    exact hB (a : L) ha (b : L) hb
  have hcard : Nat.card B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← hcard]
  exact ThreeA5OrS5.card_le_of_comm hx hB'

theorem exists_orderOf_eq_five_commute (hx : ThreeA5OrS5 ↥(centralizer ({x} : Set L))) :
    ∃ y : L, orderOf y = 5 ∧ y * x = x * y := by
  obtain ⟨y', hy'⟩ := ThreeA5OrS5.exists_orderOf_eq_five hx
  refine ⟨(y' : L), ?_, (Subgroup.mem_centralizer_singleton_iff.mp y'.2)⟩
  rw [Subgroup.orderOf_coe]
  exact hy'

end Cat3

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
