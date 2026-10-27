module

public import CFSG.HardMathSupport.Cooperstein.Proving.CentralTransfer
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaShapes
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.SwapTypeOffender
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open Equiv Equiv.Perm Subgroup

section OddOrder

variable {H : Type*} [Group H]

theorem eq_one_of_pow_two_pow_eq_one {N : Subgroup H} (hodd : Odd (Nat.card N)) {k : H}
    (hk : k ∈ N) {e : ℕ} (he : k ^ 2 ^ e = 1) : k = 1 := by
  have h1 : orderOf k ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one he
  have h2 : orderOf k ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk k hk]
    exact orderOf_dvd_natCard _
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)) h1 h2)

end OddOrder

section AltSeven

variable {H : Type*} [Group H]

theorem mul_comm_of_mem_comap {P : Type*} [Group P] {ψ : H →* P} (hker : ψ.ker ≤ center H)
    {T : Set H} (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {E : Subgroup P}
    (hE : ∀ e ∈ E, ∃ t ∈ T, ψ t = e) : ∀ a ∈ E.comap ψ, ∀ b ∈ E.comap ψ, a * b = b * a := by
  have hdec : ∀ a ∈ E.comap ψ, ∃ t ∈ T, ∃ c ∈ center H, t * c = a := by
    intro a ha
    obtain ⟨t, ht, hta⟩ := hE _ ha
    refine ⟨t, ht, t⁻¹ * a, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hta, inv_mul_cancel]
  intro a ha b hb
  obtain ⟨t, ht, c, hc, rfl⟩ := hdec a ha
  obtain ⟨t', ht', c', hc', rfl⟩ := hdec b hb
  have htt := hT t ht t' ht'
  have hct' : t' * c = c * t' := mem_center_iff.mp hc t'
  have hc't : t * c' = c' * t := mem_center_iff.mp hc' t
  have hcc : c' * c = c * c' := mem_center_iff.mp hc c'
  calc t * c * (t' * c') = t * (c * t') * c' := by group
    _ = t * (t' * c) * c' := by rw [← hct']
    _ = t * t' * (c * c') := by group
    _ = t' * t * (c' * c) := by rw [htt, hcc]
    _ = t' * (t * c') * c := by group
    _ = t' * (c' * t) * c := by rw [hc't]
    _ = t' * c' * (t * c) := by group

theorem swap_mul_swap_mem_alternatingGroup_fin_seven {a b c d : Fin 7} (hab : a ≠ b)
    (hcd : c ≠ d) : swap a b * swap c d ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  rfl

theorem relIndex_alternatingGroup_mul_card {E : Subgroup (Perm (Fin 7))}
    (hE : E ≤ alternatingGroup (Fin 7)) :
    E.relIndex (alternatingGroup (Fin 7)) * 2 * Nat.card E = 5040 := by
  have h1 := Subgroup.relIndex_mul_index hE
  rw [alternatingGroup.index_eq_two] at h1
  rw [h1, Subgroup.index_mul_card, Nat.card_perm, Nat.card_fin]
  rfl

def sylowThreeMap (p : Fin 3 × Fin 3) : Perm (Fin 7) :=
  (swap 0 1 * swap 1 2) ^ (p.1 : ℕ) * (swap 3 4 * swap 4 5) ^ (p.2 : ℕ)

theorem sylowThreeMap_add (p q : Fin 3 × Fin 3) :
    sylowThreeMap (p + q) = sylowThreeMap p * sylowThreeMap q := by
  have h1 : (swap (0 : Fin 7) 1 * swap 1 2) ^ 3 = 1 := by decide +kernel
  have h2 : (swap (3 : Fin 7) 4 * swap 4 5) ^ 3 = 1 := by decide +kernel
  have hc : Commute (swap (0 : Fin 7) 1 * swap 1 2) (swap 3 4 * swap 4 5) := by
    show _ * _ = _ * _
    decide +kernel
  simp only [sylowThreeMap, Prod.fst_add, Prod.snd_add, Fin.val_add]
  generalize swap (0 : Fin 7) 1 * swap 1 2 = x at h1 hc ⊢
  generalize swap (3 : Fin 7) 4 * swap 4 5 = y at h2 hc ⊢
  rw [← pow_eq_pow_mod _ h1, ← pow_eq_pow_mod _ h2, pow_add, pow_add]
  calc x ^ (p.1 : ℕ) * x ^ (q.1 : ℕ) * (y ^ (p.2 : ℕ) * y ^ (q.2 : ℕ)) =
        x ^ (p.1 : ℕ) * ((x ^ (q.1 : ℕ) * y ^ (p.2 : ℕ)) * y ^ (q.2 : ℕ)) := by
        simp only [mul_assoc]
    _ = x ^ (p.1 : ℕ) * ((y ^ (p.2 : ℕ) * x ^ (q.1 : ℕ)) * y ^ (q.2 : ℕ)) := by
        rw [(hc.pow_pow (q.1 : ℕ) (p.2 : ℕ)).eq]
    _ = x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ) * (x ^ (q.1 : ℕ) * y ^ (q.2 : ℕ)) := by
        simp only [mul_assoc]

theorem sylowThreeMap_injective : Function.Injective sylowThreeMap := by
  have h : ∀ p q : Fin 3 × Fin 3, sylowThreeMap p 0 = sylowThreeMap q 0 →
      sylowThreeMap p 3 = sylowThreeMap q 3 → p = q := by decide +kernel
  intro p q hpq
  exact h p q (by rw [hpq]) (by rw [hpq])

def sylowThree : Subgroup (Perm (Fin 7)) where
  carrier := Set.range sylowThreeMap
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, sylowThreeMap_add p q⟩
  one_mem' := ⟨0, by simp [sylowThreeMap]⟩
  inv_mem' := by
    rintro _ ⟨p, rfl⟩
    refine ⟨-p, ?_⟩
    rw [eq_inv_iff_mul_eq_one, ← sylowThreeMap_add, neg_add_cancel]
    simp [sylowThreeMap]

theorem card_sylowThree : Nat.card sylowThree = 9 := by
  show Nat.card (Set.range sylowThreeMap) = 9
  rw [Nat.card_range_of_injective sylowThreeMap_injective]
  simp

theorem sylowThree_le_alternatingGroup : sylowThree ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨p, rfl⟩
  exact mul_mem (pow_mem (swap_mul_swap_mem_alternatingGroup_fin_seven (by decide) (by decide)) _)
    (pow_mem (swap_mul_swap_mem_alternatingGroup_fin_seven (by decide) (by decide)) _)

theorem orderOf_five_cycle : orderOf (swap (0 : Fin 7) 1 * swap 1 2 * (swap 2 3 * swap 3 4)) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem orderOf_seven_cycle :
    orderOf (swap (0 : Fin 7) 1 * swap 1 2 * (swap 2 3 * swap 3 4) * (swap 4 5 * swap 5 6)) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem center_eq_bot_of_commute_lifts [Finite H] (hH : commutator H = ⊤)
    (hodd : Odd (Nat.card (center H))) {ψ : H →* Perm (Fin 7)}
    (hψ : alternatingGroup (Fin 7) ≤ ψ.range) (hker : ψ.ker ≤ center H) {h₁ h₂ : H}
    (h1 : ψ h₁ = swap 0 1 * swap 1 2) (h2 : ψ h₂ = swap 3 4 * swap 4 5)
    (h12 : h₁ * h₂ = h₂ * h₁) : center H = ⊥ := by
  have hrange : ψ.range = alternatingGroup (Fin 7) := by
    refine le_antisymm ?_ hψ
    rintro _ ⟨h, rfl⟩
    have hk := Abelianization.commutator_subset_ker (Perm.sign.comp ψ)
    rw [hH] at hk
    exact mem_alternatingGroup.mpr (MonoidHom.mem_ker.mp (hk (mem_top h)))
  have hpow : ∀ (E : Subgroup (Perm (Fin 7))) (T : Set H), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) →
      (∀ e ∈ E, ∃ t ∈ T, ψ t = e) → ∀ z ∈ center H,
        z ^ E.relIndex (alternatingGroup (Fin 7)) = 1 := by
    intro E T hT hE z hz
    have : Group.IsPerfect H := ⟨hH⟩
    have hB := mul_comm_of_mem_comap hker hT hE
    have h := Cooperstein.Proving.pow_index_eq_one_of_central_of_perfect (E.comap ψ)
      (fun x y => Subtype.ext (hB x x.2 y y.2)) hz
    rwa [index_comap, hrange] at h
  have hcyc : ∀ h : H, ∀ z ∈ center H,
      z ^ (zpowers (ψ h)).relIndex (alternatingGroup (Fin 7)) = 1 := by
    intro h z hz
    refine hpow (zpowers (ψ h)) (Set.range fun n : ℤ => h ^ n) ?_ ?_ z hz
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      exact ((Commute.refl h).zpow_zpow m n).eq
    · intro e he
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
      exact ⟨h ^ n, ⟨n, rfl⟩, map_zpow ψ h n⟩
  have hc5 : swap (0 : Fin 7) 1 * swap 1 2 * (swap 2 3 * swap 3 4) ∈ alternatingGroup (Fin 7) :=
    mul_mem (swap_mul_swap_mem_alternatingGroup_fin_seven (by decide) (by decide))
      (swap_mul_swap_mem_alternatingGroup_fin_seven (by decide) (by decide))
  have hc7 : swap (0 : Fin 7) 1 * swap 1 2 * (swap 2 3 * swap 3 4) * (swap 4 5 * swap 5 6) ∈
      alternatingGroup (Fin 7) :=
    mul_mem hc5 (swap_mul_swap_mem_alternatingGroup_fin_seven (by decide) (by decide))
  obtain ⟨h₅, h5⟩ := MonoidHom.mem_range.mp (hψ hc5)
  obtain ⟨h₇, h7⟩ := MonoidHom.mem_range.mp (hψ hc7)
  have hr5 : (zpowers (ψ h₅)).relIndex (alternatingGroup (Fin 7)) = 504 := by
    have h := relIndex_alternatingGroup_mul_card (E := zpowers (ψ h₅))
      (zpowers_le.mpr (by rw [h5]; exact hc5))
    have hcard : Nat.card (zpowers (ψ h₅)) = 5 := by
      rw [Nat.card_zpowers, h5, orderOf_five_cycle]
    rw [hcard] at h
    omega
  have hr7 : (zpowers (ψ h₇)).relIndex (alternatingGroup (Fin 7)) = 360 := by
    have h := relIndex_alternatingGroup_mul_card (E := zpowers (ψ h₇))
      (zpowers_le.mpr (by rw [h7]; exact hc7))
    have hcard : Nat.card (zpowers (ψ h₇)) = 7 := by
      rw [Nat.card_zpowers, h7, orderOf_seven_cycle]
    rw [hcard] at h
    omega
  have hr9 : sylowThree.relIndex (alternatingGroup (Fin 7)) = 280 := by
    have h := relIndex_alternatingGroup_mul_card sylowThree_le_alternatingGroup
    rw [card_sylowThree] at h
    omega
  have h9 : ∀ z ∈ center H, z ^ sylowThree.relIndex (alternatingGroup (Fin 7)) = 1 := by
    refine hpow sylowThree {x | ∃ i j : ℕ, h₁ ^ i * h₂ ^ j = x} ?_ ?_
    · rintro _ ⟨i, j, rfl⟩ _ ⟨i', j', rfl⟩
      have hc : Commute h₁ h₂ := h12
      exact (((Commute.refl h₁).pow_pow i i').mul_right (hc.pow_pow i j')).mul_left
        ((hc.symm.pow_pow j i').mul_right ((Commute.refl h₂).pow_pow j j')) |>.eq
    · rintro _ ⟨⟨i, j⟩, rfl⟩
      exact ⟨h₁ ^ (i : ℕ) * h₂ ^ (j : ℕ), ⟨i, j, rfl⟩, by rw [map_mul, map_pow, map_pow, h1, h2]; rfl⟩
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  have h280 := h9 z hz
  have h504 := hcyc h₅ z hz
  have h360 := hcyc h₇ z hz
  rw [hr9] at h280
  rw [hr5] at h504
  rw [hr7] at h360
  have h56 : z ^ Nat.gcd 280 504 = 1 := pow_gcd_eq_one.mpr ⟨h280, h504⟩
  have h8 : z ^ Nat.gcd (Nat.gcd 280 504) 360 = 1 := pow_gcd_eq_one.mpr ⟨h56, h360⟩
  have h8' : z ^ 2 ^ 3 = 1 := by
    have e : Nat.gcd (Nat.gcd 280 504) 360 = 2 ^ 3 := by norm_num
    rwa [e] at h8
  exact eq_one_of_pow_two_pow_eq_one hodd hz h8'

end AltSeven

section Commutator

variable {K : Type*} [Group K]

theorem commutator_mul_mul_eq {u v p q : K} (hpv : Commute p v) (hpq : Commute p q)
    (hqu : Commute q u) :
    u * p * (v * q) * (u * p)⁻¹ * (v * q)⁻¹ = u * v * u⁻¹ * v⁻¹ := by
  have e1 : p * (v * q) * p⁻¹ = v * q := by rw [(hpv.mul_right hpq).eq]; group
  have e2 : q * u⁻¹ * q⁻¹ = u⁻¹ := by rw [hqu.inv_right.eq]; group
  calc u * p * (v * q) * (u * p)⁻¹ * (v * q)⁻¹ = u * (p * (v * q) * p⁻¹) * u⁻¹ * q⁻¹ * v⁻¹ := by
        group
    _ = u * v * (q * u⁻¹ * q⁻¹) * v⁻¹ := by rw [e1]; group
    _ = u * v * u⁻¹ * v⁻¹ := by rw [e2]

theorem commute_of_inverting {y₁ y₂ a q₁ q₂ c : K} (hq₁ : q₁ = y₁ * (a * y₁ * a⁻¹))
    (hq₂ : q₂ = y₂⁻¹ * (a * y₂ * a⁻¹)) (hc : c = y₁ * y₂ * y₁⁻¹ * y₂⁻¹)
    (hac : a * c * a⁻¹ * c⁻¹ = 1) (h12 : Commute q₁ y₂) (h1q : Commute q₁ q₂)
    (h21 : Commute q₂ y₁) (hc1 : Commute c y₁) :
    c * c = 1 := by
  have e1 : a * y₁ * a⁻¹ = y₁⁻¹ * q₁ := by rw [hq₁]; group
  have e2 : a * y₂ * a⁻¹ = y₂ * q₂ := by rw [hq₂]; group
  have e3 : a * c * a⁻¹ = c := by
    calc a * c * a⁻¹ = a * c * a⁻¹ * c⁻¹ * c := by group
      _ = c := by rw [hac, one_mul]
  have e4 : c = y₁⁻¹ * y₂ * y₁ * y₂⁻¹ := by
    calc c = a * c * a⁻¹ := e3.symm
      _ = a * y₁ * a⁻¹ * (a * y₂ * a⁻¹) * (a * y₁ * a⁻¹)⁻¹ * (a * y₂ * a⁻¹)⁻¹ := by
          rw [hc]; group
      _ = y₁⁻¹ * q₁ * (y₂ * q₂) * (y₁⁻¹ * q₁)⁻¹ * (y₂ * q₂)⁻¹ := by rw [e1, e2]
      _ = y₁⁻¹ * y₂ * y₁⁻¹⁻¹ * y₂⁻¹ :=
          commutator_mul_mul_eq h12 h1q h21.inv_right
      _ = y₁⁻¹ * y₂ * y₁ * y₂⁻¹ := by rw [inv_inv]
  have e5 : c = y₂ * y₁ * y₂⁻¹ * y₁⁻¹ := by
    calc c = y₁ * c * y₁⁻¹ := by rw [← hc1.eq]; group
      _ = y₂ * y₁ * y₂⁻¹ * y₁⁻¹ := by rw [e4]; group
  calc c * c = c * (y₂ * y₁ * y₂⁻¹ * y₁⁻¹) := by rw [← e5]
    _ = y₁ * y₂ * y₁⁻¹ * y₂⁻¹ * (y₂ * y₁ * y₂⁻¹ * y₁⁻¹) := by rw [← hc]
    _ = 1 := by group

end Commutator

section NaturalSeven

open CFSG.AGLEmbedding CFSG.Open
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (NaturalSectionLSL
  odd_card_center_barM_sup mem_barM)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender (SwapType
  le_closure_swaps_of_swapType OffenderShapeConcl)
open MulAction

theorem swapType_of_odd_card {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hodd : Odd (Fintype.card Ω)) {E : Subgroup (Perm Ω)} (h : OffenderShapeConcl E) :
    SwapType E := by
  by_cases hf : ∃ p, ∀ g ∈ E, g p = p
  · exact h.1 hf
  · exfalso
    have heven : ∀ i : Ω, Even (Nat.card (orbit E i)) := by
      rcases h.2 hf with ⟨hall, -⟩ | ⟨-, h24, -⟩
      · intro i; rw [hall i]; exact even_two
      · intro i
        rcases h24 i with h2 | h4
        · rw [h2]; exact even_two
        · rw [h4]; exact ⟨2, rfl⟩
    have hsum := CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender.card_eq_sum_orbits E
    have hev : Even (Nat.card Ω) := by
      rw [hsum]
      exact Finset.sum_induction _ Even (fun a b ha hb => ha.add hb) (by decide : Even 0)
        (fun ω _ => heven _)
    rw [Nat.card_eq_fintype_card] at hev
    exact (Nat.not_even_iff_odd.2 hodd) hev


variable {G : Type} [Group G] [Finite G]

theorem center_barM_eq_bot_of_natural_seven {X S L : Subgroup G}
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hN : NaturalSectionLSL S L 7) : center ↥(barM (L ⊔ S) L) = ⊥ := by
  classical
  have hSL : S ≤ normalizer (L : Set G) :=
    Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : IsTwoPrimeComponent (L ⊔ S) L :=
    Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1
      hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S :=
    Cooperstein.Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hodd := odd_card_center_barM_sup hA' hSL
  have hLM : L ≤ L ⊔ S := le_sup_left
  have hSM : S ≤ L ⊔ S := le_sup_right
  obtain ⟨θ, hAlt, hkerC, hsh⟩ := hN.exists_theta_shapes (Or.inl rfl)
    (Cooperstein.Coordinator.blockV_le hA hL hSL)
    (Cooperstein.Coordinator.sup_le_normalizer_blockV S L) (isElemAbelian_omegaOneCenterOf _)
  obtain ⟨A, hAmax, hAQ⟩ := Cooperstein.Coordinator.exists_isMaxElemAbelian_not_le hA hL hSL
  have hAC := Cooperstein.Coordinator.not_le_centralizer_blockV_of_not_le hA hL hSL hAmax.1 hAQ
  have hsw : SwapType ((A.subgroupOf (L ⊔ S)).map θ) :=
    swapType_of_odd_card ⟨3, by simp⟩ (hsh A hAmax)
  obtain ⟨a₀, ha₀A, ha₀C⟩ := Set.not_subset.mp hAC
  have ha₀M : a₀ ∈ L ⊔ S := hSM (hAmax.1 ha₀A)
  have hne : θ ⟨a₀, ha₀M⟩ ≠ 1 := fun h => ha₀C ((hkerC ⟨a₀, ha₀M⟩).mp h)
  have hex : ∃ t ∈ (A.subgroupOf (L ⊔ S)).map θ, t.IsSwap := by
    by_contra hno
    have hempty : {t : Perm (Fin 7) | t ∈ (A.subgroupOf (L ⊔ S)).map θ ∧ t.IsSwap} = ∅ :=
      Set.eq_empty_of_forall_notMem fun t ht => hno ⟨t, ht.1, ht.2⟩
    have hmem : (⟨a₀, ha₀M⟩ : ↥(L ⊔ S)) ∈ A.subgroupOf (L ⊔ S) := mem_subgroupOf.mpr ha₀A
    have h1 := le_closure_swaps_of_swapType hsw (mem_map_of_mem θ hmem)
    rw [hempty, Subgroup.closure_empty, mem_bot] at h1
    exact hne h1
  obtain ⟨t, htE, i, j, hij, hθt⟩ := hex
  obtain ⟨⟨a, haM⟩, haA, rfl⟩ := mem_map.mp htE
  have haS : a ∈ S := hAmax.1 (mem_subgroupOf.mp haA)
  have hj0 : swap i 0 j ≠ 0 := by
    intro h
    rw [swap_apply_eq_iff, swap_apply_right] at h
    exact hij h.symm
  set τ : Perm (Fin 7) := swap (swap i 0 j) 1 * swap i 0 with hτ
  have hτi : τ i = 0 := by
    rw [hτ, Perm.mul_apply, swap_apply_left]
    exact swap_apply_of_ne_of_ne (Ne.symm hj0) (by decide)
  have hτj : τ j = 1 := by
    rw [hτ, Perm.mul_apply, swap_apply_left]
  set θ' : ↥(L ⊔ S) →* Perm (Fin 7) := (MulAut.conj τ).toMonoidHom.comp θ with hθ'
  have hθ'a : θ' ⟨a, haM⟩ = swap 0 1 := by
    show τ * θ ⟨a, haM⟩ * τ⁻¹ = swap 0 1
    rw [hθt, ← swap_apply_apply, hτi, hτj]
  have hker' : ∀ m : ↥(L ⊔ S), θ' m = 1 ↔ (m : G) ∈ centralizer (blockV S L : Set G) :=
    fun m => by
      rw [← hkerC m]
      show τ * θ m * τ⁻¹ = 1 ↔ θ m = 1
      constructor
      · intro h
        calc θ m = τ⁻¹ * (τ * θ m * τ⁻¹) * τ := by group
          _ = 1 := by rw [h]; group
      · intro h
        rw [h]
        group
  have hAlt' : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l : ↥L, θ' ⟨l, hLM l.2⟩ = σ := by
    intro σ hσ
    obtain ⟨l, hl⟩ := hAlt (τ⁻¹ * σ * τ⁻¹⁻¹) (Normal.conj_mem inferInstance σ hσ τ⁻¹)
    refine ⟨l, ?_⟩
    show τ * θ ⟨l, hLM l.2⟩ * τ⁻¹ = σ
    rw [hl]
    group
  set φ : ↥L →* Perm (Fin 7) := θ'.comp (inclusion hLM) with hφ
  set π : ↥L →* ↥(barM (L ⊔ S) L) := Cooperstein.Proving.barMHomSub hLM with hπ
  have hπs : Function.Surjective π := Cooperstein.Proving.barMHomSub_surjective hLM
  have hQC : pCoreOf 2 (L ⊔ S) ≤ centralizer (blockV S L : Set G) := fun x hx =>
    AscTenThree.le_centralizer_omegaOneCenterOf_self _ hx
  have hle : π.ker ≤ φ.ker := by
    intro l hl
    rw [hπ, Cooperstein.Proving.ker_barMHomSub, mem_subgroupOf] at hl
    exact MonoidHom.mem_ker.mpr ((hker' (inclusion hLM l)).mpr (hQC hl))
  let ψ : ↥(barM (L ⊔ S) L) →* Perm (Fin 7) :=
    (QuotientGroup.lift π.ker φ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm.toMonoidHom
  have hψπ : ∀ l, ψ (π l) = φ l := by
    intro l
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm (π l) =
        (QuotientGroup.mk l : ↥L ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift π.ker φ hle
      ((QuotientGroup.quotientKerEquivOfSurjective π hπs).symm (π l)) = φ l
    rw [h1, QuotientGroup.lift_mk]
  have hcentral := Cooperstein.Coordinator.barM_inf_le_center_of_core_le hLs
    (hLM.trans (Cooperstein.Coordinator.le_normalizer_centralizer_blockV S L))
    (inf_le_right.trans hQC) (Cooperstein.Coordinator.not_le_centralizer_blockV hA hL hSL)
  have hcen : ∀ l : ↥L, φ l = 1 → π l ∈ center ↥(barM (L ⊔ S) L) := by
    intro l hl
    have hlC : (l : G) ∈ centralizer (blockV S L : Set G) := (hker' (inclusion hLM l)).mp hl
    have hmem : (QuotientGroup.mk (inclusion hLM l) : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S)) ∈
        barM (L ⊔ S) (L ⊓ centralizer (blockV S L : Set G)) :=
      (mem_barM _).2 ⟨inclusion hLM l, ⟨l.2, hlC⟩, rfl⟩
    obtain ⟨z, hz, hzl⟩ := hcentral hmem
    have hzπ : z = π l := Subtype.ext hzl
    rw [← hzπ]
    exact hz
  have hker : ψ.ker ≤ center ↥(barM (L ⊔ S) L) := by
    intro w hw
    obtain ⟨l, rfl⟩ := hπs w
    rw [MonoidHom.mem_ker, hψπ] at hw
    exact hcen l hw
  have hrange : alternatingGroup (Fin 7) ≤ ψ.range := by
    intro σ hσ
    obtain ⟨l, hl⟩ := hAlt' σ hσ
    exact ⟨π l, by rw [hψπ]; exact hl⟩
  obtain ⟨y₁, hy₁⟩ := hAlt' (swap 0 1 * swap 1 2)
    (swap_mul_swap_mem_alternatingGroup_fin_seven (by decide) (by decide))
  obtain ⟨y₂, hy₂⟩ := hAlt' (swap 3 4 * swap 4 5)
    (swap_mul_swap_mem_alternatingGroup_fin_seven (by decide) (by decide))
  have hnorm : ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun l hl => (mem_normalizer_iff.mp (hSL haS) l).mp hl
  set â : ↥(L ⊔ S) := ⟨a, haM⟩ with hâ
  set ŷ₁ : ↥(L ⊔ S) := inclusion hLM y₁ with hŷ₁
  set ŷ₂ : ↥(L ⊔ S) := inclusion hLM y₂ with hŷ₂
  have hθy₁ : θ' ŷ₁ = swap 0 1 * swap 1 2 := hy₁
  have hθy₂ : θ' ŷ₂ = swap 3 4 * swap 4 5 := hy₂
  have hq₁L : ((ŷ₁ * (â * ŷ₁ * â⁻¹) : ↥(L ⊔ S)) : G) ∈ L := L.mul_mem y₁.2 (hnorm _ y₁.2)
  have hq₂L : ((ŷ₂⁻¹ * (â * ŷ₂ * â⁻¹) : ↥(L ⊔ S)) : G) ∈ L :=
    L.mul_mem (L.inv_mem y₂.2) (hnorm _ y₂.2)
  have hcL : ((ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹ : ↥(L ⊔ S)) : G) ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem y₁.2 y₂.2) (L.inv_mem y₁.2)) (L.inv_mem y₂.2)
  have hq₁θ : θ' (ŷ₁ * (â * ŷ₁ * â⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, hθy₁, hθ'a]
    decide +kernel
  have hq₂θ : θ' (ŷ₂⁻¹ * (â * ŷ₂ * â⁻¹)) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hθy₂, hθ'a]
    decide +kernel
  have hcθ : θ' (ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hθy₁, hθy₂]
    decide +kernel
  have hq₁Z := hcen ⟨_, hq₁L⟩ hq₁θ
  have hq₂Z := hcen ⟨_, hq₂L⟩ hq₂θ
  have hcZ := hcen ⟨_, hcL⟩ hcθ
  have hcC : ((ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹ : ↥(L ⊔ S)) : G) ∈ centralizer (blockV S L : Set G) :=
    (hker' _).mp hcθ
  set c : G := ((ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹ : ↥(L ⊔ S)) : G) with hcdef
  have hcN : c ∈ normalizer (S : Set G) :=
    Cooperstein.Coordinator.inf_centralizer_blockV_le_normalizer hA hL hSL
      ⟨(ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹ : ↥(L ⊔ S)).2, hcC⟩
  have hacS : a * c * a⁻¹ * c⁻¹ ∈ S := by
    have h1 : c * a⁻¹ * c⁻¹ ∈ S := (mem_normalizer_iff.mp hcN a⁻¹).mp (S.inv_mem haS)
    have h2 := S.mul_mem haS h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  have hacC : a * c * a⁻¹ * c⁻¹ ∈ centralizer (blockV S L : Set G) := by
    have h1 : a * c * a⁻¹ ∈ centralizer (blockV S L : Set G) :=
      (mem_normalizer_iff.mp (Cooperstein.Coordinator.le_normalizer_centralizer_blockV S L haM)
        c).mp hcC
    exact mul_mem h1 (inv_mem hcC)
  have hacQ : a * c * a⁻¹ * c⁻¹ ∈ pCoreOf 2 (L ⊔ S) :=
    Cooperstein.Coordinator.inf_centralizer_blockV_le_twoCore hA hL hSL ⟨hacS, hacC⟩
  set mk : ↥(L ⊔ S) →* ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S) :=
    QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ S)) with hmk
  have hmk1 : ∀ x : ↥(L ⊔ S), (x : G) ∈ pCoreOf 2 (L ⊔ S) → mk x = 1 := by
    intro x hx
    have h : x ∈ (Cooperstein.Proving.barMHomOf (le_refl (L ⊔ S))).ker := by
      rw [Cooperstein.Proving.ker_barMHomOf, mem_subgroupOf]
      exact hx
    exact MonoidHom.mem_ker.mp h
  have hcomm : ∀ u w : ↥L, π u ∈ center ↥(barM (L ⊔ S) L) →
      Commute (mk (inclusion hLM u)) (mk (inclusion hLM w)) := by
    intro u w hu
    exact (congrArg Subtype.val (mem_center_iff.mp hu (π w))).symm
  have hcc : mk (ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹) * mk (ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹) = 1 := by
    refine commute_of_inverting (y₁ := mk ŷ₁) (y₂ := mk ŷ₂) (a := mk â)
      (q₁ := mk (ŷ₁ * (â * ŷ₁ * â⁻¹))) (q₂ := mk (ŷ₂⁻¹ * (â * ŷ₂ * â⁻¹)))
      (by simp only [map_mul, map_inv]) (by simp only [map_mul, map_inv])
      (by simp only [map_mul, map_inv]) ?_ (hcomm ⟨_, hq₁L⟩ y₂ hq₁Z)
      (hcomm ⟨_, hq₁L⟩ ⟨_, hq₂L⟩ hq₁Z) (hcomm ⟨_, hq₂L⟩ y₁ hq₂Z) (hcomm ⟨_, hcL⟩ y₁ hcZ)
    have h := hmk1 (â * (ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹) * â⁻¹ * (ŷ₁ * ŷ₂ * ŷ₁⁻¹ * ŷ₂⁻¹)⁻¹) hacQ
    simpa only [map_mul, map_inv] using h
  have hc1 : π ⟨_, hcL⟩ = 1 :=
    eq_one_of_pow_two_pow_eq_one (N := center ↥(barM (L ⊔ S) L)) hodd hcZ (e := 1)
      (Subtype.ext (by rw [pow_one, pow_two]; exact hcc))
  have h12 : π y₁ * π y₂ = π y₂ * π y₁ := by
    have h : π y₁ * π y₂ * (π y₁)⁻¹ * (π y₂)⁻¹ = 1 := by
      rw [← hc1]
      apply Subtype.ext
      rfl
    calc π y₁ * π y₂ = π y₁ * π y₂ * (π y₁)⁻¹ * (π y₂)⁻¹ * (π y₂ * π y₁) := by group
      _ = π y₂ * π y₁ := by rw [h, one_mul]
  exact center_eq_bot_of_commute_lifts hLs.component.2.2.1 hodd hrange hker
    (by rw [hψπ]; exact hy₁) (by rw [hψπ]; exact hy₂) h12

end NaturalSeven

end CFSG.HardMathSupport.RichardWeiss.Coordinator
