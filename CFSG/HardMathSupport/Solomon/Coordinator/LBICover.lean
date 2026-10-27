module

public import CFSG.HardMathSupport.Solomon.Coordinator.LBIHopf

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

@[expose] def lbiPull {X Y S : Type} [Group X] [Group Y] [Group S] (π : Y →* X) (θ : S →* X) :
    Subgroup (Y × S) :=
  (π.comp (MonoidHom.fst Y S)).eqLocus (θ.comp (MonoidHom.snd Y S))

theorem lbi_card_ge_three {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (h3 : ∀ w ∈ K, w ^ 3 = 1) (w : G) (hw : w ∈ K) (hw1 : w ≠ 1) : 3 ≤ Nat.card K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 K := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hg : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (h3 g g.2))
    rcases (Nat.dvd_prime Nat.prime_three).1 hg with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exfalso
    have : Subsingleton K := (Nat.card_eq_one_iff_unique.1 (by simpa using hk)).1
    exact hw1 (congrArg Subtype.val (Subsingleton.elim (⟨w, hw⟩ : K) 1))
  · rw [hk]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk0

theorem lbi_cover_equiv {X Y S : Type} [Group X] [Group Y] [Group S] [Finite Y] [Finite S]
    (π : Y →* X) (hπ : Function.Surjective π) (hcenπ : π.ker ≤ Subgroup.center Y)
    (hperfY : commutator Y = ⊤) (hZ : Nat.card π.ker = 3)
    (θ : S →* X) (hθ : Function.Surjective θ) (hcenθ : θ.ker ≤ Subgroup.center S)
    (hperfS : commutator S = ⊤) (hθ3 : ∀ w ∈ θ.ker, w ^ 3 = 1)
    (hθne : ∃ w ∈ θ.ker, w ≠ 1)
    (hbound : ∀ (P : Type) [Group P] [Finite P] (η : P →* X), Function.Surjective η →
      η.ker ≤ Subgroup.center P → commutator P = ⊤ → (∀ w ∈ η.ker, w ^ 3 = 1) →
        Nat.card η.ker ∣ 3) :
    Nonempty (Y ≃* S) := by
  classical
  set P : Subgroup (Y × S) := lbiPull π θ with hP
  set Q : Subgroup (Y × S) := ⁅P, P⁆ with hQ
  have hQP : Q ≤ P := by
    rw [hQ, Subgroup.commutator_le]
    intro a ha b hb
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  have hP1 : P.map (MonoidHom.fst Y S) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨s, hs⟩ := hθ (π y)
    exact ⟨(y, s), hs.symm, rfl⟩
  have hP2 : P.map (MonoidHom.snd Y S) = ⊤ := by
    rw [eq_top_iff]
    intro s _
    obtain ⟨y, hy⟩ := hπ (θ s)
    exact ⟨(y, s), hy, rfl⟩
  have hQ1 : Q.map (MonoidHom.fst Y S) = ⊤ := by
    rw [hQ, Subgroup.map_commutator, hP1, ← commutator_def]
    exact hperfY
  have hQ2 : Q.map (MonoidHom.snd Y S) = ⊤ := by
    rw [hQ, Subgroup.map_commutator, hP2, ← commutator_def]
    exact hperfS
  let ρ1 : ↥Q →* Y := (MonoidHom.fst Y S).comp Q.subtype
  let ρ2 : ↥Q →* S := (MonoidHom.snd Y S).comp Q.subtype
  have hρ1 : Function.Surjective ρ1 := by
    intro y
    have : y ∈ Q.map (MonoidHom.fst Y S) := by rw [hQ1]; trivial
    obtain ⟨q, hq, rfl⟩ := this
    exact ⟨⟨q, hq⟩, rfl⟩
  have hρ2 : Function.Surjective ρ2 := by
    intro s
    have : s ∈ Q.map (MonoidHom.snd Y S) := by rw [hQ2]; trivial
    obtain ⟨q, hq, rfl⟩ := this
    exact ⟨⟨q, hq⟩, rfl⟩
  let η : ↥Q →* X := π.comp ρ1
  have hη : Function.Surjective η := hπ.comp hρ1
  have hkerη : ∀ q : ↥Q, q ∈ η.ker → ((q : Y × S).1 ∈ π.ker ∧ (q : Y × S).2 ∈ θ.ker) := by
    intro q hq
    have h1 : π (q : Y × S).1 = 1 := hq
    have hpq : π (q : Y × S).1 = θ (q : Y × S).2 := hQP q.2
    have h2 : θ (q : Y × S).2 = 1 := by
      rw [← hpq]
      exact h1
    exact ⟨h1, h2⟩
  have hcenη : η.ker ≤ Subgroup.center ↥Q := by
    intro q hq
    obtain ⟨h1, h2⟩ := hkerη q hq
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Prod.ext
    · exact (Subgroup.mem_center_iff.1 (hcenπ h1) (g : Y × S).1)
    · exact (Subgroup.mem_center_iff.1 (hcenθ h2) (g : Y × S).2)
  have hexpη : ∀ w ∈ η.ker, w ^ 3 = 1 := by
    intro q hq
    obtain ⟨h1, h2⟩ := hkerη q hq
    apply Subtype.ext
    apply Prod.ext
    · have := pow_card_eq_one' (G := π.ker) (x := ⟨_, h1⟩)
      rw [hZ] at this
      exact congrArg Subtype.val this
    · exact hθ3 _ h2
  have : Finite X := Finite.of_surjective π hπ
  have hX : commutator X = ⊤ := by
    have := Subgroup.map_commutator (⊤ : Subgroup Y) (⊤ : Subgroup Y) π
    rw [Subgroup.map_top_of_surjective π hπ] at this
    rw [commutator_def, ← this, ← commutator_def, hperfY, Subgroup.map_top_of_surjective π hπ]
  have hdec : ∀ p ∈ P, ∃ q ∈ Q, ∃ c : Y × S, c.1 ∈ π.ker ∧ c.2 ∈ θ.ker ∧ p = q * c := by
    intro p hp
    obtain ⟨q', hq', hq'1⟩ : ∃ q' ∈ Q, π q'.1 = π p.1 := by
      obtain ⟨y, hy⟩ := hπ (π p.1)
      have : y ∈ Q.map (MonoidHom.fst Y S) := by rw [hQ1]; trivial
      obtain ⟨q, hq, rfl⟩ := this
      exact ⟨q, hq, hy⟩
    refine ⟨q', hq', q'⁻¹ * p, ?_, ?_, by group⟩
    · show π (q'⁻¹ * p).1 = 1
      simp only [Prod.fst_mul, Prod.fst_inv, map_mul, map_inv, hq'1, inv_mul_cancel]
    · show θ (q'⁻¹ * p).2 = 1
      have h1 : π q'.1 = θ q'.2 := hQP hq'
      have h2 : π p.1 = θ p.2 := hp
      simp only [Prod.snd_mul, Prod.snd_inv, map_mul, map_inv, ← h1, ← h2, hq'1, inv_mul_cancel]
  have hcentral : ∀ c : Y × S, c.1 ∈ π.ker → c.2 ∈ θ.ker → ∀ g : Y × S, Commute c g := by
    intro c h1 h2 g
    apply Prod.ext
    · exact (Subgroup.mem_center_iff.1 (hcenπ h1) g.1).symm
    · exact (Subgroup.mem_center_iff.1 (hcenθ h2) g.2).symm
  have hQQ : ⁅Q, Q⁆ = Q := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
    · rw [hQ, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨q, hq, c, hc1, hc2, rfl⟩ := hdec a ha
      obtain ⟨q', hq', c', hc1', hc2', rfl⟩ := hdec b hb
      rw [lbi_commutatorElement_mul_mul (hcentral c hc1 hc2 _) (hcentral c hc1 hc2 c')
        (hcentral c' hc1' hc2' _)]
      rw [← hQ]
      exact Subgroup.commutator_mem_commutator hq hq'
  have hperfQ : commutator ↥Q = ⊤ := by
    have : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQQ
    exact this.commutator_eq_top
  have hbd := hbound ↥Q η hη hcenη hperfQ hexpη
  have cQ : Nat.card η.ker * Nat.card X = Nat.card ↥Q := Subgroup.card_ker_mul_card_of_surjective hη
  have cY : Nat.card π.ker * Nat.card X = Nat.card Y := Subgroup.card_ker_mul_card_of_surjective hπ
  have cS : Nat.card θ.ker * Nat.card X = Nat.card S := Subgroup.card_ker_mul_card_of_surjective hθ
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hYQ : Nat.card Y ≤ Nat.card ↥Q := Nat.card_le_card_of_surjective _ hρ1
  have hk3 : Nat.card η.ker ≤ 3 := Nat.le_of_dvd (by norm_num) hbd
  have hkQ : Nat.card ↥Q = Nat.card Y := by
    rw [hZ] at cY
    have : 3 * Nat.card X ≤ Nat.card η.ker * Nat.card X := by rw [cQ, cY]; omega
    have h3 : 3 ≤ Nat.card η.ker := Nat.le_of_mul_le_mul_right this hXpos
    have : Nat.card η.ker = 3 := le_antisymm hk3 h3
    rw [← cQ, this, ← cY]
  have hθge := lbi_card_ge_three θ.ker hθ3 hθne.choose hθne.choose_spec.1 hθne.choose_spec.2
  have hQS : Nat.card ↥Q ≤ Nat.card S := by
    rw [hkQ, ← cY, ← cS, hZ]
    exact Nat.mul_le_mul_right _ hθge
  have hb1 : Function.Bijective ρ1 :=
    Function.Surjective.bijective_of_nat_card_le hρ1 (by rw [hkQ])
  have hb2 : Function.Bijective ρ2 := Function.Surjective.bijective_of_nat_card_le hρ2 hQS
  exact ⟨(MulEquiv.ofBijective ρ1 hb1).symm.trans (MulEquiv.ofBijective ρ2 hb2)⟩

end CFSG.HardMathSupport.Solomon.Coordinator
