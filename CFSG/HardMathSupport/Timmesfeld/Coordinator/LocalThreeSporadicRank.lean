module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadic

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.ComponentClassification.OuterAutomorphisms

variable {p : ℕ} {S : Type*} [Group S]

theorem le_inner_of_isPGroup (hout : Nat.Coprime p (Nat.card (Outer S)))
    {D : Subgroup (MulAut S)} (hD : IsPGroup p D) : D ≤ inner S := by
  intro d hd
  obtain ⟨k, hk⟩ := hD ⟨d, hd⟩
  have hdk : d ^ p ^ k = 1 := congrArg Subtype.val hk
  set q : Outer S := (QuotientGroup.mk' (inner S)) d with hq
  have h1 : q ^ p ^ k = 1 := by rw [hq, ← map_pow, hdk, map_one]
  have h2 : q ^ Nat.card (Outer S) = 1 := pow_card_eq_one'
  have h3 : orderOf q ∣ Nat.gcd (p ^ k) (Nat.card (Outer S)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k hout), Nat.dvd_one, orderOf_eq_one_iff]
    at h3
  exact (QuotientGroup.eq_one_iff d).mp h3

theorem exists_elemAbelian_of_le_inner (hcen : Subgroup.center S = ⊥) {D : Subgroup (MulAut S)}
    (hDi : D ≤ inner S) (hD : IsElemAbelian p D) :
    ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = Nat.card D := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    intro a b hab
    have hc : a⁻¹ * b ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut S => φ g) hab
      simp only [MulAut.conj_apply] at h
      calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
        _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h]
        _ = a⁻¹ * b * g := by group
    rw [hcen, Subgroup.mem_bot] at hc
    calc a = a * (a⁻¹ * b) := by rw [hc, mul_one]
      _ = b := by group
  refine ⟨D.comap MulAut.conj, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext
    apply hinj
    have hab := hD.1.is_comm.comm (⟨MulAut.conj (a : S), a.2⟩ : D) ⟨MulAut.conj (b : S), b.2⟩
    have := congrArg Subtype.val hab
    simpa only [Subgroup.coe_mul, map_mul] using this
  · apply hinj
    rw [map_pow, map_one]
    exact hD.2 _ hx
  · have hmap : (D.comap MulAut.conj).map (MulAut.conj : S →* MulAut S) = D := by
      rw [Subgroup.map_comap_eq, inf_eq_right]
      exact hDi
    rw [← Subgroup.card_map_of_injective hinj, hmap]

variable [Finite S]

theorem coprime_of_le_two (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn0 : n ≠ 0) (hn : n ≤ 2) :
    Nat.Coprime p n := by
  interval_cases n
  · exact absurd rfl hn0
  · exact Nat.coprime_one_right p
  · exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2

theorem exists_cube_of_aut (hp : p.Prime) (hp2 : p ≠ 2) (hcen : Subgroup.center S = ⊥)
    (hout : Nat.card (Outer S) ≤ 2) {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 3) : ∃ E : Subgroup S, IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have hcop : Nat.Coprime p (Nat.card (Outer S)) :=
    coprime_of_le_two hp hp2 Nat.card_pos.ne' hout
  have hDp : IsPGroup p D := fun d => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hD.2 d d.2)⟩
  obtain ⟨E, hE, hEc⟩ := exists_elemAbelian_of_le_inner hcen (le_inner_of_isPGroup hcop hDp) hD
  exact ⟨E, hE, hEc.trans hcard⟩

theorem noElemAbelianCubeAut_of_not_dvd (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hout : Nat.card (Outer S) ≤ 2) (h3 : ¬ p ^ 3 ∣ Nat.card S) :
    NoElemAbelianCubeAut p S := by
  intro D hD hcard
  obtain ⟨E, -, hEc⟩ := exists_cube_of_aut hp hp2 hcen hout hD hcard
  exact h3 (hEc ▸ Subgroup.card_subgroup_dvd_card E)

theorem noElemAbelianCubeAut_of_noncomm (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center S = ⊥) (hout : Nat.card (Outer S) ≤ 2) (h4 : ¬ p ^ 4 ∣ Nat.card S)
    (hnc : ∃ x y : S, x ^ p = 1 ∧ y ^ p = 1 ∧ x * y ≠ y * x ∧
      IsPGroup p (Subgroup.closure ({x, y} : Set S))) :
    NoElemAbelianCubeAut p S := by
  have : Fact p.Prime := ⟨hp⟩
  intro D hD hcard
  obtain ⟨E, hE, hEc⟩ := exists_cube_of_aut hp hp2 hcen hout hD hcard
  obtain ⟨x, y, -, -, hxy, hP⟩ := hnc
  have hEp : IsPGroup p E := IsPGroup.of_card hEc
  have hdvd : p ^ 3 ∣ Nat.card S := hEc ▸ Subgroup.card_subgroup_dvd_card E
  have hfac : (Nat.card S).factorization p = 3 := by
    have hpos : Nat.card S ≠ 0 := Nat.card_pos.ne'
    have h3 : 3 ≤ (Nat.card S).factorization p :=
      (hp.pow_dvd_iff_le_factorization hpos).mp hdvd
    have h4' : ¬ 4 ≤ (Nat.card S).factorization p :=
      fun h => h4 ((hp.pow_dvd_iff_le_factorization hpos).mpr h)
    omega
  let PE : Sylow p S := Sylow.ofCard E (by rw [hEc, hfac])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S PE Q
  have hmem : ∀ a ∈ (Q : Subgroup S), ∃ s ∈ E, a = g * s * g⁻¹ := by
    intro a ha
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨s, hs, rfl⟩ := ha
    exact ⟨s, hs, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  have hcomm : ∀ a ∈ (Q : Subgroup S), ∀ b ∈ (Q : Subgroup S), a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, hs, rfl⟩ := hmem a ha
    obtain ⟨t, ht, rfl⟩ := hmem b hb
    have hst : s * t = t * s := congrArg Subtype.val (hE.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
    calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
      _ = g * (t * s) * g⁻¹ := by rw [hst]
      _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group
  exact hxy (hcomm x (hQ (Subgroup.subset_closure (by simp)))
    y (hQ (Subgroup.subset_closure (by simp))))

@[expose] def SporadicLocalOneData : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ name : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ^ 3 ∣ Nat.card S →
        (p ^ 4 ∣ Nat.card S ∨ ¬ ∃ x y : S, x ^ p = 1 ∧ y ^ p = 1 ∧ x * y ≠ y * x ∧
          IsPGroup p (Subgroup.closure ({x, y} : Set S))) →
        IsLocallyOneBalancedAbs p S

@[expose] def SporadicOuterLeTwo : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ name : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      Nat.card (Outer S) ≤ 2

theorem center_eq_bot_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center G := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem localThreeBalanceSporadic_of_one (hout : SporadicOuterLeTwo) (h1 : SporadicLocalOneData) :
    LocalThreeBalanceSporadic := by
  intro S _ _ _ hnab name he p hp hp2
  have hcen := center_eq_bot_of_isSimpleGroup hnab
  have hO := hout S ‹_› hnab name he
  by_cases h3 : p ^ 3 ∣ Nat.card S
  · by_cases halt : ¬ p ^ 4 ∣ Nat.card S ∧ ∃ x y : S, x ^ p = 1 ∧ y ^ p = 1 ∧ x * y ≠ y * x ∧
        IsPGroup p (Subgroup.closure ({x, y} : Set S))
    · exact isLocallyBalancedAbs_three_of_noElemAbelianCubeAut
        (noElemAbelianCubeAut_of_noncomm hp hp2 hcen hO halt.1 halt.2)
    · have h' : p ^ 4 ∣ Nat.card S ∨ ¬ ∃ x y : S, x ^ p = 1 ∧ y ^ p = 1 ∧ x * y ≠ y * x ∧
          IsPGroup p (Subgroup.closure ({x, y} : Set S)) := by
        by_cases h4 : p ^ 4 ∣ Nat.card S
        · exact Or.inl h4
        · exact Or.inr fun hex => halt ⟨h4, hex⟩
      exact (h1 S ‹_› hnab name he p hp hp2 h3 h').isLocallyBalancedAbs hp (by norm_num)
  · exact isLocallyBalancedAbs_three_of_noElemAbelianCubeAut
      (noElemAbelianCubeAut_of_not_dvd hp hp2 hcen hO h3)

end CFSG.HardMathSupport.Timmesfeld.Coordinator
