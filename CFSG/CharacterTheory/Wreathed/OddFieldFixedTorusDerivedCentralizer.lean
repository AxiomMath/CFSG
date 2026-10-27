module

public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizerSupport

public section

namespace CFSG.Wreathed.OddFieldTorus

theorem odd_field_fixed_torus_derived_centralizer {F : Type*} [Field F] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (ε : ℤ) (hε : ε = if p ^ f % 4 = 1 then 1 else -1)
    (m : ℕ) (hm : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - ε))
    (Γ : Subgroup (F ≃+* F)) (hΓ : Odd (Nat.card Γ)) :
    (J₀ F : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] ∧ 4 ≤ m ∧
    (∀ g : Matrix.SpecialLinearGroup (Fin 2) F, g ∈ Subgroup.centralizer {J₀ F} ↔
      ∃ v w : F, v ^ 2 + w ^ 2 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) F) = !![v, -w; w, v]) ∧
    (∃ W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      ∀ g, g ∈ W ↔ g ∈ Subgroup.centralizer {J₀ F} ∧ Odd (orderOf g)) ∧
    ∀ W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      (∀ g, g ∈ W ↔ g ∈ Subgroup.centralizer {J₀ F} ∧ Odd (orderOf g)) →
      IsCyclic W ∧ (Nat.card W : ℤ) = ((p ^ f : ℕ) - ε) / m ∧
      (∀ σ ∈ Γ,
        p ^ f = Nat.card {a : F // σ a = a} ^ orderOf σ ∧
        Nat.card {a : F // σ a = a} % 4 = p ^ f % 4 ∧
        2 ^ padicValInt 2 ((Nat.card {a : F // σ a = a} : ℤ) - ε) = m ∧
        (Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} : ℤ) =
          ((Nat.card {a : F // σ a = a} : ℤ) - ε) / m ∧
        (σ ≠ 1 → Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} ^ 2 <
          Nat.card W)) ∧
      (∃ φ : Γ →* MulAut W, ∀ σ w, ((φ σ w : W) : Matrix.SpecialLinearGroup (Fin 2) F) =
        Matrix.SpecialLinearGroup.map (σ : F ≃+* F).toRingHom w) ∧
      ∀ φ : Γ →* MulAut W, (∀ σ w, ((φ σ w : W) : Matrix.SpecialLinearGroup (Fin 2) F) =
          Matrix.SpecialLinearGroup.map (σ : F ≃+* F).toRingHom w) →
        ∀ σ₀ : Γ, Subgroup.zpowers σ₀ = ⊤ →
          commutator (W ⋊[φ] Γ) = ⁅(SemidirectProduct.inl : W →* W ⋊[φ] Γ).range,
              Subgroup.zpowers (SemidirectProduct.inr σ₀ : W ⋊[φ] Γ)⁆ ∧
            commutator (W ⋊[φ] Γ) =
              (Subgroup.closure (Set.range fun w : W => w⁻¹ * φ σ₀ w)).map
                (SemidirectProduct.inl : W →* W ⋊[φ] Γ) ∧
            Nat.card (commutator (W ⋊[φ] Γ)) = Nat.card W /
              Nat.card {g // g ∈ W ∧ ∀ σ ∈ Γ, Matrix.SpecialLinearGroup.map σ.toRingHom g = g} ∧
            Subgroup.centralizer (commutator (W ⋊[φ] Γ) : Set (W ⋊[φ] Γ)) =
              (SemidirectProduct.inl : W →* W ⋊[φ] Γ).range := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact (pow_pos hp.pos f).ne')
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hpodd with ⟨k, hk⟩
    omega
  have hchar : CharP F p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hF
  have h2F : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq1 : 1 < p ^ f := Nat.one_lt_pow (by omega) (by omega)
  have hm4 : 4 ≤ m := by
    rw [hm, hε]
    exact four_le_two_part hqodd hq1
  refine ⟨rfl, hm4, mem_torus_iff, exists_oddTorus F, fun W hW => ?_⟩
  have hcardW : (Nat.card W : ℤ) = ((p ^ f : ℕ) - ε) / m := by
    rw [card_W W hW, card_oddTorus h2F, hF, hm, hε]
    push_cast
    rfl
  have hcyc : IsCyclic W := by
    have := torus_isCyclic h2F
    exact (Subgroup.subgroupOfEquivOfLe (W_le_torus W hW)).isCyclic.mp inferInstance
  have hfixed : ∀ σ ∈ Γ,
      p ^ f = Nat.card {a : F // σ a = a} ^ orderOf σ ∧
      Nat.card {a : F // σ a = a} % 4 = p ^ f % 4 ∧
      2 ^ padicValInt 2 ((Nat.card {a : F // σ a = a} : ℤ) - ε) = m ∧
      (Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} : ℤ) =
        ((Nat.card {a : F // σ a = a} : ℤ) - ε) / m ∧
      (σ ≠ 1 → Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} ^ 2 <
        Nat.card W) := by
    intro σ hσ
    have he : Odd (orderOf σ) := Odd.of_dvd_nat hΓ (Subgroup.orderOf_dvd_natCard Γ hσ)
    obtain ⟨hdvd, hcardS⟩ := card_fixedField hp hf hF σ
    rw [card_fixedField_eq] at hcardS
    set r := Nat.card {a : F // σ a = a} with hr
    have hepos : 0 < orderOf σ := he.pos
    have hfe : 1 ≤ f / orderOf σ := (Nat.one_le_div_iff hepos).mpr (Nat.le_of_dvd (by omega) hdvd)
    have hq : p ^ f = r ^ orderOf σ := by
      rw [hcardS, ← pow_mul, Nat.div_mul_cancel hdvd]
    have hrodd : Odd r := by rw [hcardS]; exact hpodd.pow
    have hr3 : 3 ≤ r := by
      rw [hcardS]
      calc 3 ≤ p := hp3
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (f / orderOf σ) := Nat.pow_le_pow_right hp.pos hfe
    have hr4 : r % 4 = p ^ f % 4 := by rw [hq, pow_mod_four hrodd he]
    have hεr : (if r % 4 = 1 then (1 : ℤ) else -1) = ε := by rw [hr4, hε]
    have hεcases : ε = 1 ∨ ε = -1 := by rw [hε]; exact eps_cases _
    have hne : (r : ℤ) - ε ≠ 0 := by rcases hεcases with h | h <;> rw [h] <;> omega
    have hval : padicValInt 2 ((r : ℤ) - ε) = padicValInt 2 ((p ^ f : ℕ) - ε) := by
      rw [hq, Nat.cast_pow]
      exact (padicValInt_pow_sub_eps ε hεcases (by exact_mod_cast hrodd) he hne).symm
    have hmr : 2 ^ padicValInt 2 ((r : ℤ) - ε) = m := by rw [hval, hm]
    have h2S : (2 : fixedField σ) ≠ 0 := by
      intro h
      apply h2F
      have := congrArg (fixedField σ).subtype h
      rwa [map_ofNat, map_zero] at this
    have hcardC : (Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} : ℤ) =
        ((r : ℤ) - ε) / m := by
      have hmrZ : (2 : ℤ) ^ padicValInt 2 ((r : ℤ) - ε) = m := by exact_mod_cast hmr
      rw [card_fixed_oddTorus W hW σ, card_oddTorus h2S, card_fixedField_eq, ← hr, hεr, hmrZ]
    refine ⟨hq, hr4, hmr, hcardC, fun hσ1 => ?_⟩
    have he3 : 3 ≤ orderOf σ := by
      have h1 : orderOf σ ≠ 1 := fun h => hσ1 (orderOf_eq_one_iff.mp h)
      rcases he with ⟨k, hk⟩
      omega
    have hmpos : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
    have hdivr : (m : ℤ) ∣ (r : ℤ) - ε := by
      rw [← hmr]
      push_cast
      exact padicValInt_dvd _
    have hdivq : (m : ℤ) ∣ ((p ^ f : ℕ) : ℤ) - ε := by
      rw [hm]
      push_cast
      exact padicValInt_dvd _
    obtain ⟨c, hc⟩ := hdivr
    obtain ⟨w, hw⟩ := hdivq
    have hcC : (Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} : ℤ) =
        c := by rw [hcardC, hc, Int.mul_ediv_cancel_left _ hmpos.ne']
    have hwW : (Nat.card W : ℤ) = w := by rw [hcardW, hw, Int.mul_ediv_cancel_left _ hmpos.ne']
    have hlt := sq_lt_of_three_le (r := (r : ℤ)) (e := orderOf σ) (m := (m : ℤ)) ε hεcases
      (by exact_mod_cast hr3) he3 (by exact_mod_cast hm4)
    have hqr : ((p ^ f : ℕ) : ℤ) = (r : ℤ) ^ orderOf σ := by rw [hq]; push_cast; ring
    rw [← hqr, hw, hc] at hlt
    have hm2 : (0 : ℤ) < (m : ℤ) ^ 2 := by positivity
    have hlt' : c ^ 2 < w := by
      have h' : (m : ℤ) ^ 2 * c ^ 2 < (m : ℤ) ^ 2 * w := by
        calc (m : ℤ) ^ 2 * c ^ 2 = ((m : ℤ) * c) ^ 2 := by ring
          _ < (m : ℤ) * ((m : ℤ) * w) := hlt
          _ = (m : ℤ) ^ 2 * w := by ring
      exact lt_of_mul_lt_mul_left h' hm2.le
    have : ((Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map σ.toRingHom g = g} ^ 2 : ℕ) :
        ℤ) < (Nat.card W : ℤ) := by
      push_cast
      rw [hcC, hwW]
      exact hlt'
    exact_mod_cast this
  refine ⟨hcyc, hcardW, hfixed, ⟨(oddTorusAction W hW).comp Γ.subtype, fun σ w => rfl⟩,
    fun φ hφ σ₀ hg₀ => ?_⟩
  have hfixφ : ∀ (s : Γ) (n : W), φ s n = n ↔
      Matrix.SpecialLinearGroup.map (s : F ≃+* F).toRingHom
        (n : Matrix.SpecialLinearGroup (Fin 2) F) = n := by
    intro s n
    rw [← hφ s n, Subtype.ext_iff]
  have hsmall : ∀ s : Γ, s ≠ 1 → Nat.card {n : W // φ s n = n} ^ 2 < Nat.card W := by
    intro s hs
    have hs1 : (s : F ≃+* F) ≠ 1 := fun h => hs (Subtype.ext h)
    have h := (hfixed s s.2).2.2.2.2 hs1
    have hequiv : Nat.card {n : W // φ s n = n} =
        Nat.card {g // g ∈ W ∧ Matrix.SpecialLinearGroup.map (s : F ≃+* F).toRingHom g = g} :=
      Nat.card_congr ⟨fun n => ⟨n.1, n.1.2, (hfixφ s n.1).mp n.2⟩,
        fun g => ⟨⟨g.1, g.2.1⟩, (hfixφ s ⟨g.1, g.2.1⟩).mpr g.2.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [hequiv]
    exact h
  have : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    (fun a b h => RingEquiv.ext (congrFun h))
  obtain ⟨h1, h2, h3, h4⟩ := semidirect_cyclic_derived φ (W_comm W hW) σ₀ hg₀ hsmall
  have hfixall : Nat.card {n : W // ∀ s, φ s n = n} =
      Nat.card {g // g ∈ W ∧ ∀ σ ∈ Γ, Matrix.SpecialLinearGroup.map σ.toRingHom g = g} :=
    Nat.card_congr ⟨fun n => ⟨n.1, n.1.2, fun σ hσ => (hfixφ ⟨σ, hσ⟩ n.1).mp (n.2 ⟨σ, hσ⟩)⟩,
      fun g => ⟨⟨g.1, g.2.1⟩, fun s => (hfixφ s ⟨g.1, g.2.1⟩).mpr (g.2.2 s s.2)⟩,
      fun _ => rfl, fun _ => rfl⟩
  refine ⟨h1, h2, ?_, h4⟩
  have : Nonempty {g // g ∈ W ∧ ∀ σ ∈ Γ, Matrix.SpecialLinearGroup.map σ.toRingHom g = g} :=
    ⟨⟨1, W.one_mem, fun σ _ => map_one _⟩⟩
  rw [← h3, hfixall, Nat.mul_div_cancel _ Nat.card_pos]

end CFSG.Wreathed.OddFieldTorus
