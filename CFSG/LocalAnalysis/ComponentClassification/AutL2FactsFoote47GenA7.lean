module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteRankThree
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteGen

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG Subgroup Equiv

@[expose] def e1Set : Finset (Perm (Fin 7)) :=
  {1, swap 0 2, swap 1 3, swap 4 5, swap 0 2 * swap 1 3, swap 0 2 * swap 4 5, swap 1 3 * swap 4 5,
    swap 0 2 * swap 1 3 * swap 4 5}

theorem e1Set_mul : ∀ x ∈ e1Set, ∀ y ∈ e1Set, x * y ∈ e1Set := by
  simp only [e1Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) y
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem e1Set_sq : ∀ x ∈ e1Set, x * x = 1 := by
  simp only [e1Set, Finset.mem_insert, Finset.mem_singleton]
  rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

theorem one_mem_e1Set : (1 : Perm (Fin 7)) ∈ e1Set := by decide +kernel

@[expose] def e1 : Subgroup (Perm (Fin 7)) where
  carrier := ↑e1Set
  mul_mem' ha hb := e1Set_mul _ ha _ hb
  one_mem' := one_mem_e1Set
  inv_mem' {x} hx := by
    change x⁻¹ ∈ e1Set
    rw [inv_eq_of_mul_eq_one_right (e1Set_sq x hx)]
    exact hx

theorem card_e1 : Nat.card e1 = 8 := by
  change Nat.card (↑e1Set : Set (Perm (Fin 7))) = 8
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rfl

theorem alternatingGroup_le_of_three_cycles (G' : Subgroup (Perm (Fin 7)))
    (h₁ : swap 4 5 * swap 4 6 ∈ G') (h₂ : swap 1 3 * swap 1 6 ∈ G')
    (h₃ : swap 0 2 * swap 0 6 ∈ G') : alternatingGroup (Fin 7) ≤ G' := by
  have hsm : ∀ (w : Perm (Fin 7)), w ∈ G' → ∀ y : Fin 7, w 0 = y →
      ∃ g : G', g • (0 : Fin 7) = y := fun w hw y h => ⟨⟨w, hw⟩, h⟩
  have htr : MulAction.IsPretransitive G' (Fin 7) := by
    rw [MulAction.isPretransitive_iff_base (0 : Fin 7)]
    intro y
    fin_cases y
    · exact hsm 1 (one_mem _) _ (by decide)
    · exact hsm _ (mul_mem h₂ (mul_mem h₂ h₃)) _ (by decide)
    · exact hsm _ (mul_mem h₃ h₃) _ (by decide)
    · exact hsm _ (mul_mem h₂ h₃) _ (by decide)
    · exact hsm _ (mul_mem h₁ (mul_mem h₁ h₃)) _ (by decide)
    · exact hsm _ (mul_mem h₁ h₃) _ (by decide)
    · exact hsm _ h₃ _ (by decide)
  have hprim : MulAction.IsPreprimitive G' (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num)
  exact Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)) h₁

theorem foote47FourgroupGeneration_a7 {S : Type} [Group S] [Finite S]
    (e : S ≃* alternatingGroup (Fin 7)) (T : Subgroup (MulAut S)) (hT2 : IsPGroup 2 T)
    (hF : ∃ F : Subgroup (MulAut S), F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8)
    (hnab : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) :
    ⨆ (W : Subgroup (MulAut S)) (_ : IsKleinFour W)
      (_ : ∃ F : Subgroup (MulAut S), W ≤ F ∧ F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8),
        ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ψ : MulAut S ≃* Perm (Fin 7) := (MulAut.congr e).trans a7AutEquiv.symm with hΨ
  have hΨapp : ∀ (π : Perm (Fin 7)) (s : S),
      ((e (Ψ.symm π s) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = π * (e s) * π⁻¹ := by
    intro π s
    change ((e (e.symm (a7Conj π (e s))) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = _
    rw [MulEquiv.apply_symm_apply, a7Conj_apply]
  have hcard : Nat.card (Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  obtain ⟨F₀, hF₀T, hF₀2, hF₀8⟩ := hF
  set T' := T.map Ψ.toMonoidHom with hT'
  have hT'2 : IsPGroup 2 T' := hT2.map _
  have hT'card : Nat.card T' = 16 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT'2
    have hdvd : 2 ^ k ∣ 5040 := by
      rw [← hk, ← hcard]
      exact T'.card_subgroup_dvd_card
    have hk4 : k ≤ 4 := by
      by_contra h
      have : 2 ^ 5 ∣ 5040 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    have hlt : 8 < Nat.card T' := by
      have hF'8 : Nat.card (F₀.map Ψ.toMonoidHom) = 8 := by
        rw [card_map_of_injective Ψ.injective, hF₀8]
      rw [← hF'8]
      apply Subgroup.card_lt_of_lt
      refine lt_of_le_of_ne (map_mono hF₀T) ?_
      intro heq
      obtain ⟨x, hx, y, hy, hxy⟩ := hnab
      have hx' : Ψ x ∈ F₀.map Ψ.toMonoidHom := heq ▸ mem_map_of_mem _ hx
      have hy' : Ψ y ∈ F₀.map Ψ.toMonoidHom := heq ▸ mem_map_of_mem _ hy
      obtain ⟨x₀, hx₀, hx₀e⟩ := hx'
      obtain ⟨y₀, hy₀, hy₀e⟩ := hy'
      have hxe : x = x₀ := Ψ.injective hx₀e.symm
      have hye : y = y₀ := Ψ.injective hy₀e.symm
      rw [hxe, hye] at hxy
      exact hxy (commute_of_forall_sq F₀ hF₀2 hx₀ hy₀)
    rw [hk] at hlt ⊢
    have h4k : 4 ≤ k := by
      by_contra h
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [show k = 4 by omega]
    norm_num
  have hidx : ¬ 2 ∣ T'.index := by
    have h1 := T'.card_mul_index
    rw [hT'card, hcard] at h1
    omega
  have he12 : IsPGroup 2 e1 := IsPGroup.of_card (n := 3) (by rw [card_e1]; norm_num)
  obtain ⟨Q, hQ⟩ := he12.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 7)) Q (hT'2.toSylow hidx)
  have hgT : ∀ y ∈ e1, g * y * g⁻¹ ∈ T' := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ ((g • Q : Sylow 2 (Perm (Fin 7))) : Subgroup (Perm (Fin 7))) := by
      rw [mem_smul_sylow_iff_conj, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      exact hQ hy
    rw [hg] at h1
    exact h1
  set F := (e1.map (MulAut.conj g).toMonoidHom).map Ψ.symm.toMonoidHom with hFdef
  have hFT : F ≤ T := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨t, ht, hte⟩ := hgT y hy
    change Ψ.symm (g * y * g⁻¹) ∈ T
    rw [← show Ψ t = g * y * g⁻¹ from hte, MulEquiv.symm_apply_apply]
    exact ht
  have hF2 : ∀ x ∈ F, x * x = 1 := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, e1Set_sq y hy, map_one, map_one]
  have hF8 : Nat.card F = 8 := by
    rw [hFdef, card_map_of_injective Ψ.symm.injective,
      card_map_of_injective (MulAut.conj g).injective, card_e1]
  set HS := ⨆ (W : Subgroup (MulAut S)) (_ : IsKleinFour W)
      (_ : ∃ F : Subgroup (MulAut S), W ≤ F ∧ F ≤ T ∧ (∀ x ∈ F, x * x = 1) ∧ Nat.card F = 8),
        ⨅ w ∈ W, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) with hHS
  have key : ∀ (c y₁ y₂ : Perm (Fin 7)) (hc : c ∈ alternatingGroup (Fin 7)), y₁ ∈ e1Set →
      y₂ ∈ e1Set → y₁ ≠ 1 → y₂ ≠ 1 → y₁ ≠ y₂ → y₁ * c = c * y₁ → y₂ * c = c * y₂ →
      e.symm ⟨g * c * g⁻¹, by
        rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_inv, (Perm.mem_alternatingGroup).mp hc,
          mul_one, mul_inv_cancel]⟩ ∈ HS := by
    intro c y₁ y₂ hc hy₁ hy₂ hy₁1 hy₂1 hne h₁ h₂
    set s := e.symm ⟨g * c * g⁻¹, by
        rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_inv, (Perm.mem_alternatingGroup).mp hc,
          mul_one, mul_inv_cancel]⟩ with hs
    have hmemF : ∀ y ∈ e1Set, Ψ.symm (g * y * g⁻¹) ∈ F := fun y hy =>
      ⟨g * y * g⁻¹, ⟨y, hy, rfl⟩, rfl⟩
    have hfix : ∀ y ∈ e1Set, y * c = c * y → Ψ.symm (g * y * g⁻¹) s = s := by
      intro y hy hyc
      apply e.injective
      apply Subtype.ext
      rw [hΨapp, hs, MulEquiv.apply_symm_apply]
      change g * y * g⁻¹ * (g * c * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * c * g⁻¹
      have hy2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (e1Set_sq y hy)
      calc g * y * g⁻¹ * (g * c * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * c) * y⁻¹ * g⁻¹ := by group
        _ = g * (c * y) * y⁻¹ * g⁻¹ := by rw [hyc]
        _ = g * c * g⁻¹ := by group
    have hord : ∀ y ∈ e1Set, y ≠ 1 → orderOf (Ψ.symm (g * y * g⁻¹)) = 2 := by
      intro y hy hy1
      apply orderOf_eq_prime
      · rw [pow_two, ← map_mul, show g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ by group,
          e1Set_sq y hy, mul_one, mul_inv_cancel, map_one]
      · intro h
        apply hy1
        have h' : g * y * g⁻¹ = 1 := Ψ.symm.injective (h.trans (map_one _).symm)
        calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = 1 := by rw [h']; group
    have hcomm : Ψ.symm (g * y₁ * g⁻¹) * Ψ.symm (g * y₂ * g⁻¹) =
        Ψ.symm (g * y₂ * g⁻¹) * Ψ.symm (g * y₁ * g⁻¹) :=
      commute_of_forall_sq F hF2 (hmemF y₁ hy₁) (hmemF y₂ hy₂)
    have hne' : Ψ.symm (g * y₁ * g⁻¹) ≠ Ψ.symm (g * y₂ * g⁻¹) := by
      intro h
      apply hne
      have h' := Ψ.symm.injective h
      calc y₁ = g⁻¹ * (g * y₁ * g⁻¹) * g := by group
        _ = g⁻¹ * (g * y₂ * g⁻¹) * g := by rw [h']
        _ = y₂ := by group
    obtain ⟨V, hVle, hVea, hV4⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
        (hord y₁ hy₁ hy₁1) (hord y₂ hy₂ hy₂1) hcomm hne'
    have hVF : V ≤ F := hVle.trans ((closure_le F).mpr (by
      rintro _ (rfl | rfl)
      · exact hmemF y₁ hy₁
      · exact hmemF y₂ hy₂))
    have hVfix : V ≤ MulAction.stabilizer (MulAut S) s := hVle.trans ((closure_le _).mpr (by
      rintro _ (rfl | rfl)
      · exact hfix y₁ hy₁ h₁
      · exact hfix y₂ hy₂ h₂))
    have hK : IsKleinFour V := isKleinFour_of_card_four_sq hV4 fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      exact hF2 _ (hVF x.2))
    have hsV : s ∈ ⨅ w ∈ V, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S) := by
      rw [mem_iInf]
      intro w
      rw [mem_iInf]
      intro hw
      exact hVfix hw
    exact (show (⨅ w ∈ V, MonoidHom.eqLocus (w : MulAut S).toMonoidHom (MonoidHom.id S)) ≤ HS
      from le_iSup₂_of_le V hK (le_iSup_of_le ⟨F, hVF, hFT, hF2, hF8⟩ le_rfl)) hsV
  set G' := ((HS.map e.toMonoidHom).map (alternatingGroup (Fin 7)).subtype).map
    (MulAut.conj g⁻¹).toMonoidHom with hG'
  have hmemG : ∀ (c : Perm (Fin 7)) (hc : c ∈ alternatingGroup (Fin 7)),
      e.symm ⟨g * c * g⁻¹, by
        rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_inv, (Perm.mem_alternatingGroup).mp hc,
          mul_one, mul_inv_cancel]⟩ ∈ HS → c ∈ G' := by
    intro c hc h
    refine ⟨g * c * g⁻¹, ⟨_, ⟨_, h, rfl⟩, ?_⟩, ?_⟩
    · change ((e (e.symm _) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = _
      rw [MulEquiv.apply_symm_apply]
    · change g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c
      group
  have hc₁ : swap 4 5 * swap 4 6 ∈ alternatingGroup (Fin 7) :=
    (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).mem_alternatingGroup
  have hc₂ : swap 1 3 * swap 1 6 ∈ alternatingGroup (Fin 7) :=
    (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).mem_alternatingGroup
  have hc₃ : swap 0 2 * swap 0 6 ∈ alternatingGroup (Fin 7) :=
    (Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).mem_alternatingGroup
  have hA := alternatingGroup_le_of_three_cycles G'
    (hmemG _ hc₁ (key _ (swap 0 2) (swap 1 3) hc₁ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))
    (hmemG _ hc₂ (key _ (swap 0 2) (swap 4 5) hc₂ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))
    (hmemG _ hc₃ (key _ (swap 1 3) (swap 4 5) hc₃ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))
  rw [eq_top_iff]
  intro s _
  have hes : g⁻¹ * ((e s : alternatingGroup (Fin 7)) : Perm (Fin 7)) * g ∈ G' := by
    apply hA
    rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_inv, (e s).2, mul_one, inv_mul_cancel]
  obtain ⟨x, ⟨a, ⟨s₀, hs₀, rfl⟩, rfl⟩, hconj⟩ := hes
  change g⁻¹ * ((e s₀ : alternatingGroup (Fin 7)) : Perm (Fin 7)) * g⁻¹⁻¹ =
    g⁻¹ * ((e s : alternatingGroup (Fin 7)) : Perm (Fin 7)) * g at hconj
  rw [inv_inv, mul_left_inj, mul_right_inj] at hconj
  rw [← e.injective (Subtype.ext hconj)]
  exact hs₀

end CFSG.ComponentClassification.AutL2Facts
