module

public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsAlt
public import CFSG.CGT.PushingUpLit.BHS6.FaithfulAlt

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {n : ℕ}

theorem eq_altOn_movFin_of_card (hn : Odd n) {F : Subgroup (Equiv.Perm (Fin n))}
    (hF : opResidual 2 F = F)
    (hirr : IsIrrSection (F.map (coreAct n))
      (commV (F.map (coreAct n)) ⊔ fixV (F.map (coreAct n))) (fixV (F.map (coreAct n))))
    {k : ℕ} (hk : Odd k) (hcV : Nat.card (commV (F.map (coreAct n))) = Nat.card (coreMod k))
    (hcF : Nat.card F = k.factorial / 2) : F = altOn (movFin F) ∧ (movFin F).card = k := by
  obtain ⟨x₀, hx₀⟩ := exists_moved_of_irr hirr
  have hsame : ∀ a, (∃ f ∈ F, f a ≠ a) → ∃ f ∈ F, f x₀ = a :=
    fun a ha => same_orbit_of_moved hn hF hirr ha hx₀
  set S := movFin F with hS
  have hm3 : 3 ≤ S.card := three_le_card_movFin hF hx₀
  have h1 := card_commV_mul hn hx₀ hsame
  have h2 := card_coreMod_mul_two hk
  have h3 := card_movFin_add F
  rw [hcV, mul_right_comm, h2, ← pow_add] at h1
  have hkN := Nat.pow_right_injective (le_refl 2) h1
  have hSk : S.card = k := by rw [hS]; omega
  have hFS : F = altOn S := Subgroup.eq_of_le_of_card_ge (le_altOn_movFin hF) (by
    rw [card_altOn (by omega), hcF, hSk])
  exact ⟨hFS, hSk⟩

theorem exists_isMaxSwapGroup_ge (hn : Odd n) {T' : Set (Equiv.Perm (Fin n))}
    (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) :
    ∃ T'' : Set (Equiv.Perm (Fin n)), T' ⊆ T'' ∧ (∀ t ∈ T'', t.IsSwap) ∧
      (∀ t ∈ T'', ∀ t' ∈ T'', t * t' = t' * t) ∧ T''.ncard = (n - 1) / 2 := by
  classical
  obtain ⟨j, hj⟩ := hn
  suffices h : ∀ d : ℕ, ∀ T' : Set (Equiv.Perm (Fin n)), (∀ t ∈ T', t.IsSwap) →
      (∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) → (n - 1) / 2 - T'.ncard = d →
      ∃ T'' : Set (Equiv.Perm (Fin n)), T' ⊆ T'' ∧ (∀ t ∈ T'', t.IsSwap) ∧
        (∀ t ∈ T'', ∀ t' ∈ T'', t * t' = t' * t) ∧ T''.ncard = (n - 1) / 2 from
    h _ T' hs hc rfl
  intro d
  induction d with
  | zero =>
    intro T' hs hc hd
    have hle : 2 * T'.ncard ≤ n := two_mul_ncard_le hs hc
    exact ⟨T', subset_rfl, hs, hc, by omega⟩
  | succ d ih =>
    intro T' hs hc hd
    have hle : 2 * T'.ncard ≤ n := two_mul_ncard_le hs hc
    obtain ⟨σ, hσ, hσt⟩ := exists_prod_swaps hs hc
    have hsupp : σ.support.card = 2 * T'.ncard := by
      rw [← Equiv.Perm.sum_cycleType, hσt, Multiset.sum_replicate, smul_eq_mul]
      ring
    have hfix : 2 ≤ (σ.supportᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin, hsupp]
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (σ.supportᶜ).card)
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at ha hb
    have hfixT : ∀ t ∈ T', t a = a ∧ t b = b := by
      intro t ht
      have ht' : t ∈ σ.cycleFactorsFinset := by
        have : t ∈ (σ.cycleFactorsFinset : Set (Equiv.Perm (Fin n))) := hσ ▸ ht
        exact this
      have hcyc := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp ht').2
      refine ⟨?_, ?_⟩
      · by_contra hne
        have := hcyc a (Equiv.Perm.mem_support.mpr hne)
        exact hne (this.trans ha)
      · by_contra hne
        have := hcyc b (Equiv.Perm.mem_support.mpr hne)
        exact hne (this.trans hb)
    set t₁ : Equiv.Perm (Fin n) := Equiv.swap a b with ht₁
    have ht₁s : t₁.IsSwap := ⟨a, b, hab, rfl⟩
    have ht₁c : ∀ t ∈ T', t * t₁ = t₁ * t := by
      intro t ht
      obtain ⟨h1, h2⟩ := hfixT t ht
      rw [ht₁, Equiv.mul_swap_eq_swap_mul, h1, h2]
    have ht₁n : t₁ ∉ T' := by
      intro h
      have := (hfixT t₁ h).1
      rw [ht₁, Equiv.swap_apply_left] at this
      exact hab this.symm
    have hs₁ : ∀ t ∈ insert t₁ T', t.IsSwap := by
      intro t ht
      rcases Set.mem_insert_iff.mp ht with rfl | ht
      · exact ht₁s
      · exact hs t ht
    have hc₁ : ∀ t ∈ insert t₁ T', ∀ t' ∈ insert t₁ T', t * t' = t' * t := by
      intro t ht t' ht'
      rcases Set.mem_insert_iff.mp ht with rfl | ht <;>
        rcases Set.mem_insert_iff.mp ht' with rfl | ht'
      · rfl
      · exact (ht₁c t' ht').symm
      · exact ht₁c t ht
      · exact hc t ht t' ht'
    have hncard : (insert t₁ T').ncard = T'.ncard + 1 :=
      Set.ncard_insert_of_notMem ht₁n (Set.toFinite T')
    obtain ⟨T'', hT'', h1, h2, h3⟩ := ih (insert t₁ T') hs₁ hc₁ (by omega)
    exact ⟨T'', (Set.subset_insert t₁ T').trans hT'', h1, h2, h3⟩

theorem exists_even_conj_le_setStab (hn : Odd n) {T' : Set (Equiv.Perm (Fin n))}
    (hne : T'.Nonempty) (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    (S : Finset (Fin n)) :
    ∃ π ∈ alternatingGroup (Fin n), ∀ y ∈ Subgroup.closure T', π * y * π⁻¹ ∈ setStab S := by
  obtain ⟨T'', hT'', hs'', hc'', hcard⟩ := exists_isMaxSwapGroup_ge hn hs hc
  have hY : IsMaxSwapGroup (Subgroup.closure T'') := ⟨T'', hs'', hc'', hcard, rfl⟩
  obtain ⟨g, hg⟩ := exists_conjSub_le_setStab hn hY S
  obtain ⟨t₀, ht₀⟩ := hne
  have hs0 : Equiv.Perm.sign t₀ = -1 := (hs t₀ ht₀).sign_eq
  have ht₀Y : t₀ ∈ Subgroup.closure T'' := Subgroup.subset_closure (hT'' ht₀)
  have h1 : ∀ y ∈ Subgroup.closure T'', g * y * g⁻¹ ∈ setStab S := fun y hy => hg (by
    rw [A1b.mem_conjSub_iff]
    simpa [mul_assoc] using hy)
  have h2 : ∀ y ∈ Subgroup.closure T'', (g * t₀) * y * (g * t₀)⁻¹ ∈ setStab S := by
    intro y hy
    have : (g * t₀) * y * (g * t₀)⁻¹ = g * (t₀ * y * t₀⁻¹) * g⁻¹ := by group
    rw [this]
    exact h1 _ ((Subgroup.closure T'').mul_mem ((Subgroup.closure T'').mul_mem ht₀Y hy)
      ((Subgroup.closure T'').inv_mem ht₀Y))
  have hcl : ∀ y ∈ Subgroup.closure T', y ∈ Subgroup.closure T'' := fun y hy =>
    Subgroup.closure_mono hT'' hy
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hsg | hsg
  · exact ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hsg, fun y hy => h1 y (hcl y hy)⟩
  · refine ⟨g * t₀, Equiv.Perm.mem_alternatingGroup.mpr ?_, fun y hy => h2 y (hcl y hy)⟩
    rw [Equiv.Perm.sign_mul, hsg, hs0]
    decide

theorem mem_normalizer_altOn_of_mem_setStab {S : Finset (Fin n)} {y : Equiv.Perm (Fin n)}
    (hy : y ∈ setStab S) : y ∈ Subgroup.normalizer (altOn S : Set (Equiv.Perm (Fin n))) :=
  setStab_le_normalizer_altOn S hy

end CFSG.CGT.PushingUpLit.BHS6
