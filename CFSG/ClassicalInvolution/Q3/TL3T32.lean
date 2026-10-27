module

public import CFSG.ClassicalInvolution.Q3.TL3T30
public import CFSG.ClassicalInvolution.Q3.TL4D1MAN

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem perm_keep_or_swap : ∀ c : Equiv.Perm (Fin 4),
    ((∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList) ∧
      (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList)) ∨
    ((∀ k ∈ kList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kStarList) ∧
      (∀ k ∈ kStarList, ofPerm c * k * (ofPerm c)⁻¹ ∈ kList)) := by
  decide +kernel

theorem vec_keep_or_swap : ∀ v : Fin 4 → ZMod 2,
    ((∀ k ∈ kList, ofVec v * k * (ofVec v)⁻¹ ∈ kList) ∧
      (∀ k ∈ kStarList, ofVec v * k * (ofVec v)⁻¹ ∈ kStarList)) ∨
    ((∀ k ∈ kList, ofVec v * k * (ofVec v)⁻¹ ∈ kStarList) ∧
      (∀ k ∈ kStarList, ofVec v * k * (ofVec v)⁻¹ ∈ kList)) := by
  decide +kernel

theorem exists_mul_eq_vec4 : ∀ i k : Fin 4, i ≠ k →
    ∃ p ∈ kList, ∃ q ∈ kStarList, p * q = ofVec (vec4 [i, k]) := by
  decide +kernel

variable {n : ℕ}

@[expose] def Keeps (γ : Finset (Fin n)) (h : γ.card = 4) (g : Wr n) : Prop :=
  ∀ b : Bool, ∀ k ∈ memAt γ h b, g * k * g⁻¹ ∈ memAt γ h b

@[expose] def Swaps (γ : Finset (Fin n)) (h : γ.card = 4) (g : Wr n) : Prop :=
  ∀ b : Bool, ∀ k ∈ memAt γ h b, g * k * g⁻¹ ∈ memAt γ h (!b)

section KeepSwap

variable {γ : Finset (Fin n)} {h : γ.card = 4} {g g' : Wr n}

theorem conj_mul_eq' (g g' k : Wr n) : g * g' * k * (g * g')⁻¹ = g * (g' * k * g'⁻¹) * g⁻¹ := by
  group

theorem Keeps.mul (h1 : Keeps γ h g) (h2 : Keeps γ h g') : Keeps γ h (g * g') :=
  fun b k hk => by
    rw [conj_mul_eq']
    exact h1 b _ (h2 b k hk)

theorem Swaps.mul_keeps (h1 : Swaps γ h g) (h2 : Keeps γ h g') : Swaps γ h (g * g') :=
  fun b k hk => by
    rw [conj_mul_eq']
    exact h1 b _ (h2 b k hk)

theorem Keeps.mul_swaps (h1 : Keeps γ h g) (h2 : Swaps γ h g') : Swaps γ h (g * g') :=
  fun b k hk => by
    rw [conj_mul_eq']
    exact h1 (!b) _ (h2 b k hk)

theorem Swaps.mul (h1 : Swaps γ h g) (h2 : Swaps γ h g') : Keeps γ h (g * g') :=
  fun b k hk => by
    rw [conj_mul_eq']
    have := h1 (!b) _ (h2 b k hk)
    rwa [Bool.not_not] at this

theorem keeps_or_swaps_mul (h1 : Keeps γ h g ∨ Swaps γ h g) (h2 : Keeps γ h g' ∨ Swaps γ h g') :
    Keeps γ h (g * g') ∨ Swaps γ h (g * g') := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h1.mul h2)
  · exact Or.inr (h1.mul_swaps h2)
  · exact Or.inr (h1.mul_keeps h2)
  · exact Or.inl (h1.mul h2)

theorem keeps_or_swaps_of_local {c : Wr 4}
    (hg : ∀ k₀ : Wr 4, g * embed (emb γ h) k₀ * g⁻¹ = embed (emb γ h) (c * k₀ * c⁻¹))
    (hc : ((∀ k ∈ kList, c * k * c⁻¹ ∈ kList) ∧ (∀ k ∈ kStarList, c * k * c⁻¹ ∈ kStarList)) ∨
      ((∀ k ∈ kList, c * k * c⁻¹ ∈ kStarList) ∧ (∀ k ∈ kStarList, c * k * c⁻¹ ∈ kList))) :
    Keeps γ h g ∨ Swaps γ h g := by
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    intro b k hk
    cases b
    · obtain ⟨k₀, hk₀, rfl⟩ := (show k ∈ memKStar (emb γ h) from hk)
      rw [hg]
      exact ⟨_, h2 k₀ hk₀, rfl⟩
    · obtain ⟨k₀, hk₀, rfl⟩ := (show k ∈ memK (emb γ h) from hk)
      rw [hg]
      exact ⟨_, h1 k₀ hk₀, rfl⟩
  · right
    intro b k hk
    cases b
    · obtain ⟨k₀, hk₀, rfl⟩ := (show k ∈ memKStar (emb γ h) from hk)
      rw [hg]
      exact ⟨_, h2 k₀ hk₀, rfl⟩
    · obtain ⟨k₀, hk₀, rfl⟩ := (show k ∈ memK (emb γ h) from hk)
      rw [hg]
      exact ⟨_, h1 k₀ hk₀, rfl⟩

theorem keeps_or_swaps (a : Wr n) (ha : ∀ x ∈ γ, a.perm x ∈ γ) : Keeps γ h a ∨ Swaps γ h a := by
  classical
  set ι := emb γ h with hι
  have hr : Set.range ι = (γ : Set (Fin n)) := range_emb γ h
  set v := a.vec with hv
  set v₁ : Fin n → ZMod 2 := fun x => if x ∈ γ then v x else 0 with hv₁
  set v₂ : Fin n → ZMod 2 := fun x => if x ∈ γ then 0 else v x with hv₂
  have hdec : a = ofVec v₁ * ofVec v₂ * ofPerm a.perm := by
    refine Wr.ext (funext fun x => ?_) ?_
    · show v x = v₁ x + v₂ x + 0
      simp only [hv₁, hv₂]
      split_ifs <;> simp
    · show a.perm = 1 * 1 * a.perm
      rw [one_mul, one_mul]
  have h2 : Keeps γ h (ofVec v₂) ∨ Swaps γ h (ofVec v₂) := by
    refine keeps_or_swaps_of_local (c := 1) (fun k₀ => ?_) (Or.inl ⟨fun k hk => by simpa using hk,
      fun k hk => by simpa using hk⟩)
    have hsupp : SupportedOn (ofVec v₂) ((γ : Set (Fin n))ᶜ) := by
      intro x hx
      simp only [Set.mem_compl_iff, not_not] at hx
      refine ⟨?_, rfl⟩
      show (if x ∈ γ then 0 else v x) = 0
      have hx' : x ∈ γ := by exact_mod_cast hx
      simp [hx']
    have hc := comm_of_disjoint hsupp (embed_supportedOn ι k₀) (by rw [hr]; exact disjoint_compl_left)
    rw [hc, mul_assoc, mul_inv_cancel, mul_one, one_mul, inv_one, mul_one]
  have h1 : Keeps γ h (ofVec v₁) ∨ Swaps γ h (ofVec v₁) := by
    set u : Fin 4 → ZMod 2 := fun i => v (ι i) with hu
    have he : embed ι (ofVec u) = ofVec v₁ := by
      refine Wr.ext (funext fun x => ?_) (embedPerm_one ι)
      rw [embed_vec]
      by_cases hx : x ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hx
        rw [embedVec_apply]
        show v (ι i) = if ι i ∈ γ then v (ι i) else 0
        have : ι i ∈ γ := by
          have := Set.mem_range_self (f := ι) i
          rw [hr] at this
          exact_mod_cast this
        simp [this]
      · rw [embedVec_of_not_mem ι _ hx]
        show (0 : ZMod 2) = if x ∈ γ then v x else 0
        have : x ∉ γ := fun h' => hx (by rw [hr]; exact_mod_cast h')
        simp [this]
    refine keeps_or_swaps_of_local (c := ofVec u) (fun k₀ => ?_) (vec_keep_or_swap u)
    rw [← he, ← map_mul, ← map_inv, ← map_mul]
  have h3 : Keeps γ h (ofPerm a.perm) ∨ Swaps γ h (ofPerm a.perm) := by
    have hmap : ∀ i, a.perm (ι i) ∈ Set.range ι := by
      intro i
      have h1 : ι i ∈ γ := by
        have := Set.mem_range_self (f := ι) i
        rw [hr] at this
        exact_mod_cast this
      rw [hr]
      exact_mod_cast ha _ h1
    refine keeps_or_swaps_of_local (c := ofPerm (localPerm ι a.perm hmap)) (fun k₀ => ?_)
      (perm_keep_or_swap _)
    exact ofPerm_conj_embed (localPerm_spec ι a.perm hmap) k₀
  rw [hdec]
  exact keeps_or_swaps_mul (keeps_or_swaps_mul h1 h2) h3

end KeepSwap

section Four

variable {α : Type*} [DecidableEq α]

theorem card_four {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : ({a, b, c, d} : Finset α).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]

theorem exists_invariant_four {σ τ : Equiv.Perm α} (hσ : σ * σ = 1) (hτ : τ * τ = 1)
    (hστ : σ * τ = τ * σ) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) (hne : σ ≠ τ) :
    ∃ γ : Finset α, γ.card = 4 ∧ (∀ x ∈ γ, σ x ∈ γ) ∧ (∀ x ∈ γ, τ x ∈ γ) ∧
      ∃ x ∈ γ, σ x ≠ x ∨ τ x ≠ x := by
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : Equiv.Perm α => f x) hσ
    simpa [Equiv.Perm.mul_apply] using this
  have hττ : ∀ x, τ (τ x) = x := fun x => by
    have := congrArg (fun f : Equiv.Perm α => f x) hτ
    simpa [Equiv.Perm.mul_apply] using this
  have hc : ∀ x, σ (τ x) = τ (σ x) := fun x => by
    have := congrArg (fun f : Equiv.Perm α => f x) hστ
    simpa [Equiv.Perm.mul_apply] using this
  have hex : ∀ π : Equiv.Perm α, π ≠ 1 → ∃ x, π x ≠ x := fun π hπ => by
    by_contra h
    push Not at h
    exact hπ (Equiv.ext h)
  have hρ1 : σ * τ ≠ 1 := by
    intro h
    apply hne
    calc σ = σ * (τ * τ) := by rw [hτ, mul_one]
      _ = (σ * τ) * τ := by rw [mul_assoc]
      _ = τ := by rw [h, one_mul]
  have hmem : ∀ {a b c d y : α}, y = a ∨ y = b ∨ y = c ∨ y = d → y ∈ ({a, b, c, d} : Finset α) := by
    intro a b c d y hy
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hy
  by_cases hreg : ∃ i, σ i ≠ i ∧ τ i ≠ i ∧ σ (τ i) ≠ i
  · obtain ⟨i, h1, h2, h3⟩ := hreg
    have e1 : σ i ≠ τ i := fun h => h3 (by rw [← h, hσσ])
    have e2 : σ i ≠ σ (τ i) := fun h => h2 (σ.injective h).symm
    have e3 : τ i ≠ σ (τ i) := fun h => h1 (by
      have h' : σ (τ i) = τ i := h.symm
      rw [hc] at h'
      exact τ.injective h')
    refine ⟨{i, σ i, τ i, σ (τ i)}, card_four (Ne.symm h1) (Ne.symm h2) (Ne.symm h3) e1 e2 e3,
      ?_, ?_, i, by simp, Or.inl h1⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx] <;> apply hmem
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (hσσ i)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (hσσ (τ i))))
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx] <;> apply hmem
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (hc i).symm))
      · exact Or.inl (hττ i)
      · right; left
        rw [← hc, hττ]
  · push Not at hreg
    obtain ⟨i, hi⟩ := hex σ hσ1
    by_cases hτi : τ i = i
    · obtain ⟨j, hj⟩ := hex τ hτ1
      have hσi' : τ (σ i) = σ i := by rw [← hc, hτi]
      have hij : i ≠ j := fun h => hj (h ▸ hτi)
      have hiτj : i ≠ τ j := fun h => hij (by
        have := congrArg τ h
        rw [hττ, hτi] at this
        exact this)
      have hσij : σ i ≠ j := fun h => hj (h ▸ hσi')
      have hσiτj : σ i ≠ τ j := fun h => hj (by
        have := congrArg τ h
        rw [hσi', hττ] at this
        rw [← this, hσi'])
      refine ⟨{i, σ i, j, τ j}, card_four (Ne.symm hi) hij hiτj hσij hσiτj (Ne.symm hj),
        ?_, ?_, i, by simp, Or.inl hi⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx | hx <;> rw [hx] <;> apply hmem
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (hσσ i)
        · by_cases hσj : σ j = j
          · exact Or.inr (Or.inr (Or.inl hσj))
          · have h3 := hreg j hσj hj
            right; right; right
            have := congrArg σ h3
            rw [hσσ] at this
            exact this.symm
        · by_cases hσj : σ j = j
          · right; right; right
            rw [hc, hσj]
          · exact Or.inr (Or.inr (Or.inl (hreg j hσj hj)))
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx | hx <;> rw [hx] <;> apply hmem
        · exact Or.inl hτi
        · exact Or.inr (Or.inl hσi')
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inr (Or.inr (Or.inl (hττ j)))
    · have hρi : σ (τ i) = i := hreg i hi hτi
      have hτi' : τ i = σ i := by
        have := congrArg σ hρi
        rwa [hσσ] at this
      obtain ⟨j, hj⟩ := hex (σ * τ) hρ1
      simp only [Equiv.Perm.mul_apply] at hj
      have hρσi : σ (τ (σ i)) = σ i := by rw [← hc, hσσ, hτi']
      have hρρ : ∀ y, σ (τ (σ (τ y))) = y := fun y => by rw [hc (σ (τ y)), hσσ, hττ]
      have hij : i ≠ j := fun h => hj (h ▸ hρi)
      have hiρj : i ≠ σ (τ j) := fun h => hij (by
        have h' := hρρ j
        rw [← h, hρi] at h'
        exact h')
      have hσij : σ i ≠ j := fun h => hj (h ▸ hρσi)
      have hσiρj : σ i ≠ σ (τ j) := fun h => hσij (by
        have h1 := σ.injective h
        have h2 : τ i = j := by rw [h1, hττ]
        rw [← hτi']
        exact h2)
      refine ⟨{i, σ i, j, σ (τ j)}, card_four (Ne.symm hi) hij hiρj hσij hσiρj (Ne.symm hj),
        ?_, ?_, i, by simp, Or.inl hi⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx | hx <;> rw [hx] <;> apply hmem
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (hσσ i)
        · by_cases hσj : σ j = j
          · exact Or.inr (Or.inr (Or.inl hσj))
          · have h3 : τ j = j := by
              by_contra hτx
              exact hj (hreg j hσj hτx)
            right; right; right
            rw [h3]
        · by_cases hσj : σ j = j
          · right; right; right
            rw [hσσ, hc, hσj]
          · have h3 : τ j = j := by
              by_contra hτx
              exact hj (hreg j hσj hτx)
            right; right; left
            rw [hσσ, h3]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx | hx <;> rw [hx] <;> apply hmem
        · exact Or.inr (Or.inl hτi')
        · left
          rw [← hc, hτi', hσσ]
        · by_cases hτj : τ j = j
          · exact Or.inr (Or.inr (Or.inl hτj))
          · have h3 : σ j = j := by
              by_contra hσx
              exact hj (hreg j hσx hτj)
            right; right; right
            rw [hc, h3]
        · by_cases hτj : τ j = j
          · right; right; right
            rw [hτj, ← hc, hτj]
          · have h3 : σ j = j := by
              by_contra hσx
              exact hj (hreg j hσx hτj)
            right; right; left
            rw [← hc, hττ, h3]

end Four

section Model

variable {n : ℕ}

@[expose] noncomputable def permQ (n : ℕ) : AEQ n →* Equiv.Perm (Fin n) :=
  QuotientGroup.lift (piSub n) (permHom n) fun x hx => by
    rcases mem_piSub.mp hx with rfl | rfl
    · exact map_one _
    · rfl

theorem permQ_mkQ (a : Wr n) : permQ n (mkQ n a) = a.perm := rfl

theorem mul_self_of_mem_ker_permQ {x : AEQ n} (hx : x ∈ (permQ n).ker) : x * x = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have ha : a ∈ vecSub n := hx
  show mkQ n a * mkQ n a = 1
  rw [← map_mul, vecSub_mul_self ha, map_one]

theorem permQ_mem_of_mem_aeBarOver {A : Subgroup (Equiv.Perm (Fin n))} {x : AEQ n}
    (hx : x ∈ aeBarOver A) : permQ n x ∈ A := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ha.2

theorem mkQ_ofPerm_mem_aeBarOver {A : Subgroup (Equiv.Perm (Fin n))} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ A) (hσa : σ ∈ alternatingGroup (Fin n)) : mkQ n (ofPerm σ) ∈ aeBarOver A := by
  refine ⟨ofPerm σ, ⟨mem_aeSub.mpr ⟨?_, hσa⟩, hσ⟩, rfl⟩
  simp [wsum, ofPerm]

theorem le_ker_permQ_of_normal {A : Subgroup (Equiv.Perm (Fin n))}
    (hAalt : A ≤ alternatingGroup (Fin n))
    (hO2 : ∀ N : Subgroup (Equiv.Perm (Fin n)), N ≤ A → (∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N) →
      IsPGroup 2 ↥N → N = ⊥)
    {T : Subgroup (AEQ n)} (hTM : T ≤ aeBarOver A)
    (hTn : ∀ x ∈ aeBarOver A, ∀ t ∈ T, x * t * x⁻¹ ∈ T) (hT2 : IsPGroup 2 ↥T) :
    T ≤ (permQ n).ker := by
  rw [← Subgroup.map_eq_bot_iff]
  refine hO2 _ (fun _ ⟨t, ht, e⟩ => e ▸ permQ_mem_of_mem_aeBarOver (hTM ht)) ?_ (hT2.map _)
  rintro σ hσ _ ⟨t, ht, rfl⟩
  refine ⟨mkQ n (ofPerm σ) * t * (mkQ n (ofPerm σ))⁻¹,
    hTn _ (mkQ_ofPerm_mem_aeBarOver hσ (hAalt hσ)) t ht, ?_⟩
  rw [map_mul, map_mul, map_inv, permQ_mkQ]
  rfl

theorem eq_bot_of_normal_two_alternating (hn : 5 ≤ n) {N : Subgroup (Equiv.Perm (Fin n))}
    (hNA : N ≤ alternatingGroup (Fin n))
    (hNn : ∀ a ∈ alternatingGroup (Fin n), ∀ x ∈ N, a * x * a⁻¹ ∈ N) (hN2 : IsPGroup 2 ↥N) :
    N = ⊥ := by
  have : (N.subgroupOf (alternatingGroup (Fin n))).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr (hNn g g.2 x (Subgroup.mem_subgroupOf.mp hx))⟩
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by rw [Nat.card_fin]; exact hn)
    (N := N.subgroupOf (alternatingGroup (Fin n))) with h | h
  · have hd := Subgroup.subgroupOf_eq_bot.mp h
    rw [disjoint_iff, inf_eq_left.mpr hNA] at hd
    exact hd
  · exfalso
    have h0 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
    have h1 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
    have h2 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
    have hc3 := Equiv.Perm.isThreeCycle_swap_mul_swap_same h0 h2 h1
    set c := Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ *
      Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨2, by omega⟩ with hc
    have hcN : c ∈ N := by
      have : (⟨c, hc3.mem_alternatingGroup⟩ : alternatingGroup (Fin n)) ∈
          N.subgroupOf (alternatingGroup (Fin n)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨k, hk⟩ := hN2 ⟨c, hcN⟩
    have hk' : c ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [hc3.orderOf] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem conj_ofVec (a : Wr n) (v : Fin n → ZMod 2) :
    a * ofVec v * a⁻¹ = ofVec (fun x => v (a.perm.symm x)) := by
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [mul_vec, mul_vec, inv_vec]
    show a.vec x + v (a.perm.symm x) + a.vec (a.perm ((a.perm * 1).symm x)) = v (a.perm.symm x)
    rw [mul_one, Equiv.apply_symm_apply, add_comm (a.vec x), add_assoc, zmod_two_add_self,
      add_zero]
  · show a.perm * 1 * a.perm⁻¹ = 1
    rw [mul_one, mul_inv_cancel]

theorem q8_facts {M : Type} [Group M] {B : Subgroup M} {w : M} (hBw : IsUniqueInvolution B w)
    (hB8 : Nat.card ↥B = 8) (hBnc : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) :
    (∀ g ∈ B, g * w = w * g) ∧ ∀ g ∈ B, g * g = 1 ∨ g * g = w := by
  have : Finite ↥B := Nat.finite_of_card_ne_zero (by rw [hB8]; norm_num)
  have hwc : ∀ g ∈ B, g * w = w * g := by
    intro g hg
    have h1 : g * w * g⁻¹ ∈ B := B.mul_mem (B.mul_mem hg hBw.mem) (B.inv_mem hg)
    have h2 : (g * w * g⁻¹) * (g * w * g⁻¹) = 1 := by
      calc (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
        _ = 1 := by rw [hBw.sq, mul_one, mul_inv_cancel]
    rcases hBw.unique _ h1 h2 with h3 | h3
    · exfalso
      apply hBw.ne_one
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = 1 := by rw [h3, mul_one, inv_mul_cancel]
    · calc g * w = g * w * g⁻¹ * g := by group
        _ = w * g := by rw [h3]
  refine ⟨hwc, fun g hg => ?_⟩
  have hord : orderOf g ∣ 8 := hB8 ▸ Subgroup.orderOf_dvd_natCard B hg
  have h8 : orderOf g ≠ 8 := by
    intro h8
    obtain ⟨x, hx, y, hy, hxy⟩ := hBnc
    have hz : Subgroup.zpowers g = B := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr hg) (by rw [Nat.card_zpowers, h8, hB8])
    obtain ⟨i, rfl⟩ : x ∈ Subgroup.zpowers g := hz ▸ hx
    obtain ⟨j, rfl⟩ : y ∈ Subgroup.zpowers g := hz ▸ hy
    exact hxy (by simp only [← zpow_add, add_comm])
  have h4 : orderOf g ∣ 4 := by
    have : orderOf g ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hord, by norm_num⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]
    · exact absurd h h8
  have hg4 : g ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp h4
  refine hBw.unique (g * g) (B.mul_mem hg hg) ?_
  rw [← pow_four_eq]
  exact hg4

theorem false_of_twCore (hn : 5 ≤ n) {A : Subgroup (Equiv.Perm (Fin n))}
    {𝒜 : Set (Finset (Fin n))} {B : Subgroup (AEQ n)} {w : AEQ n} (hBM : B ≤ aeBarOver A)
    (hBw : IsUniqueInvolution B w) (hB8 : Nat.card ↥B = 8)
    (hBnc : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x) (hwE : permQ n w = 1)
    (hthinE : ∀ x ∈ B, permQ n x = 1 → x = 1 ∨ x = w)
    (horb : ∀ a b : Wr n, mkQ n a ∈ B → mkQ n b ∈ B → mkQ n a * mkQ n b ≠ mkQ n b * mkQ n a →
      ∃ γ ∈ 𝒜, ∃ _ : γ.card = 4, (∀ x ∈ γ, a.perm x ∈ γ) ∧ (∀ x ∈ γ, b.perm x ∈ γ) ∧
        ∃ x ∈ γ, a.perm x ≠ x ∨ b.perm x ≠ x)
    (hi : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool),
      (∃ x ∈ B, orderOf x = 4 ∧ ∀ k ∈ memBar α h b, x * k * x⁻¹ ∈ memBar α h b) →
      Commutes (memBar α h b) B) : False := by
  classical
  obtain ⟨hwc, hsq⟩ := q8_facts hBw hB8 hBnc
  obtain ⟨x, hx, y, hy, hxy⟩ := hBnc
  obtain ⟨a, -, rfl⟩ := hBM hx
  obtain ⟨b, -, rfl⟩ := hBM hy
  have hnc_of : ∀ g ∈ B, g = 1 ∨ g = w → ∀ g' ∈ B, g * g' = g' * g := by
    rintro g - (rfl | rfl) g' hg'
    · rw [one_mul, mul_one]
    · exact (hwc g' hg').symm
  obtain ⟨γ, hγ𝒜, hγ, hσγ, hτγ, i₀, hi₀, hmove⟩ := horb a b hx hy hxy
  have hx1 : mkQ n a ≠ 1 := fun h => hxy (hnc_of _ hx (Or.inl h) _ hy)
  have hxw : mkQ n a ≠ w := fun h => hxy (hnc_of _ hx (Or.inr h) _ hy)
  have hy1 : mkQ n b ≠ 1 := fun h => hxy (hnc_of _ hy (Or.inl h) _ hx).symm
  have hyw : mkQ n b ≠ w := fun h => hxy (hnc_of _ hy (Or.inr h) _ hx).symm
  have hxy1 : mkQ n a * mkQ n b ≠ 1 := fun h => hxy (by
    rw [eq_inv_of_mul_eq_one_right h]
    group)
  have hxyw : mkQ n a * mkQ n b ≠ w := fun h => hxy (by
    have h3 : mkQ n b = (mkQ n a)⁻¹ * w := by rw [← h, inv_mul_cancel_left]
    rw [h3, mul_inv_cancel_left, mul_assoc, ← hwc _ hx, inv_mul_cancel_left])
  obtain ⟨c, hcB, hcK, hc1, hcw⟩ : ∃ c : Wr n, mkQ n c ∈ B ∧ Keeps γ hγ c ∧ mkQ n c ≠ 1 ∧
      mkQ n c ≠ w := by
    rcases keeps_or_swaps (h := hγ) a hσγ with ka | ka
    · exact ⟨a, hx, ka, hx1, hxw⟩
    · rcases keeps_or_swaps (h := hγ) b hτγ with kb | kb
      · exact ⟨b, hy, kb, hy1, hyw⟩
      · exact ⟨a * b, by rw [map_mul]; exact B.mul_mem hx hy, ka.mul kb,
          by rw [map_mul]; exact hxy1, by rw [map_mul]; exact hxyw⟩
  have hcord : orderOf (mkQ n c) = 4 := by
    have hcc : mkQ n c * mkQ n c = w := by
      rcases hsq _ hcB with h | h
      · rcases hBw.unique _ hcB h with h' | h'
        · exact absurd h' hc1
        · exact absurd h' hcw
      · exact h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_pow (n := 1) (p := 2) ?_ ?_
    · rw [pow_one, pow_two, hcc]
      exact hBw.ne_one
    · have h4 : mkQ n c ^ 4 = 1 := by
        rw [pow_four_eq, hcc]
        exact hBw.sq
      simpa using h4
  have hcN : ∀ b' : Bool, ∀ k ∈ memBar γ hγ b', mkQ n c * k * (mkQ n c)⁻¹ ∈ memBar γ hγ b' := by
    rintro b' _ ⟨k₀, hk₀, rfl⟩
    exact ⟨_, hcK b' k₀ hk₀, by rw [map_mul, map_mul, map_inv]⟩
  have hcomm : ∀ b' : Bool, Commutes (memBar γ hγ b') B := fun b' =>
    hi γ hγ𝒜 hγ b' ⟨mkQ n c, hcB, hcord, hcN b'⟩
  have key : ∀ d : Wr n, mkQ n d ∈ B → (∀ x ∈ γ, d.perm x ∈ γ) → ∀ i ∈ γ, d.perm i ≠ i →
      False := by
    intro d hd hdγ i hi hdi
    have hj : d.perm i ∈ γ := hdγ i hi
    obtain ⟨k, hk, hki, hkj⟩ : ∃ k ∈ γ, k ≠ i ∧ k ≠ d.perm i := by
      have hje : d.perm i ∈ γ.erase i := Finset.mem_erase.mpr ⟨hdi, hj⟩
      have hcard : ((γ.erase i).erase (d.perm i)).card = 2 := by
        rw [Finset.card_erase_of_mem hje, Finset.card_erase_of_mem hi, hγ]
      obtain ⟨k, hk⟩ : ((γ.erase i).erase (d.perm i)).Nonempty := by
        rw [← Finset.card_pos, hcard]
        norm_num
      simp only [Finset.mem_erase] at hk
      exact ⟨k, hk.2.2, hk.2.1, hk.1⟩
    set ι := emb γ hγ with hι
    have hr : Set.range ι = (γ : Set (Fin n)) := range_emb γ hγ
    have hmemr : ∀ y ∈ γ, y ∈ Set.range ι := fun y hy => by
      rw [hr]
      exact_mod_cast hy
    obtain ⟨i', hi'⟩ := hmemr i hi
    obtain ⟨k', hk'⟩ := hmemr k hk
    obtain ⟨j', hj'⟩ := hmemr _ hj
    have hik' : i' ≠ k' := fun h => hki (by rw [← hk', ← h, hi'])
    have hji' : j' ≠ i' := fun h => hdi (by rw [← hj', h, hi'])
    have hjk' : j' ≠ k' := fun h => hkj (by rw [← hk', ← h, hj'])
    obtain ⟨p, hp, q, hq, hpq⟩ := exists_mul_eq_vec4 i' k' hik'
    have hcp := hcomm true (mkQ n (embed ι p)) ⟨embed ι p, ⟨p, hp, rfl⟩, rfl⟩ _ hd
    have hcq := hcomm false (mkQ n (embed ι q)) ⟨embed ι q, ⟨q, hq, rfl⟩, rfl⟩ _ hd
    set v := embedVec ι (vec4 [i', k']) with hv
    have hev : embed ι (ofVec (vec4 [i', k'])) = ofVec v := Wr.ext rfl (embedPerm_one ι)
    have hcv : mkQ n (ofVec v) * mkQ n d = mkQ n d * mkQ n (ofVec v) := by
      rw [← hev, ← hpq, map_mul, map_mul, mul_assoc, hcq, ← mul_assoc, hcp, mul_assoc]
    have heq : mkQ n (ofVec (fun x => v (d.perm.symm x))) = mkQ n (ofVec v) := by
      rw [← conj_ofVec, map_mul, map_mul, map_inv, ← hcv, mul_inv_cancel_right]
    have hs1 : SupportedOn (ofVec v) (Set.range ι) :=
      fun x hx => ⟨embedVec_of_not_mem ι _ hx, rfl⟩
    have hs2 : SupportedOn (ofVec (fun x => v (d.perm.symm x))) (Set.range ι) := by
      intro x hx
      refine ⟨?_, rfl⟩
      show v (d.perm.symm x) = 0
      refine embedVec_of_not_mem ι _ fun hm => hx ?_
      rw [hr] at hm ⊢
      have hm' : d.perm.symm x ∈ γ := by exact_mod_cast hm
      have := hdγ _ hm'
      rw [Equiv.apply_symm_apply] at this
      exact_mod_cast this
    have hinj := mkQ_inj_of_supportedOn hn hs2 hs1 heq
    have hval := congrFun (congrArg Wr.vec hinj) (d.perm i)
    change v (d.perm.symm (d.perm i)) = v (d.perm i) at hval
    rw [Equiv.symm_apply_apply, ← hj', ← hi', hv, embedVec_apply, embedVec_apply] at hval
    simp [vec4, hji', hjk'] at hval
  rcases hmove with h | h
  · exact key a hx hσγ i₀ hi₀ h
  · exact key b hy hτγ i₀ hi₀ h

theorem modelTwCore_aeBarOver (hn : 5 ≤ n) {A : Subgroup (Equiv.Perm (Fin n))}
    (hAalt : A ≤ alternatingGroup (Fin n))
    (hO2 : ∀ N : Subgroup (Equiv.Perm (Fin n)), N ≤ A → (∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N) →
      IsPGroup 2 ↥N → N = ⊥)
    {𝒜 : Set (Finset (Fin n))}
    (horb : ∀ σ ∈ A, ∀ τ ∈ A, σ * σ = 1 → τ * τ = 1 → σ * τ = τ * σ → σ ≠ 1 → τ ≠ 1 → σ ≠ τ →
      ∃ γ ∈ 𝒜, ∃ _ : γ.card = 4, (∀ x ∈ γ, σ x ∈ γ) ∧ (∀ x ∈ γ, τ x ∈ γ) ∧
        ∃ x ∈ γ, σ x ≠ x ∨ τ x ≠ x) :
    ModelTwCore 𝒜 (aeBarOver A) := by
  intro B w hBM hBw hB8 hBnc hT hthin hi
  set M := aeBarOver A with hM
  set E : Subgroup (AEQ n) := M ⊓ (permQ n).ker with hE
  have hEn : ∀ x ∈ M, ∀ t ∈ E, x * t * x⁻¹ ∈ E := by
    intro x hx t ht
    refine ⟨M.mul_mem (M.mul_mem hx ht.1) (M.inv_mem hx), ?_⟩
    show permQ n (x * t * x⁻¹) = 1
    rw [map_mul, map_mul, map_inv, show permQ n t = 1 from ht.2, mul_one, mul_inv_cancel]
  have hE2 : IsPGroup 2 ↥E := fun t => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (mul_self_of_mem_ker_permQ t.2.2)⟩
  obtain ⟨T₀, hT₀M, hT₀n, hT₀2, hwT₀⟩ := hT
  have hwE : permQ n w = 1 := le_ker_permQ_of_normal hAalt hO2 hT₀M hT₀n hT₀2 hwT₀
  have hthinE : ∀ x ∈ B, permQ n x = 1 → x = 1 ∨ x = w :=
    fun x hx hx1 => hthin E inf_le_left hEn hE2 x hx ⟨hBM hx, hx1⟩
  obtain ⟨hwc, hsq⟩ := q8_facts hBw hB8 hBnc
  refine false_of_twCore hn hBM hBw hB8 hBnc hwE hthinE (fun a b hx hy hxy => ?_) hi
  have hsqE : ∀ g ∈ B, permQ n (g * g) = 1 := fun g hg => by
    rcases hsq g hg with h | h <;> rw [h]
    · exact map_one _
    · exact hwE
  have hnc_of : ∀ g ∈ B, g = 1 ∨ g = w → ∀ g' ∈ B, g * g' = g' * g := by
    rintro g - (rfl | rfl) g' hg'
    · rw [one_mul, mul_one]
    · exact (hwc g' hg').symm
  have hσσ : a.perm * a.perm = 1 := hsqE _ hx
  have hττ : b.perm * b.perm = 1 := hsqE _ hy
  have hστ : a.perm * b.perm = b.perm * a.perm := by
    have h1 : a.perm * b.perm * (a.perm * b.perm) = 1 := by
      have := hsqE _ (B.mul_mem hx hy)
      simp only [map_mul, permQ_mkQ] at this
      exact this
    have ha' : a.perm⁻¹ = a.perm := inv_eq_of_mul_eq_one_left hσσ
    have hb' : b.perm⁻¹ = b.perm := inv_eq_of_mul_eq_one_left hττ
    calc a.perm * b.perm = (a.perm * b.perm)⁻¹ := (eq_inv_of_mul_eq_one_left h1)
      _ = b.perm * a.perm := by rw [mul_inv_rev, ha', hb']
  have hσ1 : a.perm ≠ 1 := fun h => hxy (hnc_of _ hx (hthinE _ hx (by rw [permQ_mkQ, h])) _ hy)
  have hτ1 : b.perm ≠ 1 := fun h =>
    hxy (hnc_of _ hy (hthinE _ hy (by rw [permQ_mkQ, h])) _ hx).symm
  have hστne : a.perm ≠ b.perm := by
    intro h
    have h1 : permQ n ((mkQ n a)⁻¹ * mkQ n b) = 1 := by
      rw [map_mul, map_inv, permQ_mkQ, permQ_mkQ, h, inv_mul_cancel]
    rcases hthinE _ (B.mul_mem (B.inv_mem hx) hy) h1 with h2 | h2
    · apply hxy
      rw [inv_mul_eq_one.mp h2]
    · apply hxy
      have h3 : mkQ n b = mkQ n a * w := by rw [← h2, mul_inv_cancel_left]
      rw [h3, mul_assoc (mkQ n a) w, ← hwc _ hx]
  exact horb _ (permQ_mem_of_mem_aeBarOver (hBM hx)) _ (permQ_mem_of_mem_aeBarOver (hBM hy)) hσσ
    hττ hστ hσ1 hτ1 hστne

theorem modelTwCore_aeModel (m : ℕ) (hm : 5 ≤ m) :
    ModelTwCore (Set.univ : Set (Finset (Fin m))) (TL4.aeModel m) := by
  rw [TL4.aeModel_eq]
  refine modelTwCore_aeBarOver hm le_rfl
    (fun N hNA hNn hN2 => eq_bot_of_normal_two_alternating hm hNA hNn hN2) ?_
  intro σ _ τ _ hσσ hττ hστ hσ1 hτ1 hne
  obtain ⟨γ, hγ, hσγ, hτγ, hmv⟩ := exists_invariant_four hσσ hττ hστ hσ1 hτ1 hne
  exact ⟨γ, Set.mem_univ _, hγ, hσγ, hτγ, hmv⟩

end Model

end CFSG.ClassicalInvolution.Q3.TC.Thin
