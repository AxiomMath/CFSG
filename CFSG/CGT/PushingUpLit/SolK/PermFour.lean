module

public import CFSG.CGT.PushingUpLit.SolK.PermBlock

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

variable {d : ℕ} {N : Subgroup (Perm (Fin d))}

theorem swap_not_mem {I : Finset (Fin d)} (hN2 : IsPGroup 2 N)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) {y z w : Fin d} (hy : y ∈ I) (hz : z ∈ I)
    (hw : w ∈ I) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : swap y z ∉ N := by
  intro hs
  have hc : cyc y z w ∈ altOn I := cyc_mem_altOn_of_mem hy hz hw hyz hyw hzw
  have h1 := hA _ hc _ hs
  have hcy : cyc y z w y = w := cyc_apply_first hyw hzw
  have hcz : cyc y z w z = y := cyc_apply_second hyz hzw
  have hconj : cyc y z w * swap y z * (cyc y z w)⁻¹ = swap y w := by
    rw [← swap_apply_apply, hcy, hcz, swap_comm]
  rw [hconj] at h1
  have h2 : swap y z * swap y w ∈ N := Subgroup.mul_mem _ hs h1
  have h3 := Equiv.Perm.isThreeCycle_swap_mul_swap_same hyz hyw hzw
  obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one hN2 h2
  have hd : 3 ∣ 2 ^ j := h3.orderOf ▸ orderOf_dvd_of_pow_eq_one hj
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hd
  omega

theorem fpf_of_mem {I : Finset (Fin d)} (hI4 : I.card = 4) (hN2 : IsPGroup 2 N)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) {σ : Perm (Fin d)} (hσN : σ ∈ N)
    (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) (hout : ∀ x, x ∉ I → σ x = x)
    (hpres : ∀ x, σ x ∈ I ↔ x ∈ I) : ∀ p ∈ I, σ p ≠ p := by
  classical
  intro p hp hσp
  obtain ⟨y, hy⟩ : ∃ y, σ y ≠ y := by
    by_contra hall
    push Not at hall
    exact hσ1 (Equiv.ext hall)
  have hyI : y ∈ I := by
    by_contra h
    exact hy (hout y h)
  obtain ⟨z, hz⟩ : ∃ z, σ y = z := ⟨_, rfl⟩
  have hzI : z ∈ I := hz ▸ (hpres y).2 hyI
  have hσz : σ z = y := by
    have := congrArg (fun f : Perm (Fin d) => f y) hσ2
    simp only [Perm.mul_apply, Perm.one_apply, hz] at this
    exact this
  have hyz : y ≠ z := fun h => hy (hz.trans h.symm)
  have hyp : y ≠ p := fun h => hy (by rw [h]; exact hσp)
  have hzp : z ≠ p := fun h => hyp (σ.injective (by rw [hz, h, hσp]))
  have hσswap : σ = swap y z := by
    refine Equiv.ext fun u => ?_
    by_cases huy : u = y
    · subst huy
      rw [swap_apply_left, hz]
    by_cases huz : u = z
    · subst huz
      rw [swap_apply_right, hσz]
    rw [swap_apply_of_ne_of_ne huy huz]
    by_cases huI : u ∈ I
    · by_contra hne
      have hup : u ≠ p := fun h => hne (by rw [h]; exact hσp)
      obtain ⟨u', hu'⟩ : ∃ u', σ u = u' := ⟨_, rfl⟩
      have hu'I : u' ∈ I := hu' ▸ (hpres u).2 huI
      have hu'u : u' ≠ u := fun h => hne (hu'.trans h)
      have hu'y : u' ≠ y := fun h => huz (σ.injective (hu'.trans (h.trans hσz.symm)))
      have hu'z : u' ≠ z := fun h => huy (σ.injective (hu'.trans (h.trans hz.symm)))
      have hu'p : u' ≠ p := fun h => hup (σ.injective (hu'.trans (h.trans hσp.symm)))
      have h5 : ({p, y, z, u, u'} : Finset (Fin d)).card = 5 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hu'u)]
        all_goals simp [*, Ne.symm]
      have hsub : ({p, y, z, u, u'} : Finset (Fin d)) ⊆ I := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      omega
    · exact hout u huI
  rw [hσswap] at hσN
  exact swap_not_mem hN2 hA hyI hzI hp hyz hyp hzp hσN

theorem card_orbQ_le_of_merge (A : Subgroup (Perm (Fin d))) {t : Finset (Fin d)}
    (h : ∀ x ∈ t, ∃ y ∉ t, orbOf A y = orbOf A x) : Nat.card (OrbQ A) ≤ d - t.card := by
  classical
  have hsurj : Function.Surjective (fun y : ↥(tᶜ : Finset (Fin d)) => orbOf A (y : Fin d)) := by
    intro q
    obtain ⟨x, rfl⟩ := orbOf_surjective A q
    by_cases hx : x ∈ t
    · obtain ⟨y, hy, hyx⟩ := h x hx
      exact ⟨⟨y, Finset.mem_compl.2 hy⟩, hyx⟩
    · exact ⟨⟨x, Finset.mem_compl.2 hx⟩, rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := ↥(tᶜ : Finset (Fin d))), Fintype.card_coe,
    Finset.card_compl, Fintype.card_fin] at this
  exact this

theorem card_le_of_free {I : Finset (Fin d)} {F : Subgroup (Perm (Fin d))} (a : Fin d) (haI : a ∈ I)
    (hpres : ∀ σ ∈ F, ∀ x, σ x ∈ I ↔ x ∈ I) (hfree : ∀ σ ∈ F, σ ≠ 1 → σ a ≠ a) :
    Nat.card F ≤ I.card := by
  classical
  let f : ↥F → ↥I := fun σ => ⟨(σ : Perm (Fin d)) a, (hpres σ σ.2 a).2 haI⟩
  have hf : Function.Injective f := by
    intro σ τ h
    have h1 : (σ : Perm (Fin d)) a = (τ : Perm (Fin d)) a := congrArg Subtype.val h
    have h2 : ((τ : Perm (Fin d))⁻¹ * σ) a = a := by
      rw [Perm.mul_apply, h1, perm_inv_apply_self]
    have h3 : (τ : Perm (Fin d))⁻¹ * σ ∈ F := F.mul_mem (F.inv_mem τ.2) σ.2
    have h4 : (τ : Perm (Fin d))⁻¹ * σ = 1 := by
      by_contra hne
      exact hfree _ h3 hne h2
    exact Subtype.ext (inv_mul_eq_one.1 h4).symm
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card (α := ↥I), Fintype.card_coe] at this

theorem card_fixV_mul_card_lt (hd : Odd d) (hd5 : 5 ≤ d) {I : Finset (Fin d)}
    (hI4 : I.card = 4) (hN2 : IsPGroup 2 N) (hNI : N ≤ setStab I)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (hA' : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    {F : Subgroup (Perm (Fin d))} (hFN : F ≤ N) (hF1 : F ≠ ⊥) (hF2 : ∀ σ ∈ F, σ * σ = 1) :
    Nat.card (fixV (F.map (coreAct d))) * Nat.card F < Nat.card (coreMod d) := by
  classical
  have hNI' : N ≤ setStab Iᶜ := fun σ hσ x => by
    have := mem_setStab.1 (hNI hσ) x
    simp [this]
  have hI'card : Iᶜ.card ≤ 1 ∨ Iᶜ.card = 3 ∨ 5 ≤ Iᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, hI4]
    obtain ⟨k, hk⟩ := hd
    omega
  have hfix : ∀ σ ∈ N, ∀ x ∈ Iᶜ, σ x = x := block_fixes hN2 hNI' hA' hI'card
  have hpres : ∀ σ ∈ F, ∀ x, σ x ∈ I ↔ x ∈ I := fun σ hσ => mem_setStab.1 (hNI (hFN hσ))
  have hfree : ∀ σ ∈ F, σ ≠ 1 → ∀ p ∈ I, σ p ≠ p := fun σ hσ hσ1 =>
    fpf_of_mem hI4 hN2 hA (hFN hσ) (hF2 σ hσ) hσ1
      (fun x hx => hfix σ (hFN hσ) x (Finset.mem_compl.2 hx)) (hpres σ hσ)
  obtain ⟨a, haI⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  have hFcard : Nat.card F ≤ 4 :=
    hI4 ▸ card_le_of_free a haI hpres (fun σ hσ hσ1 => hfree σ hσ hσ1 a haI)
  obtain ⟨⟨σ, hσF⟩, hσ1⟩ : ∃ x : ↥F, x ≠ 1 := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
  have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : Perm (Fin d) => f x) (hF2 σ hσF)
    simpa [Perm.mul_apply] using this
  obtain ⟨b, hb⟩ : ∃ b, σ a = b := ⟨_, rfl⟩
  have hbI : b ∈ I := hb ▸ (hpres σ hσF a).2 haI
  have hba : b ≠ a := fun h => hfree σ hσF hσ1' a haI (hb.trans h)
  have hσb : σ b = a := by rw [← hb, hσσ]
  have hc : ((I.erase a).erase b).Nonempty := Finset.card_pos.1 (by
    have h1 := Finset.pred_card_le_card_erase (s := I.erase a) (a := b)
    have h2 := Finset.pred_card_le_card_erase (s := I) (a := a)
    omega)
  obtain ⟨c, hcmem⟩ := hc
  simp only [Finset.mem_erase] at hcmem
  obtain ⟨hcb, hca, hcI⟩ := hcmem
  obtain ⟨e, he⟩ : ∃ e, σ c = e := ⟨_, rfl⟩
  have heI : e ∈ I := he ▸ (hpres σ hσF c).2 hcI
  have hec : e ≠ c := fun h => hfree σ hσF hσ1' c hcI (he.trans h)
  have hea : e ≠ a := fun h => hcb (σ.injective (by rw [he, h, hσb]))
  have heb : e ≠ b := fun h => hca (σ.injective (by rw [he, h, hb]))
  have horbab : orbOf F b = orbOf F a := orbOf_eq_iff.2 ⟨σ, hσF, hb⟩
  have horbce : orbOf F e = orbOf F c := orbOf_eq_iff.2 ⟨σ, hσF, he⟩
  have hM := card_coreMod_mul_two hd
  have hK := card_fixV_mul_two hd F
  have h2d : (2 : ℕ) ^ d = 2 ^ (d - 2) * 4 := by
    have : d = (d - 2) + 2 := by omega
    conv_lhs => rw [this]
    rw [pow_add]; norm_num
  have h2d3 : (2 : ℕ) ^ d = 2 ^ (d - 3) * 8 := by
    have : d = (d - 3) + 3 := by omega
    conv_lhs => rw [this]
    rw [pow_add]; norm_num
  by_cases h3 : 3 ≤ Nat.card F
  ·
    have hex : ∃ σ' ∈ F, σ' ≠ 1 ∧ σ' ≠ σ := by
      by_contra hall
      push Not at hall
      have hinj : Function.Injective (fun x : ↥F => decide ((x : Perm (Fin d)) = 1)) := by
        intro x y hxy
        simp only [decide_eq_decide] at hxy
        by_cases hx1 : (x : Perm (Fin d)) = 1
        · exact Subtype.ext (hx1.trans (hxy.1 hx1).symm)
        · have hy1 : (y : Perm (Fin d)) ≠ 1 := fun h => hx1 (hxy.2 h)
          exact Subtype.ext ((hall x x.2 hx1).trans (hall y y.2 hy1).symm)
      have h2 : Nat.card ↥F ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2
      omega
    obtain ⟨σ', hσ'F, hσ'1, hσ'σ⟩ := hex
    have hσ'a : σ' a ∈ I := (hpres σ' hσ'F a).2 haI
    have hσ'a_ne_a : σ' a ≠ a := hfree σ' hσ'F hσ'1 a haI
    have hσ'a_ne_b : σ' a ≠ b := fun h => by
      have h4 : (σ'⁻¹ * σ) a = a := by
        rw [Perm.mul_apply, hb, ← h, perm_inv_apply_self]
      have h5 : σ'⁻¹ * σ ∈ F := F.mul_mem (F.inv_mem hσ'F) hσF
      have h6 : σ'⁻¹ * σ = 1 := by
        by_contra hne
        exact hfree _ h5 hne a haI h4
      exact hσ'σ (inv_mul_eq_one.1 h6)
    have hIeq : I = {a, b, c, e} := by
      symm
      refine Finset.eq_of_subset_of_card_le ?_ (by
        have h4 : ({a, b, c, e} : Finset (Fin d)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_pair (Ne.symm hec)]
          all_goals simp [*, Ne.symm]
        omega)
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl <;> assumption
    have horbca : orbOf F c = orbOf F a := by
      have : σ' a ∈ ({a, b, c, e} : Finset (Fin d)) := hIeq ▸ hσ'a
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h | h
      · exact absurd h hσ'a_ne_a
      · exact absurd h hσ'a_ne_b
      · exact orbOf_eq_iff.2 ⟨σ', hσ'F, h⟩
      · exact horbce.symm.trans (orbOf_eq_iff.2 ⟨σ', hσ'F, h⟩)
    have hcard3 : ({b, c, e} : Finset (Fin d)).card = 3 :=
      Finset.card_eq_three.2 ⟨b, c, e, Ne.symm hcb, Ne.symm heb, Ne.symm hec, rfl⟩
    have horb : Nat.card (OrbQ F) ≤ d - 3 := by
      have := card_orbQ_le_of_merge F (t := {b, c, e}) (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        refine ⟨a, ?_, ?_⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hba, Ne.symm hca, Ne.symm hea⟩
        · rcases hx with rfl | rfl | rfl
          · exact horbab.symm
          · exact horbca.symm
          · exact (horbce.trans horbca).symm)
      rwa [hcard3] at this
    have hpow : (2 : ℕ) ^ Nat.card (OrbQ F) ≤ 2 ^ (d - 3) := Nat.pow_le_pow_right (by norm_num) horb
    have hpos : 0 < (2 : ℕ) ^ (d - 3) := by positivity
    rw [h2d3] at hM
    calc Nat.card (fixV (F.map (coreAct d))) * Nat.card F
        ≤ Nat.card (fixV (F.map (coreAct d))) * 4 := Nat.mul_le_mul_left _ hFcard
      _ < Nat.card (coreMod d) := by omega
  ·
    have hcard2 : ({b, e} : Finset (Fin d)).card = 2 := Finset.card_pair (Ne.symm heb)
    have horb : Nat.card (OrbQ F) ≤ d - 2 := by
      have := card_orbQ_le_of_merge F (t := {b, e}) (fun x hx => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · refine ⟨a, ?_, horbab.symm⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hba, Ne.symm hea⟩
        · refine ⟨c, ?_, horbce.symm⟩
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hcb, Ne.symm hec⟩)
      rwa [hcard2] at this
    have hpow : (2 : ℕ) ^ Nat.card (OrbQ F) ≤ 2 ^ (d - 2) := Nat.pow_le_pow_right (by norm_num) horb
    have hpos : 0 < (2 : ℕ) ^ (d - 2) := by positivity
    rw [h2d] at hM
    have hF2' : Nat.card F ≤ 2 := by omega
    calc Nat.card (fixV (F.map (coreAct d))) * Nat.card F
        ≤ Nat.card (fixV (F.map (coreAct d))) * 2 := Nat.mul_le_mul_left _ hF2'
      _ < Nat.card (coreMod d) := by omega

theorem card_le_two_of_two (hd : Odd d) (hd5 : 5 ≤ d) {I : Finset (Fin d)} (hI2 : I.card = 2)
    (hN2 : IsPGroup 2 N) (hNI : N ≤ setStab I)
    (hA' : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) : Nat.card N ≤ 2 := by
  classical
  have hNI' : N ≤ setStab Iᶜ := fun σ hσ x => by
    have := mem_setStab.1 (hNI hσ) x
    simp [this]
  have hI'card : Iᶜ.card ≤ 1 ∨ Iᶜ.card = 3 ∨ 5 ≤ Iᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, hI2]
    obtain ⟨k, hk⟩ := hd
    omega
  have hfix : ∀ σ ∈ N, ∀ x ∈ Iᶜ, σ x = x := block_fixes hN2 hNI' hA' hI'card
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 hI2
  have hcases : ∀ σ ∈ N, σ = 1 ∨ σ = swap i j := by
    intro σ hσ
    have hpres := mem_setStab.1 (hNI hσ)
    have hout : ∀ x, x ≠ i → x ≠ j → σ x = x := fun x hxi hxj =>
      hfix σ hσ x (by simp [hxi, hxj])
    have hi : σ i ∈ ({i, j} : Finset (Fin d)) := (hpres i).2 (by simp)
    have hj : σ j ∈ ({i, j} : Finset (Fin d)) := (hpres j).2 (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi
    · left
      refine Equiv.ext fun x => ?_
      by_cases hxi : x = i
      · subst hxi; simpa using hi
      by_cases hxj : x = j
      · subst hxj
        rcases hj with hj | hj
        · exact absurd (σ.injective (hj.trans hi.symm)) (Ne.symm hij)
        · simpa using hj
      · simpa using hout x hxi hxj
    · right
      refine Equiv.ext fun x => ?_
      by_cases hxi : x = i
      · subst hxi; simpa using hi
      by_cases hxj : x = j
      · subst hxj
        rcases hj with hj | hj
        · simpa using hj
        · exact absurd (σ.injective (hj.trans hi.symm)) (Ne.symm hij)
      · rw [swap_apply_of_ne_of_ne hxi hxj]
        exact hout x hxi hxj
  have hinj : Function.Injective (fun σ : ↥N => decide ((σ : Perm (Fin d)) = 1)) := by
    intro σ τ h
    simp only [decide_eq_decide] at h
    by_cases h1 : (σ : Perm (Fin d)) = 1
    · exact Subtype.ext (h1.trans (h.1 h1).symm)
    · have h2 : (τ : Perm (Fin d)) ≠ 1 := fun h' => h1 (h.2 h')
      rcases hcases σ σ.2 with h3 | h3
      · exact absurd h3 h1
      · rcases hcases τ τ.2 with h4 | h4
        · exact absurd h4 h2
        · exact Subtype.ext (h3.trans h4.symm)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this

end CFSG.CGT.PushingUpLit.SolK
