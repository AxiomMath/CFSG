module

public import CFSG.CGT.PushingUpLit.BHS.SymNatNormalizer

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open Equiv CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin.G6

section Perm

variable {α : Type} [DecidableEq α]

theorem eq_of_swap_mem_of_isPGroup [Fintype α] {Q : Subgroup (Perm α)} (hQ : IsPGroup 2 Q) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (h1 : swap a b ∈ Q) (h2 : swap a c ∈ Q) : b = c := by
  by_contra hbc
  have h3 : (swap a b * swap a c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hmem : swap a b * swap a c ∈ Q := Q.mul_mem h1 h2
  obtain ⟨k, hk⟩ := hQ ⟨_, hmem⟩
  have hk' : (swap a b * swap a c) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf (swap a b * swap a c) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [h3.orderOf] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem swap_eq_or_disjoint {Z : Subgroup (Perm α)}
    (hmatch : ∀ a b c : α, a ≠ b → a ≠ c → swap a b ∈ Z → swap a c ∈ Z → b = c)
    {a d c e : α} (had : a ≠ d) (hce : c ≠ e) (hs : swap a d ∈ Z) (ht : swap c e ∈ Z) :
    swap c e = swap a d ∨ ∀ x, swap a d x = x ∨ swap c e x = x := by
  by_cases hca : c = a
  · subst hca
    exact Or.inl (by rw [hmatch c d e had hce hs ht])
  by_cases hcd : c = d
  · subst hcd
    left
    have hs' : swap c a ∈ Z := by rwa [swap_comm]
    have := hmatch c a e had.symm hce hs' ht
    rw [← this, swap_comm]
  by_cases hea : e = a
  · subst hea
    left
    have ht' : swap e c ∈ Z := by rwa [swap_comm]
    have := hmatch e d c had hce.symm hs ht'
    rw [← this, swap_comm]
  by_cases hed : e = d
  · subst hed
    left
    have hs' : swap e a ∈ Z := by rwa [swap_comm]
    have ht' : swap e c ∈ Z := by rwa [swap_comm]
    have := hmatch e a c had.symm hce.symm hs' ht'
    rw [← this]
  right
  intro x
  by_cases hxa : x = a
  · subst hxa
    exact Or.inr (swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hea))
  by_cases hxd : x = d
  · subst hxd
    exact Or.inr (swap_apply_of_ne_of_ne (Ne.symm hcd) (Ne.symm hed))
  exact Or.inl (swap_apply_of_ne_of_ne hxa hxd)

theorem pair_of_swap_conj {σ : Perm α} {c d : α} (hcd : c ≠ d)
    (h : σ * swap c d * σ⁻¹ = swap c d) :
    (σ c = c ∧ σ d = d) ∨ (σ c = d ∧ σ d = c) := by
  have hs : swap (σ c) (σ d) = swap c d := by rw [swap_apply_apply, h]
  have h1 := congrArg (fun f : Perm α => f (σ c)) hs
  simp only [swap_apply_left] at h1
  by_cases hc1 : σ c = c
  · left
    refine ⟨hc1, ?_⟩
    rw [hc1, swap_apply_left] at h1
    exact h1
  by_cases hc2 : σ c = d
  · right
    refine ⟨hc2, ?_⟩
    rw [hc2, swap_apply_right] at h1
    exact h1
  · exfalso
    rw [swap_apply_of_ne_of_ne hc1 hc2] at h1
    exact hcd (σ.injective h1.symm)

end Perm

section Matching

variable {m : ℕ}

theorem mem_of_commute_swaps (Z : Subgroup (Perm (Fin m))) (i₀ : Fin m)
    (hZi : ∀ z ∈ Z, z i₀ = i₀) (hcov : ∀ c, c ≠ i₀ → ∃ d, d ≠ c ∧ swap c d ∈ Z)
    (hmatch : ∀ a b c : Fin m, a ≠ b → a ≠ c → swap a b ∈ Z → swap a c ∈ Z → b = c)
    (σ : Perm (Fin m))
    (hσ : ∀ c d : Fin m, c ≠ d → swap c d ∈ Z → σ * swap c d * σ⁻¹ = swap c d) : σ ∈ Z := by
  classical
  have hne_i₀ : ∀ c d : Fin m, c ≠ d → swap c d ∈ Z → c ≠ i₀ ∧ d ≠ i₀ := by
    intro c d hcd hs
    have h1 := hZi _ hs
    refine ⟨fun hc => ?_, fun hd => ?_⟩
    · subst hc
      rw [swap_apply_left] at h1
      exact hcd h1.symm
    · subst hd
      rw [swap_apply_right] at h1
      exact hcd h1
  have key : ∀ n : ℕ, ∀ σ : Perm (Fin m),
      (∀ c d : Fin m, c ≠ d → swap c d ∈ Z → σ * swap c d * σ⁻¹ = swap c d) →
      (Finset.univ.filter (fun x => σ x ≠ x)).card = n → σ ∈ Z := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro σ hσ hn
      by_cases h1 : σ = 1
      · rw [h1]
        exact Z.one_mem
      obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
        by_contra hcon
        push Not at hcon
        exact h1 (Equiv.ext hcon)
      have hai : a ≠ i₀ := by
        intro hai0
        have ha' : σ i₀ ≠ i₀ := by rw [← hai0]; exact ha
        obtain ⟨e, hed, hse⟩ := hcov (σ i₀) ha'
        have hne := hne_i₀ _ _ (Ne.symm hed) hse
        rcases pair_of_swap_conj (Ne.symm hed) (hσ _ _ (Ne.symm hed) hse) with ⟨h2, -⟩ | ⟨-, h2⟩
        · exact ha' (σ.injective h2)
        · exact hne.2 (σ.injective h2)
      obtain ⟨d, hda, hsd⟩ := hcov a hai
      have had : a ≠ d := Ne.symm hda
      have hσa : σ a = d ∧ σ d = a := by
        rcases pair_of_swap_conj had (hσ _ _ had hsd) with ⟨h2, -⟩ | h2
        · exact absurd h2 ha
        · exact h2
      set s : Perm (Fin m) := swap a d with hs
      have hsZ : s ∈ Z := hsd
      have hcomm : ∀ c e : Fin m, c ≠ e → swap c e ∈ Z → s * swap c e * s⁻¹ = swap c e := by
        intro c e hce ht
        rcases swap_eq_or_disjoint hmatch had hce hsd ht with h2 | h2
        · rw [h2]
          simp [hs]
        · have hc : Commute s (swap c e) := by
            refine Equiv.Perm.Disjoint.commute ?_
            intro x
            exact h2 x
          rw [hc.eq]
          group
      have hσ' : ∀ c e : Fin m, c ≠ e → swap c e ∈ Z → (s * σ) * swap c e * (s * σ)⁻¹ = swap c e := by
        intro c e hce ht
        have : (s * σ) * swap c e * (s * σ)⁻¹ = s * (σ * swap c e * σ⁻¹) * s⁻¹ := by group
        rw [this, hσ c e hce ht, hcomm c e hce ht]
      have hsub : (Finset.univ.filter (fun x => (s * σ) x ≠ x)) ⊂
          (Finset.univ.filter (fun x => σ x ≠ x)) := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨a, by simpa using ha, ?_⟩
          simp [hσa.1, hs]
        · intro b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          intro hbσ
          apply hb
          have : (s * σ) b = s b := by simp [Equiv.Perm.mul_apply, hbσ]
          rw [this]
          by_cases hba : b = a
          · subst hba
            exact absurd hbσ ha
          by_cases hbd : b = d
          · subst hbd
            exfalso
            have := hσa.2
            rw [hbσ] at this
            exact had this.symm
          · exact swap_apply_of_ne_of_ne hba hbd
      have hlt : (Finset.univ.filter (fun x => (s * σ) x ≠ x)).card < n := hn ▸ Finset.card_lt_card hsub
      have hmem : s * σ ∈ Z := ih _ hlt (s * σ) hσ' rfl
      have : σ = s⁻¹ * (s * σ) := by group
      rw [this]
      exact Z.mul_mem (Z.inv_mem hsZ) hmem
  exact key _ σ hσ rfl

end Matching

section Natural

variable {m : ℕ} (hm : Odd m)

theorem vcoord_uvec_mul (p q j : Fin m) :
    vcoord (uvec hm p * uvec hm q) j = (if j = p then 1 else 0) + (if j = q then 1 else 0) := by
  rw [vcoord_mul, vcoord_uvec, vcoord_uvec]
  split_ifs <;> decide

include hm in
theorem pair_of_fix_uvec {π : Perm (Fin m)} {a b : Fin m} (hab : a ≠ b)
    (hfix : coreAct m π (uvec hm a * uvec hm b) = uvec hm a * uvec hm b) :
    π * swap a b * π⁻¹ = swap a b := by
  rw [map_mul, coreAct_uvec, coreAct_uvec] at hfix
  have hcoord : ∀ j, ((if j = π a then (1 : ZMod 2) else 0) + (if j = π b then 1 else 0)) =
      (if j = a then 1 else 0) + (if j = b then 1 else 0) := by
    intro j
    have := congrArg (fun v => vcoord v j) hfix
    simpa only [vcoord_uvec_mul] using this
  have hπab : π a ≠ π b := fun h => hab (π.injective h)
  have h1 : π a = a ∨ π a = b := by
    have := hcoord (π a)
    simp only [ite_true, hπab, ite_false, add_zero] at this
    by_contra hcon
    push Not at hcon
    simp [hcon.1, hcon.2] at this
  have h2 : π b = a ∨ π b = b := by
    have := hcoord (π b)
    simp only [ite_true, Ne.symm hπab, ite_false, zero_add] at this
    by_contra hcon
    push Not at hcon
    simp [hcon.1, hcon.2] at this
  rw [← swap_apply_apply]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hπab
  · rw [h1, h2]
  · rw [h1, h2, swap_comm]
  · exact absurd (h1.trans h2.symm) hπab

include hm in
theorem coreAct_swap_fix_pair {a b c d : Fin m} (hab : a ≠ b)
    (h : swap c d = swap a b ∨ ∀ x, swap a b x = x ∨ swap c d x = x) :
    coreAct m (swap c d) (uvec hm a * uvec hm b) = uvec hm a * uvec hm b := by
  rw [map_mul, coreAct_uvec, coreAct_uvec]
  rcases h with h | h
  · rw [h, swap_apply_left, swap_apply_right, mul_comm]
  · have ha : swap c d a = a := by
      rcases h a with h1 | h1
      · rw [swap_apply_left] at h1
        exact absurd h1.symm hab
      · exact h1
    have hb : swap c d b = b := by
      rcases h b with h1 | h1
      · rw [swap_apply_right] at h1
        exact absurd h1 hab
      · exact h1
    rw [ha, hb]

include hm in
theorem eq_one_of_fix_all (v : ↥(coreMod m)) (hv : ∀ σ : Perm (Fin m), coreAct m σ v = v) :
    v = 1 := by
  have hconst : ∀ i j : Fin m, vcoord v i = vcoord v j := by
    intro i j
    have := congrArg (fun w => vcoord w j) (hv (swap i j))
    simp only [vcoord_coreAct] at this
    rw [swap_inv, swap_apply_right] at this
    exact this
  obtain ⟨i₀⟩ : Nonempty (Fin m) := ⟨⟨0, by obtain ⟨k, hk⟩ := hm; omega⟩⟩
  have hsum := sum_vcoord v
  have hc : ∑ i, vcoord v i = (m : ZMod 2) * vcoord v i₀ := by
    rw [Finset.sum_congr rfl (fun i _ => hconst i i₀)]
    simp
  rw [hc, (ZMod.natCast_eq_one_iff_odd.2 hm), one_mul] at hsum
  apply vcoord_ext
  intro i
  rw [hconst i i₀, hsum, vcoord_one]

include hm in
theorem eq_one_or_uvec_of_fix_stab (h3 : 3 ≤ m) (i : Fin m) (v : ↥(coreMod m))
    (hv : ∀ σ : Perm (Fin m), σ i = i → coreAct m σ v = v) : v = 1 ∨ v = uvec hm i := by
  classical
  have hconst : ∀ j k : Fin m, j ≠ i → k ≠ i → vcoord v j = vcoord v k := by
    intro j k hj hk
    have hfix : swap j k i = i := swap_apply_of_ne_of_ne (Ne.symm hj) (Ne.symm hk)
    have := congrArg (fun w => vcoord w k) (hv (swap j k) hfix)
    simp only [vcoord_coreAct] at this
    rw [swap_inv, swap_apply_right] at this
    exact this
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨j₀, hj₀⟩ := exists_ne i
  have hsum := sum_vcoord v
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
  have hrest : ∑ j ∈ Finset.univ.erase i, vcoord v j = ((m - 1 : ℕ) : ZMod 2) * vcoord v j₀ := by
    rw [Finset.sum_congr rfl (fun j hj => hconst j j₀ (Finset.ne_of_mem_erase hj) hj₀)]
    simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  have hev : ((m - 1 : ℕ) : ZMod 2) = 0 := by
    rw [ZMod.natCast_eq_zero_iff_even]
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, by omega⟩
  rw [hrest, hev, zero_mul, add_zero] at hsum
  rcases zmod_two_eq_ite (vcoord v j₀) with hd
  by_cases hd1 : vcoord v j₀ = 1
  · right
    apply vcoord_ext
    intro j
    rw [vcoord_uvec]
    by_cases hji : j = i
    · simp [hji, hsum]
    · simp [hji, hconst j j₀ hji hj₀, hd1]
  · left
    have hd0 : vcoord v j₀ = 0 := by simpa [hd1] using hd
    apply vcoord_ext
    intro j
    rw [vcoord_one]
    by_cases hji : j = i
    · rw [hji, hsum]
    · rw [hconst j j₀ hji hj₀, hd0]

include hm in
theorem eq_self_of_commute (h3 : 3 ≤ m) (ζ : ↥(coreMod m) →* ↥(coreMod m))
    (hinj : Function.Injective ζ)
    (hζ : ∀ (σ : Perm (Fin m)) (d : ↥(coreMod m)), ζ (coreAct m σ d) = coreAct m σ (ζ d)) :
    ∀ d, ζ d = d := by
  have hne1 : ∀ i, uvec hm i ≠ 1 := by
    intro i h
    have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    obtain ⟨j, hj⟩ := exists_ne i
    have := congrArg (fun v => vcoord v j) h
    simp [vcoord_uvec, hj, vcoord_one] at this
  have hu : ∀ i, ζ (uvec hm i) = uvec hm i := by
    intro i
    rcases eq_one_or_uvec_of_fix_stab hm h3 i (ζ (uvec hm i))
      (fun σ hσ => by rw [← hζ, coreAct_uvec, hσ]) with h | h
    · exfalso
      apply hne1 i
      apply hinj
      rw [h, map_one]
    · exact h
  have hagree : Set.EqOn ζ (MonoidHom.id _) (Set.range (uvec hm)) := by
    rintro _ ⟨i, rfl⟩
    exact hu i
  have := MonoidHom.eqOn_closure hagree
  rw [closure_uvec hm] at this
  intro d
  exact this (Set.mem_univ d)

include hm in
theorem uvec_mul_ne_one {a b : Fin m} (hab : a ≠ b) : uvec hm a * uvec hm b ≠ 1 := by
  intro h
  have := congrArg (fun v => vcoord v a) h
  simp only [vcoord_uvec_mul, vcoord_one] at this
  simp [hab] at this

end Natural

end CFSG.AGLEmbeddingD2.Tits.E23
