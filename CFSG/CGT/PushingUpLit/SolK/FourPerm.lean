module

public import CFSG.CGT.PushingUpLit.SolK.PermFour

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

variable {d : ℕ}

structure FourGroup (I : Finset (Fin d)) (N : Subgroup (Perm (Fin d))) : Prop where
  two : IsPGroup 2 N
  stab : N ≤ setStab I
  fix : ∀ σ ∈ N, ∀ x, x ∉ I → σ x = x
  norm : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N

theorem exists_fourth {I : Finset (Fin d)} (hI : I.card = 4) (S : Finset (Fin d))
    (hS : S.card ≤ 3) : ∃ e ∈ I, e ∉ S :=
  Finset.exists_mem_notMem_of_card_lt_card (by omega)

namespace FourGroup

variable {I : Finset (Fin d)} {N : Subgroup (Perm (Fin d))}

theorem free (h : FourGroup I N) (hI : I.card = 4) {σ : Perm (Fin d)} (hσ : σ ∈ N)
    (hσ1 : σ ≠ 1) : ∀ p ∈ I, σ p ≠ p := by
  classical
  intro p hp hσp
  have hpres : ∀ x, σ x ∈ I ↔ x ∈ I := mem_setStab.1 (h.stab hσ)
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
    by_contra hall
    push Not at hall
    exact hσ1 (Equiv.ext hall)
  have hbI : b ∈ I := by
    by_contra hbI
    exact hb (h.fix σ hσ b hbI)
  obtain ⟨c, hc⟩ : ∃ c, σ b = c := ⟨_, rfl⟩
  have hcI : c ∈ I := hc ▸ (hpres b).2 hbI
  have hcb : c ≠ b := fun h' => hb (hc.trans h')
  have hbp : b ≠ p := fun h' => hb (by rw [h']; exact hσp)
  have hcp : c ≠ p := fun h' => hbp (σ.injective (by rw [hc, h', hσp]))
  obtain ⟨e, heI, hes⟩ := exists_fourth hI {p, b, c} Finset.card_le_three
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hes
  obtain ⟨hep, heb, hec⟩ := hes
  have hIeq : I = {p, b, c, e} := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ (by
      have h4 : ({p, b, c, e} : Finset (Fin d)).card = 4 := by
        rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_pair (Ne.symm hec)]
        all_goals simp [*, Ne.symm]
      omega)
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> assumption
  have hmem : ∀ x ∈ I, x = p ∨ x = b ∨ x = c ∨ x = e := by
    intro x hx
    rw [hIeq] at hx
    simpa using hx
  obtain ⟨c2, hc2⟩ : ∃ c2, σ c = c2 := ⟨_, rfl⟩
  have hc2I : c2 ∈ I := hc2 ▸ (hpres c).2 hcI
  have hc2c : c2 ≠ c := fun h' => hcb (σ.injective (by rw [hc, hc2, h']))
  have hc2p : c2 ≠ p := fun h' => hcp (σ.injective (by rw [hc2, h', hσp]))
  have hc2be : c2 = b ∨ c2 = e := by
    rcases hmem c2 hc2I with h' | h' | h' | h'
    · exact absurd h' hc2p
    · exact Or.inl h'
    · exact absurd h' hc2c
    · exact Or.inr h'
  obtain ⟨e2, he2⟩ : ∃ e2, σ e = e2 := ⟨_, rfl⟩
  have he2I : e2 ∈ I := he2 ▸ (hpres e).2 heI
  have he2p : e2 ≠ p := fun h' => hep (σ.injective (by rw [he2, h', hσp]))
  rcases hc2be with hcb' | hce
  ·
    have he2e : e2 = e := by
      rcases hmem e2 he2I with h' | h' | h' | h'
      · exact absurd h' he2p
      · exact absurd (σ.injective ((he2.trans h').trans (hc2.trans hcb').symm)) hec
      · exact absurd (σ.injective ((he2.trans h').trans hc.symm)) heb
      · exact h'
    have hσeq : σ = swap b c := by
      refine Equiv.ext fun x => ?_
      by_cases hxb : x = b
      · subst hxb
        rw [swap_apply_left, hc]
      by_cases hxc : x = c
      · subst hxc
        rw [swap_apply_right, hc2, hcb']
      rw [swap_apply_of_ne_of_ne hxb hxc]
      by_cases hxI : x ∈ I
      · rcases hmem x hxI with h' | h' | h' | h'
        · rw [h']; exact hσp
        · exact absurd h' hxb
        · exact absurd h' hxc
        · rw [h']; exact he2.trans he2e
      · exact h.fix σ hσ x hxI
    rw [hσeq] at hσ
    exact swap_not_mem h.two h.norm hbI hcI hp hcb.symm hbp hcp hσ
  ·
    have he2b : e2 = b := by
      rcases hmem e2 he2I with h' | h' | h' | h'
      · exact absurd h' he2p
      · exact h'
      · exact absurd (σ.injective (by rw [he2, h', hc])) heb
      · exact absurd (σ.injective (by rw [he2, h', hc2, hce])) hec
    have hσ3 : σ ^ 3 = 1 := by
      refine Equiv.ext fun x => ?_
      simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply]
      by_cases hxI : x ∈ I
      · rcases hmem x hxI with h' | h' | h' | h'
        · rw [h', hσp, hσp, hσp]
        · rw [h', hc, hc2, hce, he2, he2b]
        · rw [h', hc2, hce, he2, he2b, hc]
        · rw [h', he2, he2b, hc, hc2, hce]
      · rw [h.fix σ hσ x hxI, h.fix σ hσ x hxI, h.fix σ hσ x hxI]
    obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one h.two hσ
    have hd1 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ3
    have hd2 : orderOf σ ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have hcop : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
    have h3 : orderOf σ ∣ Nat.gcd 3 (2 ^ j) := Nat.dvd_gcd hd1 hd2
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    exact hσ1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))

theorem card_le_four (h : FourGroup I N) (hI : I.card = 4) : Nat.card ↥N ≤ 4 := by
  classical
  obtain ⟨a, haI⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  have := card_le_of_free (F := N) (I := I) a haI (fun σ hσ => mem_setStab.1 (h.stab hσ))
    (fun σ hσ hσ1 => h.free hI hσ hσ1 a haI)
  omega

theorem card_eq_four (h : FourGroup I N) (hI : I.card = 4) (hN : N ≠ ⊥) : Nat.card ↥N = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := h.card_le_four hI
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h.two
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk0 : k ≠ 0 := by
    intro hk0
    apply hN
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq N hk
  interval_cases k
  · exact absurd rfl hk0
  ·
    exfalso
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hN
    have hu1' : u ≠ 1 := fun h' => hu1 (Subtype.ext h')
    have hcard : Nat.card ↥N = 2 := by simpa using hk
    obtain ⟨y₀, -, hy₀⟩ := (Nat.card_eq_two_iff' (1 : ↥N)).1 hcard
    have hall : ∀ σ ∈ N, σ ≠ 1 → σ = u := fun σ hσ hσ1 => by
      have h1 := hy₀ ⟨σ, hσ⟩ (fun h' => hσ1 (congrArg Subtype.val h'))
      have h2 := hy₀ ⟨u, hu⟩ hu1
      exact congrArg Subtype.val (h1.trans h2.symm)
    have hpres : ∀ x, u x ∈ I ↔ x ∈ I := mem_setStab.1 (h.stab hu)
    obtain ⟨a, haI⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨b, hb⟩ : ∃ b, u a = b := ⟨_, rfl⟩
    have hbI : b ∈ I := hb ▸ (hpres a).2 haI
    have hba : b ≠ a := fun h' => h.free hI hu hu1' a haI (hb.trans h')
    have huu : u * u = 1 := by
      have hmem : u * u ∈ N := N.mul_mem hu hu
      by_contra hne
      have h1 := hall _ hmem hne
      have h2 : u * u = u * 1 := by rw [h1, mul_one]
      exact hu1' (mul_left_cancel h2)
    have hub : u b = a := by
      have := congrArg (fun f : Perm (Fin d) => f a) huu
      simpa [Perm.mul_apply, hb] using this
    obtain ⟨c, hcI, hcs⟩ := exists_fourth hI {a, b} (Finset.card_le_two.trans (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcs
    obtain ⟨hca, hcb⟩ := hcs
    obtain ⟨c', hc'I, hc's⟩ := exists_fourth hI {a, b, c} Finset.card_le_three
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc's
    obtain ⟨hc'a, hc'b, hc'c⟩ := hc's
    have hτ : cyc a c c' ∈ altOn I :=
      cyc_mem_altOn_of_mem haI hcI hc'I (Ne.symm hca) (Ne.symm hc'a) (Ne.symm hc'c)
    have hu' : cyc a c c' * u * (cyc a c c')⁻¹ ∈ N := h.norm _ hτ u hu
    have hne1 : cyc a c c' * u * (cyc a c c')⁻¹ ≠ 1 := by
      intro h'
      apply hu1'
      have := congrArg (fun t => (cyc a c c')⁻¹ * t * cyc a c c') h'
      simpa [mul_assoc] using this
    have heq := hall _ hu' hne1
    have hτb : cyc a c c' b = b := cyc_apply_of_ne hba (Ne.symm hcb) (Ne.symm hc'b)
    have hτb' : (cyc a c c')⁻¹ b = b := (Equiv.Perm.inv_eq_iff_eq).2 hτb.symm
    have h1 := congrArg (fun f : Perm (Fin d) => f b) heq
    simp only [Perm.mul_apply, hτb', hub] at h1
    rw [cyc_apply_first (Ne.symm hc'a) (Ne.symm hc'c)] at h1
    exact hc'a h1
  · simpa using hk

theorem eq_of_le (h : FourGroup I N) (hI : I.card = 4) {N' : Subgroup (Perm (Fin d))}
    (hle : N' ≤ N) (hN' : N' ≠ ⊥) (hnorm : ∀ τ ∈ altOn I, ∀ σ ∈ N', τ * σ * τ⁻¹ ∈ N') :
    N' = N := by
  have h' : FourGroup I N' :=
    ⟨fun g => by
      obtain ⟨k, hk⟩ := h.two ⟨g.1, hle g.2⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩,
    fun σ hσ => h.stab (hle hσ), fun σ hσ => h.fix σ (hle hσ), hnorm⟩
  have h4 := h'.card_eq_four hI hN'
  have h4' := h.card_eq_four hI (fun hb => hN' (le_bot_iff.1 (hb ▸ hle)))
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem exists_ne (h : FourGroup I N) (hI : I.card = 4) (hN : N ≠ ⊥) (σ : Perm (Fin d)) :
    ∃ σ' ∈ N, σ' ≠ 1 ∧ σ' ≠ σ := by
  classical
  by_contra hall
  push Not at hall
  have hinj : Function.Injective (fun x : ↥N => decide ((x : Perm (Fin d)) = 1)) := by
    intro x y hxy
    simp only [decide_eq_decide] at hxy
    by_cases hx1 : (x : Perm (Fin d)) = 1
    · exact Subtype.ext (hx1.trans (hxy.1 hx1).symm)
    · have hy1 : (y : Perm (Fin d)) ≠ 1 := fun h' => hx1 (hxy.2 h')
      exact Subtype.ext ((hall x x.2 hx1).trans (hall y y.2 hy1).symm)
  have h2 : Nat.card ↥N ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2
  have := h.card_eq_four hI hN
  omega

theorem apart (h : FourGroup I N) (hI : I.card = 4) {σ σ' : Perm (Fin d)} (hσ : σ ∈ N)
    (hσ' : σ' ∈ N) (hne : σ ≠ σ') {a : Fin d} (ha : a ∈ I) : σ a ≠ σ' a := by
  intro hsa
  have hρ : σ'⁻¹ * σ ∈ N := N.mul_mem (N.inv_mem hσ') hσ
  have hρa : (σ'⁻¹ * σ) a = a := by
    rw [Perm.mul_apply, hsa, perm_inv_apply_self]
  by_cases hρ1 : σ'⁻¹ * σ = 1
  · exact hne (by simpa using (inv_mul_eq_one.1 hρ1).symm)
  · exact h.free hI hρ hρ1 a ha hρa

theorem pair_move (h : FourGroup I N) (hI : I.card = 4) {σ σ' : Perm (Fin d)} (hσ : σ ∈ N)
    (hσ1 : σ ≠ 1) (hσ' : σ' ∈ N) (hσ'1 : σ' ≠ 1) (hne : σ ≠ σ') {a : Fin d} (ha : a ∈ I) :
    coreAct d σ (pairVec a (σ' a)) ≠ pairVec a (σ' a) := by
  intro heq
  rw [coreAct_pairVec] at heq
  have hsa : σ a ≠ a := h.free hI hσ hσ1 a ha
  have hsa' : σ a ≠ σ' a := h.apart hI hσ hσ' hne ha
  have haa' : a ≠ σ' a := fun h' => h.free hI hσ' hσ'1 a ha h'.symm
  have h1 := congrArg (fun v => vcoord v (σ a)) heq
  simp only [vcoord_pairVec] at h1
  have hsσ : σ a ≠ σ (σ' a) := fun h' => haa' (σ.injective h')
  simp [hsa, hsa', hsσ] at h1

theorem transitive (h : FourGroup I N) (hI : I.card = 4) (hN : N ≠ ⊥) {a b : Fin d}
    (ha : a ∈ I) (hb : b ∈ I) : ∃ σ ∈ N, σ a = b := by
  classical
  have hpres : ∀ σ ∈ N, ∀ x, σ x ∈ I ↔ x ∈ I := fun σ hσ => mem_setStab.1 (h.stab hσ)
  let f : ↥N → ↥I := fun σ => ⟨(σ : Perm (Fin d)) a, (hpres σ σ.2 a).2 ha⟩
  have hf : Function.Injective f := by
    intro σ τ hστ
    by_contra hne
    have hne' : (σ : Perm (Fin d)) ≠ τ := fun h' => hne (Subtype.ext h')
    exact h.apart hI σ.2 τ.2 hne' ha (congrArg Subtype.val hστ)
  have hcard : Nat.card ↥I ≤ Nat.card ↥N := by
    rw [Nat.card_eq_fintype_card (α := ↥I), Fintype.card_coe, hI, h.card_eq_four hI hN]
  obtain ⟨σ, hσ⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨b, hb⟩
  exact ⟨σ, σ.2, congrArg Subtype.val hσ⟩

end FourGroup

end CFSG.CGT.PushingUpLit.SolK
