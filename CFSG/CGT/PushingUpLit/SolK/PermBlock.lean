module

public import CFSG.CGT.PushingUpLit.BHS.SymNatOrbitsAlt

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

variable {d : ℕ}

theorem cyc_mem_altOn_of_mem {B : Finset (Fin d)} {i j k : Fin d} (hi : i ∈ B) (hj : j ∈ B)
    (hk : k ∈ B) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : cyc i j k ∈ altOn B := by
  rw [mem_altOn]
  refine ⟨fun m hm => cyc_apply_of_ne ?_ ?_ ?_, (cyc_isThreeCycle hij hik hjk).sign⟩ <;>
    rintro rfl <;> contradiction

theorem apply_eq_of_pow_odd {σ : Perm (Fin d)} (h2 : ∃ j : ℕ, σ ^ (2 ^ j) = 1) {m : ℕ}
    (hm : Odd m) {x : Fin d} (hx : (σ ^ m) x = x) : σ x = x := by
  obtain ⟨j, hj⟩ := h2
  have hord : orderOf σ ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hcop : m.Coprime (orderOf σ) := by
    rw [hi]
    exact (Nat.coprime_two_right.2 hm).pow_right i
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  have h1 : ((σ ^ m) ^ t) x = x := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hx t
  rwa [ht] at h1

variable {N : Subgroup (Perm (Fin d))}

theorem exists_pow_two_pow_eq_one (hN2 : IsPGroup 2 N) {σ : Perm (Fin d)} (hσ : σ ∈ N) :
    ∃ j : ℕ, σ ^ (2 ^ j) = 1 := by
  obtain ⟨j, hj⟩ := hN2 ⟨σ, hσ⟩
  exact ⟨j, by simpa using congrArg Subtype.val hj⟩

theorem eq_one_of_mem_altOn {B : Finset (Fin d)} (hN2 : IsPGroup 2 N)
    (hnorm : ∀ τ ∈ altOn B, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) (hB : 5 ≤ B.card ∨ B.card = 3)
    {σ : Perm (Fin d)} (hσN : σ ∈ N) (hσA : σ ∈ altOn B) : σ = 1 := by
  classical
  rcases hB with h5 | h3
  ·
    have hA : IsSimpleGroup ↥(alternatingGroup ↥B) :=
      alternatingGroup.isSimpleGroup (by simpa using h5)
    have hsimple : IsSimpleGroup ↥(altOn B) :=
      (MulEquiv.isSimpleGroup_congr (Subgroup.equivMapOfInjective (alternatingGroup ↥B)
        (Perm.ofSubtype : Perm ↥B →* Perm (Fin d)) Perm.ofSubtype_injective)).1 hA
    have hKnormal : (N.subgroupOf (altOn B)).Normal := ⟨fun k hk g => by
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      exact hnorm g g.2 _ hk⟩
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf (altOn B)) with hbot | htop
    · have : (⟨σ, hσA⟩ : ↥(altOn B)) ∈ N.subgroupOf (altOn B) := hσN
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      obtain ⟨x, y, z, hxB, hyB, hzB, hxy, hxz, hyz⟩ :=
        Finset.two_lt_card_iff.1 (by omega : 2 < B.card)
      have hτA : cyc x y z ∈ altOn B := cyc_mem_altOn_of_mem hxB hyB hzB hxy hxz hyz
      have hτN : cyc x y z ∈ N := by
        have : (⟨cyc x y z, hτA⟩ : ↥(altOn B)) ∈ N.subgroupOf (altOn B) :=
          htop ▸ Subgroup.mem_top _
        exact this
      obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one hN2 hτN
      have h3 : orderOf (cyc x y z) = 3 := (cyc_isThreeCycle hxy hxz hyz).orderOf
      have hd : 3 ∣ 2 ^ j := h3 ▸ orderOf_dvd_of_pow_eq_one hj
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hd
      omega
  · have hcard : Nat.card (altOn B) = 3 := by
      rw [card_altOn (by omega), h3]
      decide
    have hdvd : orderOf σ ∣ 3 := by
      have := orderOf_dvd_natCard (⟨σ, hσA⟩ : ↥(altOn B))
      rwa [Subgroup.orderOf_mk, hcard] at this
    obtain ⟨j, hj⟩ := exists_pow_two_pow_eq_one hN2 hσN
    have hdvd2 : orderOf σ ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
    have h1 : orderOf σ ∣ Nat.gcd 3 (2 ^ j) := Nat.dvd_gcd hdvd hdvd2
    have hcop : Nat.gcd 3 (2 ^ j) = 1 :=
      (Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2))
    rw [hcop] at h1
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)


theorem commute_altOn {B : Finset (Fin d)} (hN2 : IsPGroup 2 N) (hNB : N ≤ setStab B)
    (hnorm : ∀ τ ∈ altOn B, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N) (hB : 5 ≤ B.card ∨ B.card = 3)
    {σ τ : Perm (Fin d)} (hσ : σ ∈ N) (hτ : τ ∈ altOn B) : σ * τ = τ * σ := by
  have hnormalizer := setStab_le_normalizer_altOn B (hNB hσ)
  have h1 : σ * τ * σ⁻¹ ∈ altOn B := (Subgroup.mem_normalizer_iff.1 hnormalizer τ).1 hτ
  have h2 : σ * τ * σ⁻¹ * τ⁻¹ ∈ altOn B := Subgroup.mul_mem _ h1 ((altOn B).inv_mem hτ)
  have h3 : σ * τ * σ⁻¹ * τ⁻¹ ∈ N := by
    have := Subgroup.mul_mem N hσ (hnorm τ hτ σ⁻¹ (N.inv_mem hσ))
    simpa [mul_assoc] using this
  have h4 := eq_one_of_mem_altOn hN2 hnorm hB h3 h2
  have h5 : σ * τ * σ⁻¹ = τ := mul_inv_eq_one.1 h4
  calc σ * τ = σ * τ * σ⁻¹ * σ := by group
    _ = τ * σ := by rw [h5]

theorem fixes_of_commute {B : Finset (Fin d)} (hB : 5 ≤ B.card ∨ B.card = 3)
    {σ : Perm (Fin d)} (h2 : ∃ j : ℕ, σ ^ (2 ^ j) = 1) (hσB : ∀ a, σ a ∈ B ↔ a ∈ B)
    (hc : ∀ τ ∈ altOn B, σ * τ = τ * σ) : ∀ a ∈ B, σ a = a := by
  classical
  have key : ∀ {x y z : Fin d}, x ∈ B → y ∈ B → z ∈ B → x ≠ y → x ≠ z → y ≠ z →
      σ x = x ∨ σ x = y ∨ σ x = z := by
    intro x y z hx hy hz hxy hxz hyz
    have hcomm := hc _ (cyc_mem_altOn_of_mem hx hy hz hxy hxz hyz)
    have h1 : σ z = cyc x y z (σ x) := by
      have := congrArg (fun f : Perm (Fin d) => f x) hcomm
      simpa [Perm.mul_apply, cyc_apply_first hxz hyz] using this
    by_contra hne
    simp only [not_or] at hne
    have h2 : cyc x y z (σ x) = σ x := cyc_apply_of_ne hne.1 hne.2.1 hne.2.2
    rw [h2] at h1
    exact hxz (σ.injective h1).symm
  rcases hB with h5 | h3
  · intro a ha
    by_contra hne
    have haB : σ a ∈ B := (hσB a).2 ha
    have hcard : 1 < ((B.erase a).erase (σ a)).card := by
      have h1 := Finset.pred_card_le_card_erase (s := B.erase a) (a := σ a)
      have h2 := Finset.pred_card_le_card_erase (s := B) (a := a)
      omega
    obtain ⟨b, hb, c, hc', hbc⟩ := Finset.one_lt_card.1 hcard
    simp only [Finset.mem_erase] at hb hc'
    rcases key ha hb.2.2 hc'.2.2 (Ne.symm hb.2.1) (Ne.symm hc'.2.1) hbc with h | h | h
    · exact hne h
    · exact hb.1 h.symm
    · exact hc'.1 h.symm
  · obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 h3
    have hx : x ∈ ({x, y, z} : Finset (Fin d)) := by simp
    have hy : y ∈ ({x, y, z} : Finset (Fin d)) := by simp
    have hz : z ∈ ({x, y, z} : Finset (Fin d)) := by simp
    have hcomm := hc _ (cyc_mem_altOn_of_mem hx hy hz hxy hxz hyz)
    have hτx : cyc x y z x = z := cyc_apply_first hxz hyz
    have hτy : cyc x y z y = x := cyc_apply_second hxy hyz
    have hτz : cyc x y z z = y := cyc_apply_third x y z
    have hsx : σ x = x := by
      rcases key hx hy hz hxy hxz hyz with h | h | h
      · exact h
      · exfalso
        have e1 : σ z = x := by
          have := congrArg (fun f : Perm (Fin d) => f x) hcomm
          simpa [Perm.mul_apply, hτx, h, hτy] using this
        have e2 : σ y = z := by
          have := congrArg (fun f : Perm (Fin d) => f z) hcomm
          simpa [Perm.mul_apply, hτz, e1, hτx] using this
        have e3 : (σ ^ 3) x = x := by
          simp [pow_succ, Perm.mul_apply, h, e2, e1]
        exact hxy (h.symm.trans (apply_eq_of_pow_odd h2 (by decide) e3)).symm
      · exfalso
        have e1 : σ z = y := by
          have := congrArg (fun f : Perm (Fin d) => f x) hcomm
          simpa [Perm.mul_apply, hτx, h, hτz] using this
        have e2 : σ y = x := by
          have := congrArg (fun f : Perm (Fin d) => f z) hcomm
          simpa [Perm.mul_apply, hτz, e1, hτy] using this
        have e3 : (σ ^ 3) x = x := by
          simp [pow_succ, Perm.mul_apply, h, e2, e1]
        exact hxz (h.symm.trans (apply_eq_of_pow_odd h2 (by decide) e3)).symm
    have hsz : σ z = z := by
      have := congrArg (fun f : Perm (Fin d) => f x) hcomm
      simpa [Perm.mul_apply, hτx, hsx] using this
    have hsy : σ y = y := by
      have := congrArg (fun f : Perm (Fin d) => f z) hcomm
      simpa [Perm.mul_apply, hτz, hsz] using this
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hsx
    · exact hsy
    · exact hsz

theorem block_fixes {B : Finset (Fin d)} (hN2 : IsPGroup 2 N) (hNB : N ≤ setStab B)
    (hnorm : ∀ τ ∈ altOn B, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (hB : B.card ≤ 1 ∨ B.card = 3 ∨ 5 ≤ B.card) : ∀ σ ∈ N, ∀ a ∈ B, σ a = a := by
  intro σ hσ a ha
  rcases hB with h1 | h3 | h5
  · exact Finset.card_le_one.1 h1 _ ((mem_setStab.1 (hNB hσ) a).2 ha) _ ha
  · exact fixes_of_commute (Or.inr h3) (exists_pow_two_pow_eq_one hN2 hσ)
      (fun x => mem_setStab.1 (hNB hσ) x)
      (fun τ hτ => commute_altOn hN2 hNB hnorm (Or.inr h3) hσ hτ) a ha
  · exact fixes_of_commute (Or.inl h5) (exists_pow_two_pow_eq_one hN2 hσ)
      (fun x => mem_setStab.1 (hNB hσ) x)
      (fun τ hτ => commute_altOn hN2 hNB hnorm (Or.inl h5) hσ hτ) a ha

theorem eq_bot_of_blocks {I : Finset (Fin d)} (hN2 : IsPGroup 2 N) (hNI : N ≤ setStab I)
    (hA : ∀ τ ∈ altOn I, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (hA' : ∀ τ ∈ altOn Iᶜ, ∀ σ ∈ N, τ * σ * τ⁻¹ ∈ N)
    (hI : I.card ≤ 1 ∨ I.card = 3 ∨ 5 ≤ I.card)
    (hI' : Iᶜ.card ≤ 1 ∨ Iᶜ.card = 3 ∨ 5 ≤ Iᶜ.card) : N = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  have hNI' : N ≤ setStab Iᶜ := fun σ hσ x => by
    have := mem_setStab.1 (hNI hσ) x
    simp [this]
  have h1 := block_fixes hN2 hNI hA hI σ hσ
  have h2 := block_fixes hN2 hNI' hA' hI' σ hσ
  rw [Subgroup.mem_bot]
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ I
  · exact h1 x hx
  · exact h2 x (Finset.mem_compl.2 hx)

end CFSG.CGT.PushingUpLit.SolK
