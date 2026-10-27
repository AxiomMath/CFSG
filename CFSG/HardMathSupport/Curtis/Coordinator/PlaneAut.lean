module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

@[expose] def NonabCent {G : Type*} [Group G] (g : G) : Prop :=
  ∃ a b : G, a * g = g * a ∧ b * g = g * b ∧ a * b ≠ b * a

theorem NonabCent.map {G : Type*} [Group G] {g : G} (h : NonabCent g) (α : MulAut G) :
    NonabCent (α g) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  refine ⟨α a, α b, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ha]
  · rw [← map_mul, ← map_mul, hb]
  · intro h'
    rw [← map_mul, ← map_mul] at h'
    exact hab (α.injective h')

section Lines

variable {G : Type*} [Group G] {p : ℕ}

theorem exists_mul_of_card {E A B : Subgroup G} [Finite E] (hA : A ≤ E) (hB : B ≤ E)
    (hAB : ∀ g, g ∈ A → g ∈ B → g = 1) (hE : Nat.card E = Nat.card A * Nat.card B) :
    ∀ e ∈ E, ∃ a ∈ A, ∃ b ∈ B, e = a * b := by
  let F : ↥A × ↥B → ↥E := fun x => ⟨(x.1 : G) * x.2, E.mul_mem (hA x.1.2) (hB x.2.2)⟩
  have hFinj : Function.Injective F := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have h1 : a * b = a' * b' := congrArg Subtype.val h
    have h2 : a'⁻¹ * a = b' * b⁻¹ :=
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have h3 : a'⁻¹ * a = 1 := hAB _ (A.mul_mem (A.inv_mem ha') ha) (h2 ▸ B.mul_mem hb' (B.inv_mem hb))
    have h4 : a = a' := (inv_mul_eq_one.mp h3).symm
    have h5 : b' * b⁻¹ = 1 := h2 ▸ h3
    have h6 : b = b' := (mul_inv_eq_one.mp h5).symm
    subst h4; subst h6; rfl
  have hbij : Function.Bijective F := by
    refine hFinj.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, ← hE]
  intro e he
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 ⟨e, he⟩
  exact ⟨a, a.2, b, b.2, congrArg Subtype.val hab.symm⟩

theorem eq_zpowers_of_card_prime (hp : p.Prime) {H : Subgroup G} (hH : Nat.card H = p) {g : G}
    (hg : g ∈ H) (hg1 : g ≠ 1) : H = Subgroup.zpowers g := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; exact hp.ne_zero)
  have hgp : (⟨g, hg⟩ : H) ^ p = 1 := by
    have := pow_card_eq_one' (G := H) (x := ⟨g, hg⟩)
    rwa [hH] at this
  have hord : orderOf g = p := orderOf_eq_prime (by simpa using congrArg Subtype.val hgp) hg1
  have hz : Subgroup.zpowers g ≤ H := by rw [Subgroup.zpowers_le]; exact hg
  have hzc : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hord]
  exact (Subgroup.eq_of_le_of_card_ge hz (by rw [hzc, hH])).symm

theorem exists_ne_one_of_card_prime (hp : p.Prime) {H : Subgroup G} (hH : Nat.card H = p) :
    ∃ g ∈ H, g ≠ 1 := by
  by_contra hno
  push Not at hno
  have hbot : H = ⊥ := (Subgroup.eq_bot_iff_forall H).mpr hno
  rw [hbot, Subgroup.card_bot] at hH
  exact hp.one_lt.ne hH

theorem coprime_six_pow (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℕ) : Nat.Coprime 6 (p ^ k) := by
  refine Nat.Coprime.pow_right _ ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  have h56 : p = 5 ∨ p = 6 := by omega
  rcases h56 with rfl | rfl
  · exact absurd h (by norm_num)
  · exact absurd (hp.eq_one_or_self_of_dvd 2 (by norm_num)) (by omega)

theorem aut_eq_of_three_lines (hp : p.Prime) (hp5 : 5 ≤ p) (α : MulAut G) {k : ℕ}
    (hα : α ^ p ^ k = 1) (E : Subgroup G) (ℓ : Fin 3 → Subgroup G)
    (hcard : ∀ i, Nat.card (ℓ i) = p) (hle : ∀ i, ℓ i ≤ E)
    (hdisj : ∀ i j, i ≠ j → ∀ g, g ∈ ℓ i → g ∈ ℓ j → g = 1)
    (hnon : ∀ i, ∀ g ∈ ℓ i, g ≠ 1 → NonabCent g)
    (hcover : ∀ g ∈ E, g ≠ 1 → NonabCent g → ∃ i, g ∈ ℓ i)
    (hE : ∀ e ∈ E, α e ∈ E) (hEcard : Nat.card E = p ^ 2) :
    ∀ e ∈ E, α e = e := by
  have hp1 : p ≠ 1 := hp.ne_one
  have : Fact p.Prime := ⟨hp⟩
  choose g hgmem hg1 using fun i => exists_ne_one_of_card_prime hp (hcard i)
  have hz : ∀ i, ℓ i = Subgroup.zpowers (g i) := fun i =>
    eq_zpowers_of_card_prime hp (hcard i) (hgmem i) (hg1 i)
  have himg : ∀ i, ∃ j, α (g i) ∈ ℓ j := fun i => by
    have h1 : α (g i) ≠ 1 := fun h => hg1 i (α.injective (by rw [h, map_one]))
    exact hcover _ (hE _ (hle i (hgmem i))) h1 ((hnon i _ (hgmem i) (hg1 i)).map α)
  choose f hf using himg
  have hmap : ∀ i, ∀ x ∈ ℓ i, α x ∈ ℓ (f i) := by
    intro i x hx
    rw [hz i, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (hf i) n
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h1 : α (g j) ∈ Subgroup.zpowers (α (g i)) := by
      have hne1 : α (g i) ≠ 1 := fun h => hg1 i (α.injective (by rw [h, map_one]))
      have := eq_zpowers_of_card_prime hp (hcard (f i)) (hf i) hne1
      rw [← this, hij]
      exact hmap j _ (hgmem j)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← map_zpow] at hn
    have hgj : g j = g i ^ n := α.injective hn.symm
    have hmem : g j ∈ ℓ i := by
      rw [hgj, hz i]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
    exact hg1 j (hdisj i j (Ne.symm (fun h => hne h.symm)) _ hmem (hgmem j))
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ i, σ i = f i := fun i => rfl
  have hiter : ∀ m : ℕ, ∀ i, (α ^ m) (g i) ∈ ℓ ((σ ^ m) i) := by
    intro m
    induction m with
    | zero => intro i; simpa using hgmem i
    | succ m ih =>
      intro i
      rw [pow_succ' α m, MulAut.mul_apply, pow_succ' σ m, Equiv.Perm.mul_apply, hσ]
      exact hmap _ _ (ih i)
  have hσk : σ ^ p ^ k = 1 := by
    refine Equiv.ext fun i => ?_
    by_contra hne
    have h1 := hiter (p ^ k) i
    rw [hα, MulAut.one_apply] at h1
    exact hg1 i (hdisj i ((σ ^ p ^ k) i) (Ne.symm (by simpa using hne)) _ (hgmem i) h1)
  have hσ1 : σ = 1 := by
    have h6 : orderOf σ ∣ 6 := by
      have := orderOf_dvd_card (G := Equiv.Perm (Fin 3)) (x := σ)
      simpa [Fintype.card_perm, Nat.factorial] using this
    have hk : orderOf σ ∣ p ^ k := orderOf_dvd_of_pow_eq_one hσk
    have h1 : orderOf σ ∣ Nat.gcd 6 (p ^ k) := Nat.dvd_gcd h6 hk
    rw [(coprime_six_pow hp hp5 k).gcd_eq_one] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hfi : ∀ i, f i = i := fun i => by
    have := congrArg (fun s : Equiv.Perm (Fin 3) => s i) hσ1
    simpa [hσ] using this
  have hfix : ∀ i, α (g i) = g i := by
    intro i
    have hmem : α (g i) ∈ ℓ i := by simpa [hfi] using hf i
    rw [hz i, Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hord : orderOf (g i) = p := by
      have := hcard i
      have hgp : (⟨g i, hgmem i⟩ : ℓ i) ^ p = 1 := by
        have := pow_card_eq_one' (G := ℓ i) (x := ⟨g i, hgmem i⟩)
        rwa [hcard i] at this
      exact orderOf_eq_prime (by simpa using congrArg Subtype.val hgp) (hg1 i)
    have hpow : ∀ j : ℕ, (α ^ j) (g i) = g i ^ (n ^ j) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_zpow, ← hn, ← zpow_mul, pow_succ]
        ring_nf
    have h1 := hpow (p ^ k)
    rw [hα, MulAut.one_apply] at h1
    have h2 : (p : ℤ) ∣ n ^ p ^ k - 1 := by
      have h2' : (orderOf (g i) : ℤ) ∣ n ^ p ^ k - 1 := by
        rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub_one, ← h1, mul_inv_cancel]
      rwa [hord] at h2'
    have h3 : ((n ^ p ^ k - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h2
    have h4 : (n : ZMod p) = 1 := by
      have h5 : (n : ZMod p) ^ p ^ k = 1 := by
        rw [Int.cast_sub, Int.cast_pow, Int.cast_one, sub_eq_zero] at h3
        exact h3
      rwa [ZMod.pow_card_pow] at h5
    have h6 : (p : ℤ) ∣ n - 1 := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 ?_
      rw [Int.cast_sub, h4, Int.cast_one, sub_self]
    have h7 : g i ^ (n - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hord]; exact h6
    rw [zpow_sub_one, mul_inv_eq_one] at h7
    rw [← hn, h7]
  have hfinE : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; positivity)
  have hgen := exists_mul_of_card (E := E) (A := ℓ 0) (B := ℓ 1) (hle 0) (hle 1)
    (hdisj 0 1 (by decide)) (by rw [hEcard, hcard, hcard, sq])
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := hgen e he
  have hfixl : ∀ i, ∀ x ∈ ℓ i, α x = x := by
    intro i x hx
    rw [hz i, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [map_zpow, hfix i]
  rw [map_mul, hfixl 0 a ha, hfixl 1 b hb]

end Lines

end CFSG.HardMathSupport.Curtis.Coordinator.Plane
