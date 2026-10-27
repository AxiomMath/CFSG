module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def fixF (σ : Perm Ω) : Finset Ω := Finset.univ.filter fun x => σ x = x

theorem mem_fixF {σ : Perm Ω} {x : Ω} : x ∈ fixF σ ↔ σ x = x := by simp [fixF]

@[expose] def IsDT (F : Finset Ω) (s : Perm Ω) : Prop :=
  (∀ x, x ∉ F → s x = x) ∧ s * s = 1 ∧ ∀ x, x ∈ F → s x ≠ x

theorem card_modEq_fixF {p : ℕ} (hp : p.Prime) {σ : Perm Ω} (h : σ ^ p = 1) :
    Fintype.card Ω ≡ (fixF σ).card [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : σ ^ p ^ 1 = 1 := by simpa using h
  have h2 := Equiv.Perm.card_compl_support_modEq h1
  have hset : fixF σ = σ.supportᶜ := by
    ext x
    simp [fixF, Equiv.Perm.mem_support]
  rw [hset]
  exact h2.symm

theorem card_fixF_modEq_inter {p : ℕ} (hp : p.Prime) {σ τ : Perm Ω} (hc : Commute σ τ)
    (h : τ ^ p = 1) : (fixF σ).card ≡ (fixF σ ∩ fixF τ).card [MOD p] := by
  have hcx : ∀ x, σ (τ x) = τ (σ x) := fun x => congrArg (fun f : Perm Ω => f x) hc.eq
  have hτ : ∀ x, x ∈ fixF σ ↔ τ x ∈ fixF σ := by
    intro x
    simp only [mem_fixF]
    constructor
    · intro hx
      rw [hcx, hx]
    · intro hx
      apply τ.injective
      rw [← hcx]
      exact hx
  let τ' : Perm ↥(fixF σ) := τ.subtypePerm (fun x => (hτ x).symm)
  have h' : τ' ^ p = 1 := by
    ext ⟨x, hx⟩
    have := congrArg (fun f : Perm Ω => f x) h
    simp only [Perm.coe_one, id_eq] at this
    have h2 : ((τ' ^ p) ⟨x, hx⟩ : Ω) = (τ ^ p) x := by
      rw [Perm.subtypePerm_pow]
      rfl
    simpa [h2] using this
  have h3 := card_modEq_fixF hp h'
  have h4 : (fixF τ').card = (fixF σ ∩ fixF τ).card := by
    have himg : (fixF τ').image (Subtype.val : ↥(fixF σ) → Ω) = fixF σ ∩ fixF τ := by
      ext y
      simp only [Finset.mem_image, mem_fixF, Finset.mem_inter]
      constructor
      · rintro ⟨⟨z, hz⟩, hz2, rfl⟩
        refine ⟨mem_fixF.1 hz, ?_⟩
        have : (τ' ⟨z, hz⟩ : Ω) = z := by rw [hz2]
        exact this
      · rintro ⟨hy1, hy2⟩
        refine ⟨⟨y, mem_fixF.2 hy1⟩, ?_, rfl⟩
        exact Subtype.ext hy2
    rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [h4, Fintype.card_coe] at h3
  exact h3

theorem commute_cycleOf (σ : Perm Ω) (y : Ω) : Commute (σ.cycleOf y) σ := by
  show σ.cycleOf y * σ = σ * σ.cycleOf y
  ext z
  simp only [Perm.mul_apply, Perm.cycleOf_apply, Perm.sameCycle_apply_right]
  split_ifs <;> rfl

theorem orderOf_cycleOf_eq {p : ℕ} (hp : p.Prime) {σ : Perm Ω} (hσ : σ ^ p = 1) {y : Ω}
    (hy : σ y ≠ y) : orderOf (σ.cycleOf y) = p := by
  have h1 : orderOf (σ.cycleOf y) ∣ orderOf σ := Perm.orderOf_cycleOf_dvd_orderOf σ y
  have h2 : orderOf σ ∣ p := orderOf_dvd_of_pow_eq_one hσ
  rcases (Nat.dvd_prime hp).1 (h1.trans h2) with h | h
  · exfalso
    have : σ.cycleOf y = 1 := orderOf_eq_one_iff.1 h
    exact hy ((Perm.cycleOf_eq_one_iff σ).1 this)
  · exact h

theorem sign_cycleOf_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : Perm Ω} (hσ : σ ^ p = 1)
    (y : Ω) : sign (σ.cycleOf y) = 1 := by
  by_cases hy : σ y = y
  · rw [(Perm.cycleOf_eq_one_iff σ).2 hy]
    simp
  · have hcyc := Perm.isCycle_cycleOf σ hy
    have hord := orderOf_cycleOf_eq hp hσ hy
    rw [hcyc.sign, ← hcyc.orderOf, hord]
    have : Odd p := hp.odd_of_ne_two hp2
    simp [this.neg_one_pow]

theorem pow_apply_eq_self_iff {p : ℕ} (hp : p.Prime) {σ : Perm Ω} (hσ : σ ^ p = 1) {x : Ω}
    (hx : σ x ≠ x) (k : ℕ) : (σ ^ k) x = x ↔ p ∣ k := by
  constructor
  · intro h
    have hc : (σ.cycleOf x).IsCycle := Perm.isCycle_cycleOf σ hx
    have h1 : ((σ.cycleOf x) ^ k) x = x := by rw [Perm.cycleOf_pow_apply_self]; exact h
    have h2 : (σ.cycleOf x) x ≠ x := by rw [Perm.cycleOf_apply_self]; exact hx
    have h3 : (σ.cycleOf x) ^ k = 1 := hc.pow_eq_one_iff.2 ⟨x, h2, h1⟩
    rw [← orderOf_cycleOf_eq hp hσ hx]
    exact orderOf_dvd_of_pow_eq_one h3
  · rintro ⟨m, rfl⟩
    rw [pow_mul, hσ, one_pow]
    rfl

theorem trivial_on_moved {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ g : Perm Ω} (hσ : σ ^ p = 1)
    (hgσ : Commute g σ) {e : ℕ} (hg : g ^ (2 ^ e) = 1)
    (hkey : ∀ y, ∃ k : ℕ, (g * σ.cycleOf y * g⁻¹ * (σ.cycleOf y)⁻¹) ^ (2 ^ k) = 1) :
    ∀ x, σ x ≠ x → g x = x := by
  intro x hx
  by_cases hsc : σ.SameCycle x (g x)
  ·
    obtain ⟨j, hj⟩ := hsc.exists_nat_pow_eq
    have hcomm : Commute g (σ ^ j) := hgσ.pow_right j
    set u : Perm Ω := (σ ^ j)⁻¹ * g with hu
    have hgu : g = σ ^ j * u := by rw [hu]; group
    have hux : u x = x := by
      rw [hu, Perm.mul_apply, ← hj]
      simp
    have hcommu : Commute (σ ^ j) u := by
      rw [hu]
      exact (Commute.refl (σ ^ j)).inv_right.mul_right hcomm.symm
    have hgpow : g ^ (2 ^ e) = σ ^ (j * 2 ^ e) * u ^ (2 ^ e) := by
      have : g ^ (2 ^ e) = (σ ^ j * u) ^ (2 ^ e) := by rw [← hgu]
      rw [this, hcommu.mul_pow, ← pow_mul]
    have hfix : (σ ^ (j * 2 ^ e)) x = x := by
      have h1 : (g ^ (2 ^ e)) x = x := by rw [hg]; rfl
      rw [hgpow, Perm.mul_apply, Perm.pow_apply_eq_self_of_apply_eq_self hux] at h1
      exact h1
    have hpd : p ∣ j * 2 ^ e := (pow_apply_eq_self_iff hp hσ hx _).1 hfix
    have hcop : Nat.Coprime p (2 ^ e) := by
      apply Nat.Coprime.pow_right
      exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
    have hpj : p ∣ j := hcop.dvd_of_dvd_mul_right hpd
    rw [← hj]
    exact (pow_apply_eq_self_iff hp hσ hx j).2 hpj
  · exfalso
    set c := σ.cycleOf x with hc
    have hord : orderOf c = p := orderOf_cycleOf_eq hp hσ hx
    set c₂ := g * c * g⁻¹ with hc₂
    have hdisj : Perm.Disjoint c₂ c := by
      rw [Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
      intro y hy2 hy1
      rw [hc₂, Perm.support_conj, Finset.mem_map_equiv] at hy2
      rw [hc, Perm.mem_support_cycleOf_iff] at hy1 hy2
      obtain ⟨i, hi⟩ := hy2.1.exists_nat_pow_eq
      have h1 : (σ ^ i) (g x) = y := by
        have := congrArg (fun f : Perm Ω => f x) (hgσ.pow_right i).eq
        simp only [Perm.mul_apply] at this
        rw [← this, hi]
        simp
      have hs2 : σ.SameCycle (g x) y := ⟨(i : ℤ), by rw [zpow_natCast]; exact h1⟩
      exact hsc (hy1.1.trans hs2.symm)
    obtain ⟨k, hk⟩ := hkey x
    have hcomm' : Commute c₂ c⁻¹ := hdisj.commute.inv_right
    have h1 : c₂ ^ (2 ^ k) * (c⁻¹) ^ (2 ^ k) = 1 := by
      rw [← hcomm'.mul_pow]
      exact hk
    have h2 : c₂ ^ (2 ^ k) = c ^ (2 ^ k) := by
      rw [inv_pow] at h1
      exact mul_inv_eq_one.1 h1
    have h3 : c ^ (2 ^ k) = 1 := by
      ext y
      by_contra hne
      have hy : y ∈ (c ^ (2 ^ k)).support := by simpa [Perm.mem_support] using hne
      have hyc : y ∈ c.support := Perm.support_pow_le c _ hy
      have hy' : y ∈ (c₂ ^ (2 ^ k)).support := by rw [h2]; exact hy
      have hyc2 : y ∈ c₂.support := Perm.support_pow_le c₂ _ hy'
      exact Finset.disjoint_left.1 (Perm.disjoint_iff_disjoint_support.1 hdisj) hyc2 hyc
    have hdvd : p ∣ 2 ^ k := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

instance (F : Finset Ω) (s : Perm Ω) : Decidable (IsDT F s) := by
  unfold IsDT
  infer_instance

theorem small_alt_elem : ∀ m : ℕ, m ≤ 4 → ∀ g : Perm (Fin m), sign g = 1 →
    (∃ k : Fin 5, g ^ (2 ^ (k : ℕ)) = 1) →
      g = 1 ∨ (m = 4 ∧ IsDT (Finset.univ : Finset (Fin m)) g) := by
  intro m hm
  interval_cases m <;> decide +kernel

theorem small_odd_elem : ∀ m : ℕ, 3 ≤ m → m ≤ 4 → ∀ g : Perm (Fin m), sign g = -1 →
    (∃ k : Fin 5, g ^ (2 ^ (k : ℕ)) = 1) →
      ∃ h : Perm (Fin m), (g * h * g⁻¹ * h⁻¹) ^ 3 = 1 ∧ g * h * g⁻¹ * h⁻¹ ≠ 1 := by
  intro m h3 h4
  interval_cases m <;> decide +kernel

theorem fin4_dt_conj : ∀ s s' : Perm (Fin 4), IsDT (Finset.univ : Finset (Fin 4)) s →
    IsDT (Finset.univ : Finset (Fin 4)) s' →
      ∃ h : Perm (Fin 4), sign h = 1 ∧ h * s * h⁻¹ = s' := by
  decide +kernel

theorem isDT_univ_permCongr {F G : Type*} [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]
    (e : F ≃ G) (g : Perm F) :
    IsDT (Finset.univ : Finset G) (e.permCongr g) ↔ IsDT (Finset.univ : Finset F) g := by
  have hφ : ∀ x, e.permCongrHom x = e.permCongr x := fun x =>
    congrFun (Equiv.permCongrHom_coe e) x
  unfold IsDT
  simp only [Finset.mem_univ, not_true_eq_false, false_imp_iff, implies_true, true_and,
    forall_const]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x hx => ?_⟩
    · apply e.permCongrHom.injective
      rw [map_mul, map_one, hφ]
      exact h1
    · apply h2 (e x)
      rw [Equiv.permCongr_apply]
      simp [hx]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun y hy => ?_⟩
    · rw [← hφ, ← map_mul, h1, map_one]
    · apply h2 (e.symm y)
      rw [Equiv.permCongr_apply] at hy
      apply e.injective
      simpa using hy

theorem two_pow_le_four {F : Type*} [Fintype F] [DecidableEq F] (hF : Fintype.card F ≤ 4)
    {g : Perm F} (hg : ∃ n : ℕ, g ^ (2 ^ n) = 1) :
    ∃ k : Fin 5, g ^ (2 ^ (k : ℕ)) = 1 := by
  obtain ⟨n, hn⟩ := hg
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
  have hdvd : orderOf g ∣ (Fintype.card F).factorial := by
    have := orderOf_dvd_natCard g
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm] at this
  have hle : (Fintype.card F).factorial ≤ 24 := by
    calc (Fintype.card F).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hF
      _ = 24 := by decide
  have h24 : 2 ^ j ≤ 24 := by
    rw [← hj]
    exact (Nat.le_of_dvd (Nat.factorial_pos _) hdvd).trans hle
  have hj4 : j < 5 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 5 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  refine ⟨⟨j, hj4⟩, ?_⟩
  rw [← hj]
  exact pow_orderOf_eq_one g

theorem eq_one_of_forall_commute {F : Type*} [Fintype F] [DecidableEq F]
    (h3 : 3 ≤ Fintype.card F) {g : Perm F} (h : ∀ h' : Perm F, g * h' = h' * g) : g = 1 := by
  ext x
  by_contra hx
  have hx' : g x ≠ x := hx
  have hcard : 1 < ((Finset.univ : Finset F).erase x).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 hcard
  have hyx : y ≠ x := (Finset.mem_erase.1 hy).1
  have hzx : z ≠ x := (Finset.mem_erase.1 hz).1
  have key : ∀ w : F, w ≠ x → g x = w := by
    intro w hw
    have h1 := congrArg (fun f : Perm F => f x) (h (swap x w))
    simp only [Perm.mul_apply, swap_apply_left] at h1
    by_contra hne
    have : swap x w (g x) = g x := swap_apply_of_ne_of_ne hx' hne
    rw [this] at h1
    exact hw (g.injective h1)
  exact hyz ((key y hyx).symm.trans (key z hzx))

theorem pcore_alt {F : Type*} [Fintype F] [DecidableEq F] {N : Subgroup (Perm F)}
    (hN : ∀ g ∈ N, ∃ n : ℕ, g ^ (2 ^ n) = 1) (hev : ∀ g ∈ N, sign g = 1)
    (hn : ∀ h : Perm F, sign h = 1 → ∀ g ∈ N, h * g * h⁻¹ ∈ N) :
    ∀ g ∈ N, g = 1 ∨ (Fintype.card F = 4 ∧ IsDT (Finset.univ : Finset F) g) := by
  intro g hg
  by_cases h5 : 5 ≤ Fintype.card F
  · left
    haveI : IsSimpleGroup (alternatingGroup F) :=
      alternatingGroup.isSimpleGroup (by simpa using h5)
    let M : Subgroup (alternatingGroup F) := N.subgroupOf (alternatingGroup F)
    haveI : M.Normal := ⟨fun n hn' a => by
      have hnN : (n : Perm F) ∈ N := hn'
      exact hn (a : Perm F) (Perm.mem_alternatingGroup.1 a.2) _ hnN⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hM | hM
    · have hgM : (⟨g, Perm.mem_alternatingGroup.2 (hev g hg)⟩ : alternatingGroup F) ∈ M := hg
      rw [hM] at hgM
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hgM)
    · exfalso
      obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 (by omega : 2 < Fintype.card F)
      have hc3 : (swap a c * swap a b).IsThreeCycle :=
        isThreeCycle_swap_mul_swap_same hac hab hbc.symm
      have hcM : (⟨swap a c * swap a b, hc3.mem_alternatingGroup⟩ : alternatingGroup F) ∈ M := by
        rw [hM]; trivial
      have hcN : (swap a c * swap a b : Perm F) ∈ N := hcM
      obtain ⟨k, hk⟩ := hN _ hcN
      have h3 := hc3.orderOf
      have hd : 3 ∣ 2 ^ k := h3 ▸ orderOf_dvd_of_pow_eq_one hk
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
      omega
  · push Not at h5
    have hm : Fintype.card F ≤ 4 := by omega
    let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
    let φ : Perm F ≃* Perm (Fin (Fintype.card F)) := e.permCongrHom
    have hφ : ∀ x, φ x = e.permCongr x := fun x => congrFun (Equiv.permCongrHom_coe e) x
    obtain ⟨k, hk⟩ := two_pow_le_four hm (hN g hg)
    have hk2 : (φ g) ^ (2 ^ (k : ℕ)) = 1 := by rw [← map_pow, hk, map_one]
    have hs : sign (φ g) = 1 := by rw [hφ, sign_permCongr]; exact hev g hg
    rcases small_alt_elem (Fintype.card F) hm (φ g) hs ⟨k, hk2⟩ with h | ⟨h4, hdt⟩
    · left
      exact φ.injective (by rw [h, map_one])
    · right
      refine ⟨h4, ?_⟩
      rw [hφ] at hdt
      exact (isDT_univ_permCongr e g).1 hdt

theorem pcore_perm {F : Type*} [Fintype F] [DecidableEq F] {N : Subgroup (Perm F)}
    (hN : ∀ g ∈ N, ∃ n : ℕ, g ^ (2 ^ n) = 1) (hn : ∀ h : Perm F, ∀ g ∈ N, h * g * h⁻¹ ∈ N) :
    ∀ g ∈ N, g = 1 ∨ Fintype.card F = 2 ∨
      (Fintype.card F = 4 ∧ IsDT (Finset.univ : Finset F) g) := by
  intro g hg
  by_cases h2 : Fintype.card F = 2
  · exact Or.inr (Or.inl h2)
  have hN0 : ∀ g ∈ (N ⊓ alternatingGroup F : Subgroup (Perm F)), ∃ n : ℕ, g ^ (2 ^ n) = 1 :=
    fun g hg => hN g (Subgroup.mem_inf.1 hg).1
  have hev0 : ∀ g ∈ (N ⊓ alternatingGroup F : Subgroup (Perm F)), sign g = 1 := fun g hg =>
    Perm.mem_alternatingGroup.1 (Subgroup.mem_inf.1 hg).2
  have hn0 : ∀ h : Perm F, sign h = 1 → ∀ g ∈ (N ⊓ alternatingGroup F : Subgroup (Perm F)),
      h * g * h⁻¹ ∈ (N ⊓ alternatingGroup F : Subgroup (Perm F)) := by
    intro h hh g hg
    obtain ⟨hgN, hgA⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hn h g hgN, ?_⟩
    rw [Perm.mem_alternatingGroup] at hgA ⊢
    simp [hh, hgA]
  have hge : sign g = 1 := by
    by_contra hodd
    have hodd' : sign g = -1 := by
      rcases Int.units_eq_one_or (sign g) with h | h
      · exact absurd h hodd
      · exact h
    have hcard3 : 3 ≤ Fintype.card F := by
      by_contra hlt
      push Not at hlt
      have hle : Fintype.card F ≤ 1 := by omega
      have : Subsingleton (Perm F) := by
        have : Subsingleton F := Fintype.card_le_one_iff_subsingleton.1 hle
        infer_instance
      apply hodd
      rw [Subsingleton.elim g 1]
      simp
    have hcomm_mem : ∀ h' : Perm F,
        g * (h' * g⁻¹ * h'⁻¹) ∈ (N ⊓ alternatingGroup F : Subgroup (Perm F)) := by
      intro h'
      refine Subgroup.mem_inf.2 ⟨N.mul_mem hg (hn h' g⁻¹ (N.inv_mem hg)), ?_⟩
      rw [Perm.mem_alternatingGroup]
      simp only [map_mul, map_inv]
      rcases Int.units_eq_one_or (sign g) with h | h <;>
        rcases Int.units_eq_one_or (sign h') with h' | h' <;> simp [h, h']
    by_cases h5 : 5 ≤ Fintype.card F
    · have hcomm : ∀ h' : Perm F, g * h' = h' * g := by
        intro h'
        rcases pcore_alt hN0 hev0 hn0 _ (hcomm_mem h') with h1 | ⟨h4, -⟩
        · calc g * h' = (g * (h' * g⁻¹ * h'⁻¹)) * (h' * g) := by group
            _ = h' * g := by rw [h1, one_mul]
        · omega
      have := eq_one_of_forall_commute hcard3 hcomm
      rw [this] at hodd'
      simp at hodd'
    · push Not at h5
      have hm : Fintype.card F ≤ 4 := by omega
      let e : F ≃ Fin (Fintype.card F) := Fintype.equivFin F
      let φ : Perm F ≃* Perm (Fin (Fintype.card F)) := e.permCongrHom
      have hφ : ∀ x, φ x = e.permCongr x := fun x => congrFun (Equiv.permCongrHom_coe e) x
      obtain ⟨k, hk⟩ := two_pow_le_four hm (hN g hg)
      have hk2 : (φ g) ^ (2 ^ (k : ℕ)) = 1 := by rw [← map_pow, hk, map_one]
      have hs : sign (φ g) = -1 := by rw [hφ, sign_permCongr]; exact hodd'
      obtain ⟨h', hh1, hh2⟩ := small_odd_elem (Fintype.card F) hcard3 hm (φ g) hs ⟨k, hk2⟩
      set h := φ.symm h' with hh
      have hconj : φ (g * h * g⁻¹ * h⁻¹) = (φ g * h' * (φ g)⁻¹ * h'⁻¹) := by
        simp [hh, map_mul, map_inv]
      have hc3 : (g * h * g⁻¹ * h⁻¹) ^ 3 = 1 := by
        apply φ.injective
        rw [map_pow, hconj, map_one]
        exact hh1
      have hc1 : g * h * g⁻¹ * h⁻¹ ≠ 1 := by
        intro hc
        apply hh2
        rw [← hconj, hc, map_one]
      have hcN : g * h * g⁻¹ * h⁻¹ ∈ N := by
        have : g * h * g⁻¹ * h⁻¹ = g * (h * g⁻¹ * h⁻¹) := by group
        rw [this]
        exact N.mul_mem hg (hn h g⁻¹ (N.inv_mem hg))
      obtain ⟨n, hn2⟩ := hN _ hcN
      have hd1 : orderOf (g * h * g⁻¹ * h⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
      have hd2 : orderOf (g * h * g⁻¹ * h⁻¹) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn2
      rcases (Nat.dvd_prime Nat.prime_three).1 hd1 with h1 | h1
      · exact hc1 (orderOf_eq_one_iff.1 h1)
      · rw [h1] at hd2
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd2
        omega
  have hgM : g ∈ (N ⊓ alternatingGroup F : Subgroup (Perm F)) :=
    Subgroup.mem_inf.2 ⟨hg, Perm.mem_alternatingGroup.2 hge⟩
  rcases pcore_alt hN0 hev0 hn0 g hgM with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem isDT_preserves {F : Finset Ω} {s : Perm Ω} (hs : IsDT F s) (x : Ω) :
    x ∈ F ↔ s x ∈ F := by
  obtain ⟨h1, h2, h3⟩ := hs
  constructor
  · intro hx
    by_contra hsx
    have h4 := h1 _ hsx
    have hss : s (s x) = x := by simpa using congrArg (fun f : Perm Ω => f x) h2
    rw [hss] at h4
    exact h3 x hx h4.symm
  · intro hsx
    by_contra hx
    have h4 := h1 x hx
    rw [h4] at hsx
    exact hx hsx

theorem isDT_of_ofSubtype {F : Finset Ω} {s' : Perm ↥F}
    (h : IsDT (Finset.univ : Finset ↥F) s') : IsDT F (Perm.ofSubtype s') := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨fun x hx => Perm.ofSubtype_apply_of_not_mem s' hx, ?_, fun x hx => ?_⟩
  · rw [← map_mul, h2, map_one]
  · rw [Perm.ofSubtype_apply_of_mem s' hx]
    intro hc
    apply h3 ⟨x, hx⟩ (Finset.mem_univ _)
    exact Subtype.ext hc

theorem exists_even_conj_of_isDT {F : Finset Ω} (hF : F.card = 4) {s s' : Perm Ω}
    (hs : IsDT F s) (hs' : IsDT F s') :
    ∃ h : Perm ↥F, sign h = 1 ∧ Perm.ofSubtype h * s * (Perm.ofSubtype h)⁻¹ = s' := by
  have hcard : Fintype.card ↥F = 4 := by rw [Fintype.card_coe]; exact hF
  let sr : Perm ↥F := s.subtypePerm (fun x => (isDT_preserves hs x).symm)
  let sr' : Perm ↥F := s'.subtypePerm (fun x => (isDT_preserves hs' x).symm)
  have hsr : s = Perm.ofSubtype sr :=
    (Perm.ofSubtype_subtypePerm _ (fun x hx => by
      by_contra hxF; exact hx (hs.1 x hxF))).symm
  have hsr' : s' = Perm.ofSubtype sr' :=
    (Perm.ofSubtype_subtypePerm _ (fun x hx => by
      by_contra hxF; exact hx (hs'.1 x hxF))).symm
  have hdt : IsDT (Finset.univ : Finset ↥F) sr := by
    refine ⟨fun x hx => absurd (Finset.mem_univ x) hx, ?_, fun x _ => ?_⟩
    · apply Perm.ofSubtype_injective
      rw [map_mul, map_one, ← hsr]
      exact hs.2.1
    · intro hx
      apply hs.2.2 x.1 x.2
      exact congrArg Subtype.val hx
  have hdt' : IsDT (Finset.univ : Finset ↥F) sr' := by
    refine ⟨fun x hx => absurd (Finset.mem_univ x) hx, ?_, fun x _ => ?_⟩
    · apply Perm.ofSubtype_injective
      rw [map_mul, map_one, ← hsr']
      exact hs'.2.1
    · intro hx
      apply hs'.2.2 x.1 x.2
      exact congrArg Subtype.val hx
  let e : ↥F ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let φ : Perm ↥F ≃* Perm (Fin 4) := e.permCongrHom
  have hφ : ∀ x, φ x = e.permCongr x := fun x => congrFun (Equiv.permCongrHom_coe e) x
  obtain ⟨h4, hh4, hh4eq⟩ := fin4_dt_conj (φ sr) (φ sr') (by rw [hφ]; exact (isDT_univ_permCongr e sr).2 hdt)
    (by rw [hφ]; exact (isDT_univ_permCongr e sr').2 hdt')
  refine ⟨φ.symm h4, ?_, ?_⟩
  · have : sign (φ (φ.symm h4)) = sign (φ.symm h4) := by rw [hφ, sign_permCongr]
    rw [← this, MulEquiv.apply_symm_apply]
    exact hh4
  · rw [hsr, hsr', ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hh4eq

theorem locA {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : Perm Ω} (hσ : σ ^ p = 1)
    {Sg : Subgroup (Perm Ω)} (hexp : ∀ s ∈ Sg, ∃ n : ℕ, s ^ (2 ^ n) = 1)
    (hC : ∀ s ∈ Sg, Commute s σ)
    (hN : ∀ c : Perm Ω, Commute c σ → sign c = 1 → ∀ s ∈ Sg, c * s * c⁻¹ ∈ Sg) :
    (∀ s ∈ Sg, (∀ x, σ x ≠ x → s x = x) ∧
        (s = 1 ∨ (fixF σ).card = 2 ∨ ((fixF σ).card = 4 ∧ IsDT (fixF σ) s))) ∧
      ((fixF σ).card = 4 → Sg ≠ ⊥ → ∀ s, IsDT (fixF σ) s → s ∈ Sg) := by
  have htriv : ∀ s ∈ Sg, ∀ x, σ x ≠ x → s x = x := by
    intro s hs x hx
    obtain ⟨n, hn⟩ := hexp s hs
    refine trivial_on_moved hp hp2 hσ (hC s hs) hn ?_ x hx
    intro y
    have hc1 := commute_cycleOf σ y
    have hc2 := sign_cycleOf_eq_one hp hp2 hσ y
    have h1 : σ.cycleOf y * s⁻¹ * (σ.cycleOf y)⁻¹ ∈ Sg := hN _ hc1 hc2 s⁻¹ (Sg.inv_mem hs)
    have hmem : s * σ.cycleOf y * s⁻¹ * (σ.cycleOf y)⁻¹ ∈ Sg := by
      have : s * σ.cycleOf y * s⁻¹ * (σ.cycleOf y)⁻¹ =
          s * (σ.cycleOf y * s⁻¹ * (σ.cycleOf y)⁻¹) := by group
      rw [this]
      exact Sg.mul_mem hs h1
    exact hexp _ hmem
  have hmem_comm : ∀ s : Perm Ω, Commute s σ → ∀ x, x ∈ fixF σ ↔ s x ∈ fixF σ := by
    intro s hs x
    simp only [mem_fixF]
    have hcx : s (σ x) = σ (s x) := congrArg (fun f : Perm Ω => f x) hs.eq
    constructor
    · intro hx
      rw [← hcx, hx]
    · intro hx
      apply s.injective
      rw [hcx, hx]
  have hofc : ∀ h : Perm ↥(fixF σ), Commute (Perm.ofSubtype h) σ := by
    intro h
    show Perm.ofSubtype h * σ = σ * Perm.ofSubtype h
    ext x
    simp only [Perm.mul_apply]
    by_cases hx : x ∈ fixF σ
    · have hσx : σ x = x := mem_fixF.1 hx
      rw [hσx]
      have : Perm.ofSubtype h x ∈ fixF σ := by
        rw [Perm.ofSubtype_apply_of_mem h hx]
        exact (h ⟨x, hx⟩).2
      exact (mem_fixF.1 this).symm
    · have hσx : σ x ∉ fixF σ := fun hh => hx (by
        have h1 := mem_fixF.1 hh
        exact mem_fixF.2 (σ.injective h1))
      rw [Perm.ofSubtype_apply_of_not_mem h hx, Perm.ofSubtype_apply_of_not_mem h hσx]
  let N' : Subgroup (Perm ↥(fixF σ)) := Sg.comap (Perm.ofSubtype : Perm ↥(fixF σ) →* Perm Ω)
  have hres : ∀ s ∈ Sg, ∃ s' : Perm ↥(fixF σ), Perm.ofSubtype s' = s ∧ s' ∈ N' := by
    intro s hs
    refine ⟨s.subtypePerm (fun x => (hmem_comm s (hC s hs) x).symm), ?_, ?_⟩
    · refine Perm.ofSubtype_subtypePerm _ (fun x hx => ?_)
      by_contra hxF
      exact hx (htriv s hs x (fun hh => hxF (mem_fixF.2 hh)))
    · show Perm.ofSubtype (s.subtypePerm _) ∈ Sg
      rw [Perm.ofSubtype_subtypePerm _ (fun x hx => by
        by_contra hxF
        exact hx (htriv s hs x (fun hh => hxF (mem_fixF.2 hh))))]
      exact hs
  have hN'exp : ∀ g ∈ N', ∃ n : ℕ, g ^ (2 ^ n) = 1 := by
    intro g hg
    obtain ⟨n, hn⟩ := hexp (Perm.ofSubtype g) hg
    refine ⟨n, Perm.ofSubtype_injective ?_⟩
    rw [map_pow, hn, map_one]
  have hcardF : Fintype.card ↥(fixF σ) = (fixF σ).card := Fintype.card_coe _
  have part1 : ∀ s ∈ Sg, (∀ x, σ x ≠ x → s x = x) ∧
        (s = 1 ∨ (fixF σ).card = 2 ∨ ((fixF σ).card = 4 ∧ IsDT (fixF σ) s)) := by
    intro s hs
    refine ⟨htriv s hs, ?_⟩
    obtain ⟨s', hs'eq, hs'N⟩ := hres s hs
    by_cases hodd : ∃ s₀ ∈ Sg, sign s₀ = -1
    · obtain ⟨s₀, hs₀, hs₀sign⟩ := hodd
      have hnorm : ∀ h : Perm ↥(fixF σ), ∀ g ∈ N', h * g * h⁻¹ ∈ N' := by
        intro h g hg
        show Perm.ofSubtype (h * g * h⁻¹) ∈ Sg
        rw [map_mul, map_mul, map_inv]
        have hg' : Perm.ofSubtype g ∈ Sg := hg
        have hĥc : Commute (Perm.ofSubtype h) σ := hofc h
        rcases Int.units_eq_one_or (sign (Perm.ofSubtype h)) with hs1 | hs1
        · exact hN _ hĥc hs1 _ hg'
        · have hc : Commute (Perm.ofSubtype h * s₀) σ := hĥc.mul_left (hC s₀ hs₀)
          have hsc : sign (Perm.ofSubtype h * s₀) = 1 := by
            rw [map_mul, hs1, hs₀sign]
            rfl
          have h1 : s₀⁻¹ * Perm.ofSubtype g * s₀ ∈ Sg :=
            Sg.mul_mem (Sg.mul_mem (Sg.inv_mem hs₀) hg') hs₀
          have h2' := hN _ hc hsc _ h1
          have : Perm.ofSubtype h * Perm.ofSubtype g * (Perm.ofSubtype h)⁻¹ =
              (Perm.ofSubtype h * s₀) * (s₀⁻¹ * Perm.ofSubtype g * s₀) *
                (Perm.ofSubtype h * s₀)⁻¹ := by group
          rw [this]
          exact h2'
      rcases pcore_perm hN'exp hnorm s' hs'N with h | h | ⟨h4, hdt⟩
      · left
        rw [← hs'eq, h, map_one]
      · right; left
        rw [← hcardF]; exact h
      · right; right
        refine ⟨by rw [← hcardF]; exact h4, ?_⟩
        rw [← hs'eq]
        exact isDT_of_ofSubtype hdt
    · push Not at hodd
      have hev : ∀ g ∈ N', sign g = 1 := by
        intro g hg
        have hg' : Perm.ofSubtype g ∈ Sg := hg
        have h1 := hodd _ hg'
        rw [Perm.sign_ofSubtype] at h1
        rcases Int.units_eq_one_or (sign g) with h | h
        · exact h
        · exact absurd h h1
      have hnorm : ∀ h : Perm ↥(fixF σ), sign h = 1 → ∀ g ∈ N', h * g * h⁻¹ ∈ N' := by
        intro h hh g hg
        show Perm.ofSubtype (h * g * h⁻¹) ∈ Sg
        rw [map_mul, map_mul, map_inv]
        have hg' : Perm.ofSubtype g ∈ Sg := hg
        exact hN _ (hofc h) (by rw [Perm.sign_ofSubtype]; exact hh) _ hg'
      rcases pcore_alt hN'exp hev hnorm s' hs'N with h | ⟨h4, hdt⟩
      · left
        rw [← hs'eq, h, map_one]
      · right; right
        refine ⟨by rw [← hcardF]; exact h4, ?_⟩
        rw [← hs'eq]
        exact isDT_of_ofSubtype hdt
  refine ⟨part1, ?_⟩
  intro hc4 hne s hs
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have haS : (a : Perm Ω) ∈ Sg := a.2
  have ha1' : (a : Perm Ω) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hdt1 : IsDT (fixF σ) (a : Perm Ω) := by
    rcases (part1 a haS).2 with h | h | ⟨-, h⟩
    · exact absurd h ha1'
    · omega
    · exact h
  obtain ⟨h, hsh, hh⟩ := exists_even_conj_of_isDT hc4 hdt1 hs
  rw [← hh]
  exact hN _ (hofc h) (by rw [Perm.sign_ofSubtype]; exact hsh) _ haS

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
