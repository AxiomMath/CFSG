module

public import CFSG.CGT.PushingUpLit.BHS6.SixEightTri
public import CFSG.CGT.PushingUpLit.BHS6.SixEightPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS
open scoped Pointwise

section Three

theorem perm_three_eq_top {H : Subgroup (Equiv.Perm (Fin 3))} {a b : Equiv.Perm (Fin 3)}
    (ha : a ∈ H) (hb : b ∈ H) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    H = ⊤ := by
  have hoa : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have h2 : 2 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨a, ha⟩ : H)
    rwa [Subgroup.orderOf_mk, hoa] at this
  have h3 : 3 ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨b, hb⟩ : H)
    rwa [Subgroup.orderOf_mk, hob] at this
  have h6 : 6 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  have hG : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hle : Nat.card H ≤ 6 := hG ▸ Subgroup.card_le_card_group H
  have hpos : 0 < Nat.card H := Nat.card_pos
  have : Nat.card H = 6 := by omega
  exact (Subgroup.card_eq_iff_eq_top H).1 (this.trans hG.symm)

theorem exists_noncommute_perm_three (σ : Equiv.Perm (Fin 3)) (hσ : σ ≠ 1) :
    ∃ ρ : Equiv.Perm (Fin 3), ρ * σ * ρ⁻¹ ≠ σ := by
  revert σ
  decide

theorem eq_bot_of_normal_isPGroup_perm_three {N : Subgroup (Equiv.Perm (Fin 3))} (hN : N.Normal)
    (h2 : IsPGroup 2 ↥N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra hne
  obtain ⟨ρ, hρ⟩ := exists_noncommute_perm_three σ hne
  have hτ : ρ * σ * ρ⁻¹ ∈ N := hN.conj_mem σ hσ ρ
  have h1τ : ρ * σ * ρ⁻¹ ≠ 1 := by
    intro h
    apply hne
    have : σ = ρ⁻¹ * (ρ * σ * ρ⁻¹) * ρ := by group
    rw [this, h]
    group
  let f : Fin 3 → ↥N := ![⟨1, N.one_mem⟩, ⟨σ, hσ⟩, ⟨ρ * σ * ρ⁻¹, hτ⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first | exact absurd hij.symm hne | exact absurd hij hne | exact absurd hij.symm h1τ |
        exact absurd hij h1τ | exact absurd hij.symm hρ | exact absurd hij hρ
  have h3 : 3 ≤ Nat.card N := by
    simpa using Nat.card_le_card_of_injective f hf
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 h2
  have hdvd : Nat.card N ∣ 6 := by
    have := Subgroup.card_subgroup_dvd_card N
    have hG : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    rwa [hG] at this
  rw [hj] at h3 hdvd
  have hj2 : j ≤ 1 := by
    by_contra hj'
    have : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have h4 : 4 ∣ 6 := this.trans hdvd
    omega
  have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj2
  omega

end Three

section Ybar

variable {n : ℕ}

@[expose] def triPts (x c y : Fin n) : Fin 3 → Fin n := ![x, c, y]

theorem triCyc_triPts (x c y : Fin n) : triCyc (triPts x c y) = cyc x y c := rfl

theorem injective_triPts {x c y : Fin n} (hxc : x ≠ c) (hxy : x ≠ y) (hcy : c ≠ y) :
    Function.Injective (triPts x c y) := injective_triple hxc hxy hcy

theorem mem_triSet_triPts {x c y j : Fin n} :
    j ∈ triSet (triPts x c y) ↔ j = x ∨ j = c ∨ j = y := by
  rw [mem_triSet]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem mem_setStab_of_fixes {A : Finset (Fin n)} {σ : Equiv.Perm (Fin n)}
    (h : ∀ a ∈ A, σ a = a) : σ ∈ setStab A := by
  rw [mem_setStab]
  intro z
  constructor
  · intro hz
    by_contra hzA
    have : σ (σ z) = σ z := h _ hz
    exact hzA (σ.injective this ▸ hz)
  · intro hz
    rw [h z hz]
    exact hz

theorem mem_setStab_of_involution {A : Finset (Fin n)} {σ : Equiv.Perm (Fin n)}
    (h : ∀ a ∈ A, σ a ∈ A) (hσ : σ * σ = 1) : σ ∈ setStab A := by
  rw [mem_setStab]
  intro z
  refine ⟨fun hz => ?_, h z⟩
  have h2 : σ (σ z) = z := by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f z) hσ
    simpa using this
  rw [← h2]
  exact h _ hz

theorem sup_zpowers_le_setStab {T' : Set (Equiv.Perm (Fin n))} (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) {t₀ : Equiv.Perm (Fin n)} (ht₀ : t₀ ∈ T')
    {x : Fin n} (hx : t₀ x ≠ x) {c : Fin n} (hcfix : ∀ t ∈ T', t c = c) :
    Subgroup.closure T' ⊔ Subgroup.zpowers (cyc x (t₀ x) c) ≤
      setStab (triSet (triPts x c (t₀ x))) := by
  classical
  have e1 : t₀ = Equiv.swap x (t₀ x) := eq_swap_of_isSwap_apply_ne (hs t₀ ht₀) hx
  have hy : t₀ (t₀ x) = x := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (t₀ x)) e1
    simpa using this
  have hxy : x ≠ t₀ x := hx.symm
  have hxc : x ≠ c := fun h => hx (h ▸ hcfix t₀ ht₀)
  have hcy : c ≠ t₀ x := fun h => hx (by
    have h1 := hcfix t₀ ht₀
    rw [h, hy] at h1
    exact h1.symm)
  have hp : Function.Injective (triPts x c (t₀ x)) := injective_triPts hxc hxy hcy
  refine sup_le ((Subgroup.closure_le _).2 fun t ht => ?_) ?_
  · by_cases htt : t = t₀
    · subst htt
      refine mem_setStab_of_involution (fun a ha => ?_) ?_
      · rcases mem_triSet_triPts.1 ha with rfl | rfl | rfl
        · exact mem_triSet_triPts.2 (Or.inr (Or.inr rfl))
        · rw [hcfix t ht]
          exact mem_triSet_triPts.2 (Or.inr (Or.inl rfl))
        · rw [hy]
          exact mem_triSet_triPts.2 (Or.inl rfl)
      · rw [e1]
        exact Equiv.swap_mul_self _ _
    · refine mem_setStab_of_fixes fun a ha => ?_
      have hfx : t x = x := apply_eq_of_commute_swap (hs t₀ ht₀) (hs t ht) (hc t₀ ht₀ t ht)
        (Ne.symm htt) hx
      have hfy : t (t₀ x) = t₀ x :=
        apply_eq_of_commute_swap (hs t₀ ht₀) (hs t ht) (hc t₀ ht₀ t ht) (Ne.symm htt) (by
          rw [hy]
          exact hxy)
      rcases mem_triSet_triPts.1 ha with rfl | rfl | rfl
      · exact hfx
      · exact hcfix t ht
      · exact hfy
  · rw [Subgroup.zpowers_le]
    rw [← triCyc_triPts]
    exact triCyc_mem_setStab hp

theorem le_of_isPGroup_of_le_sup_zpowers {α : Type*} [Group α] {B P : Subgroup α} {d : α}
    (hd3 : d ^ 3 = 1) (hBn : B ≤ Subgroup.normalizer (Subgroup.zpowers d : Set α))
    (hP : IsPGroup 2 ↥P) (hBP : B ≤ P) (hPle : P ≤ B ⊔ Subgroup.zpowers d) : P ≤ B := by
  intro x hx
  have hmul : ((B ⊔ Subgroup.zpowers d : Subgroup α) : Set α) =
      (B : Set α) * (Subgroup.zpowers d : Set α) :=
    Subgroup.coe_mul_of_left_le_normalizer_right B (Subgroup.zpowers d) hBn
  have hx' : x ∈ ((B ⊔ Subgroup.zpowers d : Subgroup α) : Set α) := hPle hx
  rw [hmul] at hx'
  obtain ⟨b, hb, δ, hδ, rfl⟩ := hx'
  have hδP : δ ∈ P := by
    have := P.mul_mem (P.inv_mem (hBP hb)) hx
    simpa using this
  obtain ⟨k, hk⟩ := hP ⟨δ, hδP⟩
  have hk' : δ ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hδ
  have h3 : (d ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have hord2 : orderOf (d ^ j) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hord3 : orderOf (d ^ j) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have hone : orderOf (d ^ j) = 1 := Nat.eq_one_of_dvd_coprimes hcop hord2 hord3
  have : d ^ j = 1 := orderOf_eq_one_iff.1 hone
  rw [this]
  simpa using hb

end Ybar

section Conj

variable {n : ℕ}

theorem mem_normalizer_closure_of {α : Type*} [Group α] {T' : Set α} {π : α}
    (h1 : ∀ s ∈ T', π * s * π⁻¹ ∈ Subgroup.closure T')
    (h2 : ∀ s ∈ T', π⁻¹ * s * π ∈ Subgroup.closure T') :
    π ∈ Subgroup.normalizer (Subgroup.closure T' : Set α) := by
  have key : ∀ g : α, (∀ s ∈ T', g * s * g⁻¹ ∈ Subgroup.closure T') →
      ∀ h ∈ Subgroup.closure T', g * h * g⁻¹ ∈ Subgroup.closure T' := by
    intro g hg h hh
    have : Subgroup.closure T' ≤ (Subgroup.closure T').comap (MulAut.conj g).toMonoidHom :=
      (Subgroup.closure_le _).2 fun s hs => hg s hs
    exact this hh
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key π h1 h, fun hh => ?_⟩
  have := key π⁻¹ (by simpa using h2) _ hh
  simpa [mul_assoc] using this

theorem swap_comm_of_fixes {a b : Fin n} {s : Equiv.Perm (Fin n)} (ha : s a = a) (hb : s b = b) :
    Equiv.swap a b * s = s * Equiv.swap a b := by
  rw [Equiv.swap_mul_eq_mul_swap]
  congr 2
  · exact (Equiv.Perm.inv_eq_iff_eq.2 ha.symm)
  · exact (Equiv.Perm.inv_eq_iff_eq.2 hb.symm)

theorem exists_normalizer_conj_cyc {T' : Set (Equiv.Perm (Fin n))} (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) {t : Equiv.Perm (Fin n)} (ht : t ∈ T')
    {x : Fin n} (hx : t x ≠ x) {c : Fin n} (hcf : ∀ s ∈ T', s c = c)
    {t' : Equiv.Perm (Fin n)} (ht' : t' ∈ T') {x' : Fin n} (hx' : t' x' ≠ x') {c' : Fin n}
    (hcf' : ∀ s ∈ T', s c' = c') :
    ∃ π ∈ Subgroup.normalizer (Subgroup.closure T' : Set (Equiv.Perm (Fin n))),
      π * cyc x (t x) c * π⁻¹ = cyc x' (t' x') c' := by
  classical
  have et : t = Equiv.swap x (t x) := eq_swap_of_isSwap_apply_ne (hs t ht) hx
  have et' : t' = Equiv.swap x' (t' x') := eq_swap_of_isSwap_apply_ne (hs t' ht') hx'
  have hty : t (t x) = x := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (t x)) et
    simpa using this
  have hty' : t' (t' x') = x' := by
    have := congrArg (fun σ : Equiv.Perm (Fin n) => σ (t' x')) et'
    simpa using this
  have hxy : x ≠ t x := hx.symm
  have hxy' : x' ≠ t' x' := hx'.symm
  have hyne : t (t x) ≠ t x := by
    rw [hty]
    exact hxy
  have hyne' : t' (t' x') ≠ t' x' := by
    rw [hty']
    exact hxy'
  have hcx : c ≠ x := fun h => hx (h ▸ hcf t ht)
  have hcy : c ≠ t x := fun h => hyne (h ▸ hcf t ht)
  have hcx' : c ≠ x' := fun h => hx' (h ▸ hcf t' ht')
  have hcy' : c ≠ t' x' := fun h => hyne' (h ▸ hcf t' ht')
  have hc'x : c' ≠ x := fun h => hx (h ▸ hcf' t ht)
  have hc'y : c' ≠ t x := fun h => hyne (h ▸ hcf' t ht)
  have hc'x' : c' ≠ x' := fun h => hx' (h ▸ hcf' t' ht')
  have hc'y' : c' ≠ t' x' := fun h => hyne' (h ▸ hcf' t' ht')
  have hconj : ∀ g s : Equiv.Perm (Fin n), g * s = s * g → g * s * g⁻¹ = s ∧ g⁻¹ * s * g = s := by
    intro g s h
    refine ⟨mul_inv_eq_iff_eq_mul.2 h, ?_⟩
    calc g⁻¹ * s * g = g⁻¹ * (s * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * s) := by rw [h]
      _ = s := inv_mul_cancel_left _ _
  obtain ⟨π₂, hπ₂x, hπ₂y, hπ₂c, hπ₂N, hπ₂N'⟩ : ∃ π₂ : Equiv.Perm (Fin n), π₂ x = x' ∧
      π₂ (t x) = t' x' ∧ π₂ c = c ∧ (∀ s ∈ T', π₂ * s * π₂⁻¹ ∈ T') ∧
      (∀ s ∈ T', π₂⁻¹ * s * π₂ ∈ T') := by
    by_cases htt : t' = t
    · subst htt
      have hx'mem : x' = x ∨ x' = t' x := by
        by_contra hcon
        push Not at hcon
        apply hx'
        rw [et, Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2]
      rcases hx'mem with rfl | rfl
      · exact ⟨1, by simp, by simp, by simp, fun s hs' => by simpa using hs',
          fun s hs' => by simpa using hs'⟩
      · refine ⟨t', rfl, ?_, hcf t' ht', fun s hs' => ?_, fun s hs' => ?_⟩
        · rw [hty]
        · rw [(hconj t' s (hc t' ht' s hs')).1]
          exact hs'
        · rw [(hconj t' s (hc t' ht' s hs')).2]
          exact hs'
    · have hft : ∀ z, t z ≠ z → t' z = z := fun z hz =>
        apply_eq_of_commute_swap (hs t ht) (hs t' ht') (hc t ht t' ht') (Ne.symm htt) hz
      have hft' : ∀ z, t' z ≠ z → t z = z := fun z hz =>
        apply_eq_of_commute_swap (hs t' ht') (hs t ht) (hc t' ht' t ht) htt hz
      have h1 : x' ≠ x := fun h => hx (by rw [← h]; exact hft' x' hx')
      have h2 : x' ≠ t x := fun h => by
        have := hft' x' hx'
        rw [h, hty] at this
        exact hxy this
      have h3 : t' x' ≠ x := fun h => by
        have := hft' (t' x') hyne'
        rw [h] at this
        exact hx this
      have h4 : t' x' ≠ t x := fun h => by
        have := hft' (t' x') hyne'
        rw [h, hty] at this
        exact hxy this
      have h5 : t x ≠ x' := h2.symm
      have h6 : x ≠ t' x' := h3.symm
      have h7 : t x ≠ t' x' := h4.symm
      set π₂ : Equiv.Perm (Fin n) := Equiv.swap x x' * Equiv.swap (t x) (t' x') with hπ₂
      have e1 : π₂ x = x' := by
        rw [hπ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxy h6, Equiv.swap_apply_left]
      have e2 : π₂ (t x) = t' x' := by
        rw [hπ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne h3 hxy'.symm]
      have e3 : π₂ c = c := by
        rw [hπ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hcy hcy',
          Equiv.swap_apply_of_ne_of_ne hcx hcx']
      have e4 : π₂ x' = x := by
        rw [hπ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h2 hxy',
          Equiv.swap_apply_right]
      have e5 : π₂ (t' x') = t x := by
        rw [hπ₂, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hx h5]
      have hcomm : Equiv.swap (t x) (t' x') * Equiv.swap x x' =
          Equiv.swap x x' * Equiv.swap (t x) (t' x') :=
        swap_comm_of_fixes (Equiv.swap_apply_of_ne_of_ne hx h5)
          (Equiv.swap_apply_of_ne_of_ne h3 hxy'.symm)
      have hinv : π₂⁻¹ = π₂ := by
        rw [hπ₂, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv, hcomm]
      have hconj_t : π₂ * t * π₂⁻¹ = t' := by
        calc π₂ * t * π₂⁻¹ = π₂ * Equiv.swap x (t x) * π₂⁻¹ := by rw [← et]
          _ = Equiv.swap (π₂ x) (π₂ (t x)) := (Equiv.swap_apply_apply _ _ _).symm
          _ = Equiv.swap x' (t' x') := by rw [e1, e2]
          _ = t' := et'.symm
      have hconj_t' : π₂ * t' * π₂⁻¹ = t := by
        calc π₂ * t' * π₂⁻¹ = π₂ * Equiv.swap x' (t' x') * π₂⁻¹ := by rw [← et']
          _ = Equiv.swap (π₂ x') (π₂ (t' x')) := (Equiv.swap_apply_apply _ _ _).symm
          _ = Equiv.swap x (t x) := by rw [e4, e5]
          _ = t := et.symm
      have hother : ∀ s ∈ T', s ≠ t → s ≠ t' → π₂ * s = s * π₂ := by
        intro s hs' hst hst'
        have hsx : s x = x :=
          apply_eq_of_commute_swap (hs t ht) (hs s hs') (hc t ht s hs') (Ne.symm hst) hx
        have hsy : s (t x) = t x :=
          apply_eq_of_commute_swap (hs t ht) (hs s hs') (hc t ht s hs') (Ne.symm hst) hyne
        have hsx' : s x' = x' :=
          apply_eq_of_commute_swap (hs t' ht') (hs s hs') (hc t' ht' s hs') (Ne.symm hst') hx'
        have hsy' : s (t' x') = t' x' :=
          apply_eq_of_commute_swap (hs t' ht') (hs s hs') (hc t' ht' s hs') (Ne.symm hst') hyne'
        have c1 := swap_comm_of_fixes hsx hsx'
        have c2 := swap_comm_of_fixes hsy hsy'
        rw [hπ₂, mul_assoc, c2, ← mul_assoc, c1, mul_assoc]
      have hmain : ∀ s ∈ T', π₂ * s * π₂⁻¹ ∈ T' := by
        intro s hs'
        by_cases hst : s = t
        · subst hst
          rw [hconj_t]
          exact ht'
        · by_cases hst' : s = t'
          · subst hst'
            rw [hconj_t']
            exact ht
          · rw [(hconj π₂ s (hother s hs' hst hst')).1]
            exact hs'
      refine ⟨π₂, e1, e2, e3, hmain, fun s hs' => ?_⟩
      have := hmain s hs'
      rw [hinv] at this ⊢
      exact this
  set π : Equiv.Perm (Fin n) := Equiv.swap c c' * π₂ with hπ
  have hsw : ∀ s ∈ T', Equiv.swap c c' * s * (Equiv.swap c c')⁻¹ = s ∧
      (Equiv.swap c c')⁻¹ * s * Equiv.swap c c' = s := fun s hs' =>
    hconj _ _ (swap_comm_of_fixes (hcf s hs') (hcf' s hs'))
  have hπN : π ∈ Subgroup.normalizer (Subgroup.closure T' : Set (Equiv.Perm (Fin n))) := by
    refine mem_normalizer_closure_of (fun s hs' => ?_) (fun s hs' => ?_)
    · have h1 := hπ₂N s hs'
      have h2 : π * s * π⁻¹ = π₂ * s * π₂⁻¹ := by
        rw [hπ, mul_inv_rev]
        have := (hsw (π₂ * s * π₂⁻¹) h1).1
        calc Equiv.swap c c' * π₂ * s * (π₂⁻¹ * (Equiv.swap c c')⁻¹)
            = Equiv.swap c c' * (π₂ * s * π₂⁻¹) * (Equiv.swap c c')⁻¹ := by group
          _ = π₂ * s * π₂⁻¹ := this
      rw [h2]
      exact Subgroup.subset_closure h1
    · have h1 := hπ₂N' s hs'
      have h2 : π⁻¹ * s * π = π₂⁻¹ * s * π₂ := by
        rw [hπ, mul_inv_rev]
        have := (hsw s hs').2
        calc π₂⁻¹ * (Equiv.swap c c')⁻¹ * s * (Equiv.swap c c' * π₂)
            = π₂⁻¹ * ((Equiv.swap c c')⁻¹ * s * Equiv.swap c c') * π₂ := by group
          _ = π₂⁻¹ * s * π₂ := by rw [this]
      rw [h2]
      exact Subgroup.subset_closure h1
  refine ⟨π, hπN, ?_⟩
  rw [conj_cyc]
  have hπx : π x = x' := by
    rw [hπ, Equiv.Perm.mul_apply, hπ₂x, Equiv.swap_apply_of_ne_of_ne hcx'.symm hc'x'.symm]
  have hπy : π (t x) = t' x' := by
    rw [hπ, Equiv.Perm.mul_apply, hπ₂y, Equiv.swap_apply_of_ne_of_ne hcy'.symm hc'y'.symm]
  have hπc : π c = c' := by
    rw [hπ, Equiv.Perm.mul_apply, hπ₂c, Equiv.swap_apply_left]
  rw [hπx, hπy, hπc]

end Conj

end CFSG.CGT.PushingUpLit.BHS6
