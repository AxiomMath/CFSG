module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1Spec
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.MaxByFixedPoints

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1

open CFSG.Sporadic.J1 CFSG.Sporadic.J1.Sylow.Native

@[expose] noncomputable def H : Subgroup J := Subgroup.zpowers b

@[expose] noncomputable def N : Subgroup J := Subgroup.normalizer (H : Set J)

theorem mem_H_iff (y : J) : y ∈ H ↔ y = 1 ∨ y = b ∨ y = b * b := by
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have h := zpow_mod_orderOf b k
    rw [orderOf_b] at h
    rw [← h]
    have : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases this with e | e | e <;> rw [e]
    · left; simp
    · right; left; simp
    · right; right; simp [pow_two]
  · rintro (rfl | rfl | rfl)
    · exact H.one_mem
    · exact Subgroup.mem_zpowers b
    · have : b * b = b ^ (2 : ℤ) := (zpow_two b).symm
      rw [this]; exact Subgroup.zpow_mem_zpowers b 2

theorem b_mem_H : b ∈ H := Subgroup.mem_zpowers b

theorem conj_mem_H {g x : J} (hg : g * b * g⁻¹ ∈ H) (hx : x ∈ H) : g * x * g⁻¹ ∈ H := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hg k

theorem mem_N_of_conj {g : J} (h : g * b * g⁻¹ = b ∨ g * b * g⁻¹ = b * b) : g ∈ N := by
  have hg : g * b * g⁻¹ ∈ H := by
    rcases h with h | h
    · rw [h]; exact b_mem_H
    · rw [h]; exact (mem_H_iff _).2 (Or.inr (Or.inr rfl))
  have hg' : g⁻¹ * b * g ∈ H := by
    rcases h with h | h
    · have : g⁻¹ * b * g = b := by
        rw [mul_inv_eq_iff_eq_mul] at h
        calc g⁻¹ * b * g = g⁻¹ * (b * g) := by group
          _ = g⁻¹ * (g * b) := by rw [h]
          _ = b := by group
      rw [this]; exact b_mem_H
    · have hbb : b * b = b⁻¹ := by
        have := b_cube
        rw [pow_succ, pow_two] at this
        exact (inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact this)).symm
      rw [hbb] at h
      have : g⁻¹ * b * g = b⁻¹ := by
        have h2 : g * b * g⁻¹ = b⁻¹ := h
        calc g⁻¹ * b * g = g⁻¹ * (g * b * g⁻¹)⁻¹ * g := by
              rw [h2, inv_inv]
          _ = b⁻¹ := by group
      rw [this]; exact H.inv_mem b_mem_H
  rw [N, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_H hg
  · intro hx
    have := conj_mem_H (g := g⁻¹) (by simpa using hg') hx
    simpa [mul_assoc] using this

theorem conj_of_mem_N {g : J} (hg : g ∈ N) : g * b * g⁻¹ = b ∨ g * b * g⁻¹ = b * b := by
  have h1 : g * b * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.1 hg b).1 b_mem_H
  rcases (mem_H_iff _).1 h1 with h | h | h
  · exfalso
    apply b_ne_one
    have : g * b * g⁻¹ = 1 := h
    simpa [mul_inv_eq_one] using this
  · exact Or.inl h
  · exact Or.inr h

theorem xg_of_coset {p q : ℕ} (h : (tg q)⁻¹ * tg p ∈ N) : xg p = xg q ∨ xg p = xg q * xg q := by
  rcases conj_of_mem_N h with e | e
  · left
    unfold xg
    calc tg p * b * (tg p)⁻¹ = tg q * ((tg q)⁻¹ * tg p * b * ((tg q)⁻¹ * tg p)⁻¹) * (tg q)⁻¹ := by
          group
      _ = tg q * b * (tg q)⁻¹ := by rw [e]
  · right
    unfold xg
    calc tg p * b * (tg p)⁻¹ = tg q * ((tg q)⁻¹ * tg p * b * ((tg q)⁻¹ * tg p)⁻¹) * (tg q)⁻¹ := by
          group
      _ = tg q * (b * b) * (tg q)⁻¹ := by rw [e]
      _ = tg q * b * (tg q)⁻¹ * (tg q * b * (tg q)⁻¹) := by group

theorem coset_injective {p q : ℕ} (hp : p < 2926) (hq : q < 2926)
    (h : (QuotientGroup.mk (tg p) : J ⧸ N) = QuotientGroup.mk (tg q)) : p = q := by
  obtain ⟨-, -, -, -, hne, -, -, -, -, -, -⟩ := sylow_parts
  have hmem : (tg q)⁻¹ * tg p ∈ N := QuotientGroup.eq.1 h.symm
  have hmem' : (tg p)⁻¹ * tg q ∈ N := by
    have := N.inv_mem hmem
    simpa using this
  by_contra hpq
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · rcases xg_of_coset hmem with e | e
    · exact (hne p q hlt hq).1 e
    · exact (hne p q hlt hq).2 e
  · rcases xg_of_coset hmem' with e | e
    · exact (hne q p hgt hp).1 e
    · exact (hne q p hgt hp).2 e

theorem index_ge : 2926 ≤ N.index := by
  have hinj : Function.Injective (fun p : Fin 2926 => (QuotientGroup.mk (tg p.val) : J ⧸ N)) :=
    fun p q h => Fin.ext (coset_injective p.isLt q.isLt h)
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Subgroup.index] using this

theorem card_N_ge : 60 ≤ Nat.card N := by
  obtain ⟨-, -, -, -, -, hconj, hne, -, -, -, -⟩ := sylow_parts
  have hmem : ∀ i : Fin 60, vg i ∈ N := fun i => mem_N_of_conj (hconj i i.isLt)
  have inj : Function.Injective (fun i : Fin 60 => (⟨vg i, hmem i⟩ : N)) := by
    intro i j h
    have h' : vg i = vg j := congrArg Subtype.val h
    by_contra hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact hne i j hlt j.isLt h'
    · exact hne j i hgt i.isLt h'.symm
  have := Nat.card_le_card_of_injective _ inj
  simpa using this

theorem card_N : Nat.card N = 60 ∧ N.index = 2926 := by
  have h := N.card_mul_index
  rw [card_J] at h
  have h1 := card_N_ge
  have h2 := index_ge
  constructor <;> nlinarith

theorem cover (g : J) : ∃ p, p < 2926 ∧ (tg p)⁻¹ * g ∈ N := by
  have hinj : Function.Injective (fun p : Fin 2926 => (QuotientGroup.mk (tg p.val) : J ⧸ N)) :=
    fun p q h => Fin.ext (coset_injective p.isLt q.isLt h)
  have hle : Nat.card (J ⧸ N) ≤ Nat.card (Fin 2926) := by
    have := card_N.2
    show N.index ≤ Nat.card (Fin 2926)
    rw [this, Nat.card_fin]
  have hbij := hinj.bijective_of_nat_card_le hle
  obtain ⟨p, hp⟩ := hbij.2 (QuotientGroup.mk g)
  exact ⟨p.val, p.isLt, QuotientGroup.eq.1 hp⟩

theorem fix_lemma {s : J}
    (hs : ∀ p, 1 ≤ p → p < 2926 → s * xg p * s⁻¹ ≠ xg p ∧ s * xg p * s⁻¹ ≠ xg p * xg p) {g : J}
    (hg : g⁻¹ * s * g ∈ N) : g ∈ N := by
  obtain ⟨-, -, -, h0, -⟩ := sylow_parts
  obtain ⟨p, hp, hpn⟩ := cover g
  have hgn : g = tg p * ((tg p)⁻¹ * g) := by group
  have hc : (tg p)⁻¹ * s * tg p ∈ N := by
    have : (tg p)⁻¹ * s * tg p = ((tg p)⁻¹ * g) * (g⁻¹ * s * g) * ((tg p)⁻¹ * g)⁻¹ := by group
    rw [this]
    exact N.mul_mem (N.mul_mem hpn hg) (N.inv_mem hpn)
  by_cases hp0 : p = 0
  · subst hp0
    rw [h0, inv_one, one_mul] at hpn
    exact hpn
  · exfalso
    have h1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 hp0
    rcases conj_of_mem_N hc with e | e
    · apply (hs p h1 hp).1
      calc s * xg p * s⁻¹
          = tg p * ((tg p)⁻¹ * s * tg p * b * ((tg p)⁻¹ * s * tg p)⁻¹) * (tg p)⁻¹ := by
            unfold xg; group
        _ = tg p * b * (tg p)⁻¹ := by rw [e]
        _ = xg p := rfl
    · apply (hs p h1 hp).2
      calc s * xg p * s⁻¹
          = tg p * ((tg p)⁻¹ * s * tg p * b * ((tg p)⁻¹ * s * tg p)⁻¹) * (tg p)⁻¹ := by
            unfold xg; group
        _ = tg p * (b * b) * (tg p)⁻¹ := by rw [e]
        _ = xg p * xg p := by unfold xg; group

theorem eq_or_eq_top {W : Subgroup J} (hW : N ≤ W) : W = N ∨ W = ⊤ := by
  obtain ⟨-, -, -, -, -, hconj, -, hf5, hfne, hfix5, hfix3⟩ := sylow_parts
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hbN : H ≤ N := Subgroup.le_normalizer
  have hfN : fg ∈ N := mem_N_of_conj (hconj (fIdx ()) (by obtain ⟨-, -, h, -⟩ := sylow_parts; exact h))
  have hP5N : Subgroup.zpowers fg ≤ N := (Subgroup.zpowers_le).2 hfN
  have h3 : IsPGroup 3 H := IsPGroup.of_card (n := 1) (by
    rw [H, Nat.card_zpowers, orderOf_b, pow_one])
  have h5 : IsPGroup 5 (Subgroup.zpowers fg) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime hf5 hfne, pow_one])
  exact MaxByFixedPoints.eq_or_eq_top_of_fixed card_N.2 hbN hP5N h3 h5
    (fun g hg => fix_lemma hfix3 (hg b b_mem_H))
    (fun g hg => fix_lemma hfix5 (hg fg (Subgroup.mem_zpowers fg))) hW

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1
