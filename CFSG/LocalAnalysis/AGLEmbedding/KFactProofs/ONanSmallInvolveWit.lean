module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallInvolveComm

public section

namespace CFSG.AGLEmbedding.KFactProofs.RankOneCore

@[expose] def tabPerm {n : ℕ} (t u : Fin n → Fin n) (h : ∀ i, u (t i) = i ∧ t (u i) = i) :
    Equiv.Perm (Fin n) where
  toFun := t
  invFun := u
  left_inv i := (h i).1
  right_inv i := (h i).2

theorem not_normalizerQuotientComm_of_finset {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (M : Subgroup Γ) [Finite M] {p k m : ℕ} [Fact p.Prime] (hM : Nat.card M = p ^ k * m)
    (hm : ¬ p ∣ m) (S : Finset Γ) (hSM : ∀ s ∈ S, s ∈ M)
    (hone : (1 : Γ) ∈ S) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hcard : S.card = p ^ k) (hnt : S.card ≠ 1) (x y : Γ)
    (hxM : x ∈ M) (hyM : y ∈ M) (hx : ∀ s ∈ S, x * s * x⁻¹ ∈ S ∧ x⁻¹ * s * x ∈ S)
    (hy : ∀ s ∈ S, y * s * y⁻¹ ∈ S ∧ y⁻¹ * s * y ∈ S) (hxy : x * y * x⁻¹ * y⁻¹ ∉ S) :
    ¬ NormalizerQuotientComm p M := by
  classical
  intro hcomm
  have hfact : (Nat.card M).factorization p = k := by
    have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
    rw [hM, Nat.factorization_mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hm0,
      Finsupp.add_apply, Nat.Prime.factorization_pow Fact.out, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  let Tsub : Subgroup M :=
    { carrier := {m | (m : Γ) ∈ S}
      mul_mem' := fun {a b} ha hb => hmul _ ha _ hb
      one_mem' := hone
      inv_mem' := fun {a} ha => hinv _ ha }
  have hTcard : Nat.card Tsub = S.card := by
    have : Nat.card Tsub = Nat.card {γ : Γ // γ ∈ S} := by
      refine Nat.card_congr ⟨fun t => ⟨(t.1 : Γ), t.2⟩, fun s => ⟨⟨s.1, hSM _ s.2⟩, s.2⟩, ?_, ?_⟩
      · intro t; rfl
      · intro s; rfl
    rw [this, Nat.card_eq_fintype_card, Fintype.card_coe]
  let T : Sylow p M := Sylow.ofCard Tsub (by rw [hTcard, hfact]; exact hcard)
  have hTe : (T : Subgroup M) = Tsub := rfl
  have hTne : (T : Subgroup M) ≠ ⊥ := by
    intro h
    have h' : Tsub = ⊥ := h
    apply hnt
    rw [← hTcard, h']
    exact Subgroup.card_bot
  have hN : ∀ (g : Γ) (hgM : g ∈ M), (∀ s ∈ S, g * s * g⁻¹ ∈ S ∧ g⁻¹ * s * g ∈ S) →
      (⟨g, hgM⟩ : M) ∈ Subgroup.normalizer ((T : Subgroup M) : Set M) := by
    intro g hgM hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    change (h : Γ) ∈ S ↔ (g * (h : Γ) * g⁻¹) ∈ S
    refine ⟨fun hh => (hg _ hh).1, fun hh => ?_⟩
    have := (hg _ hh).2
    simpa [mul_assoc] using this
  have := hcomm T hTne _ (hN x hxM hx) _ (hN y hyM hy)
  exact hxy this

theorem not_normalizerQuotientComm_of_elemAbelian {Γ : Type*} [Group Γ] [DecidableEq Γ]
    (M : Subgroup Γ) [Finite M] {p m : ℕ} [Fact p.Prime] (hM : Nat.card M = p ^ 2 * m)
    (hm : ¬ p ∣ m) (a b x y : Γ) (haM : a ∈ M) (hbM : b ∈ M) (hxM : x ∈ M) (hyM : y ∈ M)
    (hab : a * b = b * a) (hap : a ^ p = 1) (hbp : b ^ p = 1)
    (hdist : ∀ i < p, ∀ j < p, ∀ i' < p, ∀ j' < p, a ^ i * b ^ j = a ^ i' * b ^ j' →
      i = i' ∧ j = j')
    (hx : (∃ i j : ℕ, x * a * x⁻¹ = a ^ i * b ^ j) ∧ (∃ i j : ℕ, x * b * x⁻¹ = a ^ i * b ^ j) ∧
      (∃ i j : ℕ, x⁻¹ * a * x = a ^ i * b ^ j) ∧ (∃ i j : ℕ, x⁻¹ * b * x = a ^ i * b ^ j))
    (hy : (∃ i j : ℕ, y * a * y⁻¹ = a ^ i * b ^ j) ∧ (∃ i j : ℕ, y * b * y⁻¹ = a ^ i * b ^ j) ∧
      (∃ i j : ℕ, y⁻¹ * a * y = a ^ i * b ^ j) ∧ (∃ i j : ℕ, y⁻¹ * b * y = a ^ i * b ^ j))
    (hxy : ∀ i < p, ∀ j < p, x * y * x⁻¹ * y⁻¹ ≠ a ^ i * b ^ j) :
    ¬ NormalizerQuotientComm p M := by
  classical
  have hp : p.Prime := Fact.out
  have hcomm : ∀ i j : ℕ, Commute (a ^ i) (b ^ j) := fun i j => (Commute.pow_pow hab i j)
  have hpowa : ∀ i : ℕ, a ^ i = a ^ (i % p) := fun i => by
    conv_lhs => rw [← Nat.mod_add_div i p, pow_add, pow_mul, hap, one_pow, mul_one]
  have hpowb : ∀ j : ℕ, b ^ j = b ^ (j % p) := fun j => by
    conv_lhs => rw [← Nat.mod_add_div j p, pow_add, pow_mul, hbp, one_pow, mul_one]
  let S : Finset Γ := (Finset.range p ×ˢ Finset.range p).image (fun ij => a ^ ij.1 * b ^ ij.2)
  have hS : ∀ i j : ℕ, a ^ i * b ^ j ∈ S := fun i j => by
    rw [hpowa i, hpowb j]
    exact Finset.mem_image.mpr ⟨(i % p, j % p), by
      simp [Finset.mem_product, Nat.mod_lt _ hp.pos], rfl⟩
  have hSmem : ∀ s ∈ S, ∃ i j : ℕ, s = a ^ i * b ^ j := fun s hs => by
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨i, j, rfl⟩
  have hone : (1 : Γ) ∈ S := by simpa using hS 0 0
  have hmul : ∀ s ∈ S, ∀ t ∈ S, s * t ∈ S := by
    intro s hs t ht
    obtain ⟨i, j, rfl⟩ := hSmem s hs
    obtain ⟨k, l, rfl⟩ := hSmem t ht
    have : a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ (i + k) * b ^ (j + l) := by
      rw [pow_add, pow_add, mul_assoc, ← mul_assoc (b ^ j), (hcomm k j).symm.eq, mul_assoc,
        ← mul_assoc]
    rw [this]
    exact hS _ _
  have hinv : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    obtain ⟨i, j, rfl⟩ := hSmem s hs
    have h1 : a ^ i * b ^ j * (a ^ ((p - 1) * i) * b ^ ((p - 1) * j)) = 1 := by
      have : a ^ i * b ^ j * (a ^ ((p - 1) * i) * b ^ ((p - 1) * j)) =
          a ^ (i + (p - 1) * i) * b ^ (j + (p - 1) * j) := by
        rw [pow_add, pow_add, mul_assoc, ← mul_assoc (b ^ j), (hcomm ((p - 1) * i) j).symm.eq,
          mul_assoc, ← mul_assoc]
      have e1 : i + (p - 1) * i = p * i := by
        have := hp.one_le
        zify [this]
        ring
      have e2 : j + (p - 1) * j = p * j := by
        have := hp.one_le
        zify [this]
        ring
      rw [this, e1, e2, pow_mul, pow_mul, hap, hbp, one_pow, one_pow, one_mul]
    rw [inv_eq_of_mul_eq_one_right h1]
    exact hS _ _
  have hpow : ∀ s ∈ S, ∀ n : ℕ, s ^ n ∈ S := by
    intro s hs n
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hs
  have hconj : ∀ g : Γ, (g * a * g⁻¹ ∈ S) → (g * b * g⁻¹ ∈ S) → ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g ha hb s hs
    obtain ⟨i, j, rfl⟩ := hSmem s hs
    have : g * (a ^ i * b ^ j) * g⁻¹ = (g * a * g⁻¹) ^ i * (g * b * g⁻¹) ^ j := by
      rw [conj_pow, conj_pow]
      group
    rw [this]
    exact hmul _ (hpow _ ha _) _ (hpow _ hb _)
  have hxS : ∀ s ∈ S, x * s * x⁻¹ ∈ S ∧ x⁻¹ * s * x ∈ S := by
    obtain ⟨⟨i1, j1, h1⟩, ⟨i2, j2, h2⟩, ⟨i3, j3, h3⟩, ⟨i4, j4, h4⟩⟩ := hx
    intro s hs
    refine ⟨hconj x ?_ ?_ s hs, ?_⟩
    · rw [h1]; exact hS _ _
    · rw [h2]; exact hS _ _
    · have := hconj x⁻¹ (by simpa using (h3 ▸ hS i3 j3)) (by simpa using (h4 ▸ hS i4 j4)) s hs
      simpa using this
  have hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S ∧ y⁻¹ * s * y ∈ S := by
    obtain ⟨⟨i1, j1, h1⟩, ⟨i2, j2, h2⟩, ⟨i3, j3, h3⟩, ⟨i4, j4, h4⟩⟩ := hy
    intro s hs
    refine ⟨hconj y ?_ ?_ s hs, ?_⟩
    · rw [h1]; exact hS _ _
    · rw [h2]; exact hS _ _
    · have := hconj y⁻¹ (by simpa using (h3 ▸ hS i3 j3)) (by simpa using (h4 ▸ hS i4 j4)) s hs
      simpa using this
  have hcard : S.card = p ^ 2 := by
    rw [Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, sq]
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hij hij'
    obtain ⟨h1, h2⟩ := hdist i hij.1 j hij.2 i' hij'.1 j' hij'.2 h
    rw [h1, h2]
  have hSM : ∀ s ∈ S, s ∈ M := by
    intro s hs
    obtain ⟨i, j, rfl⟩ := hSmem s hs
    exact M.mul_mem (M.pow_mem haM i) (M.pow_mem hbM j)
  refine not_normalizerQuotientComm_of_finset M hM hm S hSM hone hmul hinv hcard
    (by rw [hcard]; exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne') x y hxM hyM hxS hyS ?_
  intro hmem
  obtain ⟨i, j, hij⟩ := hSmem _ hmem
  rw [hpowa i, hpowb j] at hij
  exact hxy (i % p) (Nat.mod_lt _ hp.pos) (j % p) (Nat.mod_lt _ hp.pos) hij

end CFSG.AGLEmbedding.KFactProofs.RankOneCore
