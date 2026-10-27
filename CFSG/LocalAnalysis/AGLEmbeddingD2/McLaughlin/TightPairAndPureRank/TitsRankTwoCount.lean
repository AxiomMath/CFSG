module

public import CFSG.GroupTheory.TitsSystem.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

section Doset

variable {G : Type*} [Group G] [Finite G]

theorem card_doset_isPGroup {p : ℕ} [Fact p.Prime] {B Q : Subgroup G} (hB : IsPGroup p B) (g : G) :
    ∃ j : ℕ, Nat.card (((B : Set G) * {g} * (Q : Set G) : Set G)) = p ^ j * Nat.card Q := by
  classical
  set t : Set (G ⧸ Q) := MulAction.orbit B ((g : G) : G ⧸ Q) with ht
  have hS : ((B : Set G) * {g} * (Q : Set G)) = QuotientGroup.mk ⁻¹' t := by
    ext x
    simp only [Set.mem_mul, Set.mem_singleton_iff, Set.mem_preimage, ht, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨_, ⟨b, hb, g', hg', rfl⟩, q, hq, rfl⟩
      rw [hg']
      refine ⟨⟨b, hb⟩, ?_⟩
      show ((b * g : G) : G ⧸ Q) = ((b * g * q : G) : G ⧸ Q)
      rw [QuotientGroup.eq]
      have : (b * g)⁻¹ * (b * g * q) = q := inv_mul_cancel_left (b * g) q
      rw [this]; exact hq
    · rintro ⟨⟨b, hb⟩, hbx⟩
      have h : ((b * g : G) : G ⧸ Q) = (x : G ⧸ Q) := hbx
      rw [QuotientGroup.eq] at h
      refine ⟨b * g, ⟨b, hb, g, rfl, rfl⟩, (b * g)⁻¹ * x, h, mul_inv_cancel_left (b * g) x⟩
  rw [hS, QuotientGroup.card_preimage_mk]
  have hdvd : Nat.card t ∣ Nat.card B := by
    have e := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer B ((g : G) : G ⧸ Q))
    rw [ht, e]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  exact ⟨j, by rw [hj, mul_comm]⟩

end Doset

section Dihedral

variable {W : Type*} [Group W] {a b : W}

theorem mul_ne_mul_of_braid (haa : a * a = 1) (hbb : b * b = 1) (hab : a ≠ b)
    (hbraid : a * b * a = b * a * b) : a * b ≠ b * a := by
  intro h
  apply hab
  grind

theorem six_distinct (haa : a * a = 1) (hbb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hbraid : a * b * a = b * a * b) :
    (1 : W) ≠ a ∧ (1 : W) ≠ b ∧ (1 : W) ≠ b * a ∧ (1 : W) ≠ a * b ∧ (1 : W) ≠ a * b * a ∧
    a ≠ b ∧ a ≠ b * a ∧ a ≠ a * b ∧ a ≠ a * b * a ∧
    b ≠ b * a ∧ b ≠ a * b ∧ b ≠ a * b * a ∧
    b * a ≠ a * b ∧ b * a ≠ a * b * a ∧ a * b ≠ a * b * a := by
  have hc := mul_ne_mul_of_braid haa hbb hab hbraid
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> grind

theorem mem_six_of_mem_closure (haa : a * a = 1) (hbb : b * b = 1) (hbraid : a * b * a = b * a * b)
    {w : W} (hw : w ∈ Subgroup.closure ({a, b} : Set W)) :
    w = 1 ∨ w = a ∨ w = b ∨ w = b * a ∨ w = a * b ∨ w = a * b * a := by
  have hJ : ∀ s ∈ ({a, b} : Set W), s * s = 1 := by
    intro s hs
    rcases hs with rfl | rfl
    · exact haa
    · exact hbb
  obtain ⟨l, hl, rfl⟩ := (CFSG.GH74.BNPair.mem_closure_iff_exists_list hJ).1 hw
  clear hw
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx : x = a ∨ x = b := by simpa using hl x (by simp)
    have ih' := ih (fun s hs => hl s (by simp [hs]))
    simp only [List.prod_cons]
    rcases ih' with h | h | h | h | h | h <;> rcases hx with rfl | rfl <;> rw [h] <;> grind

end Dihedral

section Tits

variable {G : Type*} [Group G] [Finite G] {B N : Subgroup G} [(cartan B N).Normal]
  {S : Set (WeylGroup B N)}

theorem card_union_of_disjoint {s t : Set G} (h : Disjoint s t) :
    Nat.card ↥(s ∪ t) = Nat.card ↥s + Nat.card ↥t := by
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_union_eq h (Set.toFinite _) (Set.toFinite _)

theorem eq_one_or_eq_of_mem_closure_single {W : Type*} [Group W] {a : W} (haa : a * a = 1) {w : W}
    (hw : w ∈ Subgroup.closure ({a} : Set W)) : w = 1 ∨ w = a := by
  induction hw using Subgroup.closure_induction with
  | mem x hx => right; simpa using hx
  | one => left; rfl
  | mul x y _ _ hx hy => rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> grind
  | inv x _ hx =>
    rcases hx with h | h
    · left; rw [h, inv_one]
    · right; rw [h]; exact inv_eq_of_mul_eq_one_right haa

theorem coe_parabolic_single (h : CFSG.GroupTheory.TitsSystem.IsBNPair B N S) {a : WeylGroup B N}
    (ha : a ∈ S) :
    ((parabolic B N {a} : Subgroup G) : Set G) = (B : Set G) ∪ dc B N a := by
  have hJ : ({a} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 ha
  have haa := h.mul_self_eq_one ha
  ext x
  rw [SetLike.mem_coe, h.mem_parabolic_iff hJ]
  constructor
  · rintro ⟨w, hw, hx⟩
    rcases eq_one_or_eq_of_mem_closure_single haa hw with rfl | rfl
    · left; exact mem_dc_one.1 hx
    · right; exact hx
  · rintro (hx | hx)
    · exact ⟨1, one_mem _, mem_dc_one.2 hx⟩
    · exact ⟨a, Subgroup.subset_closure rfl, hx⟩

theorem dc_mul_dc_of_ne (h : CFSG.GroupTheory.TitsSystem.IsBNPair B N S) {s t : WeylGroup B N}
    (hs : s ∈ S) (ht : t ∈ S) (hst : s ≠ t) : dc B N s * dc B N t ⊆ dc B N (s * t) := by
  intro x hx
  have h1 := h.bnCore.mul_subset s hs t hx
  have h2 := h.bnCore.mul_subset_right ht s hx
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd h1 (Set.disjoint_left.1 (h.pairwise_disjoint_dc hst) h2)

theorem dc_union_eq_dcoset (h : CFSG.GroupTheory.TitsSystem.IsBNPair B N S) {a : WeylGroup B N}
    (ha : a ∈ S) {w : WeylGroup B N} {n : N} (hn : (n : WeylGroup B N) = w) :
    dc B N w ∪ dc B N (w * a) =
      (B : Set G) * {(n : G)} * ((parabolic B N {a} : Subgroup G) : Set G) := by
  have hJS : ({a} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 ha
  have hQS := coe_parabolic_single h ha
  have hBQ : B ≤ parabolic B N {a} := h.le_parabolic hJS
  have hDQ : dc B N a ⊆ ((parabolic B N {a} : Subgroup G) : Set G) := by
    rw [hQS]; exact Set.subset_union_right
  have hnw : (n : G) ∈ dc B N w := by
    rw [mem_dc_of_lift hn]; exact ⟨1, B.one_mem, 1, B.one_mem, by simp⟩
  ext x
  constructor
  · rintro (hx | hx)
    · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift hn).1 hx
      exact Set.mem_mul.2 ⟨b₁ * n, Set.mem_mul.2 ⟨b₁, hb₁, n, rfl, rfl⟩, b₂, hBQ hb₂, rfl⟩
    · obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 (dc_subset_mul w a hx)
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift hn).1 hy
      refine Set.mem_mul.2 ⟨b₁ * n, Set.mem_mul.2 ⟨b₁, hb₁, n, rfl, rfl⟩, b₂ * z,
        Subgroup.mul_mem _ (hBQ hb₂) (hDQ hz), by simp [mul_assoc]⟩
  · intro hx
    obtain ⟨_, hy, p, hp, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨b₁, hb₁, g, hg, rfl⟩ := Set.mem_mul.1 hy
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hp' : p ∈ ((parabolic B N {a} : Subgroup G) : Set G) := hp
    rw [hQS] at hp'
    rcases hp' with hp' | hp'
    · left
      exact (mem_dc_of_lift hn).2 ⟨b₁, hb₁, p, hp', rfl⟩
    · have h1 : (b₁ * (n : G)) ∈ dc B N w := mul_mem_dc hnw hb₁ B.one_mem |> fun h' => by
        simpa using h'
      have h2 := h.bnCore.mul_subset_right ha w (Set.mul_mem_mul h1 hp')
      rcases h2 with h2 | h2
      · right; exact h2
      · left; exact h2

theorem arith_pow_two {o e : ℕ} (h : 3 * 2 ^ o = 2 + 2 ^ e) (he : 2 ≤ 2 ^ e) : 2 ^ o = 2 := by
  rcases o with _ | _ | o
  · rcases e with _ | _ | e <;> simp [pow_succ] at h he ⊢ <;> omega
  · simp
  · rcases e with _ | _ | e <;> simp [pow_succ] at h he ⊢ <;> omega

theorem not_nine_dvd_card_parabolic_pair (h : CFSG.GroupTheory.TitsSystem.IsBNPair B N S)
    (hB : IsPGroup 2 B) {a b : WeylGroup B N} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hbraid : a * b * a = b * a * b) (hPa : Nat.card (parabolic B N {a}) = 3 * Nat.card B)
    (hPb : Nat.card (parabolic B N {b}) = 3 * Nat.card B) :
    ¬ 9 ∣ Nat.card (parabolic B N {a, b}) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa := h.mul_self_eq_one ha
  have hbb := h.mul_self_eq_one hb
  have ha1 : a ≠ 1 := h.ne_one ha
  have hb1 : b ≠ 1 := h.ne_one hb
  obtain ⟨n1a, n1b, n1ba, n1ab, n1aba, nab, nba', nab', naaba, nbba, nbab, nbaba, nbaab, nbaaba,
    nabaaba⟩ := six_distinct haa hbb ha1 hb1 hab hbraid
  have hD : ∀ {u v : WeylGroup B N}, u ≠ v → Disjoint (dc B N u) (dc B N v) :=
    fun huv => h.pairwise_disjoint_dc huv
  have hJS : ({a, b} : Set (WeylGroup B N)) ⊆ S := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  set Q : Subgroup G := parabolic B N {a} with hQ
  have hQS := coe_parabolic_single h ha
  have hPbS := coe_parabolic_single h hb
  have hDB : Disjoint (B : Set G) (dc B N a) := by
    rw [← dc_one (B := B) (N := N)]; exact hD n1a
  have hDBb : Disjoint (B : Set G) (dc B N b) := by
    rw [← dc_one (B := B) (N := N)]; exact hD n1b
  have hcDb : Nat.card (dc B N b) = 2 * Nat.card B := by
    have h1 : Nat.card (parabolic B N {b}) = Nat.card ↥((B : Set G) ∪ dc B N b) := by
      rw [← hPbS]; rfl
    rw [card_union_of_disjoint hDBb] at h1
    have : Nat.card ↥(B : Set G) = Nat.card B := rfl
    omega
  obtain ⟨na, hna⟩ := QuotientGroup.mk_surjective a
  obtain ⟨nb, hnb⟩ := QuotientGroup.mk_surjective b
  have hnab : ((na * nb : N) : WeylGroup B N) = a * b := by rw [QuotientGroup.mk_mul, hna, hnb]
  have hnba : ((nb * na : N) : WeylGroup B N) = b * a := by rw [QuotientGroup.mk_mul, hna, hnb]
  have hJa : a ∈ Subgroup.closure ({a, b} : Set (WeylGroup B N)) := Subgroup.subset_closure (by simp)
  have hJb : b ∈ Subgroup.closure ({a, b} : Set (WeylGroup B N)) := Subgroup.subset_closure (by simp)
  set X₀ : Set G := dc B N 1 ∪ dc B N a with hX₀
  set X₁ : Set G := dc B N b ∪ dc B N (b * a) with hX₁
  set X₂ : Set G := dc B N (a * b) ∪ dc B N (a * b * a) with hX₂
  have hPJ : ((parabolic B N {a, b} : Subgroup G) : Set G) = X₀ ∪ X₁ ∪ X₂ := by
    ext x
    rw [SetLike.mem_coe, h.mem_parabolic_iff hJS]
    constructor
    · rintro ⟨w, hw, hx⟩
      rcases mem_six_of_mem_closure haa hbb hbraid hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl hx))
      · exact Or.inl (Or.inl (Or.inr hx))
      · exact Or.inl (Or.inr (Or.inl hx))
      · exact Or.inl (Or.inr (Or.inr hx))
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · rintro (((hx | hx) | (hx | hx)) | (hx | hx))
      · exact ⟨1, one_mem _, hx⟩
      · exact ⟨a, hJa, hx⟩
      · exact ⟨b, hJb, hx⟩
      · exact ⟨b * a, mul_mem hJb hJa, hx⟩
      · exact ⟨a * b, mul_mem hJa hJb, hx⟩
      · exact ⟨a * b * a, mul_mem (mul_mem hJa hJb) hJa, hx⟩
  have hd01 : Disjoint X₀ X₁ := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hD n1b, hD n1ba⟩,
      Set.disjoint_union_right.2 ⟨hD nab, hD nba'⟩⟩
  have hd02 : Disjoint X₀ X₂ := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hD n1ab, hD n1aba⟩,
      Set.disjoint_union_right.2 ⟨hD nab', hD naaba⟩⟩
  have hd12 : Disjoint X₁ X₂ := by
    refine Set.disjoint_union_left.2 ⟨Set.disjoint_union_right.2 ⟨hD nbab, hD nbaba⟩,
      Set.disjoint_union_right.2 ⟨hD nbaab, hD nbaaba⟩⟩
  have hcard : Nat.card (parabolic B N {a, b}) = Nat.card X₀ + Nat.card X₁ + Nat.card X₂ := by
    have h1 : Nat.card (parabolic B N {a, b}) = Nat.card ↥(X₀ ∪ X₁ ∪ X₂) := by
      rw [← hPJ]; rfl
    rw [h1, card_union_of_disjoint (Set.disjoint_union_left.2 ⟨hd02, hd12⟩),
      card_union_of_disjoint hd01]
  have hX₀Q : Nat.card X₀ = Nat.card Q := by
    have : X₀ = (Q : Set G) := by rw [hX₀, hQS, dc_one]
    rw [this]; rfl
  obtain ⟨o₁, ho₁⟩ := card_doset_isPGroup (p := 2) (Q := Q) hB (nb : G)
  obtain ⟨o₂, ho₂⟩ := card_doset_isPGroup (p := 2) (Q := Q) hB ((na * nb : N) : G)
  have hX1 := dc_union_eq_dcoset h ha hnb
  have hX2 := dc_union_eq_dcoset h ha hnab
  have hX₁c : Nat.card X₁ = 2 ^ o₁ * Nat.card Q := by
    rw [hX₁, hX1]; exact ho₁
  have hX₂c : Nat.card X₂ = 2 ^ o₂ * Nat.card Q := by
    rw [hX₂, hX2]; exact ho₂
  have hDba : dc B N (b * a) = (B : Set G) * {((nb * na : N) : G)} * (B : Set G) := by
    ext x
    rw [mem_dc_of_lift hnba, mem_dcoset_iff]
  obtain ⟨e, he⟩ := card_doset_isPGroup (p := 2) (Q := B) hB ((nb * na : N) : G)
  rw [← hDba] at he
  have hlow : Nat.card (dc B N b) ≤ Nat.card (dc B N (b * a)) := by
    have hnaa : (na : G) ∈ dc B N a := by
      rw [mem_dc_of_lift hna]; exact ⟨1, B.one_mem, 1, B.one_mem, by simp⟩
    have hsub : (fun y : G => y * (na : G)) '' (dc B N b) ⊆ dc B N (b * a) := by
      rintro _ ⟨y, hy, rfl⟩
      exact dc_mul_dc_of_ne h hb ha hab.symm (Set.mul_mem_mul hy hnaa)
    simp only [Nat.card_coe_set_eq]
    calc (dc B N b).ncard = ((fun y : G => y * (na : G)) '' (dc B N b)).ncard :=
          (Set.ncard_image_of_injective _ (mul_left_injective (na : G))).symm
      _ ≤ (dc B N (b * a)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hX₁split : Nat.card X₁ = Nat.card (dc B N b) + Nat.card (dc B N (b * a)) :=
    card_union_of_disjoint (hD nbba)
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hBe : 2 ≤ 2 ^ e := by
    have h1 := hlow
    rw [hcDb, he] at h1
    exact Nat.le_of_mul_le_mul_right h1 hBpos
  have heq : 3 * 2 ^ o₁ = 2 + 2 ^ e := by
    have h1 : (3 * 2 ^ o₁) * Nat.card B = (2 + 2 ^ e) * Nat.card B := by
      calc (3 * 2 ^ o₁) * Nat.card B = 2 ^ o₁ * (3 * Nat.card B) := by ring
        _ = 2 ^ o₁ * Nat.card Q := by rw [hPa]
        _ = Nat.card X₁ := hX₁c.symm
        _ = Nat.card (dc B N b) + Nat.card (dc B N (b * a)) := hX₁split
        _ = 2 * Nat.card B + 2 ^ e * Nat.card B := by rw [hcDb, he]
        _ = (2 + 2 ^ e) * Nat.card B := by ring
    exact Nat.eq_of_mul_eq_mul_right hBpos h1
  have ho : 2 ^ o₁ = 2 := arith_pow_two heq hBe
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
  have htot : Nat.card (parabolic B N {a, b}) = 3 * 2 ^ k * (3 + 2 ^ o₂) := by
    rw [hcard, hX₀Q, hX₁c, hX₂c, ho, hPa, hk]
    ring
  rw [htot]
  intro h9
  have h3 : 3 ∣ 2 ^ k * (3 + 2 ^ o₂) := by
    have : 3 * 3 ∣ 3 * (2 ^ k * (3 + 2 ^ o₂)) := by
      have e1 : 3 * 2 ^ k * (3 + 2 ^ o₂) = 3 * (2 ^ k * (3 + 2 ^ o₂)) := by ring
      rw [← e1]; simpa using h9
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h4 | h4
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
    omega
  · have h5 : 3 ∣ 2 ^ o₂ := (Nat.dvd_add_right (dvd_refl 3)).1 h4
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
    omega

end Tits

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
