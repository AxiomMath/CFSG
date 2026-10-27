module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA

theorem ext_tag_of_iso_A {lab : LargeEvenLabel} {r f : ℕ}
    (h : CFSG.StandardType.GGLabelIso lab ⟨.A, r, f⟩) :
    lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2) := by
  obtain ⟨t, l, m⟩ := lab
  unfold CFSG.StandardType.GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ext_tag_of_iso_twA {lab : LargeEvenLabel} {r f : ℕ}
    (h : CFSG.StandardType.GGLabelIso lab ⟨.twA, r, f⟩) :
    lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3) := by
  obtain ⟨t, l, m⟩ := lab
  unfold CFSG.StandardType.GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ext_label_of_iso_g2der {lab : LargeEvenLabel}
    (h : CFSG.StandardType.GGLabelIso lab ⟨.G2der, 0, 1⟩) : lab = ⟨.G2der, 0, 1⟩ := by
  obtain ⟨t, l, m⟩ := lab
  unfold CFSG.StandardType.GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ext_split_untwisted {p l n : ℕ} {t : LargeEvenLieTag} (ht : LargeEvenUntwisted t)
    (h : GLASplit16 p ⟨t, l, n⟩) : p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
  rw [GLASplit16, LargeEvenSplit16] at h
  rcases h with h | h | h | h
  · exact Or.inl h.2
  · exact absurd ht h.1
  · exfalso
    obtain ⟨h1, -⟩ := h
    have h1' : t = .twD ∨ t = .triD4 ∨ t = .twB2 ∨ t = .twF4 := h1
    rcases h1' with rfl | rfl | rfl | rfl <;> exact ht
  · exact Or.inr h

theorem ext_split_twA {p l n : ℕ} (h : GLASplit16 p ⟨.twA, l, n⟩) : p ∣ 2 ^ n + 1 := by
  rw [GLASplit16, LargeEvenSplit16] at h
  rcases h with h | h | h | h
  · exact absurd h.1 (by simp [LargeEvenUntwisted])
  · exact h.2.2.2
  · rcases h.1 with h' | h' | h' | h' <;> simp at h'
  · obtain ⟨h1, h2⟩ := h
    have h1' : n = 1 := h1
    subst h1' h2
    norm_num

theorem ext_split_twD {p l n : ℕ} (h : GLASplit16 p ⟨.twD, l, n⟩) :
    p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
  rw [GLASplit16, LargeEvenSplit16] at h
  rcases h with h | h | h | h
  · exact absurd h.1 (by simp [LargeEvenUntwisted])
  · exact Or.inl h.2.2.2
  · exact Or.inr (Or.inl h.2)
  · exact Or.inr (Or.inr h)

theorem ext_rk2Ord_eq_one {p n : ℕ} (h : p ∣ 2 ^ n - 1) : rk2Ord p n = 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h0 : ((2 ^ n - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  rw [Nat.cast_sub h1] at h0
  push_cast at h0
  have h2 : (2 : ZMod p) ^ n = 1 := sub_eq_zero.1 h0
  unfold rk2Ord
  rw [h2, orderOf_one]

theorem ext_rk2Mult_twD_three (n : ℕ) : rk2Mult ⟨.twD, 3, n⟩ 1 = 2 := by
  simp [rk2Mult]

theorem ext_lin_data {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω} {lab : GLALabel}
    (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2))
    (hraw : GLARawDatum lab fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥S ⧸ Subgroup.center ↥S ≃* R, GLASplit16 p lab ∧
        B ≤ Subgroup.normalizer (S : Set Ω) ∧
        ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) φ) :
    LinModelData p S B := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with htag | ⟨htag, hl⟩ | ⟨htag, hl⟩
  ·
    have ht : t = .A := htag
    subst ht
    simp only [GLAInLambda2, LargeEvenInLambda2] at hlab
    obtain ⟨hn, hl1, hl2⟩ := hlab
    dsimp only [GLARawDatum, LargeEvenRawDatum] at hraw
    obtain ⟨K, hF, hfin, hK, -, -, θ, hsplit, hN, hind⟩ := hraw
    exact ⟨n, l + 1, K, hF, hfin, θ, hK, hn, by omega, fun h => hl2 (by omega),
      ext_split_untwisted (t := .A) trivial hsplit, hN, hind⟩
  ·
    have ht : t = .D := htag
    have hl3 : l = 3 := hl
    subst ht hl3
    simp only [GLAInLambda2, LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [GLARawDatum, LargeEvenRawDatum] at hraw
    rw [if_pos rfl] at hraw
    obtain ⟨K, hF, hfin, hK, -, -, θ, hsplit, hN, hind⟩ := hraw
    exact ⟨n, 4, K, hF, hfin, θ, hK, hn, by norm_num, fun h => absurd h (by norm_num),
      ext_split_untwisted (t := .D) trivial hsplit, hN, hind⟩
  ·
    have ht : t = .twD := htag
    have hl2 : l = 2 := hl
    subst ht hl2
    simp only [GLAInLambda2, LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [GLARawDatum, LargeEvenRawDatum] at hraw
    rw [if_pos rfl] at hraw
    obtain ⟨K, hF, hfin, hK, -, -, θ, hsplit, hN, hind⟩ := hraw
    have hcard : Nat.card K = 2 ^ (2 * n) := by
      rw [hK, ← pow_mul, mul_comm n 2]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ h1
    have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [mul_comm 2 n, pow_mul]
      zify [h1, h2]
      ring
    refine ⟨2 * n, 2, K, hF, hfin, θ, hcard, by omega, le_rfl, fun _ => by omega, ?_, hN, hind⟩
    rcases ext_split_twD hsplit with h | h | ⟨h1', h2'⟩
    · exact Or.inl (by rw [hfac]; exact Dvd.dvd.mul_right h _)
    · exact Or.inl (by rw [hfac]; exact Dvd.dvd.mul_left h _)
    · subst h1' h2'
      exact Or.inl (by norm_num)

theorem ext_uni_data {p : ℕ} {Ω : Type} [Group Ω] {S B : Subgroup Ω} {lab : GLALabel}
    (hlab : GLAInLambda2 lab) (htag : lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3))
    (hrank : 3 ≤ rk2Mult lab (rk2Ord p lab.n))
    (hraw : GLARawDatum lab fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥S ⧸ Subgroup.center ↥S ≃* R, GLASplit16 p lab ∧
        B ≤ Subgroup.normalizer (S : Set Ω) ∧
        ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' : ↥S => (l' : Ω) = b⁻¹ * l * b) φ) :
    UniModelData p S B := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with htag | ⟨htag, hl⟩
  ·
    have ht : t = .twA := htag
    subst ht
    simp only [GLAInLambda2, LargeEvenInLambda2] at hlab
    obtain ⟨hn, hl1, hl2⟩ := hlab
    dsimp only [GLARawDatum, LargeEvenRawDatum] at hraw
    obtain ⟨K, hF, hfin, hK, -, -, θ, hsplit, hN, hind⟩ := hraw
    exact ⟨n, l + 1, K, hF, hfin, θ, hK, hn, by omega, fun h => hl2 (by omega),
      ext_split_twA hsplit, hN, hind⟩
  ·
    have ht : t = .twD := htag
    have hl3 : l = 3 := hl
    subst ht hl3
    simp only [GLAInLambda2, LargeEvenInLambda2] at hlab
    obtain ⟨hn, -⟩ := hlab
    dsimp only [GLARawDatum, LargeEvenRawDatum] at hraw
    rw [if_neg (by decide : ¬ ((3 : ℕ) = 2)), if_pos rfl] at hraw
    obtain ⟨K, hF, hfin, hK, -, -, θ, hsplit, hN, hind⟩ := hraw
    have hdiv : p ∣ 2 ^ n + 1 := by
      rcases ext_split_twD hsplit with h | h | ⟨h1, h2⟩
      · exact h
      · exfalso
        have h1 : rk2Ord p n = 1 := ext_rk2Ord_eq_one h
        have h2 : rk2Mult (⟨.twD, 3, n⟩ : GLALabel) (rk2Ord p n) = 2 := by
          rw [h1]
          exact ext_rk2Mult_twD_three n
        have h3 : 3 ≤ rk2Mult (⟨.twD, 3, n⟩ : GLALabel) (rk2Ord p n) := hrank
        omega
      · subst h1 h2
        norm_num
    exact ⟨n, 4, K, hF, hfin, θ, hK, hn, by norm_num, fun h => absurd h (by norm_num),
      hdiv, hN, hind⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
