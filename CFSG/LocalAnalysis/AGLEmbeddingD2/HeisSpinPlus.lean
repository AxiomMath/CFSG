module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinPlusPart
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinPlusReal
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisSpinPlusBlock

public section

namespace CFSG.AGLEmbeddingD2.HeisSpinPlus

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.SquareGeneric CFSG.AGLEmbeddingD2.SquareSpinPlus

section Orth

variable {n : ℕ}

theorem cartanD_eq_zero_of_gap {a b : Fin n} (h : a.val + 2 ≤ b.val) (h3 : a.val + 3 ≠ n) :
    a ≠ b ∧ cartanD n a b = 0 := by
  have hab : a ≠ b := fun e => by rw [e] at h; omega
  exact ⟨hab, cartanD_eq_zero_of_not_adj hab (by omega)⟩

@[expose] def OrthTriples (a₁ a₂ a₃ b₁ b₂ b₃ : Fin n) : Prop :=
  ∀ x ∈ ({a₁, a₂, a₃} : Set (Fin n)), ∀ y ∈ ({b₁, b₂, b₃} : Set (Fin n)),
    x ≠ y ∧ cartanD n x y = 0

variable {F : Type} [Field F] {hn : 3 ≤ n} {w : Fin n → spinGroup (quadPlus n F)}
  {H : Fin n → Subgroup (spinGroup (quadPlus n F))}

theorem commutes_of_orthTriples (hext : SteinbergExtras (plusDatum n F hn) w H)
    {a₁ a₂ a₃ b₁ b₂ b₃ : Fin n} (h : OrthTriples a₁ a₂ a₃ b₁ b₂ b₃) :
    Commutes (rankOne (plusDatum n F hn).rootGroup a₁ ⊔ rankOne (plusDatum n F hn).rootGroup a₂ ⊔
      rankOne (plusDatum n F hn).rootGroup a₃)
      (rankOne (plusDatum n F hn).rootGroup b₁ ⊔ rankOne (plusDatum n F hn).rootGroup b₂ ⊔
        rankOne (plusDatum n F hn).rootGroup b₃) := by
  have c : ∀ x ∈ ({a₁, a₂, a₃} : Set (Fin n)), ∀ y ∈ ({b₁, b₂, b₃} : Set (Fin n)),
      Commutes (rankOne (plusDatum n F hn).rootGroup x) (rankOne (plusDatum n F hn).rootGroup y) :=
    fun x hx y hy => commutes_rankOne_of_cartan_eq_zero hext (h x hx y hy).1 (h x hx y hy).2
  refine Commutes.sup_left (Commutes.sup_left ?_ ?_) ?_ <;>
    refine Commutes.sup_right (Commutes.sup_right ?_ ?_) ?_ <;>
    exact c _ (by simp) _ (by simp)

end Orth

section Arith

variable {F : Type} [Field F] [Finite F]

theorem exists_unit_order_five {f : ℕ} (hf : 4 ∣ f) (hF : Nat.card F = 2 ^ f) :
    ∃ t : Fˣ, t ^ 5 = 1 ∧ t ≠ 1 := by
  have h5 : 5 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    exact (CyclicSylowGL.five_dvd_two_pow_sub_one_iff f).2 hf
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 5 h5
  refine ⟨t, by rw [← ht, pow_orderOf_eq_one], fun h => ?_⟩
  rw [h, orderOf_one] at ht
  omega

theorem exists_omega {f : ℕ} (hf : Even f) (hF : Nat.card F = 2 ^ f) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨k, hk⟩ := hf
  have hq : Nat.card F = 4 ^ k := by rw [hF, hk, ← two_mul, pow_mul]; norm_num
  have hq3 : 3 ∣ Nat.card F - 1 := by
    rw [hq]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
  have h3 : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact hq3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω3 : ω ^ 3 = 1 := by rw [← hω, pow_orderOf_eq_one]
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hω
    omega
  refine ⟨(ω : F), ?_⟩
  have h1 : ((ω : F) - 1) * ((ω : F) ^ 2 + ω + 1) = 0 := by
    have : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
    linear_combination this
  have h2 : (ω : F) - 1 ≠ 0 := fun h => hω1 (Units.ext (sub_eq_zero.1 h))
  exact (mul_eq_zero.1 h1).resolve_left h2

end Arith

section Slice

variable {n : ℕ} {F : Type} [Field F] {Y : Type} [Group Y] {X : Type} [Group X] [Finite X]
  {M : ℕ} {π : spinGroup (quadPlus n F) →* Y} {J : Subgroup Y} {hn : 3 ≤ n}

theorem three_le_pRank_of_pieces
    (hb : BorelQuotient (plusDatum n F hn) (weylD F hn) (fun k => (torusD F hn k).range) π M)
    (hBJ : borel (plusDatum n F hn) (fun k => (torusD F hn k).range) ≤ J.comap π)
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ : Fin n} (hA : Piece5 hn F a₁ a₂ a₃) (hB : Piece5 hn F b₁ b₂ b₃)
    (hC : Piece5 hn F c₁ c₂ c₃)
    (hAI : ∀ k ∈ ({a₁, a₂, a₃} : Set (Fin n)), k ∈ negIndices (plusDatum n F hn) (J.comap π))
    (hBI : ∀ k ∈ ({b₁, b₂, b₃} : Set (Fin n)), k ∈ negIndices (plusDatum n F hn) (J.comap π))
    (hCI : ∀ k ∈ ({c₁, c₂, c₃} : Set (Fin n)), k ∈ negIndices (plusDatum n F hn) (J.comap π))
    (cAB : OrthTriples a₁ a₂ a₃ b₁ b₂ b₃) (cAC : OrthTriples a₁ a₂ a₃ c₁ c₂ c₃)
    (cBC : OrthTriples b₁ b₂ b₃ c₁ c₂ c₃) : 3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hL : ∀ k ∈ negIndices (plusDatum n F hn) (J.comap π),
      rankOne (plusDatum n F hn).rootGroup k ≤ J.comap π := fun k hk =>
    rankOne_le_of_mem_negIndices hBJ hk
  exact HeisEngine.three_le_pRank_of_triple (by decide) hb.ker_central ρ hρ hρker
    (commutes_of_orthTriples hb.extras cAB) (commutes_of_orthTriples hb.extras cAC)
    (commutes_of_orthTriples hb.extras cBC)
    (realOver_piece hn hA (hL _ (hAI _ (by simp))) (hL _ (hAI _ (by simp)))
      (hL _ (hAI _ (by simp))))
    (realOver_piece hn hB (hL _ (hBI _ (by simp))) (hL _ (hBI _ (by simp)))
      (hL _ (hBI _ (by simp))))
    (realOver_piece hn hC (hL _ (hCI _ (by simp))) (hL _ (hCI _ (by simp)))
      (hL _ (hCI _ (by simp))))

variable [CharP F 2]

theorem three_le_pRank_of_torus_nodes (hn4 : 4 ≤ n)
    (hb : BorelQuotient (plusDatum n F hn) (weylD F hn) (fun k => (torusD F hn k).range) π M)
    (hBJ : borel (plusDatum n F hn) (fun k => (torusD F hn k).range) ≤ J.comap π)
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X) {t : Fˣ}
    (ht5 : t ^ 5 = 1) (ht1 : t ≠ 1) : 3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨n - 2, by omega⟩
  let c : Fin n := ⟨n - 1, by omega⟩
  have hab : a ≠ b := fun h => by have := congrArg Fin.val h; simp [a, b] at this; omega
  have hac : a ≠ c := fun h => by have := congrArg Fin.val h; simp [a, c] at this; omega
  have hbc : b ≠ c := fun h => by have := congrArg Fin.val h; simp [b, c] at this; omega
  have cab : cartanD n a b = 0 := cartanD_eq_zero_of_not_adj hab (by simp [a, b]; omega)
  have cac : cartanD n a c = 0 := cartanD_eq_zero_of_not_adj hac (by simp [a, c]; omega)
  have cbc : cartanD n b c = 0 := cartanD_eq_zero_of_not_adj hbc (by simp [b, c]; omega)
  exact HeisEngine.three_le_pRank_of_triple (by decide) hb.ker_central ρ hρ hρker
    (commutes_rankOne_of_cartan_eq_zero hb.extras hab cab)
    (commutes_rankOne_of_cartan_eq_zero hb.extras hac cac)
    (commutes_rankOne_of_cartan_eq_zero hb.extras hbc cbc) (realOver_torus hn hBJ ht5 ht1 a)
    (realOver_torus hn hBJ ht5 ht1 b) (realOver_torus hn hBJ ht5 ht1 c)

theorem three_le_pRank_of_omega_nodes
    (hb : BorelQuotient (plusDatum n F hn) (weylD F hn) (fun k => (torusD F hn k).range) π M)
    (hBJ : borel (plusDatum n F hn) (fun k => (torusD F hn k).range) ≤ J.comap π)
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (cab : cartanD n a b = 0) (cac : cartanD n a c = 0) (cbc : cartanD n b c = 0)
    (ha : a ∈ negIndices (plusDatum n F hn) (J.comap π))
    (hb2 : b ∈ negIndices (plusDatum n F hn) (J.comap π))
    (hc : c ∈ negIndices (plusDatum n F hn) (J.comap π)) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact HeisEngine.three_le_pRank_of_triple (by decide) hb.ker_central ρ hρ hρker
    (commutes_rankOne_of_cartan_eq_zero hb.extras hab cab)
    (commutes_rankOne_of_cartan_eq_zero hb.extras hac cac)
    (commutes_rankOne_of_cartan_eq_zero hb.extras hbc cbc)
    (realOver_omega hn hω (rankOne_le_of_mem_negIndices hBJ ha))
    (realOver_omega hn hω (rankOne_le_of_mem_negIndices hBJ hb2))
    (realOver_omega hn hω (rankOne_le_of_mem_negIndices hBJ hc))

theorem three_le_pRank_of_badA
    (hb : BorelQuotient (plusDatum n F hn) (weylD F hn) (fun k => (torusD F hn k).range) π M)
    (hBJ : borel (plusDatum n F hn) (fun k => (torusD F hn k).range) ≤ J.comap π)
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X) {u : ℕ}
    (hu : BadA (n := n) (negIndices (plusDatum n F hn) (J.comap π)) u) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  obtain ⟨hun, hI⟩ := hu
  refine three_le_pRank_of_pieces hb hBJ ρ hρ hρker (piece_A3 hn (u := u) (by omega))
    (piece_A3 hn (u := u + 4) (by omega)) (piece_A3 hn (u := u + 8) (by omega)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl <;>
      exact hI _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl <;>
      exact hI _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl <;>
      exact hI _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)
  all_goals
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      exact cartanD_eq_zero_of_gap (by dsimp only; omega) (by dsimp only; omega)

theorem three_le_pRank_of_badD
    (hb : BorelQuotient (plusDatum n F hn) (weylD F hn) (fun k => (torusD F hn k).range) π M)
    (hBJ : borel (plusDatum n F hn) (fun k => (torusD F hn k).range) ≤ J.comap π)
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (hD : BadD (n := n) (negIndices (plusDatum n F hn) (J.comap π))) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  obtain ⟨hun, hI⟩ := hD
  refine three_le_pRank_of_pieces hb hBJ ρ hρ hρker (piece_A3 hn (u := n - 11) (by omega))
    (piece_A3 hn (u := n - 7) (by omega)) (piece_D3 hn) ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl <;>
      exact hI _ (Or.inl ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩)
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl <;>
      exact hI _ (Or.inl ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩)
  · intro k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl <;> exact hI _ (Or.inr (by dsimp only; omega))
  all_goals
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      exact cartanD_eq_zero_of_gap (by dsimp only; omega) (by dsimp only; omega)

end Slice

section Main

theorem three_le_pRank_five_spinPlus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) {X : Type} [Group X] [Finite X]
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (hρ5 : Nat.Coprime 5 (Nat.card ρ.ker)) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (P : Subgroup Y) (hPJ : P ≤ J) (hP : IsPGroup 5 P) (hPc : ¬ IsMulCommutative P) :
    3 ≤ CFSG.Open.pRank 5 (J.comap ρ) := by
  classical
  have _ := hJ
  have _ := hρ5
  have hn3 : 3 ≤ n := by omega
  have := Fintype.ofFinite F
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hb := borelQuotient_spinPlus hn3 e
  obtain ⟨π', hb', hker', hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨Q, hQle, hQ5, hQc⟩ :=
    HeisEngine.exists_nonabelian_le_torus_sup_leviM hb' hBJ (p := 5) (by norm_num) hPJ hP hPc
  set I : Set (Fin n) := negIndices (plusDatum n F hn3) (J.comap π') with hI
  have hQs : Q ≤ partSub (F := F) (part I) :=
    hQle.trans (sup_le (torus_le_partSub hn3 _)
      (leviM_le_partSub hn3 fun k hk => compat_part hn3 hk))
  have hcases : 4 ∣ (f : ℕ) ∨ (f : ℕ) % 4 = 2 ∨ Odd (f : ℕ) := by
    rcases Nat.even_or_odd (f : ℕ) with ⟨k, hk⟩ | hfo
    · omega
    · exact Or.inr (Or.inr hfo)
  rcases hcases with h4 | h2 | hfo
  ·
    obtain ⟨t, ht5, ht1⟩ := exists_unit_order_five h4 hfc
    exact three_le_pRank_of_torus_nodes hn hb' hBJ ρ hρ hρker ht5 ht1
  ·
    obtain ⟨ω, hω⟩ := exists_omega (⟨(f : ℕ) / 2, by omega⟩ : Even (f : ℕ)) hfc
    by_cases ho : ∃ a ∈ I, ∃ b ∈ I, ∃ c ∈ I, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ cartanD n a b = 0 ∧
        cartanD n a c = 0 ∧ cartanD n b c = 0
    · obtain ⟨a, ha, b, hb2, c, hc, hab, hac, hbc, cab, cac, cbc⟩ := ho
      exact three_le_pRank_of_omega_nodes hb' hBJ ρ hρ hρker hω hab hac hbc cab cac cbc ha hb2 hc
    · exfalso
      rcases exists_orth_triple_or_card_lt_ten hn3 I with htri | hsmall
      · exact ho htri
      · exact hQc (isMulCommutative_of_part_two h2 hfc hQs hQ5 hsmall)
  ·
    rcases badA_or_badD_or_card hn3 I with ⟨u, hu⟩ | hD | hsmall
    · exact three_le_pRank_of_badA hb' hBJ ρ hρ hρker hu
    · exact three_le_pRank_of_badD hb' hBJ ρ hρ hρker hD
    · exact (hQc (isMulCommutative_of_part_odd hfo hfc hQs hQ5 hsmall)).elim

end Main

end CFSG.AGLEmbeddingD2.HeisSpinPlus
