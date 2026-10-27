module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverFamilies
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSpin
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverModels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSep

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem cartanD_eq_zero (hn : 4 ≤ n) (a c : Fin n) (hac : a.val < c.val)
    (h : (a.val = 0 ∧ c.val + 2 = n) ∨ (a.val = 0 ∧ c.val + 1 = n) ∨
      (a.val + 2 = n ∧ c.val + 1 = n)) : cartanD n a c = 0 := by
  simp only [cartanD]
  have h1 : a ≠ c := fun h => by subst h; omega
  have h2 : ¬ ((a.val + 1 = c.val ∧ c.val + 1 < n) ∨ (c.val + 1 = a.val ∧ a.val + 1 < n) ∨
      (a.val + 3 = n ∧ c.val + 1 = n) ∨ (c.val + 3 = n ∧ a.val + 1 = n)) := by omega
  simp [h1, h2]

theorem spin_card_rankOne (hF : Nat.card F = 2) (hn : 3 ≤ n) [Finite (spinGroup (quadPlus n F))]
    (k : Fin n) : Nat.card (rankOne (plusDatum n F hn).rootGroup k) = 6 := by
  obtain ⟨φ, hφ, hx, hy⟩ := SpinPlus.rankOne (K := F) hn k
  exact card_rankOne_eq_six hF (SpinPlus.isParametrization (K := F) hn) hφ hx hy

theorem spin_hfam (hF : Nat.card F = 2) (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    [Finite (spinGroup (quadPlus n F))] {π : spinGroup (quadPlus n F) →* Y} {M : ℕ} (hM : M = 1)
    (h : BorelQuotient (plusDatum n F (by omega)) (weylD F (by omega : 3 ≤ n))
      (fun k => (torusD F (by omega : 3 ≤ n) k).range) π M) (col : Fin n → Bool) :
    ∃ i j : Fin n, i ≠ j ∧ col i = col j ∧
      (OrthSep (plusDatum n F (by omega)) π i j ∨
        ¬ CFSG.HallHigman.IsPSolvable 3
          ↥((rankOne (plusDatum n F (by omega)).rootGroup i ⊔
            rankOne (plusDatum n F (by omega)).rootGroup j).map π)) := by
  subst hM
  have hn3 : 3 ≤ n := by omega
  have hinj := borelQuotient_injective_of_one h
  have hH := borelQuotient_torus_eq_bot_of_one h
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨n - 2, by omega⟩
  let c : Fin n := ⟨n - 1, by omega⟩
  have horth : ∀ i j : Fin n, i ≠ j → (plusDatum n F hn3).cartan i j = 0 →
      OrthSep (plusDatum n F hn3) π i j := fun i j hij hcart => by
    obtain ⟨xi, hxi, yi, hyi, xj, hxj, yj, hyj, hi3, hi1, hj3, hj1, hnot, hnoconj⟩ :=
      spin_orth hF hn3 i j hij hcart
    exact orthSep_of_noConj h hinj hH (spin_card_rankOne hF hn3)
      (fun k => hasOrderThree_data (hasSL2Node_spinPlus (F := F) hn3 k).hasOrderThree)
      hij hcart hxi hyi hxj hyj hi3 hi1 hj3 hj1 hnot hnoconj
  have hab : OrthSep (plusDatum n F hn3) π a b :=
    horth a b (fun h => by have := congrArg Fin.val h; simp [a, b] at this; omega)
      (cartanD_eq_zero hn a b (by simp [a, b]; omega) (Or.inl ⟨rfl, by simp [b]; omega⟩))
  have hac : OrthSep (plusDatum n F hn3) π a c :=
    horth a c (fun h => by have := congrArg Fin.val h; simp [a, c] at this; omega)
      (cartanD_eq_zero hn a c (by simp [a, c]; omega) (Or.inr (Or.inl ⟨rfl, by simp [c]; omega⟩)))
  have hbc : OrthSep (plusDatum n F hn3) π b c :=
    horth b c (fun h => by have := congrArg Fin.val h; simp [b, c] at this; omega)
      (cartanD_eq_zero hn b c (by simp [b, c]; omega)
        (Or.inr (Or.inr ⟨by simp [b]; omega, by simp [c]; omega⟩)))
  obtain ⟨i, j, hcol, hP, hij⟩ := exists_pair_of_three a b c
    (fun i j => OrthSep (plusDatum n F hn3) π i j ∨
      ¬ CFSG.HallHigman.IsPSolvable 3
        ↥((rankOne (plusDatum n F hn3).rootGroup i ⊔
          rankOne (plusDatum n F hn3).rootGroup j).map π))
    (Or.inl hab) (Or.inl hac) (Or.inl hbc) col
  refine ⟨i, j, ?_, hcol, hP⟩
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Fin.ext_iff, a, b, c] <;> omega

theorem CoverCtx.false_of_pomegaPlus_two {W : Type} [Group W] [Finite W]
    {L S₀ A₁ A₂ : Subgroup W} (ctx : CoverCtx L S₀ A₁ A₂)
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 1) : False := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hM : Nat.card F - 1 = 1 := by omega
  exact false_of_cover_two ctx.comp ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ ctx.trans
    (borelQuotient_spinPlus hn3 e)
    (fun γ hγ x hx => sq_eq_one_of_isParametrization (SpinPlus.isParametrization (K := F) hn3) hγ hx)
    (fun {π'} hπ' col => spin_hfam hF2 hn hM hπ' col)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
