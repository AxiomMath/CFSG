module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrthSp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverModels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSep

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sp_card_rankOne (hF : Nat.card F = 2) (k : Fin n) :
    Nat.card (rankOne (rootDatum n F).rootGroup k) = 6 := by
  obtain ⟨φ, hφ, hx, hy⟩ := Sp.rankOne (F := F) k
  exact card_rankOne_eq_six hF Sp.isParametrization hφ hx hy

theorem sp_cartan_eq_zero (a c : Fin n) (hac : a.val + 2 ≤ c.val) :
    (rootDatum n F).cartan a c = 0 := by
  simp only [rootDatum, cartanC]
  have h1 : a ≠ c := fun h => by subst h; omega
  have h2 : ¬ (a.val + 1 = c.val ∨ c.val + 1 = a.val) := by omega
  simp [h1, h2]

theorem sp_hfam (hF : Nat.card F = 2) (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    [Finite ↥(StatedSp n F)] {π : ↥(StatedSp n F) →* Y} {M : ℕ} (hM : M = 1)
    (h : BorelQuotient (rootDatum n F) (weylRep n F) (torus n F) π M) (col : Fin n → Bool) :
    ∃ i j : Fin n, i ≠ j ∧ col i = col j ∧
      (OrthSep (rootDatum n F) π i j ∨
        ¬ CFSG.HallHigman.IsPSolvable 3
          ↥((rankOne (rootDatum n F).rootGroup i ⊔ rankOne (rootDatum n F).rootGroup j).map π)) := by
  subst hM
  have hinj := borelQuotient_injective_of_one h
  have hH := borelQuotient_torus_eq_bot_of_one h
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hadj : ∀ i j : Fin n, i.val + 1 = j.val →
      ¬ CFSG.HallHigman.IsPSolvable 3
        ↥((rankOne (rootDatum n F).rootGroup i ⊔ rankOne (rootDatum n F).rootGroup j).map π) :=
    fun i j hij => not_isPSolvable_map_of_injective hinj (sp_adj hF i j hij)
  have hac : OrthSep (rootDatum n F) π a c := by
    obtain ⟨xi, hxi, yi, hyi, xj, hxj, yj, hyj, hi3, hi1, hj3, hj1, hnot, hnoconj⟩ :=
      CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoCoverOrth.sp_orth (n := n) (F := F) (i := a) (j := c) hF
        (fun h => by have := congrArg Fin.val h; simp [a, c] at this)
        (by simp [a, c]) (by simp [a, c])
    exact orthSep_of_noConj h hinj hH (sp_card_rankOne hF)
      (fun k => hasOrderThree_data (hasSL2Node_sp (n := n) (F := F) k).hasOrderThree)
      (fun h => by have := congrArg Fin.val h; simp [a, c] at this)
      (sp_cartan_eq_zero a c (by simp [a, c])) hxi hyi hxj hyj hi3 hi1 hj3 hj1 hnot hnoconj
  obtain ⟨i, j, hcol, hP, hij⟩ := exists_pair_of_three a b c
    (fun i j => OrthSep (rootDatum n F) π i j ∨
      ¬ CFSG.HallHigman.IsPSolvable 3
        ↥((rankOne (rootDatum n F).rootGroup i ⊔ rankOne (rootDatum n F).rootGroup j).map π))
    (Or.inr (hadj a b rfl)) (Or.inl hac) (Or.inr (hadj b c rfl)) col
  refine ⟨i, j, ?_, hcol, hP⟩
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Fin.ext_iff, a, b, c]

theorem CoverCtx.false_of_psp_two {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}
    (ctx : CoverCtx L S₀ A₁ A₂)
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 1) : False := by
  obtain ⟨⟨-, -, hn2, hne⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have : n = 2 := by omega
    subst this
    exact hne (by simp)
  have hM : Nat.card F - 1 = 1 := by omega
  exact false_of_cover_two ctx.comp ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ ctx.trans
    (borelQuotient_sp e)
    (fun γ hγ x hx => sq_eq_one_of_isParametrization Sp.isParametrization hγ hx)
    (fun {π'} hπ' col => sp_hfam hF2 hn3 hM hπ' col)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
