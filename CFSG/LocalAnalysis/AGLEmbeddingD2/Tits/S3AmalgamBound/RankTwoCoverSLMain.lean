module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverFamilies
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverModels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverSep

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank

variable {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sl_card_rankOne (hF : Nat.card F = 2) (k : Fin m) :
    Nat.card (rankOne (rootDatum m F).rootGroup k) = 6 := by
  obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (F := F) k
  exact card_rankOne_eq_six hF SL.isParametrization hφ hx hy

theorem sl_cartan_eq_zero (a c : Fin m) (hac : a.val + 2 ≤ c.val) :
    (rootDatum m F).cartan a c = 0 := by
  simp only [rootDatum, CartanMatrix.A]
  have h1 : a ≠ c := fun h => by subst h; omega
  have h2 : ¬ (a.val + 1 = c.val ∨ c.val + 1 = a.val) := by omega
  simp [h1, h2]

theorem sl_hfam (hF : Nat.card F = 2) (hm : 3 ≤ m) {Y : Type} [Group Y] [Finite Y]
    [Finite (Matrix.SpecialLinearGroup (Fin (m + 1)) F)]
    {π : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* Y} {M : ℕ} (hM : M = 1)
    (h : BorelQuotient (rootDatum m F) (weylRep m F) (torus m F) π M) (col : Fin m → Bool) :
    ∃ i j : Fin m, i ≠ j ∧ col i = col j ∧
      (OrthSep (rootDatum m F) π i j ∨
        ¬ CFSG.HallHigman.IsPSolvable 3
          ↥((rankOne (rootDatum m F).rootGroup i ⊔ rankOne (rootDatum m F).rootGroup j).map π)) := by
  subst hM
  have hinj := borelQuotient_injective_of_one h
  have hH := borelQuotient_torus_eq_bot_of_one h
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let c : Fin m := ⟨2, by omega⟩
  have hadj : ∀ i j : Fin m, i.val + 1 = j.val →
      ¬ CFSG.HallHigman.IsPSolvable 3
        ↥((rankOne (rootDatum m F).rootGroup i ⊔ rankOne (rootDatum m F).rootGroup j).map π) :=
    fun i j hij => not_isPSolvable_map_of_injective hinj (sl_adj hF i j hij)
  have hac : OrthSep (rootDatum m F) π a c := by
    obtain ⟨xi, hxi, yi, hyi, xj, hxj, yj, hyj, hi3, hi1, hj3, hj1, hnot, hnoconj⟩ :=
      sl_orth hF a c (by simp [a, c])
    exact orthSep_of_noConj h hinj hH (sl_card_rankOne hF)
      (fun k => hasOrderThree_data (hasSL2Node_sl (m := m) (F := F) k).hasOrderThree) (fun h => by have := congrArg Fin.val h; simp [a, c] at this)
      (sl_cartan_eq_zero a c (by simp [a, c])) hxi hyi hxj hyj hi3 hi1 hj3 hj1 hnot hnoconj
  obtain ⟨i, j, hcol, hP, hij⟩ := exists_pair_of_three a b c
    (fun i j => OrthSep (rootDatum m F) π i j ∨
      ¬ CFSG.HallHigman.IsPSolvable 3
        ↥((rankOne (rootDatum m F).rootGroup i ⊔ rankOne (rootDatum m F).rootGroup j).map π))
    (Or.inr (hadj a b rfl)) (Or.inl hac) (Or.inr (hadj b c rfl)) col
  refine ⟨i, j, ?_, hcol, hP⟩
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Fin.ext_iff, a, b, c]

theorem CoverCtx.false_of_psl_two {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}
    (ctx : CoverCtx L S₀ A₁ A₂) (hm : 3 ≤ m) (hF : Nat.card F = 2)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* ↥L ⧸ Subgroup.center ↥L) :
    False := by
  have hM : Nat.card F - 1 = 1 := by omega
  exact false_of_cover_two ctx.comp ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ ctx.trans
    (borelQuotient_sl e)
    (fun γ hγ x hx => sq_eq_one_of_isParametrization SL.isParametrization hγ hx)
    (fun {π'} hπ' col => sl_hfam hF hm hM hπ' col)

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
