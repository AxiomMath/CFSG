module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCtx
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpin
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSpinMinus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement

section SixNodes

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

theorem rankOne_six_of_sl2 {i : Fin D.rank} {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : Nat.card k = 2) {x : (Fin D.rank → ℤ) → k → K}
    (hx : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x)
    {ρ : Matrix.SpecialLinearGroup (Fin 2) k →* K} (hinj : Function.Injective ρ)
    (hU : ∀ c, ρ (sl2Upper c) = x (Pi.single i 1) c)
    (hL : ∀ c, ρ (sl2Lower c) = x (-Pi.single i 1) c) :
    Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a := by
  have hrange := rankOne_eq_range_of_sl2 hx hU hL
  refine ⟨?_, ?_⟩
  · rw [hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, card_sl2, hk]
    norm_num
  · refine ⟨ρ (sl2Upper (1 : k) * sl2Lower 1), hrange ▸ ⟨_, rfl⟩, ρ (sl2Upper 1),
      hrange ▸ ⟨_, rfl⟩, fun h => ?_⟩
    apply sl2_upper_lower_not_commute (F := k)
    apply hinj
    simp only [map_mul, mul_assoc] at h ⊢
    exact h

end SixNodes

section SL

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {m : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem CoverCtx.false_sl_big (ctx : CoverCtx L S₀ A₁ A₂) (hm : 1 ≤ m) (hq4 : 4 ≤ Nat.card F)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* ↥L ⧸ Subgroup.center ↥L) :
    False := by
  have h := borelQuotient_sl e
  exact ctx.false_of_node h (hasSL2Node_sl (⟨0, hm⟩ : Fin m)).hasOrderThree
    ((rankOneNode_sl (⟨0, hm⟩ : Fin m)).perfect hq4)

theorem CoverCtx.false_sl_two (ctx : CoverCtx L S₀ A₁ A₂) (hF : Nat.card F = 2) (hm : 3 ≤ m)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* ↥L ⧸ Subgroup.center ↥L) :
    False := by
  have h := borelQuotient_sl e
  have hM : Nat.card F - 1 = 1 := by omega
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin m) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  refine ctx.false_of_three_nodes h hM (twoLevi_sl hF) (fun i => (hasSL2Node_sl i).hasOrderThree)
    (fun i => ?_) (fun _ _ h => h.elim) h01 h02 h12
  obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (F := F) i
  exact rankOne_six_of_sl2 hF SL.isParametrization hφ hx hy

end SL

section Sp

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {n : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem CoverCtx.false_sp_big (ctx : CoverCtx L S₀ A₁ A₂) (hn : 1 ≤ n) (hq4 : 4 ≤ Nat.card F)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSp n F)) : False := by
  have h := borelQuotient_sp e
  exact ctx.false_of_node h (hasSL2Node_sp (⟨0, hn⟩ : Fin n)).hasOrderThree
    ((rankOneNode_sp (⟨0, hn⟩ : Fin n)).perfect hq4)

section SpTail

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic
open CFSG.LieType.Universal.Symplectic.SpExtras (ne_succ')

theorem sp_tail_exc3 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {k : Fin n}
    (hk2 : k.val + 2 = n) :
    ∃ V : Subgroup (StatedSp n K),
      V ≤ rankOne (rootGroup n K) k ⊔ rankOne (rootGroup n K) ⟨k.val + 1, by omega⟩ ∧
        ⁅V, V⁆ = V ∧ 3 ∣ Nat.card V := by
  have hk : k.val + 1 < n := by omega
  have hlong : ¬(⟨k.val + 1, hk⟩ : Fin n).val + 1 < n := by
    simp only
    omega
  have hsup : rankOne (rootGroup n K) k ⊔ rankOne (rootGroup n K) ⟨k.val + 1, hk⟩ =
      (spEmbed (K := K) (pairMap k ⟨k.val + 1, hk⟩) (pairMap_injective (ne_succ' hk))).range := by
    rw [← range_shortBlock_eq_rankOne hk, ← range_longBlock_eq_rankOne hlong]
    exact shortBlock_sup_longBlock (ne_succ' hk)
  have := Fintype.ofFinite K
  have hK2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  set θ := spEmbed (K := K) (pairMap k ⟨k.val + 1, hk⟩) (pairMap_injective (ne_succ' hk)) with hθ
  have hθinj : Function.Injective θ := spEmbed_injective (pairMap_injective (ne_succ' hk))
  let Φ : θ.range ≃* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective hθinj).symm.trans
      (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm K hK2)
  obtain ⟨V, hVS, hV, h360, h720⟩ := exists_perfect_of_equiv_perm_six Φ
  exact ⟨V, hsup ▸ hVS, hV, by rw [h360]; norm_num⟩

end SpTail

theorem CoverCtx.false_sp_two (ctx : CoverCtx L S₀ A₁ A₂) (hF : Nat.card F = 2) (hn : 3 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSp n F)) : False := by
  have h := borelQuotient_sp e
  have hM : Nat.card F - 1 = 1 := by omega
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  refine ctx.false_of_three_nodes h hM (twoLevi_sp hF) (fun i => (hasSL2Node_sp i).hasOrderThree)
    (fun i => ?_) (fun i j hij => ?_) h01 h02 h12
  · obtain ⟨φ, hφ, hx, hy⟩ := Sp.rankOne (F := F) i
    exact rankOne_six_of_sl2 hF Sp.isParametrization hφ hx hy
  · rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hi1 : i.val + 1 < n := by omega
      have hk : j = ⟨i.val + 1, hi1⟩ := Fin.ext (by simp; omega)
      subst hk
      exact sp_tail_exc3 hF h1
    · have hj1 : j.val + 1 < n := by omega
      have hk : i = ⟨j.val + 1, hj1⟩ := Fin.ext (by simp; omega)
      subst hk
      rw [sup_comm]
      exact sp_tail_exc3 hF h1

end Sp

section SpinPlus

open CFSG.LieType.Universal.Spin

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {n : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem CoverCtx.false_spinPlus_big (ctx : CoverCtx L S₀ A₁ A₂) (hn : 3 ≤ n)
    (hq4 : 4 ≤ Nat.card F)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) : False := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have h := borelQuotient_spinPlus hn e
  exact ctx.false_of_node h (hasSL2Node_spinPlus hn (⟨0, by omega⟩ : Fin n)).hasOrderThree
    ((rankOneNode_spinPlus hn (⟨0, by omega⟩ : Fin n)).perfect hq4)

theorem CoverCtx.false_spinPlus_two (ctx : CoverCtx L S₀ A₁ A₂) (hF : Nat.card F = 2)
    (hn : 3 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) : False := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have h := borelQuotient_spinPlus hn e
  have hM : Nat.card F - 1 = 1 := by omega
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  refine ctx.false_of_three_nodes h hM (twoLevi_spinPlus hF hn h.ct h.extras)
    (fun i => (hasSL2Node_spinPlus hn i).hasOrderThree) (fun i => ?_) (fun _ _ h => h.elim)
    h01 h02 h12
  obtain ⟨φ, hφ, hx, hy⟩ := SpinPlus.rankOne (K := F) hn i
  exact rankOne_six_of_sl2 hF (SpinPlus.isParametrization (K := F) hn) hφ hx hy

end SpinPlus

section SU

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {n f : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2]

theorem CoverCtx.false_su_big (ctx : CoverCtx L S₀ A₁ A₂) (hF : Nat.card F = (2 ^ f) ^ 2)
    (hn : 3 ≤ n) (hq4 : 4 ≤ 2 ^ f)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n (2 ^ f) F)) : False := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  have h := borelQuotient_su hF (by omega) ζ hζ e
  have hk : 0 < n / 2 := by omega
  exact ctx.false_of_node h (hasOrderThree_su hF (⟨0, hk⟩ : Fin (n / 2)))
    ((rankOneNode_su hF (⟨0, hk⟩ : Fin (n / 2))).perfect hq4)

theorem CoverCtx.false_su_two (ctx : CoverCtx L S₀ A₁ A₂) (hF : Nat.card F = (2 ^ 1) ^ 2)
    (hn : 4 ≤ n) (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n (2 ^ 1) F)) :
    False := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have : Finite (SU (unitaryInvolution F 2 1) n) := Finite.of_injective _ Subtype.val_injective
  have h := borelQuotient_su hF (by omega) ζ hζ e
  have hk : 0 + 1 < n / 2 := by omega
  exact ctx.false_of_node h (hasOrderThree_su hF (⟨0, by omega⟩ : Fin (n / 2)))
    (commutator_eq_self_of_isPerfect (su_short_isPerfect hF (k := ⟨0, by omega⟩) hk))

end SU

section SpinMinus

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {n : ℕ} {F : Type} [Field F]
  [Finite F] [CharP F 2] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem CoverCtx.false_spinMinus_big (ctx : CoverCtx L S₀ A₁ A₂) (hn : 4 ≤ n)
    (hq4 : 4 ≤ Nat.card F)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) :
    False := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have h := borelQuotient_spinMinus hirr hn e
  have hk : 0 + 1 < n - 1 := by omega
  exact ctx.false_of_node h (hasOrderThree_spinMinus hirr (⟨0, by omega⟩ : Fin (n - 1)))
    ((rankOneNode_spinMinus_long hirr (k := ⟨0, by omega⟩) hk).perfect hq4)

include hirr in
theorem CoverCtx.false_spinMinus_two (ctx : CoverCtx L S₀ A₁ A₂) (hF : Nat.card F = 2)
    (hn : 4 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) :
    False := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have h := borelQuotient_spinMinus hirr hn e
  have hk : ¬ (n - 2) + 1 < n - 1 := by omega
  exact ctx.false_of_node h (hasOrderThree_spinMinus hirr (⟨n - 2, by omega⟩ : Fin (n - 1)))
    (spinMinus_short_perfect hirr hF (k := ⟨n - 2, by omega⟩) hk)

end SpinMinus

section All

theorem eq_one_of_card_two_pow_lt {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (h4 : ¬ 4 ≤ Nat.card F) : f = 1 := by
  have h1 := Finite.one_lt_card (α := F)
  have hf1 : f ≤ 1 := by
    by_contra h
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hF
    omega
  omega

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W} {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem CoverCtx.false_sl_all (ctx : CoverCtx L S₀ A₁ A₂) {m f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hm : 1 ≤ m) (hm3 : f = 1 → 3 ≤ m)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* ↥L ⧸ Subgroup.center ↥L) :
    False := by
  by_cases h4 : 4 ≤ Nat.card F
  · exact ctx.false_sl_big hm h4 e
  · have hf := eq_one_of_card_two_pow_lt hF h4
    subst hf
    exact ctx.false_sl_two (by simpa using hF) (hm3 rfl) e

theorem CoverCtx.false_sp_all (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hn : 1 ≤ n) (hn3 : f = 1 → 3 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSp n F)) : False := by
  by_cases h4 : 4 ≤ Nat.card F
  · exact ctx.false_sp_big hn h4 e
  · have hf := eq_one_of_card_two_pow_lt hF h4
    subst hf
    exact ctx.false_sp_two (by simpa using hF) (hn3 rfl) e

theorem CoverCtx.false_spinPlus_all (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hn : 3 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) : False := by
  by_cases h4 : 4 ≤ Nat.card F
  · exact ctx.false_spinPlus_big hn h4 e
  · have hf := eq_one_of_card_two_pow_lt hF h4
    subst hf
    exact ctx.false_spinPlus_two (by simpa using hF) hn e

theorem CoverCtx.false_su_all (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hn4 : f = 1 → 4 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU n (2 ^ f) F)) : False := by
  by_cases h4 : 4 ≤ 2 ^ f
  · exact ctx.false_su_big hF hn h4 e
  · have h1 := Finite.one_lt_card (α := F)
    have hf1 : f ≤ 1 := by
      by_contra h
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact h4 (by simpa using this)
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hF
      omega
    have hf : f = 1 := by omega
    subst hf
    exact ctx.false_su_two hF (hn4 rfl) e

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted in
theorem CoverCtx.false_spinMinus_all {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ} (hF : Nat.card F = 2 ^ f) (hn : 4 ≤ n)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) :
    False := by
  by_cases h4 : 4 ≤ Nat.card F
  · exact ctx.false_spinMinus_big hirr hn h4 e
  · have hf := eq_one_of_card_two_pow_lt hF h4
    subst hf
    exact ctx.false_spinMinus_two hirr (by simpa using hF) hn e

end All

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
