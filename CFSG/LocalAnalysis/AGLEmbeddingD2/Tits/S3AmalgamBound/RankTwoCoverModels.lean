module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverBig
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeCensus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCore
public import CFSG.Timmesfeld.RankTwo.LevisBRankOne
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.RankThreeTheoremC

structure CoverCtx {W : Type} [Group W] [Finite W] (L S₀ A₁ A₂ : Subgroup W) : Prop where
  comp : CFSG.Open.IsComponentOf L ⊤
  syl : IsSylowTwoOf S₀ L
  cov : CoveredByTwo L S₀ A₁ A₂
  solv₁ : CFSG.HallHigman.IsPSolvable 3 ↥A₁
  solv₂ : CFSG.HallHigman.IsPSolvable 3 ↥A₂
  trans : ∀ E : Subgroup W, (E ≤ A₁ ⊓ L ∨ E ≤ A₂ ⊓ L) → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
    TransitiveOnNonidentity (Subgroup.normalizer (E : Set W)) E

variable {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}

theorem CoverCtx.false_of_psl (ctx : CoverCtx L S₀ A₁ A₂) {m : ℕ} (hm : 1 ≤ m) {F : Type}
    [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* ↥L ⧸ Subgroup.center ↥L) :
    False :=
  false_of_big_node ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ (borelQuotient_sl e) ⟨0, hm⟩
    (fun hπ' => not_isPSolvable_map_rankOne_of_sl2Node hπ' hF (hasSL2Node_sl ⟨0, hm⟩))

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem CoverCtx.false_of_psp (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) (hf : 2 ≤ f) : False := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hF4 := four_le_card_of_card_eq_two_pow hcard hf
  exact false_of_big_node ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ (borelQuotient_sp e) ⟨0, by change 0 < n; omega⟩
    (fun hπ' => not_isPSolvable_map_rankOne_of_sl2Node hπ' hF4
      (hasSL2Node_sp ⟨0, by change 0 < n; omega⟩))

open CFSG.LieType.Universal.Spin in
theorem CoverCtx.false_of_pomegaPlus (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f) (hf : 2 ≤ f) :
    False := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ n := by omega
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have hF4 := four_le_card_of_card_eq_two_pow hcard hf
  exact false_of_big_node ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ (borelQuotient_spinPlus hn3 e)
    ⟨0, by change 0 < n; omega⟩ (fun hπ' => not_isPSolvable_map_rankOne_of_sl2Node hπ' hF4
      (hasSL2Node_spinPlus hn3 ⟨0, by change 0 < n; omega⟩))

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem CoverCtx.false_of_psu (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) (hn4 : 4 ≤ n) : False := by
  obtain ⟨⟨-, hf1, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) n) := Finite.of_injective _ Subtype.val_injective
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left (by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1) 2
  have hk : (0 : ℕ) + 1 < n / 2 := by omega
  exact false_of_big_node ctx.syl ctx.cov ctx.solv₁ ctx.solv₂
    (borelQuotient_su hcard (by omega) ζ hζ e) (⟨0, by omega⟩ : Fin (n / 2))
    (fun hπ' => not_isPSolvable_map_rankOne_of_sl2Node hπ' hF4
      (hasSL2Node_su_short hcard (k := ⟨0, by omega⟩) hk))

section G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem CoverCtx.false_of_g2 (ctx : CoverCtx L S₀ A₁ A₂) {K : Type} [Field K] [Finite K]
    [CharP K 2] (e : ↥L ⧸ Subgroup.center ↥L ≃* AdjointQuotient .G2 K) (hK : 4 ≤ Nat.card K) :
    False := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  exact false_of_big_node ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ (borelQuotient_g2 e)
    (⟨0, by decide⟩ : Fin (Tag.rank .G2)) (fun hπ' => not_isPSolvable_map_rankOne_of_sl2Node hπ' hK
      (hasSL2Node_g2 (⟨0, by decide⟩ : Fin (Tag.rank .G2))))

end G2

section RankOne

open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank in
theorem CoverCtx.false_of_rank_one (ctx : CoverCtx L S₀ A₁ A₂) {K : Type} [Group K] [Finite K]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {M : ℕ}
    {π : K →* ↥L ⧸ Subgroup.center ↥L} (h : BorelQuotient D n H π M) (hr : D.rank = 1)
    (h3 : ∀ i, HasOrderThree D i) : False := by
  have hS : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := ctx.comp.2.2.2
  have hperfL : Group.IsPerfect ↥L := ⟨ctx.comp.2.2.1⟩
  have hperf : Group.IsPerfect (↥L ⧸ Subgroup.center ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective _)
  have hnc : ¬ IsMulCommutative (↥L ⧸ Subgroup.center ↥L) := by
    intro hc
    have : Subsingleton (↥L ⧸ Subgroup.center ↥L) := Group.IsPerfect.subsingleton_of_isMulCommutative
    exact not_subsingleton _ this
  have i0 : Fin D.rank := ⟨0, by omega⟩
  refine false_of_big_node ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ h i0 (fun {π'} hπ' hsolv => ?_)
  have htop : rankOne D.rootGroup i0 = ⊤ := by
    rw [eq_top_iff, ← hπ'.ct.iSup_eq_top]
    refine iSup₂_le fun γ hγ => hπ'.ct.le_rankOne i0 γ hγ (fun k hk => ?_)
    exact absurd (Fin.ext (by have := k.2; have := i0.2; omega)) hk
  rw [htop, Subgroup.map_top_of_surjective _ hπ'.surj] at hsolv
  have hsolv' : CFSG.HallHigman.IsPSolvable 3 (↥L ⧸ Subgroup.center ↥L) :=
    OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv Subgroup.topEquiv hsolv
  obtain ⟨u, -, hu⟩ := exists_order_three_map (h3 i0) (fun z hz => hπ'.ker_central z hz)
  have h3dvd : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := hu ▸ orderOf_dvd_natCard u
  exact not_isPSolvable_three_of_simple hS hnc h3dvd hsolv'

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits in
theorem CoverCtx.false_of_psu_three (ctx : CoverCtx L S₀ A₁ A₂) {f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 f) : False := by
  obtain ⟨⟨-, -, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hcard
  have : Finite (SU (unitaryInvolution F 2 f) 3) := Finite.of_injective _ Subtype.val_injective
  exact ctx.false_of_rank_one (borelQuotient_su hcard (by omega) ζ hζ e) rfl
    (fun i => hasOrderThree_su hcard i)

end RankOne

section SpinMinusShort

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg.CentralExt in
theorem hasSL2Node_spinMinus_short {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    [Finite (ShortField b c)] [CharP (ShortField b c) 2] (h4 : 4 ≤ Nat.card (ShortField b c))
    {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) :
    HasSL2Node (minusDatum n hirr) k (ShortField b c) := by
  obtain ⟨φ, hx, hy⟩ := CFSG.Timmesfeld.RankTwo.exists_hom_of_rankOneRels (shortRels n hirr k)
  have hS := sl2_isSimpleGroup (k := ShortField b c) h4
  have hx0 : (shortRels n hirr k).x 0 = 1 := RankOneRels.x_zero _
  refine ⟨φ, ?_, fun a => ?_, fun a => ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hb | ht
    · exact hb
    · exfalso
      have hmem : sl2Upper (1 : ShortField b c) ∈ φ.ker := by rw [ht]; exact Subgroup.mem_top _
      have h1 : φ (sl2Upper (1 : ShortField b c)) = 1 := MonoidHom.mem_ker.1 hmem
      rw [hx] at h1
      exact one_ne_zero (shortRels_x_injective hirr k (h1.trans hx0.symm))
  · rw [hx a]
    exact (mem_minusRootGroup_single_iff hirr hk _).2 ⟨a, rfl⟩
  · rw [hy a]
    exact (mem_minusRootGroup_neg_single_iff hirr hk _).2 ⟨a, rfl⟩

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg.CentralExt in
theorem CoverCtx.false_of_pomegaMinus_short (ctx : CoverCtx L S₀ A₁ A₂) {n f : ℕ}
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f) : False := by
  obtain ⟨⟨-, hf1, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap F (ShortField b c)).injective 2
  have hF2 : 2 ≤ Nat.card F := by have := Finite.one_lt_card (α := F); omega
  have h4 : 4 ≤ Nat.card (ShortField b c) := by
    rw [SpinMinusClosed.card_shortField]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hF2 2
  have hk : ¬ (n - 2) + 1 < n - 1 := by omega
  exact false_of_big_node ctx.syl ctx.cov ctx.solv₁ ctx.solv₂ (borelQuotient_spinMinus hirr hn e)
    (⟨n - 2, by omega⟩ : Fin (n - 1)) (fun hπ' => not_isPSolvable_map_rankOne_of_sl2Node hπ' h4
      (hasSL2Node_spinMinus_short hirr h4 (k := ⟨n - 2, by omega⟩) hk))

end SpinMinusShort

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
