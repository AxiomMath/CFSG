module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

section Constrained

variable {H : Type*} [Group H] [Finite H] {p : ℕ}

theorem exists_isComponentOf_of_not_hasPrimeConstraint (hp : p.Prime)
    (hcon : ¬ HasPrimeConstraint (G := H) p) :
    ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  apply exists_isComponentOf_of_layer_ne_bot
  intro hlayer
  apply hcon
  have hchar : CFSG.IsCharacteristicP p (H ⧸ CFSG.pPrimeCore p H) :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ p
      (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p) hlayer
  exact ⟨CFSG.pCore p (H ⧸ CFSG.pPrimeCore p H), CFSG.pCore_normal, CFSG.pCore_isPGroup, hchar⟩

end Constrained


structure RedConfig (p : ℕ) {X : Type*} [Group X] [Finite X] (P : Sylow p X) (z : X)
    (D : Subgroup X) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  core : primeComplementCore (G := X) p = ⊥
  rank : CFSG.Open.pRank p (P : Subgroup X) = 3
  ord : orderOf z = p
  central : z ∈ centralizer ((P : Subgroup X) : Set X)
  unique : ∀ y ∈ (P : Subgroup X), y ∈ centralizer ((P : Subgroup X) : Set X) → y ^ p = 1 →
    y ∈ zpowers z
  le : D ≤ (P : Subgroup X)
  elem : IsElemAbelian p D
  card : Nat.card D = p ^ 2
  mem : z ∈ D
  notNormal : ¬ (P : Subgroup X) ≤ normalizer (D : Set X)
  sylow : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X))

section Reduce

variable {H : Type*} [Group H] [Finite H] {p : ℕ}

noncomputable def redSylow [Fact p.Prime] (P : Sylow p H) :
    Sylow p (H ⧸ primeComplementCore (G := H) p) :=
  P.mapSurjective (QuotientGroup.mk'_surjective (primeComplementCore (G := H) p))

theorem coe_redSylow [Fact p.Prime] (P : Sylow p H) :
    ((redSylow P : Sylow p (H ⧸ primeComplementCore (G := H) p)) :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) =
      (P : Subgroup H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
  Sylow.coe_mapSurjective _ P

theorem pRank_map_mk_of_isPGroup (hp : p.Prime) (O : Subgroup H) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {T : Subgroup H} (hT : IsPGroup p T) :
    CFSG.Open.pRank p (T.map (QuotientGroup.mk' O)) = CFSG.Open.pRank p T := by
  apply le_antisymm
  · obtain ⟨E, hEle, hE, hEcard⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (T.map (QuotientGroup.mk' O))
    obtain ⟨E₁, hE₁T, -, hE₁, hcard⟩ := exists_isElemAbelian_lift hp O hO hT hE hEle
    exact le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp T)
      ⟨E₁, hE₁T, hE₁, hcard.trans hEcard⟩
  · obtain ⟨E, hEle, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp T
    refine le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp _)
      ⟨E.map (QuotientGroup.mk' O), Subgroup.map_mono hEle,
        CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _, ?_⟩
    rw [card_map_mk_of_isPGroup hp O hO (hT.to_le hEle), hEcard]


theorem centralizer_map_le_map_centralizer (hp : p.Prime) (O : Subgroup H) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {D : Subgroup H} (hD : IsPGroup p D) :
    centralizer ((D.map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O)) ≤
      (centralizer (D : Set H)).map (QuotientGroup.mk' O) := by
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O x
  have hy : y ∈ ((O ⊔ centralizer (D : Set H) : Subgroup H) : Set H) :=
    comap_centralizer_map_le_sup hp O hO hD hx
  rw [Subgroup.normal_mul, Set.mem_mul] at hy
  obtain ⟨n, hn, g, hg, rfl⟩ := hy
  refine ⟨g, hg, ?_⟩
  have hn1 : QuotientGroup.mk' O n = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hn
  rw [map_mul, hn1, one_mul]

theorem isSylowOf_map_centralizer [Fact p.Prime] (O : Subgroup H) [O.Normal]
    (hO : p.Coprime (Nat.card O)) {D : Subgroup H} (hDe : IsElemAbelian p D)
    (hS : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set H))) :
    CFSG.ABGLocalTools.IsSylowOf p (D.map (QuotientGroup.mk' O))
      (centralizer ((D.map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) : Set (H ⧸ O))) := by
  have hp : p.Prime := Fact.out
  set π := QuotientGroup.mk' O with hπ
  set C := centralizer (D : Set H) with hC
  set C' := centralizer ((D.map π : Subgroup (H ⧸ O)) : Set (H ⧸ O)) with hC'
  have hDp : IsPGroup p D := elementary_isPGroup p D hDe
  have hcomm : IsElemAbelian p (D.map π) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hDe π
  have hle : D.map π ≤ C' := le_centralizer_iff_isMulCommutative.mpr hcomm.1
  have hCC' : C' ≤ C.map π := centralizer_map_le_map_centralizer hp O hO hDp
  have hdvd : Nat.card C' ∣ Nat.card C :=
    (Subgroup.card_dvd_of_le hCC').trans (C.card_map_dvd π)
  have hDcard : Nat.card (D.map π) = Nat.card D := card_map_mk_of_isPGroup hp O hO hDp
  have hDcardC : Nat.card D = p ^ (Nat.card C).factorization p := hS.card_eq
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hC'0 : Nat.card C' ≠ 0 := Nat.card_pos.ne'
  have h1 : (Nat.card C').factorization p ≤ (Nat.card C).factorization p :=
    (Nat.factorization_le_iff_dvd hC'0 hC0).2 hdvd p
  have h2 : (Nat.card C).factorization p ≤ (Nat.card C').factorization p := by
    rw [← hp.pow_dvd_iff_le_factorization hC'0, ← hDcardC, ← hDcard]
    exact Subgroup.card_dvd_of_le hle
  refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
  rw [hDcard, hDcardC, le_antisymm h1 h2]


theorem Lemma212Config.reduce [hp : Fact p.Prime] (hodd : p ≠ 2) {P : Sylow p H} {z : H}
    {D : Subgroup H} (h : Lemma212Config p P z D) :
    RedConfig p (redSylow P) (QuotientGroup.mk' (primeComplementCore (G := H) p) z)
      (D.map (QuotientGroup.mk' (primeComplementCore (G := H) p))) := by
  have hp' : p.Prime := hp.out
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  have hO : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  set π := QuotientGroup.mk' O with hπ
  have hPp : IsPGroup p (P : Subgroup H) := P.isPGroup'
  have hDp : IsPGroup p D := elementary_isPGroup p D h.elem
  have hinj : ∀ a ∈ (P : Subgroup H), ∀ b ∈ (P : Subgroup H), π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp' O hO hPp ha hb hab
  refine ⟨hp', hodd, primeComplementCore_quotient_eq_bot p, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [coe_redSylow, pRank_map_mk_of_isPGroup hp' O hO hPp, h.rank]
  · exact orderOf_mk_of_coprime hp' O hO h.ord
  · rw [mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ (P : Subgroup H).map π := by
      have := SetLike.mem_coe.1 hy
      rwa [coe_redSylow] at this
    obtain ⟨t, ht, rfl⟩ := hy'
    have h1 : t * z = z * t := mem_centralizer_iff.1 h.central t ht
    show π t * π z = π z * π t
    rw [← map_mul, ← map_mul, h1]
  · intro y hy hyC hyp
    have hy' : y ∈ (P : Subgroup H).map π := by rwa [coe_redSylow] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy'
    have hy₀C : y₀ ∈ centralizer ((P : Subgroup H) : Set H) := by
      rw [mem_centralizer_iff]
      intro t ht
      apply hinj (t * y₀) (mul_mem ht hy₀) (y₀ * t) (mul_mem hy₀ ht)
      have := mem_centralizer_iff.1 hyC (π t) (by
        rw [SetLike.mem_coe, coe_redSylow]; exact mem_map_of_mem _ ht)
      simpa [map_mul] using this
    have hy₀p : y₀ ^ p = 1 := by
      apply hinj (y₀ ^ p) (pow_mem hy₀ p) 1 (one_mem _)
      simpa [map_pow] using hyp
    have h2 := h.unique y₀ hy₀ hy₀C hy₀p
    rw [← MonoidHom.map_zpowers]
    exact mem_map_of_mem π h2
  · rw [coe_redSylow]
    exact map_mono h.le
  · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p h.elem π
  · exact (card_map_mk_of_isPGroup hp' O hO hDp).trans h.card
  · exact mem_map_of_mem π h.mem
  · intro hle
    apply h.notNormal
    refine le_normalizer_of_map_le_normalizer_map hp' O hO hPp h.le ?_
    rwa [coe_redSylow] at hle
  · exact isSylowOf_map_centralizer O hO h.elem h.sylow

end Reduce

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
