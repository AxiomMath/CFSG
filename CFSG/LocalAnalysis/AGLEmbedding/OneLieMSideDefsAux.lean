module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaBRel
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def StmtLemmaBCyc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L X : Subgroup G) (p r : ℕ) (t : G),
    Open.IsKGroup ↥M → Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → p.Prime → p ≠ 2 →
    (∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      ∀ A : Subgroup G, A ≤ Y → IsPGroup p A → IsCyclic A) →
    X ≤ M ⊓ Subgroup.normalizer (S : Set G) → X ≤ Subgroup.normalizer (L : Set G) →
    IsElemAbelian p X → p ^ 3 ≤ Nat.card X →
    t ∈ M ⊓ Subgroup.normalizer (S : Set G) → t ∈ Subgroup.normalizer (L : Set G) →
    t ∈ Subgroup.normalizer (X : Set G) →
    r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p → ¬ r ∣ p - 1 →
    (∀ x ∈ X, t ^ r * x * (t ^ r)⁻¹ = x) → (∃ x ∈ X, t * x * t⁻¹ ≠ x) →
    (∀ Y : Subgroup G, Y ≤ X → t ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X) →
    barM M X ≤ Subgroup.centralizer (barM M L : Set _)

@[expose] def StmtLemmaBRelCyc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L Y Z : Subgroup G) (p r : ℕ) (t : G),
    Open.IsKGroup ↥M → Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → p.Prime → p ≠ 2 →
    (∀ Y' : Subgroup G, Y' ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y', Y'⁆ = Y' →
      ∀ A : Subgroup G, A ≤ Y' → IsPGroup p A → IsCyclic A) →
    Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → Y ≤ Subgroup.normalizer (L : Set G) →
    IsPGroup p Y → ⁅Y, Y⁆ = Z → Z ≤ Subgroup.centralizer (Y : Set G) →
    (∀ y ∈ Y, y ^ p ∈ Z) → p ^ 3 ≤ Z.relIndex Y →
    t ∈ M ⊓ Subgroup.normalizer (S : Set G) → t ∈ Subgroup.normalizer (L : Set G) →
    t ∈ Subgroup.normalizer (Y : Set G) →
    r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p → ¬ r ∣ p - 1 →
    (∀ y ∈ Y, t ^ r * y * (t ^ r)⁻¹ * y⁻¹ ∈ Z) → (∃ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∉ Z) →
    (∀ V : Subgroup G, Z ≤ V → V ≤ Y → t ∈ Subgroup.normalizer (V : Set G) → V = Z ∨ V = Y) →
    barM M Y ≤ Subgroup.centralizer (barM M L : Set _)

theorem isCyclic_of_le_of_coprime {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Y A : Subgroup G} (hY : p.Coprime (Nat.card Y)) (hAY : A ≤ Y) (hA : IsPGroup p A) :
    IsCyclic A := by
  have := Fact.mk hp
  have hcop : p.Coprime (Nat.card A) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hAY) hY
  have h1 : Nat.card A = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
    rcases k with _ | k
    · simpa using hk
    · exfalso
      rw [hk] at hcop
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop (dvd_pow_self p (by omega)))
  have : Subsingleton A := (Nat.card_eq_one_iff_unique.mp h1).1
  infer_instance

theorem stmtLemmaBRel_of_cyc (h : StmtLemmaBRelCyc) : StmtLemmaBRel := by
  intro G _ _ M S L Y Z p r t hK hA hL hX1 hS hp hp2 hcop
  exact h G M S L Y Z p r t hK hA hL hX1 hS hp hp2
    (fun Y' hY' hperf A hAY hAp => isCyclic_of_le_of_coprime hp (hcop Y' hY' hperf) hAY hAp)

theorem stmtLemmaB_of_cyc (h : StmtLemmaBCyc) : StmtLemmaB := by
  intro G _ _ M S L X p r t hK hA hL hX1 hS hp hp2 hcop
  exact h G M S L X p r t hK hA hL hX1 hS hp hp2
    (fun Y' hY' hperf A hAY hAp => isCyclic_of_le_of_coprime hp (hcop Y' hY' hperf) hAY hAp)

theorem stmtLemmaBCyc_of_relCyc (h : StmtLemmaBRelCyc) : StmtLemmaBCyc := by
  intro G _ _ M S L X p r t hK hA hL hX1 hS hp hp2 hcyc hXK hXL hXel hXcard htK htL htX hr hr2
    hr3 hrp hrp1 htr htnt hirr
  have hXp : IsPGroup p X := fun x => ⟨1, Subtype.ext (by simpa using hXel.2 x x.2)⟩
  have hcomm : ⁅X, X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hXel.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩
    exact congrArg Subtype.val this
  refine h G M S L X ⊥ p r t hK hA hL hX1 hS hp hp2 hcyc hXK hXL hXp hcomm bot_le
    (fun y hy => by rw [hXel.2 y hy]; exact Subgroup.one_mem _)
    (by rw [Subgroup.relIndex_bot_left]; exact hXcard) htK htL htX hr hr2 hr3 hrp hrp1
    (fun y hy => by rw [htr y hy, mul_inv_cancel]; exact Subgroup.one_mem _) ?_
    (fun V _ hVX hV => hirr V hVX hV)
  obtain ⟨x, hx, hne⟩ := htnt
  refine ⟨x, hx, fun hmem => hne ?_⟩
  rw [Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

@[expose] def KFactOneLieIdent : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      ∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ n : ℕ, 3 ≤ n ∧ IsLinTwoIndex p n d) ∨
          (IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨ IsReeGTwoIndex p d) ∧
        Nonempty (K ≃* CatGroup d)

@[expose] def KFactOutElemRankOdd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L E : Subgroup Y), IsComponentOf L ⊤ →
    IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card L →
    E ≤ Subgroup.normalizer (L : Set Y) → IsElemAbelian p E →
    E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ → Nat.card E ≤ p

theorem kFactOutElemRank_of_odd (h : KFactOutElemRankOdd) : KFactOutElemRank :=
  fun Y _ _ L E hL hcat p hp h5 hpL hEN hE hEC =>
    h Y L E hL hcat p hp (by omega) hpL hEN hE hEC

structure OneLieTorusFacts (p : ℕ) [Fact p.Prime] (K : Type) [Group K] [Finite K]
    (T : Sylow p K) (n e : ℕ) : Prop where
  two_le : 2 ≤ n
  e_cases : e = 1 ∨ (e = 2 ∧ 3 ≤ n)
  torus : ∃ ψ : Multiplicative (GaloisField p n) →* K, Function.Injective ψ ∧
    ψ.range = (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ∧
    ∀ μ : (GaloisField p n)ˣ, ∃ c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      ∀ a : Multiplicative (GaloisField p n),
        c * ψ a * c⁻¹ =
          ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ e * Multiplicative.toAdd a))
  center_ne_of_unitary : IsUnitaryGroup p K →
    (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ≠ T
  borel_coatom : IsCoatom (Subgroup.normalizer ((T : Subgroup K) : Set K))
  borel_solvable : ∀ A : Subgroup (MulAut K),
    (∀ α ∈ A, (T : Subgroup K).map (α : K ≃* K).toMonoidHom = T) → Group.IsSolvable A
  autRank : ∀ E : Subgroup (MulAut K), IsElemAbelian p E →
    Nat.card E ≤ p ^ (if e = 2 then n else 2 * n)
  pair : n = 2 → Nat.card (T : Subgroup K) = p ^ 6 ∧
    ⁅(T : Subgroup K), (T : Subgroup K)⁆ =
      (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ∧
    (∀ u ∈ (T : Subgroup K), u ^ p = 1) ∧
    ∀ r : ℕ, r.Prime → r ∣ p ^ 4 - 1 → (∀ k : ℕ, 0 < k → k < 4 → ¬ r ∣ p ^ k - 1) →
      ∃ c ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), orderOf c = r ∧
        ∀ k : ℕ, ¬ r ∣ k →
          (∃ u ∈ (T : Subgroup K), c ^ k * u * (c ^ k)⁻¹ * u⁻¹ ∉
            (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)) ∧
          ∀ V : Subgroup K,
            (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ≤ V →
            V ≤ T → c ^ k ∈ Subgroup.normalizer (V : Set K) →
            V = (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ∨ V = T

@[expose] def KFactOneLieTorus : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      ∃ n e : ℕ, OneLieTorusFacts p K T n e

end CFSG.AGLEmbedding
