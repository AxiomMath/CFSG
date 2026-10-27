module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

structure JStarTarget (p B : ℕ) (L : Type) [Group L] [Finite L] : Prop where
  simple : IsSimpleGroup L
  nonabelian : ∃ a b : L, a * b ≠ b * a
  three_le_pRank : 3 ≤ Open.pRank p (⊤ : Subgroup L)
  outer_solvable : Group.IsSolvable (Outer L)
  prime_dvd : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ ℓ ∣ Nat.card L ∧
    ∀ k : ℕ, 0 < k → p ^ k ∣ B → ¬ ℓ ∣ p ^ k - 1

structure JStarTargetBase (p B : ℕ) (L : Type) [Group L] [Finite L] : Prop where
  simple : IsSimpleGroup L
  nonabelian : ∃ a b : L, a * b ≠ b * a
  two_le_pRank : 2 ≤ Open.pRank p (⊤ : Subgroup L)
  outer_solvable : Group.IsSolvable (Outer L)
  prime_dvd : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ ℓ ∣ Nat.card L ∧
    ∀ k : ℕ, 0 < k → p ^ k ∣ B → ¬ ℓ ∣ p ^ k - 1

theorem JStarTarget.toBase {p B : ℕ} {L : Type} [Group L] [Finite L] (h : JStarTarget p B L) :
    JStarTargetBase p B L :=
  ⟨h.simple, h.nonabelian, le_trans (by norm_num) h.three_le_pRank, h.outer_solvable,
    h.prime_dvd⟩

structure JStarTargetTwo (p B : ℕ) (L : Type) [Group L] [Finite L] : Prop
    extends JStarTargetBase p B L where
  outer_sylow_normal : ∀ S : Sylow p (Outer L), (S : Subgroup (Outer L)).Normal

structure JStarHypOf {Y : Type} [Group Y] [Finite Y] (p : ℕ) [Fact p.Prime] (Rb : Sylow p Y)
    (Y₀ : Subgroup Y) (Jt Xt : Subgroup Y) (L : Type) [Group L] [Finite L] (B : ℕ)
    (φ : Jt →* L) : Prop where
  ne_two : p ≠ 2
  red : ReducedNongeneration p Y Rb Y₀
  catalog : CatalogSimpleSections Y
  surj : Function.Surjective φ
  coprime : p.Coprime (Nat.card φ.ker)
  le_R : Xt ≤ (Rb : Subgroup Y)
  ncl : nclIn Jt Xt = Jt
  le_normalizer : (Rb : Subgroup Y) ≤ Subgroup.normalizer (Jt : Set Y)
  faithful : ∀ z ∈ (Rb : Subgroup Y),
    (∀ j ∈ Jt, z * j * z⁻¹ * j⁻¹ ∈ φ.ker.map Jt.subtype) → z = 1
  card_dvd : ∀ S : Subgroup Y, IsPGroup p S → Nat.card S ∣ B

@[expose] def JStarConclOf {Y : Type} [Group Y] (Jt : Subgroup Y) (L : Type) [Group L] : Prop :=
  Jt.Normal ∧ Nonempty (Jt ≃* L) ∧ Subgroup.centralizer (Jt : Set Y) = ⊥

@[expose] def JStarElimDataOf (L₀ : Type) [Group L₀] [Finite L₀] (p B : ℕ) (L : Type) [Group L] :
    Prop :=
  ∃ A J : Subgroup (MulAut L₀), (MulAut.conj : L₀ →* MulAut L₀).range ≤ A ∧ J ≤ A ∧
    (∀ S : Subgroup (MulAut L₀), S ≤ A → IsPGroup p S → Nat.card S ∣ B) ∧
    ∃ φ : J →* L, Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker)

@[expose] def JStarElimOf (p B : ℕ) (L : Type) [Group L] : Prop :=
  ∀ (L₀ : Type) [Group L₀] [Finite L₀], IsSimpleGroup L₀ →
    ((∃ d : TauCeti.ValidLieTypeIndex, P1ThreeLieList p d ∧
        Nonempty (L₀ ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      Nonempty (L₀ ≃* alternatingGroup (Fin (3 * p))) ∨
      (∃ s : TauCeti.SporadicName, P1ThreeSporList p s ∧
        Nonempty (L₀ ≃* (TauCeti.CFSGIndex.sporadic s).Group))) →
    JStarElimDataOf L₀ p B L → Nonempty (L₀ ≃* L)

@[expose] def StmtJStarOfO1 : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p B : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {L : Type} [Group L] [Finite L] {φ : Jt →* L},
    JStarTargetBase p B L → JStarHypOf p Rb Y₀ Jt Xt L B φ →
    (∃ O : Subgroup Y, O.Normal ∧ IsPGroup p O ∧ Subgroup.centralizer (O : Set Y) ≤ O) → False

@[expose] def StmtJStarOfII : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p B : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {L : Type} [Group L] [Finite L] {φ : Jt →* L},
    JStarTargetBase p B L → JStarHypOf p Rb Y₀ Jt Xt L B φ →
    (∃ L' : Subgroup Y, IsComponentOf L' ⊤) →
    (∀ L' : Subgroup Y, IsComponentOf L' ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L' : Subgroup Y)) →
    False

@[expose] def StmtJStarOfI : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p B : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {L : Type} [Group L] [Finite L] {φ : Jt →* L},
    JStarTargetBase p B L → JStarHypOf p Rb Y₀ Jt Xt L B φ →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ →
    ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) → ¬ K ≤ Y₀ →
    ∀ z ∈ (Rb : Subgroup Y), z ∉ K → orderOf z = p →
      z ∈ Subgroup.centralizer (K : Set Y) → False

@[expose] def StmtJStarOfIII : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p B : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {L : Type} [Group L] [Finite L] {φ : Jt →* L},
    JStarTargetBase p B L → JStarElimOf p B L → JStarHypOf p Rb Y₀ Jt Xt L B φ →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ →
    (∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = K) →
    ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
    (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) → JStarConclOf Jt L

theorem jStarConclOf_of_cases (hO1 : StmtJStarOfO1) (hII : StmtJStarOfII) (hI : StmtJStarOfI)
    (hIII : StmtJStarOfIII) {Y : Type} [Group Y] [Finite Y] {p B : ℕ} [Fact p.Prime]
    {Rb : Sylow p Y} {Y₀ Jt Xt : Subgroup Y} {L : Type} [Group L] [Finite L] {φ : Jt →* L}
    (hT : JStarTargetBase p B L) (hE : JStarElimOf p B L) (h : JStarHypOf p Rb Y₀ Jt Xt L B φ)
    (hcomp : (¬ ∃ O : Subgroup Y, O.Normal ∧ IsPGroup p O ∧
      Subgroup.centralizer (O : Set Y) ≤ O) → ∃ L' : Subgroup Y, IsComponentOf L' ⊤) :
    JStarConclOf Jt L := by
  by_cases hcon : ∃ O : Subgroup Y, O.Normal ∧ IsPGroup p O ∧
      Subgroup.centralizer (O : Set Y) ≤ O
  · exact (hO1 hT h hcon).elim
  have hE' := hcomp hcon
  by_cases hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ →
      IsCyclic ((Rb : Subgroup Y) ⊓ L' : Subgroup Y)
  · exact (hII hT h hE' hall).elim
  push Not at hall
  obtain ⟨K, hK, hnc⟩ := hall
  rcases h.red.rankOne_or_center hK hnc with ⟨z, hzR, hzK, hzp, hzc, -, hKY₀, -, -⟩ | hcent
  · exact (hI hT h K hK hnc hKY₀ z hzR hzK hzp hzc).elim
  · exact hIII hT hE h K hK (fun L' hL' => h.red.eq_of_forall_mem_center hK hL' hcent) hnc hcent

end CFSG.AGLEmbedding
