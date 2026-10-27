module

public import CFSG.GH74.GLS.Stage4.T2GoodRed
public import CFSG.GH74.GLS.Stage4.RestX2Q1
public import CFSG.GH74.GLS.Stage4.T6Ord
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage4.RestChain3
public import CFSG.GH74.GLS.Stage4.RestX2B
public import CFSG.GH74.GLS.Stage4.T2LeafC
public import CFSG.GH74.GLS.Stage4.T2OddAut
public import CFSG.GH74.GLS.Stage4.T2P53a
public import CFSG.GH74.GLS.Stage4.T6Final
public import CFSG.GH74.GLS.Stage4.T9Final
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionNontrivialTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character
public import CFSG.Walter.J1.Inv

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise

@[expose] def Ch6P71Out' {G : Type} [Group G] (n : ℕ) (z : G) (K K' : Subgroup G) : Prop :=
  ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K → N.K₂ = K' → N.q₁ = 3 ^ n → N.q₂ = 3 ^ n →
    Ch6Coord N.toT2N2.toT2N1 → Ch6Sec5 N u →
      Nat.card ↥(T6.R₂ N 3) = N.q₁ ^ 2 * N.q₂ ^ 3 ∧
        ∃ P₀ : Subgroup G, P₀ ≤ N.F ∧ IsPGroup 3 ↥P₀ ∧
          ∃ T : Sylow 3 G, (T : Subgroup G) = (T6.R₂ N 3 ⊔ N.X₁) ⊔ P₀

structure P71Env {G : Type} [Group G] [Finite G] (Gs : Type) [Group Gs] (n : ℕ) (N : T2N3 G) (u : G) : Prop where
  std : Std G
  rank : pRank 2 G = 3
  n_ge : 2 ≤ n
  at_ : IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n)
  q₁ : N.q₁ = 3 ^ n
  q₂ : N.q₂ = 3 ^ n
  coord : Ch6Coord N.toT2N2.toT2N1
  sec5 : Ch6Sec5 N u
  setup : ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂) (t : G),
    Ch6Setup G Gs (3 ^ n) (3 ^ n) N.z N.K₁ N.K₂ F₁ F₂ ∧ Ch6Rem N.z N.K₁ N.K₂ F₁ F₂ t

section Env

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {n : ℕ} {N : T2N3 G} {u : G}

theorem P71Env.ctx (h : P71Env Gs n N u) : T6.T6Ctx N u 3 := by
  obtain ⟨F₁, F₂, iF₁, iF₂, t, hS, hR⟩ := h.setup
  have hNum : Ch6NumD 3 (3 ^ n) (3 ^ n) :=
    ⟨Nat.prime_three, by norm_num, ⟨n, rfl⟩, ⟨n, rfl⟩, Or.inl rfl⟩
  exact T6.t6Ctx_of hS hR (N := N) (u := u) (p := 3) rfl rfl rfl h.q₁ h.q₂ hNum h.coord h.sec5

theorem P71Env.swap (h : P71Env Gs n N u) : P71Env Gs n N.swap u where
  std := h.std
  rank := h.rank
  n_ge := h.n_ge
  at_ := h.at_
  q₁ := h.q₂
  q₂ := h.q₁
  coord := Ch6Coord.swap h.coord
  sec5 := h.sec5.swap (h.q₁.trans h.q₂.symm)
  setup := by
    obtain ⟨F₁, F₂, iF₁, iF₂, t, hS, hR⟩ := h.setup
    exact ⟨F₂, F₁, iF₂, iF₁, t, hS.swap rfl, hR.swap⟩

end Env

@[expose] def P71Frattini : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (n : ℕ) (N : T2N3 G) (u : G),
    P71Env Gs n N u →
    (¬ ∃ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({N.z} : Set G)) →
      N.X₂ < T6.R₂ N 3 ∧ N.X₂ < T6.R₂ N 3 ⊓ centralizer (N.X₁ : Set G)

@[expose] def P71Both : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (n : ℕ) (N : T2N3 G) (u : G),
    P71Env Gs n N u →
    (¬ ∃ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({N.z} : Set G)) →
      Nat.card ↥(T6.R₂ N 3) = N.q₂ ^ 3 → Nat.card ↥(T6.R₂ N.swap 3) = N.q₁ ^ 3 →
        N.X₂ < T6.R₂ N 3 ⊓ centralizer (N.X₁ : Set G) →
          N.X₁ < T6.R₂ N.swap 3 ⊓ centralizer (N.X₂ : Set G) → False

@[expose] def P71Nonab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (n : ℕ) (N : T2N3 G) (u : G),
    P71Env Gs n N u →
    (¬ ∃ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({N.z} : Set G)) →
      Nat.card ↥(T6.R₂ N 3) = N.q₁ ^ 2 * N.q₂ ^ 3 →
        ∃ x ∈ T6.R₂ N 3, ∃ y ∈ T6.R₂ N 3, x * y ≠ y * x

@[expose] def P71Sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (n : ℕ) (N : T2N3 G) (u : G),
    P71Env Gs n N u →
    Nat.card ↥(T6.R₂ N 3) = N.q₁ ^ 2 * N.q₂ ^ 3 → (∃ x ∈ T6.R₂ N 3, ∃ y ∈ T6.R₂ N 3, x * y ≠ y * x) →
      ∃ P₀ : Subgroup G, P₀ ≤ N.F ∧ IsPGroup 3 ↥P₀ ∧
        ∃ T : Sylow 3 G, (T : Subgroup G) = (T6.R₂ N 3 ⊔ N.X₁) ⊔ P₀

@[expose] def P71L72 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (n : ℕ), 2 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
      ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
        Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
          ∀ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({z} : Set G) → (P : Subgroup G) ≤ K₁ ⊔ K₂

section Card

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_conj_sylow {p m : ℕ} [hp : Fact p.Prime] {K X X' : Subgroup G} [Finite K]
    (hX : X ≤ K) (hX' : X' ≤ K) (hc : Nat.card ↥X = p ^ m) (hc' : Nat.card ↥X' = p ^ m)
    (hK : (Nat.card ↥K).factorization p = m) :
    ∃ k ∈ K, X.map (MulAut.conj k).toMonoidHom = X' := by
  have hXp : IsPGroup p ↥(X.subgroupOf K) :=
    IsPGroup.of_card (n := m) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv, hc])
  have hXp' : IsPGroup p ↥(X'.subgroupOf K) :=
    IsPGroup.of_card (n := m) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX').toEquiv, hc'])
  obtain ⟨S, hS⟩ := hXp.exists_le_sylow
  obtain ⟨S', hS'⟩ := hXp'.exists_le_sylow
  have hSc : Nat.card ↥(S : Subgroup ↥K) = p ^ m := by rw [Sylow.card_eq_multiplicity S, hK]
  have hS'c : Nat.card ↥(S' : Subgroup ↥K) = p ^ m := by rw [Sylow.card_eq_multiplicity S', hK]
  have hXS : X.subgroupOf K = (S : Subgroup ↥K) := by
    refine Subgroup.eq_of_le_of_card_ge hS ?_
    rw [hSc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv, hc]
  have hXS' : X'.subgroupOf K = (S' : Subgroup ↥K) := by
    refine Subgroup.eq_of_le_of_card_ge hS' ?_
    rw [hS'c, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX').toEquiv, hc']
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K S S'
  have hg' : (S' : Subgroup ↥K) = MulAut.conj g • (S : Subgroup ↥K) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  refine ⟨(g : G), g.2, ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyK : y ∈ K := hX hy
    have h1 : (⟨y, hyK⟩ : ↥K) ∈ (S : Subgroup ↥K) := by
      rw [← hXS]; exact Subgroup.mem_subgroupOf.2 hy
    have h2 : MulAut.conj g • (⟨y, hyK⟩ : ↥K) ∈ MulAut.conj g • (S : Subgroup ↥K) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← hg', ← hXS'] at h2
    have h3 := Subgroup.mem_subgroupOf.1 h2
    have e : ((MulAut.conj g • (⟨y, hyK⟩ : ↥K) : ↥K) : G) = (g : G) * y * (g : G)⁻¹ := by
      simp [MulAut.smul_def, MulAut.conj_apply]
    rw [e] at h3
    simpa [MulAut.conj_apply] using h3
  · intro hx
    have hxK : x ∈ K := hX' hx
    have h1 : (⟨x, hxK⟩ : ↥K) ∈ (S' : Subgroup ↥K) := by
      rw [← hXS']; exact Subgroup.mem_subgroupOf.2 hx
    rw [hg'] at h1
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 h1
    rw [← hXS] at hy
    refine ⟨(y : G), Subgroup.mem_subgroupOf.1 hy, ?_⟩
    have := congrArg Subtype.val hyx
    have e : ((MulAut.conj g • y : ↥K) : G) = (g : G) * (y : G) * (g : G)⁻¹ := by
      simp [MulAut.smul_def, MulAut.conj_apply]
    rw [e] at this
    simpa [MulAut.conj_apply] using this

variable {Gs : Type} [Group Gs] {n : ℕ} {N : T2N3 G} {u : G}

omit [Finite G] in
theorem card_K₂_factorization (h : Ch6Loc5 N.toT2N2.toT2N1 u) (hq₂ : N.q₂ = 3 ^ n) (hn : n ≠ 0) :
    (Nat.card ↥N.K₂).factorization 3 = n := by
  obtain ⟨F, iF, fF, hcard, ⟨e⟩⟩ := h.iso₂
  have h1 : Nat.card ↥N.K₂ = 3 ^ n * ((3 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, t2C_card_sl2, hcard, hq₂]
  have h3n : 3 ∣ 3 ^ n := dvd_pow_self 3 hn
  have hm : (3 ^ n) ^ 2 - 1 ≠ 0 := by
    have h2n : 2 ≤ 3 ^ n := by
      have := Nat.le_of_dvd (by positivity) h3n
      have h0 : 0 < 3 ^ n := by positivity
      omega
    have : 4 ≤ (3 ^ n) ^ 2 := by nlinarith
    omega
  have hnd : ¬ 3 ∣ (3 ^ n) ^ 2 - 1 := by
    have h3 : 3 ∣ (3 ^ n) ^ 2 := dvd_pow h3n (by norm_num)
    have h1' : 1 ≤ (3 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    generalize (3 ^ n) ^ 2 = X at h3 h1' ⊢
    omega
  rw [h1, Nat.factorization_mul (by positivity) hm, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem card_R₂_eq_of_K₂ {N' : T2N3 G} {u' : G}
    (h : P71Env Gs n N u) (h' : P71Env Gs n N' u') (hK : N.K₂ = N'.K₂) :
    Nat.card ↥(T6.R₂ N 3) = Nat.card ↥(T6.R₂ N' 3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn0 : n ≠ 0 := by have := h.n_ge; omega
  have hloc := h.sec5.loc
  have hloc' := h'.sec5.loc
  have hX₂K : N.X₂ ≤ N.K₂ := by rw [hloc.K₂_eq]; exact le_sup_left
  have hX₂K' : N'.X₂ ≤ N.K₂ := by rw [hK, hloc'.K₂_eq]; exact le_sup_left
  have hc : Nat.card ↥N.X₂ = 3 ^ n := by rw [hloc.card_X₂, h.q₂]
  have hc' : Nat.card ↥N'.X₂ = 3 ^ n := by rw [hloc'.card_X₂, h'.q₂]
  have hfin : Finite ↥N.K₂ := inferInstance
  obtain ⟨k, -, hk⟩ := exists_conj_sylow (p := 3) hX₂K hX₂K' hc hc'
    (card_K₂_factorization hloc h.q₂ hn0)
  have e1 : T6.M₂ N' = (T6.M₂ N).map (MulAut.conj k).toMonoidHom := by
    show Subgroup.normalizer (N'.X₂ : Set G) = _
    rw [← hk]
    exact (Subgroup.map_equiv_normalizer_eq N.X₂ (MulAut.conj k)).symm
  show Nat.card ↥(CFSG.Open.pCoreOf 3 (T6.M₂ N)) = Nat.card ↥(CFSG.Open.pCoreOf 3 (T6.M₂ N'))
  rw [e1, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 3 (MulAut.conj k) (T6.M₂ N),
    Subgroup.card_map_of_injective (MulAut.conj k).injective]

theorem card_R₂_cases (h : P71Env Gs n N u) (hlt : N.X₂ < T6.R₂ N 3) :
    Nat.card ↥(T6.R₂ N 3) = N.q₂ ^ 3 ∨ Nat.card ↥(T6.R₂ N 3) = N.q₁ ^ 2 * N.q₂ ^ 3 := by
  have hctx := h.ctx
  have hq : N.q₁ = N.q₂ := h.q₁.trans h.q₂.symm
  have hcard := T6.R₂_card_RA hctx
  have hne : Nat.card ↥(T6.R₂ N 3) ≠ N.q₂ := by
    intro hc
    have h1 : Nat.card ↥N.X₂ = N.q₂ := h.sec5.loc.card_X₂
    exact hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le (by rw [hc, h1]))
  rcases (T6.RA_struct hctx).1 with h1 | h1 | h1 | h1
  · exfalso; apply hne; rw [hcard, h1]; ring
  · left; rw [hcard, h1, hq]; ring
  · left; rw [hcard, h1]; ring
  · right; rw [hcard, h1]; ring

end Card

section Glue

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {n : ℕ}

theorem ch6T2Prop71'_of_steps
    (hS0 : P71Frattini) (hS2 : P71Both) (hS3 : P71Nonab) (hS4 : P71Sylow) (hL72 : P71L72) :
    ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
      ∀ (Gs : Type) [Group Gs] (n : ℕ), 2 ≤ n → IsTwoCentralG2TypeG2At G Gs (3 ^ n) (3 ^ n) →
        ¬ Ch6Bad3 G →
          ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
            Ch6Setup G Gs (3 ^ n) (3 ^ n) z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
              Ch6P71Out' n z K₁ K₂ ∨ Ch6P71Out' n z K₂ K₁ := by
  intro G _ _ hStd hr Gs _ n hn hAt hBad z K₁ K₂ F₁ F₂ _ _ t hSet hRem
  by_contra hcon
  have h1 : ¬ Ch6P71Out' n z K₁ K₂ := fun h => hcon (Or.inl h)
  have h2 : ¬ Ch6P71Out' n z K₂ K₁ := fun h => hcon (Or.inr h)
  have hnotsyl : ¬ ∃ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rintro ⟨P, hP⟩
    have hPK := hL72 G hStd hr Gs n hn hAt z K₁ K₂ F₁ F₂ t hSet hRem P hP
    exact hBad ⟨z, hSet.central.1, P, hPK.trans hSet.le_residual⟩
  have key : ∀ (K K' : Subgroup G) (F F' : Type) [Field F] [Field F'],
      Ch6Setup G Gs (3 ^ n) (3 ^ n) z K K' F F' → Ch6Rem z K K' F F' t →
        ¬ Ch6P71Out' n z K K' →
          ∃ (N : T2N3 G) (u : G), N.z = z ∧ N.K₁ = K ∧ N.K₂ = K' ∧ P71Env Gs n N u ∧
            Nat.card ↥(T6.R₂ N 3) = N.q₂ ^ 3 := by
    intro K K' F F' _ _ hS hR hout
    by_contra hnone
    apply hout
    intro N u hz hK hK' hq₁ hq₂ hC hSec
    have hEnv : P71Env Gs n N u :=
      { std := hStd, rank := hr, n_ge := hn, at_ := hAt, q₁ := hq₁, q₂ := hq₂, coord := hC,
        sec5 := hSec
        setup := ⟨F, F', inferInstance, inferInstance, t, by rw [hz, hK, hK']; exact hS,
          by rw [hz, hK, hK']; exact hR⟩ }
    have hnotsylN : ¬ ∃ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({N.z} : Set G) := by
      rw [hz]; exact hnotsyl
    obtain ⟨hlt, -⟩ := hS0 G Gs n N u hEnv hnotsylN
    rcases card_R₂_cases hEnv hlt with hc | hc
    · exact absurd ⟨N, u, hz, hK, hK', hEnv, hc⟩ hnone
    · exact ⟨hc, hS4 G Gs n N u hEnv hc (hS3 G Gs n N u hEnv hnotsylN hc)⟩
  obtain ⟨N₁, u₁, hz₁, hK₁₁, hK₂₁, hE₁, hc₁⟩ := key K₁ K₂ F₁ F₂ hSet hRem h1
  obtain ⟨N₂, u₂, hz₂, hK₁₂, hK₂₂, hE₂, hc₂⟩ := key K₂ K₁ F₂ F₁ (hSet.swap rfl) hRem.swap h2
  have hnotsyl₁ : ¬ ∃ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({N₁.z} : Set G) := by
    rw [hz₁]; exact hnotsyl
  have hE₁' : P71Env Gs n N₁.swap u₁ := hE₁.swap
  have hc₁' : Nat.card ↥(T6.R₂ N₁.swap 3) = N₁.q₁ ^ 3 := by
    have h12 := card_R₂_eq_of_K₂ hE₁' hE₂ (by
      show N₁.K₁ = N₂.K₂
      rw [hK₁₁, hK₂₂])
    rw [h12, hc₂, hE₂.q₂, hE₁.q₁]
  have hnotsyl₁' : ¬ ∃ P : Sylow 3 G, (P : Subgroup G) ≤ centralizer ({N₁.swap.z} : Set G) :=
    hnotsyl₁
  obtain ⟨-, hD₁⟩ := hS0 G Gs n N₁ u₁ hE₁ hnotsyl₁
  obtain ⟨-, hD₁'⟩ := hS0 G Gs n N₁.swap u₁ hE₁' hnotsyl₁'
  exact hS2 G Gs n N₁ u₁ hE₁ hnotsyl₁ hc₁ hc₁' hD₁ hD₁'

end Glue

end CFSG.GH74.GLS.Stage4.Rest
