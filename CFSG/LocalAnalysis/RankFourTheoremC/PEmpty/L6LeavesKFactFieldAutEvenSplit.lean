module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.KGH
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenAbs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

@[expose] def IsExcRow (t : StatedLieTag) (n f₀ : ℕ) : Prop :=
  f₀ = 1 ∧ ((t = .PSL ∧ n = 6) ∨ (t = .PSU ∧ (n = 3 ∨ n = 4)) ∨ (t = .PSp ∧ n = 3) ∨
    (t = .POmegaPlus ∧ n = 4))

@[expose] def TwoLocalWhen (t : StatedLieTag) (P : ℕ → ℕ → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n f f₀ p : ℕ), P n f₀ → StatedLieAdmissible t n 2 f → LieModel K t n 2 f → t ≠ .Tits →
    p.Prime → 5 ≤ p → ¬ p ∣ Nat.card K → ¬ p ∣ lieOrderDivisor t n (2 ^ f) → f = p * f₀ →
    ∃ r : ℕ, r.Prime ∧ ∀ R : Subgroup K, IsPGroup 2 R → R ≠ ⊥ →
      padicValNat r (Nat.card (Subgroup.normalizer (R : Set K))) +
          padicValNat r (lieOrderDivisor t n (2 ^ f₀)) <
        padicValNat r (lieOrderNumerator t n (2 ^ f₀))

@[expose] def OvergroupLocalWhen (t : StatedLieTag) (P : ℕ → ℕ → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ (n f f₀ p : ℕ), P n f₀ → StatedLieAdmissible t n 2 f → LieModel K t n 2 f → t ≠ .Tits →
    p.Prime → 5 ≤ p → ¬ p ∣ Nat.card K → ¬ p ∣ lieOrderDivisor t n (2 ^ f) → f = p * f₀ →
    ∃ r : ℕ, r.Prime ∧ ∀ T Y : Subgroup K, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → T ≤ Y →
      Y ≠ ⊤ →
      padicValNat r (Nat.card Y) + padicValNat r (lieOrderDivisor t n (2 ^ f₀)) <
        padicValNat r (lieOrderNumerator t n (2 ^ f₀))

theorem overgroupLocalWhen_of_twoLocalWhen (hOver : CFSG.Quasithin.AsLieTwoOvergroups)
    {t : StatedLieTag} {P : ℕ → ℕ → Prop} (h : TwoLocalWhen t P) : OvergroupLocalWhen t P := by
  intro K _ _ hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup K := hs
  obtain ⟨r, hr, hloc⟩ := h K hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  refine ⟨r, hr, fun T Y hT hTY hY => ?_⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hOverK : CFSG.QuasithinUnique.Bridge.Over.Overgroups K :=
    hOver K hs (Or.inl ⟨t, n, f, hadm, hmodel⟩)
  have hchar : CFSG.QuasithinUnique.CharTwo Y := hOverK T Y (isSylowTwoOf_of_isSylowOf hT) hTY hY
  have hev : Even (Nat.card K) := CFSG.GH74.even_card_of_nonabelian_simple hab
  have hRne := pCoreOf_ne_bot_of_charTwo hchar hTY (ne_bot_of_isSylowOf_of_even hT hev)
  have hR2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hYN : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set K) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hle := padicValNat_le_of_dvd' hr Nat.card_pos.ne' (Subgroup.card_dvd_of_le hYN)
  have := hloc (CFSG.Open.pCoreOf 2 Y) hR2 hRne
  omega

theorem overgroupLocalAt_of_when {t : StatedLieTag} (P : ℕ → ℕ → Prop)
    (h₁ : OvergroupLocalWhen t P) (h₂ : OvergroupLocalWhen t (fun n f₀ => ¬ P n f₀)) :
    OvergroupLocalAt t := by
  intro K _ _ hs hab n f f₀ p hadm hmodel ht hp hp5 hpK hdiv hf
  by_cases hP : P n f₀
  · exact h₁ K hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf
  · exact h₂ K hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf

theorem OvergroupLocalWhen.mono {t : StatedLieTag} {P Q : ℕ → ℕ → Prop}
    (h : OvergroupLocalWhen t P) (hPQ : ∀ n f₀, Q n f₀ → P n f₀) : OvergroupLocalWhen t Q :=
  fun K _ _ hs hab n f f₀ p hQ hadm hmodel ht hp hp5 hpK hdiv hf =>
    h K hs hab n f f₀ p (hPQ n f₀ hQ) hadm hmodel ht hp hp5 hpK hdiv hf

theorem OvergroupLocalWhen.of_or {t : StatedLieTag} {P Q R : ℕ → ℕ → Prop}
    (h₁ : OvergroupLocalWhen t P) (h₂ : OvergroupLocalWhen t Q)
    (hR : ∀ n f₀, R n f₀ → P n f₀ ∨ Q n f₀) : OvergroupLocalWhen t R :=
  fun K _ _ hs hab n f f₀ p hRn hadm hmodel ht hp hp5 hpK hdiv hf =>
    (hR n f₀ hRn).elim
      (fun hP => h₁ K hs hab n f f₀ p hP hadm hmodel ht hp hp5 hpK hdiv hf)
      (fun hQ => h₂ K hs hab n f f₀ p hQ hadm hmodel ht hp hp5 hpK hdiv hf)

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
