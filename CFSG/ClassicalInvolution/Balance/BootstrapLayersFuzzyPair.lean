module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPair
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyBalance

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.ComponentClassification
open scoped MatrixGroups

theorem isQuasisimple_map_conj {X : Type*} [Group X] {R : Subgroup X}
    (h : CFSG.Open.IsQuasisimple ↥R) (g : X) :
    CFSG.Open.IsQuasisimple ↥(R.map (MulAut.conj g).toMonoidHom) :=
  Components.quasisimple_of_equiv
    (Subgroup.equivMapOfInjective R (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm h

theorem fundQuasisimple_of_all_nodes (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime]
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hdiv : (modelUniv t n p e hp.out).D.divisible = ∅)
    (hq : ∀ i : Fin (modelUniv t n p e hp.out).D.rank,
      CFSG.Open.IsQuasisimple ↥(rankOne (modelUniv t n p e hp.out).D.rootGroup i)) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, CFSG.Open.IsQuasisimple ↥R := by
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum t n p e hp.out hfund hadm
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := mem_roots_of_mem_fundamentalSubgroups hR
  obtain ⟨w, i, rfl⟩ : ∃ (w : (coxeterMatrix (modelUniv t n p e hp.out).D.isFiniteType).Group)
      (i : Fin (modelUniv t n p e hp.out).D.rank),
      γ = weylAction (modelUniv t n p e hp.out).D.isFiniteType w (Pi.single i 1) := by
    rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
    · exact ⟨w, i, rfl⟩
    · rw [hdiv] at hi
      exact absurd hi (Set.notMem_empty i)
  obtain ⟨g', hg'⟩ := exists_map_conj_rankOne hct w
  have h1 := hg' (Pi.single i 1) (Or.inl ⟨1, i, by simp⟩)
  rw [← h1, map_conj_map_conj]
  exact isQuasisimple_map_conj (hq i) _

section G2

theorem g2_rankOne_quasisimple {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K)
    (l : Fin (Tag.rank .G2)) :
    CFSG.Open.IsQuasisimple
      ↥(rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l) := by
  obtain ⟨φ, hinj, hup, hlow⟩ := Adjoint.g2_exists_sl2_hom (K := K) l
  have hup' : ∀ c, φ (sl2Upper c) =
      Adjoint.xPar (Chevalley.rootOperatorFamily .G2) (Pi.single l 1) c := fun c => by
    rw [hup, Adjoint.xPar_simple]
  have hlow' : ∀ c, φ (sl2Lower c) =
      Adjoint.xPar (Chevalley.rootOperatorFamily .G2) (-Pi.single l 1) c := fun c => by
    rw [hlow, Adjoint.xPar_neg_simple]
  have hle : rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l ≤ φ.range := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨c, rfl⟩ :=
        Adjoint.exists_of_mem_rootGroup_simple (Chevalley.rootOperatorFamily .G2) hg
      exact ⟨sl2Upper c, hup c⟩
    · intro g hg
      obtain ⟨c, rfl⟩ :=
        Adjoint.exists_of_mem_rootGroup_neg_simple (Chevalley.rootOperatorFamily .G2) hg
      exact ⟨sl2Lower c, hlow c⟩
  have heq : rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l = φ.range :=
    rankOne_eq_range_of_sl2 (D := Adjoint.g2Datum K) (i := l) φ
      (fun c => by rw [hup']; exact Adjoint.xPar_mem (isRoot_single .G2 l) c)
      (fun c => by rw [hlow']; exact Adjoint.xPar_mem (isRoot_neg_single .G2 l) c) hle
  rw [heq]
  exact Components.quasisimple_of_equiv (MonoidHom.ofInjective hinj).symm
    (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two h4)

variable (n p e : ℕ) [hp : Fact p.Prime]

theorem fundQuasisimple_G2 (hadm : StatedLieAdmissible .G2 n p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .G2 (modelUniv .G2 n p e hp.out).D, CFSG.Open.IsQuasisimple ↥R := by
  have h4' : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact h4
  exact fundQuasisimple_of_all_nodes .G2 n p e trivial hadm rfl fun l =>
    g2_rankOne_quasisimple (K := GaloisField p e) h4' l

end G2

section D4

open CFSG.LieType.Steinberg.TwistedD4

theorem fundQuasisimple_trialityD4 (n p e : ℕ) [hp : Fact p.Prime]
    (hadm : StatedLieAdmissible .trialityD4 n p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp.out).D,
      CFSG.Open.IsQuasisimple ↥R := by
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  have h4L : 4 ≤ Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) :=
    h4.trans (le_card_fixedField_iterateFrobenius he)
  have h4S : 4 ≤ Nat.card (GaloisField p (3 * e)) := by
    rw [hK]
    exact four_le_pow_three (by omega)
  refine fundQuasisimple_of_all_nodes .trialityD4 n p e trivial hadm rfl ?_
  intro k
  match k with
  | ⟨0, _⟩ =>
    have hr := Components.quasisimple_of_equiv
      (MonoidHom.ofInjective (slLong_injective hσ)).symm
      (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two h4L)
    rw [← rankOne_long_eq_range hσ] at hr
    exact hr
  | ⟨1, _⟩ =>
    have hr := Components.quasisimple_of_equiv
      (MonoidHom.ofInjective (slShort_injective hσ)).symm
      (CFSG.ClassicalInvolution.isQuasisimple_specialLinearGroup_two h4S)
    rw [← rankOne_short_eq_range hσ] at hr
    exact hr

end D4

end CFSG.ClassicalInvolution.ModelFacts

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.ComponentClassification CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups

theorem fundQuasisimple_core {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    {n e : ℕ} (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, CFSG.Open.IsQuasisimple ↥R := by
  by_cases hG2 : t = .G2
  · subst hG2
    exact ModelFacts.fundQuasisimple_G2 n p e hadm h4
  by_cases hD4 : t = .trialityD4
  · subst hD4
    exact ModelFacts.fundQuasisimple_trialityD4 n p e hadm h4
  intro R hR
  have h4' : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact h4
  obtain ⟨e'⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4 hR
  exact Components.quasisimple_of_equiv e'
    (isQuasisimple_specialLinearGroup_two h4')

section Inputs

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

structure FuzzyPairInputs (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Φ : Set (Subgroup G))
    (a : G) : Prop where
  quasi : ∀ (D : LocalLieSystemAt p f Φ a) (j : Fin D.card),
    ∀ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D, CFSG.Open.IsQuasisimple ↥R
  pair : ∀ (D : LocalLieSystemAt p f Φ a) (j : Fin D.card),
    LayerGenerationPairAt (D.tag j) (D.rank j) p (D.exp j) Fact.out

omit [Finite G] in
theorem FuzzyPairInputs.of_facts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hF3 : NoComponentOverF3 p f Φ a) (hpair : LayerGenerationPair) :
    FuzzyPairInputs p f Φ a where
  quasi D j R hR := by
    have h5 : 5 ≤ p ^ D.exp j :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq j).imp id And.right) (hF3 D j)
    exact fundQuasisimple_core hp2 (D.isFundTag j) (D.admissible j) (by omega) R hR
  pair D j := by
    have h5 : 5 ≤ p ^ D.exp j :=
      five_le_pow_of_ne_three Fact.out hp2 hq ((D.exp_eq j).imp id And.right) (hF3 D j)
    exact hpair _ _ _ _ _ (D.isFundTag j) (D.admissible j) hp2 h5

end Inputs

section Layers

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem SecToral.exists_pair_frame_data {A : Subgroup G} {S : Set G} (hs : SecData p f a Φ)
    (T : SecToral Φ a A S) (ha1 : a ≠ 1) (D : LocalLieSystemAt p f Φ a) (j : Fin D.card)
    {L : Subgroup (OddQuot a)} (hL : L = (secComponentHom hs.normalizes D j).range)
    (hdich : ∀ K ∈ centMembers Φ a, modOdd a K ≤ L ∨
      ∀ x ∈ modOdd a K, ∀ y ∈ L, x * y = y * x)
    {F₀ : Subgroup G} (hF : IsFaithfulFourGroupAt A a L F₀) :
    ∃ R₁ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
    ∃ R₂ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
    ∃ z₁ ∈ R₁.map (secComponentHom hs.normalizes D j),
    ∃ z₂ ∈ R₂.map (secComponentHom hs.normalizes D j),
      (∀ y ∈ R₁.map (secComponentHom hs.normalizes D j), z₁ * y = y * z₁) ∧
      (∀ y ∈ R₂.map (secComponentHom hs.normalizes D j), z₂ * y = y * z₂) ∧
      (∀ y ∈ R₁.map (secComponentHom hs.normalizes D j), z₂ * y = y * z₂) ∧
      (∀ y ∈ R₂.map (secComponentHom hs.normalizes D j), z₁ * y = y * z₁) ∧
      ∃ f₁ ∈ modOdd a F₀, ∃ f₂ ∈ modOdd a F₀, f₁ ≠ 1 ∧ f₂ ≠ 1 ∧ f₁ ≠ f₂ ∧
        (∀ y ∈ (secComponentHom hs.normalizes D j).range, f₁ * y * f₁⁻¹ = z₁ * y * z₁⁻¹) ∧
        (∀ y ∈ (secComponentHom hs.normalizes D j).range, f₂ * y * f₂⁻¹ = z₂ * y * z₂⁻¹) := by
  classical
  obtain ⟨hF₀A, hF₀4, -, hfaith⟩ := hF
  have hAC : ∀ g ∈ A, g ∈ Subgroup.centralizer ({a} : Set G) := fun g hg => T.mem_centralizer hg
  set B : Subgroup G := A ⊓ ((Subgroup.centralizer (L : Set (OddQuot a))).comap
    (oddQuotMk a)).map (Subgroup.centralizer ({a} : Set G)).subtype with hB
  have hBmem : ∀ (g : G) (hg : g ∈ A), g ∈ B ↔
      ∀ y ∈ L, oddQuotMk a ⟨g, hAC g hg⟩ * y = y * oddQuotMk a ⟨g, hAC g hg⟩ := by
    intro g hg
    constructor
    · rintro ⟨-, ⟨c, hc, hcg⟩⟩ y hy
      have hcg' : c = ⟨g, hAC g hg⟩ := Subtype.ext hcg
      subst hcg'
      exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm
    · intro h
      exact ⟨hg, ⟨⟨g, hAC g hg⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => (h y hy).symm,
        rfl⟩⟩
  have haB : a ∈ B := (hBmem a T.mem).mpr fun y _ => oddQuotMk_central (hAC a T.mem) y
  have hne1 : ∀ (g : G) (hg : g ∈ A), g ≠ 1 → oddQuotMk a ⟨g, hAC g hg⟩ ≠ 1 :=
      fun g hg hg1 h => by
    have hsq : (⟨g, hAC g hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hAC g hg⟩ = 1 :=
      Subtype.ext (T.sq hg)
    exact hg1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  have hFB : ∀ f₀ ∈ F₀, f₀ ∈ B → f₀ = 1 := by
    intro f₀ hf₀ hfB
    by_contra hne
    have hf₀A := hF₀A hf₀
    exact hfaith _ (oddQuotMk_mem_modOdd hf₀ (hAC f₀ hf₀A)) (hne1 f₀ hf₀A hne)
      ((hBmem f₀ hf₀A).mp hfB)
  obtain ⟨x, hxS, y, hyS, hxB, hyB, hxyB, hrep⟩ :=
    exists_pair_in_subgroup (fun g hg => T.sq hg) (fun g hg h hh => T.comm hg hh) T.card T.subset
      T.generate T.mem haB ha1 hF₀A hF₀4 hFB
  have hxA : x ∈ A := T.subset hxS
  have hyA : y ∈ A := T.subset hyS
  obtain ⟨Kx, hKxΦ, hKxa, hxc, hKxcomm⟩ := T.member x hxS
  obtain ⟨Ky, hKyΦ, hKya, hyc, hKycomm⟩ := T.member y hyS
  have hinL : ∀ K ∈ Φ, K ≤ Subgroup.centralizer ({a} : Set G) → ∀ z ∈ A,
      IsCentralInvolution K z → z ∉ B → modOdd a K ≤ L := by
    intro K hK hKa z hzA hz hzB
    rcases hdich K ⟨hK, hKa⟩ with h | h
    · exact h
    · exfalso
      apply hzB
      exact (hBmem z hzA).mpr fun y hy => h _ (oddQuotMk_mem_modOdd hz.mem (hAC z hzA)) y hy
  subst hL
  obtain ⟨Rx, hRx, hRxK⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hKxΦ, hKxa⟩
    (hinL Kx hKxΦ hKxa x hxA hxc hxB)
  obtain ⟨Ry, hRy, hRyK⟩ := exists_fundamental_of_modOdd_le_sec hs D j ⟨hKyΦ, hKya⟩
    (hinL Ky hKyΦ hKya y hyA hyc hyB)
  have hsqA : ∀ (g : G) (hg : g ∈ A),
      oddQuotMk a ⟨g, hAC g hg⟩ * oddQuotMk a ⟨g, hAC g hg⟩ = 1 := by
    intro g hg
    rw [← map_mul]
    have : (⟨g, hAC g hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hAC g hg⟩ = 1 :=
      Subtype.ext (T.sq hg)
    rw [this, map_one]
  refine ⟨Rx, hRx, Ry, hRy, oddQuotMk a ⟨x, hAC x hxA⟩, ?_, oddQuotMk a ⟨y, hAC y hyA⟩, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRxK]
    exact oddQuotMk_mem_modOdd hxc.mem _
  · rw [hRyK]
    exact oddQuotMk_mem_modOdd hyc.mem _
  · rw [hRxK]
    intro y' hy'
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
    rw [← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext (hxc.central _ hk))
  · rw [hRyK]
    intro y' hy'
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
    rw [← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext (hyc.central _ hk))
  · rw [hRxK]
    exact hKxcomm y (hAC y hyA) hyA
  · rw [hRyK]
    exact hKycomm x (hAC x hxA) hxA
  ·
    have hact : ∀ (g : G) (hgA : g ∈ A) (zg : G) (hzgA : zg ∈ A), g * zg ∈ B →
        ∀ y' ∈ (secComponentHom hs.normalizes D j).range,
          oddQuotMk a ⟨g, hAC g hgA⟩ * y' * (oddQuotMk a ⟨g, hAC g hgA⟩)⁻¹ =
          oddQuotMk a ⟨zg, hAC zg hzgA⟩ * y' * (oddQuotMk a ⟨zg, hAC zg hzgA⟩)⁻¹ := by
      intro g hgA zg hzgA hgB y' hy'
      have hgsq := hsqA g hgA
      have hB' := (hBmem (g * zg) (A.mul_mem hgA hzgA)).mp hgB y' hy'
      have h3 : oddQuotMk a ⟨g * zg, hAC _ (A.mul_mem hgA hzgA)⟩ =
          oddQuotMk a ⟨g, hAC g hgA⟩ * oddQuotMk a ⟨zg, hAC zg hzgA⟩ := by
        rw [← map_mul]
        rfl
      rw [h3] at hB'
      set u := oddQuotMk a ⟨g, hAC g hgA⟩ with hu
      set w := oddQuotMk a ⟨zg, hAC zg hzgA⟩ with hw
      have hu' : u * w * y' * (u * w)⁻¹ = y' := by
        rw [hB']
        group
      have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hgsq
      calc u * y' * u⁻¹ = u * (u * w * y' * (u * w)⁻¹) * u⁻¹ := by rw [hu']
        _ = (u * u) * w * y' * w⁻¹ * (u⁻¹ * u⁻¹) := by group
        _ = w * y' * w⁻¹ := by
          rw [hgsq, hui, hgsq]
          group
    obtain ⟨f₁, hf₁F, hf₁1, hf₁B⟩ := hrep x (Or.inl rfl)
    obtain ⟨f₂, hf₂F, hf₂1, hf₂B⟩ := hrep y (Or.inr (Or.inl rfl))
    have hf₁A := hF₀A hf₁F
    have hf₂A := hF₀A hf₂F
    have hact₁ := hact f₁ hf₁A x hxA hf₁B
    have hact₂ := hact f₂ hf₂A y hyA hf₂B
    refine ⟨oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩, oddQuotMk_mem_modOdd hf₁F _,
      oddQuotMk a ⟨f₂, hAC f₂ hf₂A⟩, oddQuotMk_mem_modOdd hf₂F _, hne1 f₁ hf₁A hf₁1,
      hne1 f₂ hf₂A hf₂1, ?_, hact₁, hact₂⟩
    intro heq
    apply hxyB
    rw [hBmem _ (A.mul_mem hxA hyA)]
    intro y' hy'
    set z₁ := oddQuotMk a ⟨x, hAC x hxA⟩ with hz₁
    set z₂ := oddQuotMk a ⟨y, hAC y hyA⟩ with hz₂
    have hz₁sq : z₁ * z₁ = 1 := hsqA x hxA
    have hz₂sq : z₂ * z₂ = 1 := hsqA y hyA
    have e1 := hact₁ y' hy'
    have e2 := hact₂ y' hy'
    rw [heq] at e1
    have e3 : z₁ * y' * z₁⁻¹ = z₂ * y' * z₂⁻¹ := e1.symm.trans e2
    have hc12 : z₁ * z₂ = z₂ * z₁ := by
      rw [hz₁, hz₂, ← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (T.comm hxA hyA))
    have hz₂i : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂sq
    have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁sq
    have h3 : oddQuotMk a ⟨x * y, hAC _ (A.mul_mem hxA hyA)⟩ = z₁ * z₂ := by
      rw [hz₁, hz₂, ← map_mul]
      rfl
    rw [h3]
    have e4 : z₂ * (z₁ * y' * z₁) * z₂ = y' := by
      have e3' : z₁ * y' * z₁ = z₂ * y' * z₂ := by
        simpa only [hz₁i, hz₂i] using e3
      rw [e3']
      calc z₂ * (z₂ * y' * z₂) * z₂ = (z₂ * z₂) * y' * (z₂ * z₂) := by group
        _ = y' := by rw [hz₂sq]; group
    have e5 : (z₂ * z₁) * y' * (z₁ * z₂) = y' := by
      calc (z₂ * z₁) * y' * (z₁ * z₂) = z₂ * (z₁ * y' * z₁) * z₂ := by group
        _ = y' := e4
    have e6 : (z₂ * z₁) * y' = y' * (z₂ * z₁) := by
      calc (z₂ * z₁) * y' = (z₂ * z₁) * y' * (z₁ * z₂) * (z₁ * z₂)⁻¹ := by group
        _ = y' * (z₁ * z₂)⁻¹ := by rw [e5]
        _ = y' * (z₂ * z₁) := by rw [mul_inv_rev, hz₁i, hz₂i]
    rw [hc12]
    exact e6

end Layers

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem layerGenerationLie_sec_pair {A : Subgroup G} {S : Set G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hBelow : CITBelowU p f (Nat.card G)) (hs : SecData p f a Φ)
    (T : SecToral Φ a A S) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hpair : ∀ (D : LocalLieSystemAt p f Φ a) (j : Fin D.card),
      LayerGenerationPairAt (D.tag j) (D.rank j) p (D.exp j) Fact.out) :
    LayerGenerationLie Φ A a := by
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  unfold LayerGenerationLie LayerGenerationOn
  intro L hL hlie hjoin F₀ hF
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
  obtain ⟨D', hD'Q, -⟩ := hs.lieDecomposition_comp hp2 h0 fundamentalWholeA1 hq Dsys
  have : (memberJoin Φ a).Normal := memberJoin_normal_of_normalizes hs.normalizes
  have hL' : CFSG.Open.IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · obtain ⟨j, hj⟩ := hD'Q i
    have hQ : D'.Q i = (secComponentHom hs.normalizes Dsys j).range := hj.symm
    obtain ⟨R₁, hR₁, R₂, hR₂, z₁, hz₁, z₂, hz₂, hc₁, hc₂, hc₁₂, hc₂₁, f₁, hf₁, f₂, hf₂, hf₁1,
      hf₂1, hf₁₂, hact₁, hact₂⟩ := T.exists_pair_frame_data hs ha1 Dsys j hQ
      (fun K hK => modOdd_le_or_commutes D' i hK) hF
    rw [hQ] at hF hL ⊢
    obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
    have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := fun g hg =>
      T.mem_centralizer (hF₀A hg)
    have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => T.sq (hF₀A hg)
    exact OddCentralizerFree.of_le_layers (hpair Dsys j (OddQuot a)
      (secComponentHom hs.normalizes Dsys j) (secComponentHom_ker_le_center hs.normalizes Dsys j) hL
      R₁ hR₁ R₂ hR₂ z₁ hz₁ z₂ hz₂ hc₁ hc₂ hc₁₂ hc₂₁ (modOdd a F₀)
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4])
      (modOdd_sq_eq_one (fun x hx => T.sq hx) hF₀A) hFn hfaith f₁ hf₁ f₂ hf₂ hf₁1 hf₂1 hf₁₂
      hact₁ hact₂)
  · exfalso
    exact not_commutes_self_of_isQuasisimple hL'.2.2 fun x hx y hy => hcomm x hx y (hjoin hy)

theorem componentLayersAt_sec_pair {A : Subgroup G} {S : Set G} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h0 : ModelClauseZero) (hBelow : CITBelowU p f (Nat.card G)) (hs : SecData p f a Φ)
    (T : SecToral Φ a A S) (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (hpair : ∀ (D : LocalLieSystemAt p f Φ a) (j : Fin D.card),
      LayerGenerationPairAt (D.tag j) (D.rank j) p (D.exp j) Fact.out) :
    ComponentLayersAt Φ A a :=
  componentLayersAt_of_layerGenerationOn (P := fun L => IsOddLieComponent L)
    (fun _ hL => hs.trichotomy hp2 h0 fundamentalWholeA1 hq hBelow hnc hL)
    (layerGenerationLie_sec_pair hp2 hq h0 hBelow hs T hnc hpair)

end Main

section Triangle

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {J₁ J₂ J₃ : Subgroup G}
  {z₁ z₂ z₃ : G}

theorem AxisTriangle.rankThreeBalance_pair [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1)
    (hBelow : CITBelowU p f (Nat.card G)) (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃)
    (hne₁₂ : z₁ ≠ z₂) (hne₁₃ : z₁ ≠ z₃) (hne₂₃ : z₂ ≠ z₃) (hind : z₁ * z₂ ≠ z₃)
    (hI : ∀ b ∈ triangleAxis z₁ z₂ z₃, b ≠ 1 →
      FuzzyPairInputs p f (triangleSecFamily J₁ J₂ J₃ b) b) :
    RankThreeBalance (triangleAxis z₁ z₂ z₃) := by
  have hcard := hT.card_axis hne₁₂ hne₁₃ hne₂₃ hind
  refine ⟨hT.isElemAbelian, hcard, hT.weakBalanced hnab hp2 hq h0 hA1 hBelow, ?_⟩
  refine twoBalancedWrt_of_secToral (S := {z₁, z₂, z₃}) hT.isElemAbelian fun a ha ha1 => ?_
  have hs := hT.secData ha
  have hnc := not_subset_center_of_ne_one hnab ha1
  obtain ⟨Dsys⟩ := hs.nonempty_lieSystem hBelow hnc
  have hqs : ∀ K ∈ triangleSecFamily J₁ J₂ J₃ a, CFSG.Open.IsQuasisimple ↥(modOdd a K) :=
    fun K hK => hs.isQuasisimple_modOdd Dsys ((hI a ha ha1).quasi Dsys) hK
  have T := hT.secToral ha hcard hqs
  exact ⟨_, T, componentLayersAt_sec_pair hp2 hq h0 hBelow hs T hnc (hI a ha ha1).pair⟩

end Triangle

end CFSG.ClassicalInvolution.Balance.Bootstrap
