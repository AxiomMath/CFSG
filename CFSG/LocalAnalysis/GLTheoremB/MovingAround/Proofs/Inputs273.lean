module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs27
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts5
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs196
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs183eqv
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129e
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut)
open scoped MatrixGroups

@[expose] def Input27_3On (T : ℕ → (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, GLAPComponent p ⊤ K →
    CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K → T p (↥K ⧸ Subgroup.center ↥K) →
    ∀ E A : Subgroup X, IsSCp p ⊤ E → IsSCp p ⊤ A → E ≠ A → IsPGroup p ↥(E ⊔ A) →
      CFSG.Open.pRank p (E ⊓ A) = 2 →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      ¬ K ≤ GLBCore p 2 E → E ≤ Subgroup.normalizer (K : Set X) →
      CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1 →
      CFSG.Open.pRank p E ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) + 1 →
      (CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
        5 ≤ p ∧ CFSG.Open.pRank p E = 3 ∧ CFSG.Open.pRank p A = 3 ∧
          (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K))) →
      (∃ Es : Subgroup X, IsSCp p ⊤ Es ∧ 3 ≤ CFSG.Open.pRank p Es ∧
          IsKConnectedIn p 3 ⊤ E Es ∧ K ≤ GLBCore p 2 Es) ∨
      IsKConnectedIn p 3 ⊤ E A ∨
      (∃ y ∈ GLBCore p 2 E, GLBConj y E = A) ∨
      (CFSG.Open.pRank p E = 3 ∧ 3 < CFSG.Open.pRank p A) ∨
      (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K) ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsCompLocallyBalanced p 1 A K

@[expose] def Input27_4On (T : ℕ → (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, GLAPComponent p ⊤ K →
    CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K → T p (↥K ⧸ Subgroup.center ↥K) →
    ∀ E A : Subgroup X, IsSCp p ⊤ E → IsSCp p ⊤ A → E ≠ A → IsPGroup p ↥(E ⊔ A) →
      2 ≤ CFSG.Open.pRank p (E ⊓ A) →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      ¬ (⨆ g ∈ A, GLBConj g K) ≤ GLBCore p 2 E → ¬ K ≤ GLBCore p 2 E →
      E ≤ Subgroup.normalizer (K : Set X) →
      CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1 →
      CFSG.Open.pRank p E ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) + 1 →
      (CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
        5 ≤ p ∧ CFSG.Open.pRank p E = 3 ∧ CFSG.Open.pRank p A = 3 ∧
          (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K))) →
      ((⨆ g ∈ A, GLBConj g K) ≤ GLBCore p 2 E) ∨
      (∃ n : ℕ, IsAltType n (barOf p K) ∧ ¬ p ∣ n) ∨
      (∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
          GLAPComponent p (GLAPLayer p ((⨆ g ∈ A, GLBConj g K) ⊓ Subgroup.centralizer ({a} : Set X))) J →
          IsLocallyOTwoBalancedWrtP p 1 (barOf p J) ∨
            (p = 3 ∧ IsLTwoTwentySeven (barOf p J) ∧ IsCompLocallyOTwoBalanced p 1 A J)) ∨
      (CFSG.Open.pRank p E = 3 ∧ 3 < CFSG.Open.pRank p A) ∨ (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K)

@[expose] def TypeAlt (_ : ℕ) (S : Type) [Group S] : Prop := ∃ n : ℕ, IsAltType n S

@[expose] def TypeChevP (p : ℕ) (S : Type) [Group S] : Prop :=
  IsChevSimple p S ∧ ¬ ∃ n : ℕ, IsAltType n S

@[expose] def TypeSpor (_ : ℕ) (S : Type) [Group S] : Prop := ∃ s : TauCeti.SporadicName, IsSporType s S

@[expose] def TypeChevQ (p : ℕ) (S : Type) [Group S] : Prop :=
  (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q S) ∧ ¬ IsChevSimple p S ∧ ¬ ∃ n : ℕ, IsAltType n S

abbrev Input27_3Alt : Prop := Input27_3On TypeAlt
abbrev Input27_3ChevP : Prop := Input27_3On TypeChevP
abbrev Input27_3Spor : Prop := Input27_3On TypeSpor
abbrev Input27_3ChevQ : Prop := Input27_3On TypeChevQ

abbrev Input27_4Alt : Prop := Input27_4On TypeAlt
abbrev Input27_4ChevP : Prop := Input27_4On TypeChevP
abbrev Input27_4Spor : Prop := Input27_4On TypeSpor
abbrev Input27_4ChevQ : Prop := Input27_4On TypeChevQ

theorem type_cases {S : Type} [Group S] (p : ℕ) (hnab : ∃ a b : S, a * b ≠ b * a)
    (hcat : CFSG.Open.IsCatalogGroup S) :
    TypeAlt p S ∨ TypeChevP p S ∨ TypeSpor p S ∨ TypeChevQ p S := by
  by_cases halt : ∃ n : ℕ, IsAltType n S
  · exact Or.inl halt
  by_cases hcp : IsChevSimple p S
  · exact Or.inr (Or.inl ⟨hcp, halt⟩)
  rcases Lemma1315b.catalog_cases hnab hcat with h | ⟨idx, ⟨e⟩⟩ | h
  · exact absurd h halt
  · refine Or.inr (Or.inr (Or.inr ⟨⟨idx.1.characteristic, idx.1.characteristic_prime, ?_,
      Or.inl ⟨.lie idx, rfl, ⟨e⟩⟩⟩, hcp, halt⟩))
    rintro rfl
    exact hcp (Or.inl ⟨.lie idx, rfl, ⟨e⟩⟩)
  · exact Or.inr (Or.inr (Or.inl h))

theorem input27_3Core_of_cases (hA : Input27_3Alt) (hP : Input27_3ChevP) (hS : Input27_3Spor)
    (hQ : Input27_3ChevQ) : Inputs27.Input27_3Core := by
  intro p hp hp2 X _ _ hXK hO K hK hKh E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2
  rcases type_cases p (Prop1116Design.not_isCommutative_barQuot ↥K hKh.1) hKh.2 with h | h | h | h
  · exact hA p hp hp2 X hXK hO K hK hKh h E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2
  · exact hP p hp hp2 X hXK hO K hK hKh h E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2
  · exact hS p hp hp2 X hXK hO K hK hKh h E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2
  · exact hQ p hp hp2 X hXK hO K hK hKh h E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2

theorem input27_4Core_of_cases (hA : Input27_4Alt) (hP : Input27_4ChevP) (hS : Input27_4Spor)
    (hQ : Input27_4ChevQ) : Inputs27.Input27_4Core := by
  intro p hp hp2 X _ _ hXK hO K hK hKh E A hE hA' hEA hEAp hr hc hKs hKΓ hN hC1 hAut hA2
  rcases type_cases p (Prop1116Design.not_isCommutative_barQuot ↥K hKh.1) hKh.2 with h | h | h | h
  · exact hA p hp hp2 X hXK hO K hK hKh h E A hE hA' hEA hEAp hr hc hKs hKΓ hN hC1 hAut hA2
  · exact hP p hp hp2 X hXK hO K hK hKh h E A hE hA' hEA hEAp hr hc hKs hKΓ hN hC1 hAut hA2
  · exact hS p hp hp2 X hXK hO K hK hKh h E A hE hA' hEA hEAp hr hc hKs hKΓ hN hC1 hAut hA2
  · exact hQ p hp hp2 X hXK hO K hK hKh h E A hE hA' hEA hEAp hr hc hKs hKΓ hN hC1 hAut hA2

theorem input27_3On_of_core (T : ℕ → (S : Type) → [Group S] → Prop) (h : Inputs27.Input27_3Core) :
    Input27_3On T := by
  intro p hp hp2 X _ _ hXK hO K hK hKh _ E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2
  exact h p hp hp2 X hXK hO K hK hKh E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2

theorem input27_4On_of_core (T : ℕ → (S : Type) → [Group S] → Prop) (h : Inputs27.Input27_4Core) :
    Input27_4On T := by
  intro p hp hp2 X _ _ hXK hO K hK hKh _ E A hE hA' hEA hEAp hr hc hKs hKΓ hN hC1 hAut hA2
  exact h p hp hp2 X hXK hO K hK hKh E A hE hA' hEA hEAp hr hc hKs hKΓ hN hC1 hAut hA2

section Common

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem comp_facts (hO : GLAPPrimeCore p X = ⊥) {K : Subgroup X} (hK : GLAPComponent p ⊤ K) :
    IsComponentOf K ⊤ ∧ GLAPPrimeCore p ↥K = ⊥ := by
  have hKc : IsComponentOf K ⊤ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116n_isComponentOf_of_glaPComponent hO hK
  exact ⟨hKc, CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPPrimeCore_eq_bot_of_isSubnormal hO
    hKc.2.1⟩

noncomputable def barOfEquivOfCore {K : Subgroup X} (hOK : GLAPPrimeCore p ↥K = ⊥) : barOf p K ≃* ↥K :=
  (QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot

noncomputable def equivCenterQuotOfBot {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥) :
    Y ≃* Y ⧸ Subgroup.center Y :=
  ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem two_le_pRank_aut (hp : p.Prime) {E A K : Subgroup X} (hE : IsSCp p ⊤ E) (hA : IsSCp p ⊤ A)
    (hEA : E ≠ A) (hr : 2 ≤ CFSG.Open.pRank p (E ⊓ A))
    (hAut : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) + 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) := by
  have := Inputs27.three_le_pRank_of_scp hp hE hA hEA hr
  omega

end Common

section Alt

open Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem alt_iso (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hOK : GLAPPrimeCore p K = ⊥) {n : ℕ}
    (hn : IsAltType n (K ⧸ Subgroup.center K))
    (hA2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → 5 ≤ p) :
    5 ≤ n ∧ Nonempty (K ≃* alternatingGroup (Fin n)) := by
  have hn5 := SchurFacts.five_le_of_isAltType hq hn
  obtain ⟨e⟩ := hn
  refine ⟨hn5, ?_⟩
  rcases SchurFacts.center_eq_bot_or_of_isAltType hp hp2 hq hOK ⟨e⟩ with hZ | ⟨rfl, h67⟩
  · exact ⟨(equivCenterQuotOfBot hZ).trans e⟩
  · exfalso
    haveI : Group.IsPerfect K := ⟨hq.1⟩
    have h1 := CFSG.SectionRank.pRank_top_le_of_injective Nat.prime_three.one_lt
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K)
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt (MulAut.congr e)] at h1
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥(alternatingGroup (Fin n)))) ≤ 2 := by
      rcases h67 with rfl | rfl
      · exact CFSG.AGLEmbedding.pRank_top_mulAut_alternatingGroup_six_le Nat.prime_three (by norm_num)
      · exact (CFSG.AGLEmbedding.pRank_top_mulAut_le (by norm_num) (by norm_num) (MulEquiv.refl _)
          Nat.prime_three).trans (by norm_num)
    have := hA2 (h1.trans h2)
    omega

theorem pRank_mulAut_alt_six_le_one (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))) ≤ 1 := by
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  have hd : Nat.card E ∣ 1440 := by
    have h1 := Subgroup.card_subgroup_dvd_card E
    rwa [CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6] at h1
  rw [Inputs27.card_eq_pow_pRank hp hE] at hd ⊢
  apply Nat.pow_le_pow_right hp.pos
  by_contra hlt
  push Not at hlt
  have h2 : p ^ 2 ∣ 1440 := (Nat.pow_dvd_pow p hlt).trans hd
  have h3 : p ∣ 1440 := (dvd_pow_self p (by norm_num)).trans h2
  have h1440 : (1440 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 := by norm_num
  rw [h1440] at h3
  rcases (Nat.Prime.dvd_mul hp).1 h3 with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h')
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h')
      omega
  · have hp5' : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h
    subst hp5'
    rw [h1440] at h2
    norm_num at h2

theorem isLocallyBalancedAbs_alt_of_dvd {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (hpn : p ∣ n) :
    CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs p 1 ↥(alternatingGroup (Fin n)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Φ : Perm (Fin n) ≃* MulAut ↥(alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6) with hΦ
  intro D hD hcard H hH hDH
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot, pow_one] at hcard
    exact hp.one_lt.ne hcard
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdp : d ^ p = 1 := hD.2 d hdD
  set σ : Perm (Fin n) := Φ.symm d with hσ
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hdp, map_one]
  have hΦσ : Φ σ = d := by rw [hσ, MulEquiv.apply_symm_apply]
  set H' : Subgroup (Perm (Fin n)) := H.map Φ.symm.toMonoidHom with hH'
  have hAH' : alternatingGroup (Fin n) ≤ H' := by
    intro a ha
    refine ⟨Φ a, hH ⟨⟨a, ha⟩, ?_⟩, by simp⟩
    ext x
    simp [Φ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have hHH : H'.map Φ.toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨Φ.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hmap : (H' ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin n)))).map Φ.toMonoidHom =
      H ⊓ Subgroup.centralizer ({d} : Set (MulAut ↥(alternatingGroup (Fin n)))) := by
    rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective Φ.toMonoidHom
      Φ.injective, hHH]
    simp [hΦσ]
  have hcore : GLAPPrimeCoreOf p (H' ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) = ⊥ := by
    obtain ⟨A, hA, hσA⟩ := Lemma116.exists_isSCp_above (Inputs27.isElemAbelian_zpowers' hσp)
    have hσA' : σ ∈ A := hσA (Subgroup.mem_zpowers σ)
    have hAle : A ≤ H' ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin n))) := by
      intro a ha
      refine ⟨hAH' (AltFacts5.mem_alt_of_pow (hp.odd_of_ne_two hp2) (hA.2.1.2 a ha)), ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 (Inputs27.elem_mul_comm hA.2.1 ha hσA')
    refine CFSG.HardMathSupport.Solomon.Coordinator.i271h_perm_coprime_normalized_eq_bot hA
      (by rw [Fintype.card_fin]; exact hpn) ?_ (hAle.trans (le_normalizer_glaPPrimeCoreOf p _))
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp _)
  refine eq_bot_iff.2 fun x hx => ?_
  have hx' : x ∈ GLAPPrimeCoreOf p
      (H ⊓ Subgroup.centralizer ({d} : Set (MulAut ↥(alternatingGroup (Fin n))))) :=
    (iInf₂_le_of_le d hdD (iInf_le_of_le hd1' le_rfl) :
      CFSG.HardMathSupport.Solomon.LocalBalance.localDeltaIn p H D ≤ _) hx
  rw [← hmap, ← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p
    Φ.toMonoidHom Φ.injective, hcore, Subgroup.map_bot] at hx'
  exact hx'

theorem ne_bot_of_pRank_eq_one {H : Subgroup X} (hp : p.Prime) (h : CFSG.Open.pRank p H = 1) : H ≠ ⊥ := by
  intro h0
  rw [h0] at h
  have : CFSG.Open.pRank p (⊥ : Subgroup X) ≤ 0 := CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => by
    rw [le_bot_iff.1 hE, Subgroup.card_bot, pow_zero]
  omega

@[expose] def Input27_4AltDvdComp : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X],
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, GLAPComponent p ⊤ K →
    ∀ n : ℕ, 5 ≤ n → p ∣ n → Nonempty (↥K ≃* alternatingGroup (Fin n)) →
    ∀ A : Subgroup X, IsElemAbelian p A → ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (GLAPLayer p ((⨆ g ∈ A, GLBConj g K) ⊓ Subgroup.centralizer ({a} : Set X))) J →
      IsLocallyOTwoBalancedWrtP p 1 (barOf p J)

@[expose] def Input27_3AltRegular : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, IsComponentOf K ⊤ →
    ∀ n r δ : ℕ, Nonempty (↥K ≃* alternatingGroup (Fin n)) → 2 ≤ r → 1 ≤ δ → δ < p → n = p ^ r + δ →
    ∀ E A : Subgroup X, IsSCp p ⊤ E → IsSCp p ⊤ A → E ≠ A → IsPGroup p ↥(E ⊔ A) →
      CFSG.Open.pRank p (E ⊓ A) = 2 →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      ¬ K ≤ GLBCore p 2 E → E ≤ Subgroup.normalizer (K : Set X) →
      CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1 →
      CFSG.Open.pRank p E = r + 1 →
      (E ⊓ K) ⊓ (E ⊓ Subgroup.centralizer (K : Set X)) = ⊥ →
      (∃ e1 : ↥K, (e1 : X) ∈ E ∧ e1 ≠ 1 ∧ ∃ ψ : ↥K ≃* ↥(alternatingGroup (Fin n)),
        (ψ e1).1.cycleType = Multiset.replicate (p ^ (r - 1)) p) →
      (∃ Es : Subgroup X, IsSCp p ⊤ Es ∧ 3 ≤ CFSG.Open.pRank p Es ∧
          IsKConnectedIn p 3 ⊤ E Es ∧ K ≤ GLBCore p 2 Es) ∨
      IsKConnectedIn p 3 ⊤ E A ∨
      (∃ y ∈ GLBCore p 2 E, GLBConj y E = A) ∨
      (CFSG.Open.pRank p E = 3 ∧ 3 < CFSG.Open.pRank p A) ∨
      (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K) ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsCompLocallyBalanced p 1 A K

theorem ne_six_of_dvd {K : Type} [Group K] [Finite K] {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (eK : K ≃* alternatingGroup (Fin n)) (hpn : p ∣ n)
    (hA2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → 5 ≤ p) : n ≠ 6 := by
  rintro rfl
  have hp3 : p = 3 := by
    have h6 : p ∣ 2 * 3 := hpn
    rcases (Nat.Prime.dvd_mul hp).1 h6 with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr eK)
  have h2 := CFSG.AGLEmbedding.pRank_top_mulAut_alternatingGroup_six_le hp hp2
  have := hA2 (h1 ▸ h2)
  omega

theorem input27_3Alt_of_regular (h : Input27_3AltRegular) : Input27_3Alt := by
  intro p hp hp2 X _ _ hXK hO K hK hKh hT E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, hOK⟩ := comp_facts hO hK
  obtain ⟨n, hn⟩ := hT
  obtain ⟨hn5, ⟨eK⟩⟩ := alt_iso hp hp2 hKh.1 hOK hn fun h2 => (hA2 h2).1
  have hAut2 := two_le_pRank_aut hp hE hA' hEA hr.ge hAut
  by_cases hpn : p ∣ n
  ·
    have hn6 := ne_six_of_dvd hp hp2 eK hpn fun h2 => (hA2 h2).1
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
    exact (CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs.of_mulEquiv
      ((barOfEquivOfCore hOK).trans eK) (isLocallyBalancedAbs_alt_of_dvd hp hp2 hn5 hn6 hpn)).isLocallyBalanced _
  ·
    have hn6 : n ≠ 6 := by
      rintro rfl
      have hp5 : 5 ≤ p := by
        have h3 : p ≠ 3 := by rintro rfl; exact hpn (by norm_num)
        exact Inputs27.five_le_of_prime hp hp2 h3
      have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr eK)
      have h2 := pRank_mulAut_alt_six_le_one hp hp5
      omega
    have hpltn : p < n := by
      have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr eK)
      have h2 := CFSG.AGLEmbedding.pRank_top_mulAut_le hn5 hn6 (MulEquiv.refl _) hp
      have h3 : 2 ≤ n / p := by omega
      have h4 : 2 * p ≤ n := (Nat.le_div_iff_mul_le hp.pos).1 h3 |>.trans' (by rw [mul_comm])
      have := hp.two_le
      omega
    have hE3 : 3 ≤ CFSG.Open.pRank p E := Inputs27.three_le_pRank_of_scp hp hE hA' hEA hr.ge
    have hKs : (⨆ g ∈ E, GLBConj g K) = K := Inputs27.kStar_eq_of_le_normalizer hN
    have hE0 : E ⊓ Subgroup.centralizer ((⨆ g ∈ E, GLBConj g K : Subgroup X) : Set X) ≠ ⊥ := by
      rw [hKs]
      exact ne_bot_of_pRank_eq_one hp hC1
    rcases AltFacts5.input23_6_holds X p n hp hp2 hpltn hpn E K hE hE3 hKc ⟨eK⟩ hE0 with hKΓ' |
      ⟨r, δ, hr2, hδ1, hδp, hnr, hEr, hdisj, he1⟩
    · exact absurd hKΓ' hKΓ
    · rw [hKs] at hdisj
      exact h p hp hp2 X hXK hO K hKc n r δ ⟨eK⟩ hr2 hδ1 hδp hnr E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hEr
        hdisj he1

theorem input27_4Alt_of_dvdComp (h : Input27_4AltDvdComp) : Input27_4Alt := by
  intro p hp hp2 X _ _ hXK hO K hK hKh hT E A hE hA' hEA hEAp hr hc hKs hKΓ hN hC1 hAut hA2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, hOK⟩ := comp_facts hO hK
  obtain ⟨n, hn⟩ := hT
  obtain ⟨hn5, ⟨eK⟩⟩ := alt_iso hp hp2 hKh.1 hOK hn fun h2 => (hA2 h2).1
  by_cases hpn : p ∣ n
  · exact Or.inr (Or.inr (Or.inl fun a ha ha1 J hJ =>
      Or.inl (h p hp hp2 X hO K hK n hn5 hpn ⟨eK⟩ A hA'.2.1 a ha ha1 J hJ)))
  · exact Or.inr (Or.inl ⟨n, ⟨(barOfEquivOfCore hOK).trans eK⟩, hpn⟩)

end Alt


section Spor

open CFSG.HardMathSupport.Timmesfeld.Coordinator (IsLocallyBalancedAbs IsLocallyOneBalancedAbs
  NoElemAbelianCubeAut SporadicLocalOneData SporadicOuterLeTwo autCenterQuot)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

@[expose] def SporOneBalanceCube : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ name : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ^ 3 ∣ Nat.card S → ¬ p ^ 4 ∣ Nat.card S →
        IsLocallyOneBalancedAbs p S

theorem isPGroup_center_of_core {Y : Type} [Group Y] [Finite Y] (hp : p.Prime)
    (hO : GLAPPrimeCore p Y = ⊥) : IsPGroup p ↥(Subgroup.center Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro z
  have hn0 : orderOf (z : Y) ≠ 0 := (orderOf_pos (z : Y)).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  set y : Y := (z : Y) ^ (p ^ a) with hy
  have hyo : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero a hp.ne_zero) ⟨m, hnm⟩, hnm,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos a)]
  have hyZ : y ∈ Subgroup.center Y := Subgroup.pow_mem _ z.2 _
  haveI hN : (Subgroup.zpowers y).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 hyZ)
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, hyo]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  have h0 := GL83.CompFam.eq_bot_of_isSubnormal_of_coprime hp hO
    (CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_normal hN) hcop
  have hy1 : y = 1 := by
    have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
    rw [h0, Subgroup.mem_bot] at this
    exact this
  refine ⟨a, Subtype.ext ?_⟩
  simpa [hy] using hy1

theorem map_innerAut_autCenterQuot (Y : Type*) [Group Y] :
    (innerAut Y).map (autCenterQuot Y) = innerAut (Y ⧸ Subgroup.center Y) := by
  have hconj : ∀ y : Y, autCenterQuot Y (MulAut.conj y) = MulAut.conj (y : Y ⧸ Subgroup.center Y) := by
    intro y
    ext z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_mk]
    simp [MulAut.conj_apply]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(y : Y ⧸ Subgroup.center Y), (hconj y).symm⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨MulAut.conj y, ⟨y, rfl⟩, hconj y⟩

theorem isLocallyBalancedAbs_of_centerQuot {k : ℕ} {Y : Type*} [Group Y] (hperf : commutator Y = ⊤)
    (h : IsLocallyBalancedAbs p k (Y ⧸ Subgroup.center Y)) : IsLocallyBalancedAbs p k Y :=
  CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs.of_injective (autCenterQuot Y)
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf)
    (map_innerAut_autCenterQuot Y).ge h

theorem pRank_mulAut_le_quot {Y : Type} [Group Y] [Finite Y] (hp : p.Prime) (hperf : commutator Y = ⊤) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut Y)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Y ⧸ Subgroup.center Y))) :=
  CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (autCenterQuot Y)
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf)

theorem index_innerAut_dvd {Y : Type*} [Group Y] (hperf : commutator Y = ⊤) :
    (innerAut Y).index ∣ (innerAut (Y ⧸ Subgroup.center Y)).index := by
  have h := Subgroup.index_map_of_injective (H := innerAut Y)
    (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf)
  rw [map_innerAut_autCenterQuot Y] at h
  rw [h]
  exact dvd_mul_right _ _

theorem pRank_le_two_of_noCube {S : Type} [Group S] [Finite S] (hp : p.Prime)
    (h : NoElemAbelianCubeAut p S) : CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  rw [Inputs27.card_eq_pow_pRank hp hE]
  apply Nat.pow_le_pow_right hp.pos
  by_contra hlt
  push Not at hlt
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime p (G := ↥E) (n := 3)
    (by rw [Inputs27.card_eq_pow_pRank hp hE]; exact pow_dvd_pow p hlt)
  apply h (F₀.map E.subtype) (CFSG.Open.IsElemAbelian.mono hE (Subgroup.map_subtype_le F₀))
  rw [Subgroup.card_map_of_injective E.subtype_injective, hF₀]

theorem isMulCommutative_of_card_le_sq {Q : Type*} [Group Q] [Finite Q] (hp : p.Prime) {k : ℕ}
    (hk : Nat.card Q = p ^ k) (hk2 : k ≤ 2) : IsMulCommutative Q := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · rw [pow_zero] at hk
    haveI : Subsingleton Q := (Nat.card_eq_one_iff_unique.1 hk).1
    haveI : IsCyclic Q := isCyclic_of_subsingleton
    infer_instance
  · rw [pow_one] at hk
    haveI : IsCyclic Q := isCyclic_of_prime_card hk
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hk

theorem spor_false_of_rank (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) (hp : p.Prime)
    {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K) (hOK : GLAPPrimeCore p ↥K = ⊥) {s : TauCeti.SporadicName}
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) ≤ 2)
    (h3 : 5 ≤ p → ¬ p ^ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K))
    (hA2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
      5 ≤ p ∧ (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K))) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf : commutator ↥K = ⊤ := hq.1
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnab := Prop1116Design.not_isCommutative_barQuot ↥K hq
  have hout : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) ≤ 2 := hOut _ inferInstance hnab s ⟨e⟩
  obtain ⟨hp5, hOS⟩ := hA2 ((pRank_mulAut_le_quot hp hperf).trans hrk)
  have h3' := h3 hp5
  rcases hOS with hdvd | ⟨P, hP⟩
  ·
    have h1 := hdvd.trans (index_innerAut_dvd hperf)
    have h2 : (innerAut (↥K ⧸ Subgroup.center ↥K)).index ≤ 2 := hout
    have h0 : 0 < (innerAut (↥K ⧸ Subgroup.center ↥K)).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have := Nat.le_of_dvd h0 h1
    omega
  ·
    apply hP
    have hZp := isPGroup_center_of_core hp hOK
    have hZ12 := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.card_center_dvd_twelve hSpM hq s e
    have hZ : Subgroup.center ↥K = ⊥ := by
      obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hZp
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · exact Subgroup.eq_bot_of_card_eq _ (by rw [ha, h0, pow_zero])
      · exfalso
        have hp12 : p ∣ 12 := (dvd_pow_self p hpos.ne').trans (ha ▸ hZ12)
        have h12 : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
        rw [h12] at hp12
        rcases (Nat.Prime.dvd_mul hp).1 hp12 with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
          omega
    have hcardK : Nat.card ↥K = Nat.card (↥K ⧸ Subgroup.center ↥K) :=
      Nat.card_congr (equivCenterQuotOfBot hZ).toEquiv
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
    have hk2 : k ≤ 2 := by
      by_contra hk3
      push Not at hk3
      apply h3'
      rw [← hcardK]
      have hd : p ^ k ∣ Nat.card ↥K := hk ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup ↥K)
      exact (Nat.pow_dvd_pow p hk3).trans hd
    exact isMulCommutative_of_card_le_sq hp hk hk2

theorem spor_balanced (hOne : SporadicLocalOneData) (hCube : SporOneBalanceCube) (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥K) (hOK : GLAPPrimeCore p ↥K = ⊥) {s : TauCeti.SporadicName}
    (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hA2 : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
      5 ≤ p ∧ (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K))) :
    IsLocallyBalancedAbs p 1 (↥K ⧸ Subgroup.center ↥K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnab := Prop1116Design.not_isCommutative_barQuot ↥K hq
  have hcen : Subgroup.center (↥K ⧸ Subgroup.center ↥K) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer (↥K ⧸ Subgroup.center ↥K)) ≤ 2 := hOut _ inferInstance hnab s ⟨e⟩
  by_contra hbal
  have hone : ¬ IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K) := fun h =>
    hbal (h.isLocallyBalancedAbs hp le_rfl)
  have hcube : NoElemAbelianCubeAut p (↥K ⧸ Subgroup.center ↥K) ∧
      (5 ≤ p → ¬ p ^ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) := by
    by_cases h3 : p ^ 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)
    · have h4 : ¬ p ^ 4 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := fun h4 =>
        hone (hOne _ inferInstance hnab s ⟨e⟩ p hp hp2 h3 (Or.inl h4))
      have hnc : ∃ x y : ↥K ⧸ Subgroup.center ↥K, x ^ p = 1 ∧ y ^ p = 1 ∧ x * y ≠ y * x ∧
          IsPGroup p (Subgroup.closure ({x, y} : Set (↥K ⧸ Subgroup.center ↥K))) := by
        by_contra hno
        exact hone (hOne _ inferInstance hnab s ⟨e⟩ p hp hp2 h3 (Or.inr hno))
      have hp5 : ¬ 5 ≤ p := fun hp5 => hone (hCube _ inferInstance hnab s ⟨e⟩ p hp hp5 h3 h4)
      exact ⟨CFSG.HardMathSupport.Timmesfeld.Coordinator.noElemAbelianCubeAut_of_noncomm hp hp2 hcen hout
        h4 hnc, fun h => absurd h hp5⟩
    · exact ⟨CFSG.HardMathSupport.Timmesfeld.Coordinator.noElemAbelianCubeAut_of_not_dvd hp hp2 hcen hout
        h3, fun _ => h3⟩
  exact spor_false_of_rank hOut hSpM hp hq hOK e (pRank_le_two_of_noCube hp hcube.1) hcube.2 hA2

theorem input27_3Spor_of_data (hOne : SporadicLocalOneData) (hCube : SporOneBalanceCube)
    (hOut : SporadicOuterLeTwo) (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) :
    Input27_3Spor := by
  intro p hp hp2 X _ _ _ hO K hK hKh hT E A _ _ _ _ _ _ _ _ _ _ hA2
  obtain ⟨-, hOK⟩ := comp_facts hO hK
  obtain ⟨s, ⟨e⟩⟩ := hT
  have hq : CFSG.Open.IsQuasisimple ↥K := hKh.1
  have hbal := spor_balanced hOne hCube hOut hSpM hp hp2 hq hOK e fun h => ⟨(hA2 h).1, (hA2 h).2.2.2⟩
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
  exact (CFSG.HardMathSupport.Timmesfeld.Coordinator.IsLocallyBalancedAbs.of_mulEquiv (barOfEquivOfCore hOK)
    (isLocallyBalancedAbs_of_centerQuot hq.1 hbal)).isLocallyBalanced _

end Spor


section ChevP

open CFSG.HardMathSupport.Timmesfeld.Coordinator (IsLocallyBalancedAbs DefCharInnerCoreFree autCenterQuot)
open CFSG.HardMathSupport.Dickson.I271 (DefCharOuterCoreFree)
open CFSG.Yardstones.Md0ec50421ce4 (onLie ambiguousChev)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

noncomputable def autBarQuot {K : Subgroup X} (hOK : GLAPPrimeCore p ↥K = ⊥) :
    MulAut (barOf p K) →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
  (autCenterQuot ↥K).comp (MulAut.congr (barOfEquivOfCore hOK)).toMonoidHom

theorem autBarQuot_injective {K : Subgroup X} (hOK : GLAPPrimeCore p ↥K = ⊥)
    (hperf : commutator ↥K = ⊤) : Function.Injective (autBarQuot hOK) :=
  (CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf).comp
    (MulAut.congr (barOfEquivOfCore hOK)).injective

theorem map_innerAut_autBarQuot {K : Subgroup X} (hOK : GLAPPrimeCore p ↥K = ⊥) :
    (innerAut (barOf p K)).map (autBarQuot hOK) = innerAut (↥K ⧸ Subgroup.center ↥K) := by
  have h1 : (innerAut (barOf p K)).map (MulAut.congr (barOfEquivOfCore hOK)).toMonoidHom = innerAut ↥K :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr (barOfEquivOfCore hOK)
  rw [autBarQuot, ← Subgroup.map_map, h1]
  exact map_innerAut_autCenterQuot ↥K

theorem isCompLocallyBalanced_of_coreFree (hp : p.Prime) {K A : Subgroup X} (hperf : commutator ↥K = ⊤)
    (hOK : GLAPPrimeCore p ↥K = ⊥)
    (h : ∀ d ∈ (autBar p A K).map (autBarQuot hOK), orderOf d = p →
      ∀ H : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), innerAut (↥K ⧸ Subgroup.center ↥K) ≤ H →
        d ∈ Subgroup.normalizer (H : Set (MulAut (↥K ⧸ Subgroup.center ↥K))) →
        GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (↥K ⧸ Subgroup.center ↥K)))) = ⊥) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsCompLocallyBalanced p 1 A K := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro D hD H hH hDH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot, pow_one] at hDc
    exact hp.one_lt.ne hDc
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hdo : orderOf d = p := orderOf_eq_prime (hDel.2 d hdD) hd1'
  have hψ := autBarQuot_injective hOK hperf
  have hH' : innerAut (↥K ⧸ Subgroup.center ↥K) ≤ H.map (autBarQuot hOK) := by
    rw [← map_innerAut_autBarQuot hOK]
    exact Subgroup.map_mono hH
  have hdN : autBarQuot hOK d ∈
      Subgroup.normalizer ((H.map (autBarQuot hOK) : Subgroup _) : Set (MulAut (↥K ⧸ Subgroup.center ↥K))) :=
    Subgroup.le_normalizer_map (autBarQuot hOK) ⟨d, hDH hdD, rfl⟩
  have h0 := h (autBarQuot hOK d) ⟨d, hDA hdD, rfl⟩ (by rw [orderOf_injective _ hψ]; exact hdo)
    (H.map (autBarQuot hOK)) hH' hdN
  rw [← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_inf_centralizer_of_injective _ hψ,
    ← CFSG.HardMathSupport.Timmesfeld.Coordinator.map_glaPPrimeCoreOf_of_injective p _ hψ,
    Subgroup.map_eq_bot_iff_of_injective _ hψ] at h0
  rw [eq_bot_iff]
  exact (iInf₂_le_of_le d hdD (iInf_le_of_le hd1' le_rfl) :
    CFSG.HardMathSupport.Solomon.LocalBalance.localDeltaIn p H D ≤ _).trans h0.le

@[expose] def L28AutRank : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid),
    q.card = 8 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) →
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ 2

@[expose] def Input27_3L227 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore 3 X = ⊥ → ∀ K : Subgroup X, GLAPComponent 3 ⊤ K →
    CFSG.LocalAnalysis.GLTheoremA.IsKHat ↥K → IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K) →
    ∀ E A : Subgroup X, ¬ autBar 3 A K ≤ innerAut (barOf 3 K) →
      IsSCp 3 ⊤ E → IsSCp 3 ⊤ A → E ≠ A → IsPGroup 3 ↥(E ⊔ A) →
      CFSG.Open.pRank 3 (E ⊓ A) = 2 →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      ¬ K ≤ GLBCore 3 2 E → E ≤ Subgroup.normalizer (K : Set X) →
      CFSG.Open.pRank 3 (E ⊓ Subgroup.centralizer (K : Set X)) = 1 →
      CFSG.Open.pRank 3 E ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) + 1 →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) →
      (∃ Es : Subgroup X, IsSCp 3 ⊤ Es ∧ 3 ≤ CFSG.Open.pRank 3 Es ∧
          IsKConnectedIn 3 3 ⊤ E Es ∧ K ≤ GLBCore 3 2 Es) ∨
      IsKConnectedIn 3 3 ⊤ E A ∨
      (∃ y ∈ GLBCore 3 2 E, GLBConj y E = A) ∨
      (CFSG.Open.pRank 3 E = 3 ∧ 3 < CFSG.Open.pRank 3 A) ∨
      (3 = 3 ∧ CFSG.Open.pRank 3 E = 3) ∨
      (3 = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K) ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsCompLocallyBalanced 3 1 A K

theorem input27_3ChevP_of (hDC : DefCharInnerCoreFree) (hOC : DefCharOuterCoreFree) (hL28 : L28AutRank)
    (hL227 : Input27_3L227) : Input27_3ChevP := by
  intro p hp hp2 X _ _ hXK hO K hK hKh hT E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut hA2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, hOK⟩ := comp_facts hO hK
  obtain ⟨hchev, halt⟩ := hT
  have hq : CFSG.Open.IsQuasisimple ↥K := hKh.1
  have hperf : commutator ↥K = ⊤ := hq.1
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnab := Prop1116Design.not_isCommutative_barQuot ↥K hq
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie idx =>
      have hchar : idx.1.characteristic = p := hi
      by_cases hL : p = 3 ∧ IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K)
      · obtain ⟨rfl, hL⟩ := hL
        by_cases hin : autBar 3 A K ≤ innerAut (barOf 3 K)
        · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
          refine isCompLocallyBalanced_of_coreFree hp hperf hOK fun d hd hdo H hH _ => ?_
          have hdI : d ∈ innerAut (↥K ⧸ Subgroup.center ↥K) := by
            obtain ⟨d', hd', rfl⟩ := hd
            rw [← map_innerAut_autBarQuot hOK]
            exact ⟨d', hin hd', rfl⟩
          exact hDC _ inferInstance hnab idx ⟨e⟩ 3 hp hp2 hchar d hdI hdo H hH
        · have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) := by
            by_contra h3
            have := (hA2 (by omega)).1
            omega
          exact hL227 X hXK hO K hK hKh hL E A hin hE hA' hEA hEAp hr hc hKΓ hN hC1 hAut h3
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
        refine isCompLocallyBalanced_of_coreFree hp hperf hOK fun d _ hdo H hH _ => ?_
        by_cases hdI : d ∈ innerAut (↥K ⧸ Subgroup.center ↥K)
        · exact hDC _ inferInstance hnab idx ⟨e⟩ p hp hp2 hchar d hdI hdo H hH
        · exact hOC _ inferInstance hnab idx ⟨e⟩ p hp hp2 hchar
            (fun h => hL ⟨h.1, Inputs196.isLTwoTwentySeven_of_coordinator h.2⟩) d hdo hdI H hH
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · cases i with
    | alternating n hn => exact absurd ⟨n, ⟨e⟩⟩ halt
    | lie idx =>
      obtain ⟨hp3, hidx⟩ := Inputs196.ambiguousChev_lie_odd hp2 hi
      subst hp3
      obtain ⟨d, hv⟩ := idx
      rcases hidx with ⟨q, hq', hq8⟩ | ⟨q, hq', hq2⟩
      ·
        simp only at hq'
        subst hq'
        exfalso
        have h1 := hL28 _ q hv hq8 ⟨e⟩
        have := (hA2 ((pRank_mulAut_le_quot hp hperf).trans h1)).1
        omega
      ·
        simp only at hq'
        subst hq'
        have hm := Inputs196.psp43_model_of_twistedA hq2 e
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
        refine isCompLocallyBalanced_of_coreFree hp hperf hOK fun d _ hdo H hH _ => ?_
        have hdI : d ∈ innerAut (↥K ⧸ Subgroup.center ↥K) :=
          Inputs196.mem_innerAut_of_psp43 hm (by rw [← hdo]; exact pow_orderOf_eq_one d)
        exact CFSG.HardMathSupport.Timmesfeld.DefChar.innerCoreFree_PSp_two inferInstance hnab hm
          (by norm_num) d hdI hdo H hH
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

end ChevP


section AltComp

open Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem sup_inf_centralizer_le {A B : Subgroup X} {a : X} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hd : A ⊓ B = ⊥) (haA : a ∈ Subgroup.normalizer (A : Set X))
    (haB : a ∈ Subgroup.normalizer (B : Set X)) :
    (A ⊔ B) ⊓ Subgroup.centralizer ({a} : Set X) ≤
      (A ⊓ Subgroup.centralizer ({a} : Set X)) ⊔ (B ⊓ Subgroup.centralizer ({a} : Set X)) := by
  rintro x ⟨hx, hxa⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := (GL83.CompFam.mem_sup_of_commute hc).1 hx
  have hxa' : (u * v) * a = a * (u * v) := Subgroup.mem_centralizer_singleton_iff.1 hxa
  have hu' : a * u * a⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 haA u).1 hu
  have hv' : a * v * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 haB v).1 hv
  have heq : (a * u * a⁻¹) * (a * v * a⁻¹) = u * v := by
    calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
      _ = (u * v) * a * a⁻¹ := by rw [hxa']
      _ = u * v := by group
  have hmem : u⁻¹ * (a * u * a⁻¹) ∈ A ⊓ B := by
    refine ⟨A.mul_mem (A.inv_mem hu) hu', ?_⟩
    have e : u⁻¹ * (a * u * a⁻¹) = v * (a * v * a⁻¹)⁻¹ := by
      calc u⁻¹ * (a * u * a⁻¹) = u⁻¹ * ((a * u * a⁻¹) * (a * v * a⁻¹)) * (a * v * a⁻¹)⁻¹ := by group
        _ = u⁻¹ * (u * v) * (a * v * a⁻¹)⁻¹ := by rw [heq]
        _ = v * (a * v * a⁻¹)⁻¹ := by group
    rw [e]
    exact B.mul_mem hv (B.inv_mem hv')
  rw [hd, Subgroup.mem_bot] at hmem
  have hua : a * u * a⁻¹ = u := (inv_mul_eq_one.1 hmem).symm
  have hva : a * v * a⁻¹ = v := by
    have h1 := heq
    rw [hua] at h1
    exact mul_left_cancel h1
  refine Subgroup.mul_mem_sup ⟨hu, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    ⟨hv, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  · calc u * a = a * u * a⁻¹ * a := by rw [hua]
      _ = a * u := by group
  · calc v * a = a * v * a⁻¹ * a := by rw [hva]
      _ = a * v := by group

theorem sSup_inf_centralizer_le {a : X} (𝓛 : Finset (Subgroup X))
    (hcomm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x)
    (hZ : ∀ L ∈ 𝓛, L ⊓ Subgroup.centralizer (L : Set X) = ⊥)
    (haN : ∀ L ∈ 𝓛, a ∈ Subgroup.normalizer (L : Set X)) :
    sSup (↑𝓛 : Set (Subgroup X)) ⊓ Subgroup.centralizer ({a} : Set X) ≤
      ⨆ L ∈ 𝓛, L ⊓ Subgroup.centralizer ({a} : Set X) := by
  classical
  induction 𝓛 using Finset.induction_on with
  | empty => simp
  | insert L s hLs ih =>
    have hL : L ∈ insert L s := Finset.mem_insert_self L s
    have hs : ∀ L' ∈ s, L' ∈ insert L s := fun L' h => Finset.mem_insert_of_mem h
    have ih' := ih (fun L1 h1 L2 h2 => hcomm L1 (hs L1 h1) L2 (hs L2 h2)) (fun L' h => hZ L' (hs L' h))
      (fun L' h => haN L' (hs L' h))
    rw [Finset.coe_insert, sSup_insert, Finset.iSup_insert]
    have hsC : sSup (↑s : Set (Subgroup X)) ≤ Subgroup.centralizer (L : Set X) := by
      refine sSup_le fun L' hL' => fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      have hne : L ≠ L' := fun h => hLs (h ▸ hL')
      exact hcomm L hL L' (hs L' hL') hne x hx y hy
    have hd : L ⊓ sSup (↑s : Set (Subgroup X)) = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left L hsC).trans (hZ L hL).le)
    have hc : ∀ x ∈ L, ∀ y ∈ sSup (↑s : Set (Subgroup X)), x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 (hsC hy) x hx
    have haS : a ∈ Subgroup.normalizer ((sSup (↑s : Set (Subgroup X)) : Subgroup X) : Set X) := by
      have h1 : Subgroup.zpowers a ≤ Subgroup.normalizer
          ((⨆ L' : ↥(↑s : Set (Subgroup X)), (L' : Subgroup X) : Subgroup X) : Set X) :=
        Inputs27.le_normalizer_iSup' _ fun L' => Subgroup.zpowers_le.2 (haN L' (hs L' L'.2))
      rw [sSup_eq_iSup']
      exact h1 (Subgroup.mem_zpowers a)
    exact (sup_inf_centralizer_le hc hd (haN L hL) haS).trans (sup_le_sup_left ih' _)

theorem le_of_barX_le {Y J N : Subgroup X} (hJ : GLAPComponent p Y J) (hNY : N ≤ Y) (hN : IsSubnormal N Y)
    (hle : barX p Y J ≤ barX p Y N) : J ≤ N := by
  classical
  set P := preimBarX p Y J ⊓ N with hP
  have hPsn : IsSubnormal P Y := by
    have h1 := isSubnormal_inf (isSubnormal_preimBarX p hJ.2.2.1.2.1) N
    rw [inf_eq_right.2 hNY] at h1
    exact isSubnormal_trans' h1 hN
  have hPbar : barX p Y P = barX p Y J := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨y', hy', hyy⟩ := (Subgroup.mem_subgroupOf.1 hy).1
      have : y' = y := Subtype.ext hyy
      rw [← this]
      exact hy'
    · rintro _ ⟨j, hj, rfl⟩
      obtain ⟨n, hn, hnj⟩ := hle ⟨j, hj, rfl⟩
      exact ⟨n, Subgroup.mem_subgroupOf.2 ⟨⟨n, ⟨j, hj, hnj.symm⟩, rfl⟩, Subgroup.mem_subgroupOf.1 hn⟩, hnj⟩
  obtain ⟨L, ⟨hLP, hLsn, hLbar⟩, hmin⟩ := (wellFounded_lt (α := Subgroup X)).has_min
    {L | L ≤ P ∧ IsSubnormal L Y ∧ barX p Y L = barX p Y J} ⟨P, le_rfl, hPsn, hPbar⟩
  have hLY : L ≤ Y := hLP.trans (inf_le_right.trans hNY)
  have hLc : GLAPComponent p Y L := by
    refine ⟨hLY, hLsn, ?_, ?_⟩
    · change IsComponentOf (barX p Y L) ⊤
      rw [hLbar]
      exact hJ.2.2.1
    · intro J'' hJ'' hJ''sn heq
      exact hmin J'' ⟨hJ''.le.trans hLP, hJ''sn, heq.trans hLbar⟩ hJ''
  have hJL : J = L := glaPComponent_unique hJ hLc hLbar.symm
  rw [hJL]
  exact hLP.trans inf_le_right

theorem exists_le_of_le_iSup {Y J : Subgroup X} {ι : Type*} (s : Finset ι) (N : ι → Subgroup X)
    (hJ : GLAPComponent p Y J) (hJle : J ≤ ⨆ i ∈ s, N i) (hNY : ∀ i ∈ s, N i ≤ Y)
    (hYN : ∀ i ∈ s, Y ≤ Subgroup.normalizer (N i : Set X)) : ∃ i ∈ s, J ≤ N i := by
  classical
  by_contra hno
  push Not at hno
  have hJc : IsComponentOf (barX p Y J) ⊤ := hJ.2.2.1
  have hcomm : ∀ i ∈ s, ⁅barX p Y J, barX p Y (N i)⁆ = ⊥ := by
    intro i hi
    have hnorm : (⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)) ≤
        Subgroup.normalizer ((barX p Y (N i) : Subgroup _) : Set (↥Y ⧸ GLAPPrimeCore p ↥Y)) := by
      have h1 := barX_le_normalizer (C := Y) (S := N i) (T := Y) (p := p) (hYN i hi)
      rwa [barX_self] at h1
    rcases Input183.comp_le_or_comm (CFSG.Assembly.isComponentOf_iff_open.2 hJc) le_top hnorm with h | h
    · exact absurd (le_of_barX_le hJ (hNY i hi)
        (IsSubnormal.step (hNY i hi) ((Subgroup.normal_subgroupOf_iff_le_normalizer (hNY i hi)).2 (hYN i hi))
          (IsSubnormal.refl Y)) h) (hno i hi)
    · exact h
  set Cpre : Subgroup X := ((Subgroup.centralizer ((barX p Y J : Subgroup _) :
    Set (↥Y ⧸ GLAPPrimeCore p ↥Y))).comap (QuotientGroup.mk' (GLAPPrimeCore p ↥Y))).map Y.subtype with hCpre
  have hNC : ∀ i ∈ s, N i ≤ Cpre := by
    intro i hi x hx
    have hc := Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm i hi))
    refine ⟨⟨x, hNY i hi hx⟩, ?_, rfl⟩
    exact hc ⟨⟨x, hNY i hi hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  have hJC : J ≤ Cpre := hJle.trans (iSup₂_le hNC)
  have hab : barX p Y J ≤ Subgroup.centralizer ((barX p Y J : Subgroup _) : Set (↥Y ⧸ GLAPPrimeCore p ↥Y)) := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨j', hj', hjj⟩ := hJC (Subgroup.mem_subgroupOf.1 hj)
    have : j' = j := Subtype.ext hjj
    rw [← this]
    exact hj'
  obtain ⟨r, hr, t, ht, hrt⟩ := Input183.exists_noncomm_of_isComponentOf hJc
  exact hrt (Subgroup.mem_centralizer_iff.1 (hab ht) r hr)

theorem balanced_alt_of_dvd {m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm5 : 5 ≤ m) (hpm : p ∣ m) :
    IsLocallyOTwoBalancedWrtP p 1 ↥(alternatingGroup (Fin m)) := by
  by_cases hm6 : m = 6
  · subst hm6
    have hp3 : p = 3 := by
      have h6 : p ∣ 2 * 3 := hpm
      rcases (Nat.Prime.dvd_mul hp).1 h6 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
    subst hp3
    exact Inputs123a.balanced_alt6_three
  · refine Inputs123a.balanced_alt_of_not_mod hp hp2 hm5 hm6 ?_
    have h0 : m % p = 0 := Nat.mod_eq_zero_of_dvd hpm
    rintro (h | h)
    · omega
    · rw [h0] at h
      have h4 : p ∣ 4 := Nat.dvd_of_mod_eq_zero h.symm
      have h4' : p ∣ 2 ^ 2 := h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4'))

theorem center_eq_bot_of_alt {Y : Type*} [Group Y] {n : ℕ} (hn5 : 5 ≤ n) (e : Y ≃* alternatingGroup (Fin n)) :
    Subgroup.center Y = ⊥ := by
  have hc : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center (alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx y]
  rw [hc, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hx'
  exact Subgroup.mem_bot.2 hx'

theorem input27_4AltDvdComp_holds : Input27_4AltDvdComp := by
  intro p hp hp2 X _ _ hO K hK n hn5 hpn ⟨eK⟩ A hA a ha ha1 J hJ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨hKc, hOK⟩ := comp_facts hO hK
  have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_alt hn5 eK
  set Ks : Subgroup X := ⨆ g ∈ A, GLBConj g K with hKs
  set Y : Subgroup X := Ks ⊓ Subgroup.centralizer ({a} : Set X) with hY
  have hlayer : IsSubnormal (GLAPLayer p Y) Y :=
    CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp {L | GLAPComponent p Y L} fun _ h => h
  have hJY : GLAPComponent p Y J := l119_glaPComponent_of_isSubnormal hp hlayer hJ
  suffices hm : ∃ m : ℕ, 5 ≤ m ∧ p ∣ m ∧ IsAltType m (barOf p J ⧸ Subgroup.center (barOf p J)) by
    obtain ⟨m, hm5, hpm, ⟨f⟩⟩ := hm
    have hq : CFSG.Open.IsQuasisimple (barOf p J) :=
      CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJY
    exact Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hq.1
      ((Inputs123a.isLocallyOTwoBalancedWrtP_congr f).2 (balanced_alt_of_dvd hp hp2 hm5 hpm))
  have hconjtop : ∀ g : X, GLBConj g (⊤ : Subgroup X) = ⊤ := fun g =>
    Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  have hKg : ∀ g : X, GLAPComponent p ⊤ (GLBConj g K) := fun g => by
    have h1 := glaPComponent_gLBConj hK g
    rwa [hconjtop g] at h1
  by_cases haN : a ∈ Subgroup.normalizer (K : Set X)
  ·
    set S : Set (Subgroup X) := (fun g => GLBConj g K) '' (A : Set X) with hS
    have hSfin : S.Finite := (Set.toFinite _).image _
    set 𝓛 : Finset (Subgroup X) := hSfin.toFinset with h𝓛
    have hmem : ∀ L ∈ 𝓛, ∃ g ∈ A, GLBConj g K = L := fun L hL => by
      rw [h𝓛, Set.Finite.mem_toFinset] at hL
      exact hL
    have hKs' : Ks = sSup (↑𝓛 : Set (Subgroup X)) := by
      rw [h𝓛, Set.Finite.coe_toFinset, hS, sSup_image]
      rfl
    have hLc : ∀ L ∈ 𝓛, IsComponentOf L ⊤ := fun L hL => by
      obtain ⟨g, -, rfl⟩ := hmem L hL
      exact isComponentOf_gLBConj hKc g
    have hcomm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := by
      intro L hL L' hL' hne x hx y hy
      have h1 := CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' (hLc L hL) (hLc L' hL') hne
      exact (Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1 hx) y hy).symm
    have hZ : ∀ L ∈ 𝓛, L ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by
      intro L hL
      obtain ⟨g, -, rfl⟩ := hmem L hL
      rw [eq_bot_iff]
      rintro x ⟨hxL, hxC⟩
      have hx' : g * x * g⁻¹ ∈ K ⊓ Subgroup.centralizer (K : Set X) := by
        refine ⟨mem_gLBConj.1 hxL, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
        have hk' : g⁻¹ * k * g ∈ GLBConj g K := mem_gLBConj.2 (by group; exact hk)
        have h1 := Subgroup.mem_centralizer_iff.1 hxC _ hk'
        calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
          _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
          _ = g * x * g⁻¹ * k := by group
      rw [Inputs27.inf_centralizer_self_eq_bot hZK, Subgroup.mem_bot] at hx'
      have : x = 1 := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by rw [hx']; group
      rw [this]
      exact Subgroup.one_mem _
    have haL : ∀ L ∈ 𝓛, a ∈ Subgroup.normalizer (L : Set X) := by
      intro L hL
      obtain ⟨g, hg, rfl⟩ := hmem L hL
      have hga : g * a = a * g := Inputs27.elem_mul_comm hA hg ha
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [mem_gLBConj, mem_gLBConj]
      have e : g * (a * h * a⁻¹) * g⁻¹ = a * (g * h * g⁻¹) * a⁻¹ := by
        calc g * (a * h * a⁻¹) * g⁻¹ = (g * a) * h * (g * a)⁻¹ := by group
          _ = (a * g) * h * (a * g)⁻¹ := by rw [hga]
          _ = a * (g * h * g⁻¹) * a⁻¹ := by group
      rw [e]
      exact Subgroup.mem_normalizer_iff.1 haN _
    have hYle : Y ≤ ⨆ L ∈ 𝓛, L ⊓ Subgroup.centralizer ({a} : Set X) := by
      rw [hY, hKs']
      exact sSup_inf_centralizer_le 𝓛 hcomm hZ haL
    have hLKs : ∀ L ∈ 𝓛, L ≤ Ks := fun L hL => by
      obtain ⟨g, hg, rfl⟩ := hmem L hL
      exact le_iSup₂_of_le (f := fun g (_ : g ∈ A) => GLBConj g K) g hg le_rfl
    have hLY : ∀ L ∈ 𝓛, L ⊓ Subgroup.centralizer ({a} : Set X) ≤ Y := fun L hL =>
      inf_le_inf_right _ (hLKs L hL)
    have hKsN : ∀ L ∈ 𝓛, Ks ≤ Subgroup.normalizer (L : Set X) := by
      intro L hL
      rw [hKs']
      refine sSup_le fun L' hL' => ?_
      by_cases hLL : L' = L
      · rw [hLL]
        exact Subgroup.le_normalizer
      · intro y hy
        refine Subgroup.centralizer_le_normalizer (L : Set X) (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
        exact hcomm L hL L' hL' (Ne.symm hLL) x hx y hy
    have hYN : ∀ L ∈ 𝓛, Y ≤ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) := by
      intro L hL y hy
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hKsN L hL hy.1, Subgroup.le_normalizer hy.2⟩
    obtain ⟨L, hL𝓛, hJL⟩ := exists_le_of_le_iSup 𝓛 (fun L => L ⊓ Subgroup.centralizer ({a} : Set X)) hJY
      (hJY.1.trans hYle) hLY hYN
    have hJLc : GLAPComponent p (L ⊓ Subgroup.centralizer ({a} : Set X)) J :=
      glaPComponent_of_le hp hJY hJL (hLY L hL𝓛)
    obtain ⟨g, hg, hgL⟩ := hmem L hL𝓛
    have haL' : a ∈ Subgroup.normalizer (L : Set X) := haL L hL𝓛
    have hap : a ^ p = 1 := hA.2 a ha
    obtain ⟨Q, hQ, ⟨eQ⟩⟩ := Inputs123b.exists_component_image hp haL' hap hJLc
    have hLcomp : IsComponentOf L ⊤ := hLc L hL𝓛
    have hOL : GLAPPrimeCore p ↥L = ⊥ :=
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPPrimeCore_eq_bot_of_isSubnormal hO hLcomp.2.1
    have eLK : ↥L ≃* ↥K := by
      rw [← hgL]
      exact (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm
    have eL : barOf p L ≃* alternatingGroup (Fin n) := ((barOfEquivOfCore hOL).trans eLK).trans eK
    have hqL : CFSG.Open.IsQuasisimple (barOf p L) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv (barOfEquivOfCore hOL) hLcomp.2.2
    obtain ⟨f⟩ := Lemma1315b.isAltType_center_quot hn5 ⟨eL⟩
    have hOb : GLAPPrimeCore p (barOf p L) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
    have hZb : IsPGroup p ↥(Subgroup.center (barOf p L)) := AltFacts2.isPGroup_center_of_core_eq_bot hp hOb
    set α := CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L ⟨a, haL'⟩ with hα
    have hαp : α ^ p = 1 := by
      rw [hα, ← map_pow]
      have : (⟨a, haL'⟩ : ↥(Subgroup.normalizer (L : Set X))) ^ p = 1 := Subtype.ext (by simpa using hap)
      rw [this, map_one]
    have hAp : ∀ β ∈ Subgroup.zpowers α, β ^ p = 1 := by
      intro β hβ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hβ
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hαp, one_zpow]
    obtain ⟨τ, -, hτ⟩ := AltFacts5.exists_tau hpodd hn5 hqL.1 f hAp
    set α' : ↥(Subgroup.zpowers α) := ⟨α, Subgroup.mem_zpowers α⟩ with hα'
    have hτp : τ α' ^ p = 1 := by
      rw [← map_pow, show α' ^ p = 1 from Subtype.ext (by simpa using hαp), map_one]
    obtain ⟨h5', ⟨eA⟩⟩ := AltFacts5.component_alt hp hp2 (AltFacts5.isAltRep_of_equiv f) hZb (hτ α') hτp hQ
    refine ⟨_, h5', ?_, Inputs123b.isAltType_center_congr eQ ⟨eA⟩⟩
    have hmod := Equiv.Perm.card_compl_support_modEq (p := p) (n := 1) (σ := τ α')
      (by rw [pow_one]; exact hτp)
    rw [Fintype.card_fin] at hmod
    exact Nat.modEq_zero_iff_dvd.1 (hmod.trans (Nat.modEq_zero_iff_dvd.2 hpn))
  ·
    have hKsub : IsSubnormal Ks ⊤ := by
      have h1 := CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp
        ((fun g => GLBConj g K) '' (A : Set X)) (by rintro _ ⟨g, -, rfl⟩; exact hKg g)
      rwa [sSup_image] at h1
    have hYsn : IsSubnormal Y ((⊤ : Subgroup X) ⊓ Subgroup.centralizer ({a} : Set X)) :=
      isSubnormal_inf hKsub _
    have hJ' : GLAPComponent p ((⊤ : Subgroup X) ⊓ Subgroup.centralizer ({a} : Set X)) J :=
      l119_glaPComponent_of_isSubnormal hp hYsn hJY
    have hle : barX p ⊤ J ≤ barX p ⊤ (⨆ y ∈ A, GLBConj y K) := barX_mono (hJY.1.trans inf_le_left)
    obtain ⟨π, hπs, hπk, -⟩ := Inputs183eqv.input18_3_eqv_holds X p hp hp2 ⊤ K A hK hA le_top a ha ha1
      (Subgroup.mem_top a) (Or.inl haN) J hJ' hle
    have eB : barOf p K ≃* alternatingGroup (Fin n) := (barOfEquivOfCore hOK).trans eK
    have hZB : Subgroup.center (barOf p K) = ⊥ := center_eq_bot_of_alt hn5 eB
    have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 (le_bot_iff.1 (hZB ▸ hπk))
    exact ⟨n, hn5, hpn, Lemma1315b.isAltType_center_quot hn5
      ⟨(MulEquiv.ofBijective π ⟨hinj, hπs⟩).symm.trans eB⟩⟩

theorem input27_4Alt_holds : Input27_4Alt :=
  input27_4Alt_of_dvdComp input27_4AltDvdComp_holds

end AltComp


section L227Facts

open CFSG.GorensteinWalter (PSL2 PGL2)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction pglAction_toPGL)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns (fixSub mem_fixSub)
open CFSG.Open (StatedProj StatedSL)

theorem mem_innerAut_of_pglAction_pow_three {F : Type} [Field F] [Finite F] (g : PGL2 F)
    (h3 : (pglAction F g) ^ 3 = 1) : pglAction F g ∈ innerAut (PSL2 F) := by
  have hg3 : g ^ 3 = 1 :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_injective F (by rw [map_pow, h3, map_one])
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have hmem : Matrix.ProjGenLinGroup.mk A ∈
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rw [CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare]
    have h1 : Matrix.ProjGenLinGroup.mk (A ^ 3) = 1 := by rw [map_pow]; exact hg3
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨c, hc⟩ := h1
    have hdet : ((A.det : Fˣ) : F) ^ 3 = (c : F) ^ 2 := by
      have h2 := congrArg (fun M : GL (Fin 2) F => ((Matrix.GeneralLinearGroup.det M : Fˣ) : F)) hc
      simp only [map_pow, Units.val_pow_eq_pow_val] at h2
      rw [← h2]
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_smul]
    refine ⟨(c : F) * ((A.det : Fˣ) : F)⁻¹, ?_⟩
    have hne : ((A.det : Fˣ) : F) ≠ 0 := Units.ne_zero _
    field_simp
    linear_combination hdet
  obtain ⟨u, hu⟩ := hmem
  rw [← hu, pglAction_toPGL]
  exact ⟨u, rfl⟩

theorem card_fixSub_of_outer {S : Type} [Group S] [Finite S] (e : S ≃* PSL(2, GaloisField 3 3))
    {x : MulAut S} (hx3 : orderOf x = 3) (hxI : x ∉ innerAut S) : Nat.card (fixSub x) = 12 := by
  set F := GaloisField 3 3 with hF
  set e₀ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F with he₀
  set e₁ : S ≃* StatedProj (StatedSL 2 F) := e.trans e₀ with he₁
  set β : MulAut (StatedProj (StatedSL 2 F)) := MulAut.congr e₁ x with hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hx3', map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hx1
    apply (MulAut.congr e₁).injective
    rw [map_one]
    exact h
  have hβ' : MulAut.congr e₀.symm β = MulAut.congr e x := by
    ext y
    simp [hβ, he₁, MulAut.congr_apply]
  have hD : MulAut.congr e₀.symm β ∉ (pglAction F).range := by
    rintro ⟨g, hg⟩
    apply hxI
    have h3 : (pglAction F g) ^ 3 = 1 := by rw [hg, ← map_pow, hβ3, map_one]
    have hinn := mem_innerAut_of_pglAction_pow_three g h3
    rw [hg, hβ'] at hinn
    exact Inputs196.mem_innerAut_of_congr e hinn
  obtain ⟨σ, φ, γ, hφ, hβγ⟩ := Inputs196.fieldType_of_not_mem_pglAction β hβ3 hβ1 hD
  obtain ⟨F₀, _, _, hcard, ⟨ψ⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds F β hβ3 hβ1 σ φ γ hφ hβγ
  have h27 : Nat.card F = 27 := by
    rw [hF, GaloisField.card 3 3 (by norm_num)]
    norm_num
  have h3 : Nat.card F₀ = 3 := by
    have h' : Nat.card F₀ ^ 3 = 3 ^ 3 := by rw [← hcard, h27]; norm_num
    exact Nat.pow_left_injective (by norm_num) h'
  have hmap : (fixSub x).map (e₁ : S →* StatedProj (StatedSL 2 F)) = fixSub β := by
    ext y
    rw [mem_fixSub]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : x s = s := hs
      simp [hβ, MulAut.congr_apply, hs']
    · intro hy
      refine ⟨e₁.symm y, ?_, by simp⟩
      show x (e₁.symm y) = e₁.symm y
      have hy' : e₁ (x (e₁.symm y)) = y := by simpa [hβ, MulAut.congr_apply] using hy
      simpa using congrArg e₁.symm hy'
  have hodd : Odd (Nat.card F₀) := by rw [h3]; decide
  calc Nat.card (fixSub x) = Nat.card (fixSub β) := by
        rw [← hmap, Subgroup.card_map_of_injective e₁.injective]
    _ = Nat.card (StatedProj (StatedSL 2 F₀)) := Nat.card_congr ψ.toEquiv
    _ = 12 := by rw [CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd hodd, h3]; norm_num

theorem card_L227_and_aut {S : Type} [Group S] (e : S ≃* PSL(2, GaloisField 3 3)) :
    Nat.card S = 9828 ∧ Nat.card (MulAut S) = 58968 := by
  have h27 : Nat.card (GaloisField 3 3) = 27 := by
    rw [GaloisField.card 3 3 (by norm_num)]
    norm_num
  have hodd : Odd (Nat.card (GaloisField 3 3)) := by rw [h27]; decide
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 3 3))).toEquiv, CFSG.Open.StatedAPI.card_statedProj_statedSL_two_of_odd hodd, h27]
    norm_num
  · rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact (CFSG.AGLEmbedding.card_mulAut_psl2GF 3 3 (by norm_num)).trans (by norm_num)

theorem card_le_nine_of_not_le_inner {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (e : S ≃* PSL(2, GaloisField 3 3)) {D : Subgroup (MulAut S)}
    (hD : IsElemAbelian 3 D) (hDI : ¬ D ≤ innerAut S) : Nat.card D ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφD, hφI⟩ := Set.not_subset.1 hDI
  have hφ1 : φ ≠ 1 := fun h => hφI (h ▸ (innerAut S).one_mem)
  have hφ3 : orderOf φ = 3 := orderOf_eq_prime (hD.2 φ hφD) hφ1
  have hZ : Subgroup.center S = ⊥ := CFSG.HardMathSupport.Timmesfeld.DefChar.center_eq_bot_of_simple hS hnab
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.conj_injective_of_center_eq_bot hZ
  obtain ⟨hcS, hcA⟩ := card_L227_and_aut e
  set T : Subgroup S := (D ⊓ innerAut S).comap (MulAut.conj : S →* MulAut S) with hT
  have hTfix : T ≤ fixSub φ := by
    intro s hs
    have hsD : MulAut.conj s ∈ D := hs.1
    have hc : φ * MulAut.conj s = MulAut.conj s * φ := Inputs27.elem_mul_comm hD hφD hsD
    have h1 : MulAut.conj (φ s) = MulAut.conj s := by
      have h2 : MulAut.conj (φ s) = φ * MulAut.conj s * φ⁻¹ := by
        ext y
        simp [MulAut.conj_apply]
      rw [h2, hc, mul_inv_cancel_right]
    exact hconj h1
  have hTmap : T.map (MulAut.conj : S →* MulAut S) = D ⊓ innerAut S :=
    Subgroup.map_comap_eq_self (inf_le_right : D ⊓ innerAut S ≤ (MulAut.conj : S →* MulAut S).range)
  have hTcard : Nat.card T = Nat.card (D ⊓ innerAut S : Subgroup (MulAut S)) := by
    rw [← hTmap, Subgroup.card_map_of_injective hconj]
  have hDp : ∃ m : ℕ, Nat.card D = 3 ^ m := (IsPGroup.iff_card).1 (CFSG.Open.IsElemAbelian.isPGroup hD)
  obtain ⟨m, hm⟩ := hDp
  have h1 : Nat.card (D ⊓ innerAut S : Subgroup (MulAut S)) ≤ 3 := by
    have hd12 : Nat.card T ∣ 12 := by
      rw [← card_fixSub_of_outer e hφ3 hφI]
      exact Subgroup.card_dvd_of_le hTfix
    have hdD : Nat.card (D ⊓ innerAut S : Subgroup (MulAut S)) ∣ 3 ^ m :=
      hm ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdD
    rw [hTcard, hi] at hd12
    rw [hi]
    rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h2
    · norm_num
    · norm_num
    · exfalso
      have : 3 ^ 2 ∣ 12 := (Nat.pow_dvd_pow 3 h2).trans hd12
      norm_num at this
  have h2 : (innerAut S).relIndex D ≤ 3 := by
    haveI : (innerAut S).Normal := Inputs27.innerAut_normal_local S
    have hidx : (innerAut S).index = 6 := by
      have h0 := Subgroup.card_mul_index (innerAut S)
      have hinn : Nat.card (innerAut S) = 9828 := by
        rw [← hcS]
        exact (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
      rw [hinn, hcA] at h0
      omega
    have hd6 : (innerAut S).relIndex D ∣ 6 := hidx ▸ Subgroup.relIndex_dvd_index_of_normal (innerAut S) D
    have hdD : (innerAut S).relIndex D ∣ 3 ^ m := hm ▸ Subgroup.relIndex_dvd_card _ _
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdD
    rw [hi] at hd6 ⊢
    rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h2
    · norm_num
    · norm_num
    · exfalso
      have : 3 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 3 h2).trans hd6
      norm_num at this
  have h3 := Subgroup.relIndex_mul_card (H := innerAut S) (K := D)
  rw [inf_comm] at h3
  rw [← h3]
  calc (innerAut S).relIndex D * Nat.card (D ⊓ innerAut S : Subgroup (MulAut S)) ≤ 3 * 3 :=
        Nat.mul_le_mul h2 h1
    _ = 9 := by norm_num

end L227Facts

section L227

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem card_le_card_autBar_mul {K B : Subgroup X} (hOK : GLAPPrimeCore p ↥K = ⊥)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    Nat.card B ≤ Nat.card (autBar p B K) * Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) := by
  set N : Subgroup X := Subgroup.normalizer (K : Set X) with hNdef
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  set f : ↥B' →* MulAut (barOf p K) := (barAut p K).comp B'.subtype with hf
  have hrange : f.range = autBar p B K := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    show B'.map (barAut p K) = ((B ⊓ N).subgroupOf N).map (barAut p K)
    rw [inf_eq_left.2 hBN]
  have h1 : Nat.card f.ker * f.ker.index = Nat.card B' := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange] at h1
  have hB'card : Nat.card B' = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  set g : ↥f.ker →* X := N.subtype.comp (B'.subtype.comp f.ker.subtype) with hg
  have hginj : Function.Injective g :=
    N.subtype_injective.comp (B'.subtype_injective.comp f.ker.subtype_injective)
  have hbot : GLAPPrimeCoreOf p K = ⊥ := by
    show (GLAPPrimeCore p ↥K).map K.subtype = ⊥
    rw [hOK, Subgroup.map_bot]
  have hgle : g.range ≤ B ⊓ Subgroup.centralizer (K : Set X) := by
    rintro _ ⟨y, rfl⟩
    have hyB : ((y : ↥B') : ↥N) ∈ B' := (y : ↥B').2
    have hy1 : barAut p K ((y : ↥B') : ↥N) = 1 := (MonoidHom.mem_ker).1 y.2
    refine ⟨Subgroup.mem_subgroupOf.1 hyB, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    have h := Lemma1315b.mem_primeCoreOf_of_barAut_eq_one _ hy1 hx
    rw [hbot, Subgroup.mem_bot] at h
    have h2 : (((y : ↥B') : ↥N) : X) * x * (((y : ↥B') : ↥N) : X)⁻¹ = x := (inv_mul_eq_one.1 h).symm
    show x * (((y : ↥B') : ↥N) : X) = (((y : ↥B') : ↥N) : X) * x
    calc x * (((y : ↥B') : ↥N) : X)
        = (((y : ↥B') : ↥N) : X) * x * (((y : ↥B') : ↥N) : X)⁻¹ * (((y : ↥B') : ↥N) : X) := by rw [h2]
      _ = (((y : ↥B') : ↥N) : X) * x := by group
  calc Nat.card B = Nat.card B' := hB'card.symm
    _ = Nat.card f.ker * Nat.card (autBar p B K) := h1.symm
    _ ≤ Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) * Nat.card (autBar p B K) := by
        refine Nat.mul_le_mul_right _ ?_
        calc Nat.card f.ker = Nat.card g.range := Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
          _ ≤ _ := Subgroup.card_le_of_le hgle
    _ = _ := mul_comm _ _

theorem exists_inner_of_barAut_mem {K : Subgroup X} (hOK : GLAPPrimeCore p ↥K = ⊥)
    (γ : ↥(Subgroup.normalizer (K : Set X))) (hγ : barAut p K γ ∈ innerAut (barOf p K)) :
    ∃ k ∈ K, ∀ x ∈ K, (γ : X) * x * (γ : X)⁻¹ = k * x * k⁻¹ := by
  obtain ⟨kb, hkb⟩ := hγ
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
  refine ⟨k, k.2, fun x hx => ?_⟩
  have h := congrArg (fun f : MulAut (barOf p K) => f (QuotientGroup.mk ⟨x, hx⟩)) hkb
  simp only [MulAut.conj_apply] at h
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, QuotientGroup.eq, hOK, Subgroup.mem_bot, inv_mul_eq_one] at h
  have h2 : ((k * ⟨x, hx⟩ * k⁻¹ : ↥K) : X) = ((K.normalizerMonoidHom γ ⟨x, hx⟩ : ↥K) : X) :=
    congrArg Subtype.val h
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  exact h2.symm

theorem isElemAbelian_autBar {B : Subgroup X} (hB : IsElemAbelian p B) (K : Subgroup X) :
    IsElemAbelian p (autBar p B K) :=
  CFSG.SectionRank.isElemAbelian_map (Inputs27.isElemAbelian_subgroupOf
    (CFSG.Open.IsElemAbelian.mono hB inf_le_left) _) _

theorem center_eq_bot_of_l227 (hC3 : CFSG.HardMathSupport.Solomon.Coordinator.L2CentreThree) {Y : Type} [Group Y]
    [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore 3 Y = ⊥)
    (hL : IsLTwoTwentySeven (Y ⧸ Subgroup.center Y)) : Subgroup.center Y = ⊥ := by
  obtain ⟨eL⟩ := hL
  by_contra hZ
  have h9 := hC3 Y hq (isPGroup_center_of_core Nat.prime_three hO) hZ (GaloisField 3 3)
    ⟨eL.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 3 3))⟩
  rw [GaloisField.card 3 3 (by norm_num)] at h9
  norm_num at h9

theorem isLTwoTwentySeven_of_l227 (hC3 : CFSG.HardMathSupport.Solomon.Coordinator.L2CentreThree) {Y : Type}
    [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore 3 Y = ⊥)
    (hL : IsLTwoTwentySeven (Y ⧸ Subgroup.center Y)) : IsLTwoTwentySeven Y :=
  ⟨(equivCenterQuotOfBot (center_eq_bot_of_l227 hC3 hq hO hL)).trans hL.some⟩

theorem l227_cases (hC3 : CFSG.HardMathSupport.Solomon.Coordinator.L2CentreThree) (hO : GLAPPrimeCore 3 X = ⊥)
    {K : Subgroup X} (hK : GLAPComponent 3 ⊤ K) (hq : CFSG.Open.IsQuasisimple ↥K)
    (hL : IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K)) {E A : Subgroup X} (hE : IsSCp 3 ⊤ E)
    (hA' : IsSCp 3 ⊤ A) (hEA : E ≠ A) (hEAp : IsPGroup 3 ↥(E ⊔ A)) (hr : 2 ≤ CFSG.Open.pRank 3 (E ⊓ A))
    (hN : E ≤ Subgroup.normalizer (K : Set X))
    (hC1 : CFSG.Open.pRank 3 (E ⊓ Subgroup.centralizer (K : Set X)) = 1) :
    CFSG.Open.pRank 3 E = 3 ∨ (Nat.card E = 3 ^ 4 ∧ A ≤ Subgroup.normalizer (K : Set X) ∧
      (¬ autBar 3 A K ≤ innerAut (barOf 3 K) → Nat.card A = 3 ^ 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp := Nat.prime_three
  obtain ⟨hKc, hOK⟩ := comp_facts hO hK
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hnab := Prop1116Design.not_isCommutative_barQuot ↥K hq
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_l227 hC3 hq hOK hL
  obtain ⟨eL⟩ := hL
  set ψ : barOf 3 K ≃* ↥K ⧸ Subgroup.center ↥K := (barOfEquivOfCore hOK).trans (equivCenterQuotOfBot hZ)
    with hψ
  set eK : ↥K ≃* PSL(2, GaloisField 3 3) := (equivCenterQuotOfBot hZ).trans eL with heK
  set eB : barOf 3 K ≃* PSL(2, GaloisField 3 3) := ψ.trans eL with heB
  have hSB : IsSimpleGroup (barOf 3 K) := ψ.isSimpleGroup
  have hnabB : ∃ a b : barOf 3 K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨ψ.symm a, ψ.symm b, fun h => hab ?_⟩
    simpa using congrArg ψ h
  have hcardK : Nat.card ↥K = 9828 := (card_L227_and_aut eK).1
  have hA3 : 3 ≤ CFSG.Open.pRank 3 A :=
    Inputs27.three_le_pRank_of_scp hp hA' hE hEA.symm (by rw [inf_comm]; exact hr)
  have hm := Inputs27.card_eq_pow_pRank hp hE.2.1
  set C := E ⊓ Subgroup.centralizer (K : Set X) with hCdef
  have hCel : IsElemAbelian 3 C := CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
  have hCc : Nat.card C = 3 := by rw [Inputs27.card_eq_pow_pRank hp hCel, hC1, pow_one]
  by_cases hEin : autBar 3 E K ≤ innerAut (barOf 3 K)
  ·
    have hinner : ∀ e ∈ E, ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹ := fun e he =>
      exists_inner_of_barAut_mem hOK ⟨e, hN he⟩
        (hEin ⟨⟨e, hN he⟩, Subgroup.mem_subgroupOf.2 ⟨he, hN he⟩, rfl⟩)
    have hKC := Inputs27.inf_centralizer_self_eq_bot hZ
    have hEsplit := Inputs27.eq_inf_sup_inf_of_inner hE hN hKC hinner
    have hEKel : IsElemAbelian 3 (E ⊓ K) := CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
    have hcommEKC : ∀ x ∈ E ⊓ K, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x (Subgroup.mem_inf.1 hx).2
    have hd : (E ⊓ K) ⊓ C = ⊥ := le_bot_iff.1 (hKC ▸
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
    have hcardE : Nat.card E = Nat.card (E ⊓ K : Subgroup X) * 3 := by
      have h1 := GL83.CompFam.card_sup_of_commute_of_inf_eq_bot hcommEKC hd
      rw [← hEsplit, hCc] at h1
      exact h1
    have hEK27 : Nat.card (E ⊓ K : Subgroup X) ≤ 27 := by
      obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 (CFSG.Open.IsElemAbelian.isPGroup hEKel)
      have hdvd : Nat.card (E ⊓ K : Subgroup X) ∣ 9828 := by
        rw [← hcardK]
        exact Subgroup.card_dvd_of_le inf_le_right
      rw [hj] at hdvd ⊢
      have hj3 : j ≤ 3 := by
        by_contra hj4
        have : 3 ^ 4 ∣ 9828 := (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
        norm_num at this
      calc 3 ^ j ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
        _ = 27 := by norm_num
    have hm4 : CFSG.Open.pRank 3 E ≤ 4 := by
      by_contra h5
      have h243 : 3 ^ 5 ≤ 3 ^ CFSG.Open.pRank 3 E := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← hm, hcardE] at h243
      omega
    have hE3 : 3 ≤ CFSG.Open.pRank 3 E := Inputs27.three_le_pRank_of_scp hp hE hA' hEA hr
    rcases (by omega : CFSG.Open.pRank 3 E = 3 ∨ CFSG.Open.pRank 3 E = 4) with hm3 | hm4'
    · exact Or.inl hm3
    · have hE81 : Nat.card E = 3 ^ 4 := by rw [hm, hm4']
      have hEK : Nat.card (E ⊓ K : Subgroup X) = 27 := by
        rw [hE81] at hcardE
        omega
      set Q := Subgroup.centralizer (K : Set X) ⊓ (E ⊔ A) with hQdef
      have hQp : IsPGroup 3 ↥Q := hEAp.to_le inf_le_right
      have hCQ : C ≤ Q := le_inf inf_le_right (inf_le_left.trans le_sup_left)
      have hmax : ∀ F : Subgroup X, F ≤ Q → IsElemAbelian 3 F → C ≤ F → F = C := by
        intro F hFQ hFel hCF
        have hFC : F ≤ Subgroup.centralizer (K : Set X) := hFQ.trans inf_le_left
        have hel : IsElemAbelian 3 ((E ⊓ K) ⊔ F) := Inputs27.isElemAbelian_sup_of_commute hEKel hFel
          fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hFC hy) x (Subgroup.mem_inf.1 hx).2
        have hle : E ≤ (E ⊓ K) ⊔ F := hEsplit.le.trans (sup_le_sup_left hCF _)
        have heq := hE.2.2 _ le_top hel hle
        refine le_antisymm (fun x hx => ?_) hCF
        have hxE : x ∈ E := heq ▸ (Subgroup.mem_sup_right hx)
        exact ⟨hxE, hFC hx⟩
      have hQ1 := Inputs27.mem_of_pow_eq_one_of_maximal hQp hCQ hCc hCel hmax
      have hAN : A ≤ Subgroup.normalizer (K : Set X) := by
        intro a ha
        by_contra hna
        have hKa : GL83.CompFam.cj a K ≠ K := fun h => hna (GL83.CompFam.cj_eq_iff_mem_normalizer.1 h)
        have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
          (GL83.CompFam.isComponentOf_cj hKc a) hKc hKa
        have hKaC : GL83.CompFam.cj a K ≤ Subgroup.centralizer (K : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
        have hmap : (E ⊓ K).map (MulAut.conj a).toMonoidHom ≤ C := by
          rintro _ ⟨y, hy, rfl⟩
          have hyE := (Subgroup.mem_inf.1 hy).1
          have hyK := (Subgroup.mem_inf.1 hy).2
          refine hQ1 _ ⟨hKaC (GL83.CompFam.mul_mem_cj hyK), ?_⟩ ?_
          · exact (E ⊔ A).mul_mem ((E ⊔ A).mul_mem (Subgroup.mem_sup_right ha)
              (Subgroup.mem_sup_left hyE)) ((E ⊔ A).inv_mem (Subgroup.mem_sup_right ha))
          · show ((MulAut.conj a) y) ^ 3 = 1
            rw [← map_pow, hEKel.2 y hy, map_one]
        have hcard := Subgroup.card_le_of_le hmap
        rw [Subgroup.card_map_of_injective (MulAut.conj a).injective, hEK, hCc] at hcard
        omega
      refine Or.inr ⟨hE81, hAN, fun hAout => ?_⟩
      have hACC : A ⊓ Subgroup.centralizer (K : Set X) ≤ C := fun x hx =>
        hQ1 x ⟨(Subgroup.mem_inf.1 hx).2, Subgroup.mem_sup_right (Subgroup.mem_inf.1 hx).1⟩
          (hA'.2.1.2 x (Subgroup.mem_inf.1 hx).1)
      have hA9 := card_le_nine_of_not_le_inner hSB hnabB eB (isElemAbelian_autBar hA'.2.1 K) hAout
      have hAle := card_le_card_autBar_mul hOK hAN
      have hAC3 : Nat.card (A ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) ≤ 3 :=
        hCc ▸ Subgroup.card_le_of_le hACC
      have h1 : Nat.card A ≤ 27 := hAle.trans (by
        calc Nat.card (autBar 3 A K) * Nat.card (A ⊓ Subgroup.centralizer (K : Set X) : Subgroup X)
            ≤ 9 * 3 := Nat.mul_le_mul hA9 hAC3
          _ = 27 := by norm_num)
      have h2 : 3 ^ 3 ≤ Nat.card A := by
        rw [Inputs27.card_eq_pow_pRank hp hA'.2.1]
        exact Nat.pow_le_pow_right (by norm_num) hA3
      norm_num at h2 ⊢
      omega
  ·
    have hE3 : 3 ≤ CFSG.Open.pRank 3 E := Inputs27.three_le_pRank_of_scp hp hE hA' hEA hr
    have h9 := card_le_nine_of_not_le_inner hSB hnabB eB (isElemAbelian_autBar hE.2.1 K) hEin
    have hle := card_le_card_autBar_mul hOK hN
    rw [hCc] at hle
    refine Or.inl ?_
    by_contra hm3
    have h81 : 3 ^ 4 ≤ 3 ^ CFSG.Open.pRank 3 E := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hm] at h81
    omega

theorem input27_3L227_of (hC3 : CFSG.HardMathSupport.Solomon.Coordinator.L2CentreThree) : Input27_3L227 := by
  intro X _ _ _ hO K hK hKh hL E A hAout hE hA' hEA hEAp hr _ _ hN hC1 _ _
  obtain ⟨-, hOK⟩ := comp_facts hO hK
  rcases l227_cases hC3 hO hK hKh.1 hL hE hA' hEA hEAp hr.ge hN hC1 with h3 | ⟨h81, -, hA27⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h3⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, h81, hA27 hAout, isLTwoTwentySeven_of_l227 hC3 hKh.1 hOK hL⟩)))))

end L227

section ChevP4

open CFSG.Yardstones.Md0ec50421ce4 (PSimple)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem exists_pow_mem_iSup_inf_centralizer {a : X} {e : ℕ} (𝓛 : Finset (Subgroup X))
    (hcomm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x)
    (hZ : ∀ L ∈ 𝓛, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set X), z ^ e = 1)
    (haN : ∀ L ∈ 𝓛, a ∈ Subgroup.normalizer (L : Set X)) :
    ∀ y ∈ sSup (↑𝓛 : Set (Subgroup X)) ⊓ Subgroup.centralizer ({a} : Set X),
      ∃ m : ℕ, y ^ (e ^ m) ∈ ⨆ L ∈ 𝓛, L ⊓ Subgroup.centralizer ({a} : Set X) := by
  classical
  induction 𝓛 using Finset.induction_on with
  | empty =>
    intro y hy
    have hy1 : y = 1 := by
      have h := (Subgroup.mem_inf.1 hy).1
      rwa [Finset.coe_empty, sSup_empty, Subgroup.mem_bot] at h
    exact ⟨0, by rw [hy1, one_pow]; exact Subgroup.one_mem _⟩
  | insert L s hLs ih =>
    intro y hy
    have hL : L ∈ insert L s := Finset.mem_insert_self L s
    have hs : ∀ L' ∈ s, L' ∈ insert L s := fun L' h => Finset.mem_insert_of_mem h
    have ih' := ih (fun L1 h1 L2 h2 => hcomm L1 (hs L1 h1) L2 (hs L2 h2)) (fun L' h => hZ L' (hs L' h))
      (fun L' h => haN L' (hs L' h))
    obtain ⟨hyS, hya⟩ := hy
    rw [Finset.coe_insert, sSup_insert] at hyS
    set S : Subgroup X := sSup (↑s : Set (Subgroup X)) with hSdef
    have hsC : S ≤ Subgroup.centralizer (L : Set X) := by
      refine sSup_le fun L' hL' => fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      have hne : L ≠ L' := fun h => hLs (h ▸ hL')
      exact hcomm L hL L' (hs L' hL') hne x hx y hy
    have hc : ∀ x ∈ L, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.1 (hsC hy) x hx
    have haS : a ∈ Subgroup.normalizer (S : Set X) := by
      have h1 : Subgroup.zpowers a ≤ Subgroup.normalizer
          ((⨆ L' : ↥(↑s : Set (Subgroup X)), (L' : Subgroup X) : Subgroup X) : Set X) :=
        Inputs27.le_normalizer_iSup' _ fun L' => Subgroup.zpowers_le.2 (haN L' (hs L' L'.2))
      rw [hSdef, sSup_eq_iSup']
      exact h1 (Subgroup.mem_zpowers a)
    obtain ⟨u, hu, v, hv, rfl⟩ := (GL83.CompFam.mem_sup_of_commute hc).1 hyS
    have hya' : (u * v) * a = a * (u * v) := Subgroup.mem_centralizer_singleton_iff.1 hya
    have hu' : a * u * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (haN L hL) u).1 hu
    have hv' : a * v * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 haS v).1 hv
    have heq : (a * u * a⁻¹) * (a * v * a⁻¹) = u * v := by
      calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
        _ = (u * v) * a * a⁻¹ := by rw [hya']
        _ = u * v := by group
    set c : X := u⁻¹ * (a * u * a⁻¹) with hcdef
    have hcv : c = v * (a * v * a⁻¹)⁻¹ := by
      calc c = u⁻¹ * ((a * u * a⁻¹) * (a * v * a⁻¹)) * (a * v * a⁻¹)⁻¹ := by rw [hcdef]; group
        _ = u⁻¹ * (u * v) * (a * v * a⁻¹)⁻¹ := by rw [heq]
        _ = v * (a * v * a⁻¹)⁻¹ := by group
    have hcL : c ∈ L := L.mul_mem (L.inv_mem hu) hu'
    have hcS : c ∈ S := by rw [hcv]; exact S.mul_mem hv (S.inv_mem hv')
    have hcC : c ∈ Subgroup.centralizer (L : Set X) := hsC hcS
    have hce : c ^ e = 1 := hZ L hL c ⟨hcL, hcC⟩
    have hcu : Commute u c := Subgroup.mem_centralizer_iff.1 hcC u hu
    have hcv' : Commute c v := hc c hcL v hv
    have hau : a * u * a⁻¹ = u * c := by rw [hcdef]; group
    have hav : a * v * a⁻¹ = c⁻¹ * v := by rw [hcv]; group
    have hue : u ^ e ∈ L ⊓ Subgroup.centralizer ({a} : Set X) := by
      refine ⟨L.pow_mem hu e, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : a * u ^ e * a⁻¹ = u ^ e := by rw [← conj_pow, hau, hcu.mul_pow, hce, mul_one]
      calc u ^ e * a = a * u ^ e * a⁻¹ * a := by rw [h1]
        _ = a * u ^ e := by group
    have hve : v ^ e ∈ S ⊓ Subgroup.centralizer ({a} : Set X) := by
      refine ⟨S.pow_mem hv e, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : a * v ^ e * a⁻¹ = v ^ e := by
        rw [← conj_pow, hav, (Commute.inv_left hcv').mul_pow, inv_pow, hce, inv_one, one_mul]
      calc v ^ e * a = a * v ^ e * a⁻¹ * a := by rw [h1]
        _ = a * v ^ e := by group
    obtain ⟨m, hm⟩ := ih' (v ^ e) hve
    refine ⟨m + 1, ?_⟩
    have huv : Commute u v := hc u hu v hv
    have hpow : (u * v) ^ (e ^ (m + 1)) = (u ^ e) ^ (e ^ m) * (v ^ e) ^ (e ^ m) := by
      rw [huv.mul_pow, pow_succ', pow_mul, pow_mul]
    rw [hpow, Finset.iSup_insert]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ hue _) hm

theorem le_of_perfect_of_pow_mem (hp : p.Prime) {J N : Subgroup X} (hJ : ⁅J, J⁆ = J)
    (hJN : J ≤ Subgroup.normalizer (N : Set X)) (hpow : ∀ j ∈ J, ∃ m : ℕ, j ^ (p ^ m) ∈ N) : J ≤ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N' : Subgroup ↥J := N.subgroupOf J with hN'
  haveI : N'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hJN g.2) n).1 hn
  have hQp : IsPGroup p (↥J ⧸ N') := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm⟩ := hpow j j.2
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
    simpa using hm
  have htopJ : commutator ↥J = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_subtype_commutator, hJ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hs := QuotientGroup.mk'_surjective N'
  have htopQ : commutator (↥J ⧸ N') = ⊤ := by
    have h1 : (commutator ↥J).map (QuotientGroup.mk' N') = commutator (↥J ⧸ N') := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hs]
    rw [← h1, htopJ, Subgroup.map_top_of_surjective _ hs]
  haveI : Group.IsNilpotent (↥J ⧸ N') := hQp.isNilpotent
  have hder : ∀ n, derivedSeries (↥J ⧸ N') n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, htopQ]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := ↥J ⧸ N')
  rw [hder] at hn
  intro j hj
  have hq : (QuotientGroup.mk (⟨j, hj⟩ : ↥J) : ↥J ⧸ N') ∈ (⊥ : Subgroup (↥J ⧸ N')) :=
    hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf] at hq
  exact hq

theorem glaPComponent_conj {K : Subgroup X} (hK : GLAPComponent p ⊤ K) (g : X) :
    GLAPComponent p ⊤ (GLBConj g K) := by
  have h1 := glaPComponent_gLBConj hK g
  rwa [show GLBConj g (⊤ : Subgroup X) = ⊤ from Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)] at h1

theorem nonempty_conj_center_quot (K : Subgroup X) (g : X) :
    Nonempty ((↥(GLBConj g K) ⧸ Subgroup.center ↥(GLBConj g K)) ≃* ↥K ⧸ Subgroup.center ↥K) :=
  ⟨Lemma1315b.centerQuotEquiv
    (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm⟩

theorem exists_conj_of_mem_normalizer (hp : p.Prime) (hO : GLAPPrimeCore p X = ⊥) {K : Subgroup X}
    (hK : GLAPComponent p ⊤ K) {A : Subgroup X} (hA : IsElemAbelian p A) {a : X} (ha : a ∈ A)
    (haN : a ∈ Subgroup.normalizer (K : Set X)) {J : Subgroup X}
    (hJ : GLAPComponent p (GLAPLayer p ((⨆ g ∈ A, GLBConj g K) ⊓ Subgroup.centralizer ({a} : Set X))) J) :
    ∃ g ∈ A, a ∈ Subgroup.normalizer ((GLBConj g K : Subgroup X) : Set X) ∧
      GLAPComponent p (GLBConj g K ⊓ Subgroup.centralizer ({a} : Set X)) J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, hOK⟩ := comp_facts hO hK
  set Ks : Subgroup X := ⨆ g ∈ A, GLBConj g K with hKs
  set Y : Subgroup X := Ks ⊓ Subgroup.centralizer ({a} : Set X) with hY
  have hlayer : IsSubnormal (GLAPLayer p Y) Y :=
    CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp {L | GLAPComponent p Y L} fun _ h => h
  have hJY : GLAPComponent p Y J := l119_glaPComponent_of_isSubnormal hp hlayer hJ
  set S : Set (Subgroup X) := (fun g => GLBConj g K) '' (A : Set X) with hS
  have hSfin : S.Finite := (Set.toFinite _).image _
  set 𝓛 : Finset (Subgroup X) := hSfin.toFinset with h𝓛
  have hmem : ∀ L ∈ 𝓛, ∃ g ∈ A, GLBConj g K = L := fun L hL => by
    rw [h𝓛, Set.Finite.mem_toFinset] at hL
    exact hL
  have hKs' : Ks = sSup (↑𝓛 : Set (Subgroup X)) := by
    rw [h𝓛, Set.Finite.coe_toFinset, hS, sSup_image]
    rfl
  have hLc : ∀ L ∈ 𝓛, IsComponentOf L ⊤ := fun L hL => by
    obtain ⟨g, -, rfl⟩ := hmem L hL
    exact isComponentOf_gLBConj hKc g
  have hcomm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → ∀ x ∈ L, ∀ y ∈ L', x * y = y * x := by
    intro L hL L' hL' hne x hx y hy
    have h1 := CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' (hLc L hL) (hLc L' hL') hne
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1 hx) y hy).symm
  have hZ : ∀ L ∈ 𝓛, ∀ z ∈ L ⊓ Subgroup.centralizer (L : Set X), z ^ Nat.card (Subgroup.center ↥K) = 1 := by
    intro L hL z hz
    obtain ⟨g, -, rfl⟩ := hmem L hL
    obtain ⟨hzL, hzC⟩ := hz
    have hz' : g * z * g⁻¹ ∈ K ⊓ Subgroup.centralizer (K : Set X) := by
      refine ⟨mem_gLBConj.1 hzL, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
      have hk' : g⁻¹ * k * g ∈ GLBConj g K := mem_gLBConj.2 (by group; exact hk)
      have h1 := Subgroup.mem_centralizer_iff.1 hzC _ hk'
      calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
        _ = g * z * g⁻¹ * k := by group
    have hcen : (⟨g * z * g⁻¹, hz'.1⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hz'.2 k k.2)
    have h1 := pow_card_eq_one' (G := ↥(Subgroup.center ↥K)) (x := ⟨_, hcen⟩)
    have h2 : (g * z * g⁻¹) ^ Nat.card (Subgroup.center ↥K) = 1 :=
      congrArg (fun w : ↥(Subgroup.center ↥K) => ((w : ↥K) : X)) h1
    rw [conj_pow] at h2
    calc z ^ Nat.card (Subgroup.center ↥K)
        = g⁻¹ * (g * z ^ Nat.card (Subgroup.center ↥K) * g⁻¹) * g := by group
      _ = 1 := by rw [h2]; group
  have haL : ∀ L ∈ 𝓛, a ∈ Subgroup.normalizer (L : Set X) := by
    intro L hL
    obtain ⟨g, hg, rfl⟩ := hmem L hL
    have hga : g * a = a * g := Inputs27.elem_mul_comm hA hg ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [mem_gLBConj, mem_gLBConj]
    have e : g * (a * h * a⁻¹) * g⁻¹ = a * (g * h * g⁻¹) * a⁻¹ := by
      calc g * (a * h * a⁻¹) * g⁻¹ = (g * a) * h * (g * a)⁻¹ := by group
        _ = (a * g) * h * (a * g)⁻¹ := by rw [hga]
        _ = a * (g * h * g⁻¹) * a⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 haN _
  have hLKs : ∀ L ∈ 𝓛, L ≤ Ks := fun L hL => by
    obtain ⟨g, hg, rfl⟩ := hmem L hL
    exact le_iSup₂_of_le (f := fun g (_ : g ∈ A) => GLBConj g K) g hg le_rfl
  have hLY : ∀ L ∈ 𝓛, L ⊓ Subgroup.centralizer ({a} : Set X) ≤ Y := fun L hL =>
    inf_le_inf_right _ (hLKs L hL)
  have hKsN : ∀ L ∈ 𝓛, Ks ≤ Subgroup.normalizer (L : Set X) := by
    intro L hL
    rw [hKs']
    refine sSup_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · rw [hLL]
      exact Subgroup.le_normalizer
    · intro y hy
      refine Subgroup.centralizer_le_normalizer (L : Set X) (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
      exact hcomm L hL L' hL' (Ne.symm hLL) x hx y hy
  have hYN : ∀ L ∈ 𝓛, Y ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) := by
    intro L hL y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hKsN L hL hy.1, Subgroup.le_normalizer hy.2⟩
  have hJle : J ≤ ⨆ L ∈ 𝓛, L ⊓ Subgroup.centralizer ({a} : Set X) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_center_of_core hp hOK)
    refine le_of_perfect_of_pow_mem hp (glaPComponent_perfect hJY) ?_ fun j hj => ?_
    · exact hJY.1.trans (Inputs27.le_normalizer_iSup' _ fun L =>
        Inputs27.le_normalizer_iSup' _ fun hL => hYN L hL)
    · have hjY : j ∈ sSup (↑𝓛 : Set (Subgroup X)) ⊓ Subgroup.centralizer ({a} : Set X) := by
        have h1 := hJY.1 hj
        rw [hY, hKs'] at h1
        exact h1
      obtain ⟨m, hm⟩ := exists_pow_mem_iSup_inf_centralizer 𝓛 hcomm hZ haL j hjY
      refine ⟨k * m, ?_⟩
      rw [pow_mul, ← hk]
      exact hm
  obtain ⟨L, hL𝓛, hJL⟩ := exists_le_of_le_iSup 𝓛 (fun L => L ⊓ Subgroup.centralizer ({a} : Set X)) hJY hJle
    hLY hYN
  obtain ⟨g, hg, hgL⟩ := hmem L hL𝓛
  refine ⟨g, hg, hgL ▸ haL L hL𝓛, ?_⟩
  rw [hgL]
  exact glaPComponent_of_le hp hJY hJL (hLY L hL𝓛)

theorem nonempty_pSimple_equiv_of_not_mem_normalizer (hp : p.Prime) (hp2 : p ≠ 2) (hO : GLAPPrimeCore p X = ⊥)
    {K : Subgroup X} (hK : GLAPComponent p ⊤ K) {A : Subgroup X} (hA : IsElemAbelian p A) {a : X} (ha : a ∈ A)
    (ha1 : a ≠ 1) (haN : a ∉ Subgroup.normalizer (K : Set X)) {J : Subgroup X}
    (hJ : GLAPComponent p (GLAPLayer p ((⨆ g ∈ A, GLBConj g K) ⊓ Subgroup.centralizer ({a} : Set X))) J) :
    Nonempty (PSimple p J ≃* ↥K ⧸ Subgroup.center ↥K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, hOK⟩ := comp_facts hO hK
  set Ks : Subgroup X := ⨆ g ∈ A, GLBConj g K with hKs
  set Y : Subgroup X := Ks ⊓ Subgroup.centralizer ({a} : Set X) with hY
  have hlayer : IsSubnormal (GLAPLayer p Y) Y :=
    CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp {L | GLAPComponent p Y L} fun _ h => h
  have hJY : GLAPComponent p Y J := l119_glaPComponent_of_isSubnormal hp hlayer hJ
  have hKsub : IsSubnormal Ks ⊤ := by
    have h1 := CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp
      ((fun g => GLBConj g K) '' (A : Set X)) (by rintro _ ⟨g, -, rfl⟩; exact glaPComponent_conj hK g)
    rwa [sSup_image] at h1
  have hYsn : IsSubnormal Y ((⊤ : Subgroup X) ⊓ Subgroup.centralizer ({a} : Set X)) :=
    isSubnormal_inf hKsub _
  have hJ' : GLAPComponent p ((⊤ : Subgroup X) ⊓ Subgroup.centralizer ({a} : Set X)) J :=
    l119_glaPComponent_of_isSubnormal hp hYsn hJY
  have hle : barX p ⊤ J ≤ barX p ⊤ (⨆ y ∈ A, GLBConj y K) := barX_mono (hJY.1.trans inf_le_left)
  obtain ⟨π, hπs, hπk, -⟩ := Inputs183eqv.input18_3_eqv_holds X p hp hp2 ⊤ K A hK hA le_top a ha ha1
    (Subgroup.mem_top a) (Or.inl haN) J hJ' hle
  have hqB : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (barOfEquivOfCore hOK) hKc.2.2
  obtain ⟨e1⟩ := Claims126.nonempty_quot_center_quot hqB.1 π.ker hπk
  exact ⟨((Lemma1315b.centerQuotEquiv (QuotientGroup.quotientKerEquivOfSurjective π hπs).symm).trans e1).trans
    (Lemma1315b.centerQuotEquiv (barOfEquivOfCore hOK))⟩

theorem isChevSimple_of_kstar (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ}
    (hD : CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p q) (hO : GLAPPrimeCore p X = ⊥) {K : Subgroup X}
    (hK : GLAPComponent p ⊤ K) (hchev : IsChevSimple q (↥K ⧸ Subgroup.center ↥K)) {A : Subgroup X}
    (hA : IsElemAbelian p A) {a : X} (ha : a ∈ A) (ha1 : a ≠ 1) {J : Subgroup X}
    (hJ : GLAPComponent p (GLAPLayer p ((⨆ g ∈ A, GLBConj g K) ⊓ Subgroup.centralizer ({a} : Set X))) J) :
    IsChevSimple q (PSimple p J) := by
  by_cases haN : a ∈ Subgroup.normalizer (K : Set X)
  · obtain ⟨g, -, haL, hJL⟩ := exists_conj_of_mem_normalizer hp hO hK hA ha haN hJ
    have hLc := glaPComponent_conj hK g
    obtain ⟨-, hOL⟩ := comp_facts hO hLc
    obtain ⟨e⟩ := nonempty_conj_center_quot K g
    have hchevL : IsChevSimple q (PSimple p (GLBConj g K)) :=
      CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv
        ((Lemma1315b.centerQuotEquiv (barOfEquivOfCore hOL)).trans e).symm hchev
    exact CFSG.LocalAnalysis.GLTheoremA.chevQ_step hp hD hLc hchevL haL (hA.2 a ha) hJL
  · obtain ⟨e⟩ := nonempty_pSimple_equiv_of_not_mem_normalizer hp hp2 hO hK hA ha ha1 haN hJ
    exact CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv e.symm hchev

@[expose] def Input27_4L227Up : Prop :=
  ∀ (X : Type) [Group X] [Finite X], GLAPPrimeCore 3 X = ⊥ → ∀ L : Subgroup X, GLAPComponent 3 ⊤ L →
    IsChevSimple 3 (↥L ⧸ Subgroup.center ↥L) → ¬ IsLTwoTwentySeven (↥L ⧸ Subgroup.center ↥L) →
    ∀ a b : X, a ∈ Subgroup.normalizer (L : Set X) → b ∈ Subgroup.normalizer (L : Set X) → a * b = b * a →
      a ^ 3 = 1 → b ^ 3 = 1 → ∀ J : Subgroup X, GLAPComponent 3 (L ⊓ Subgroup.centralizer ({a} : Set X)) J →
        IsLTwoTwentySeven (barOf 3 J ⧸ Subgroup.center (barOf 3 J)) →
        ∀ hbJ : b ∈ Subgroup.normalizer (J : Set X), barAut 3 J ⟨b, hbJ⟩ ∉ innerAut (barOf 3 J) → False

theorem input27_4ChevP_of (hC3 : CFSG.HardMathSupport.Solomon.Coordinator.L2CentreThree)
    (h1964 : Lemma123.Input19_6_4)
    (hKD : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ p p)
    (hUp : Input27_4L227Up) : Input27_4ChevP := by
  intro p hp hp2 X _ _ _ hO K hK hKh hT E A hE hA' hEA hEAp hr _ _ _ hN hC1 _ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hKc, hOK⟩ := comp_facts hO hK
  obtain ⟨hchev, -⟩ := hT
  have hq : CFSG.Open.IsQuasisimple ↥K := hKh.1
  set Ks : Subgroup X := ⨆ g ∈ A, GLBConj g K with hKs
  by_cases hbad : ∃ a ∈ A, a ≠ 1 ∧ ∃ J : Subgroup X,
      GLAPComponent p (GLAPLayer p (Ks ⊓ Subgroup.centralizer ({a} : Set X))) J ∧ p = 3 ∧
        IsLTwoTwentySeven (PSimple p J) ∧ ¬ autBar p A J ≤ innerAut (barOf p J)
  · obtain ⟨a, ha, ha1, J, hJ, rfl, hJL, hJout⟩ := hbad
    have hlayer : IsSubnormal (GLAPLayer 3 (Ks ⊓ Subgroup.centralizer ({a} : Set X)))
        (Ks ⊓ Subgroup.centralizer ({a} : Set X)) :=
      CFSG.LocalAnalysis.GLTheoremA.isSubnormal_sSup_glaPComponent hp _ fun _ h => h
    have hJY : GLAPComponent 3 (Ks ⊓ Subgroup.centralizer ({a} : Set X)) J :=
      l119_glaPComponent_of_isSubnormal hp hlayer hJ
    have hcJ : 9828 ≤ Nat.card J := by
      obtain ⟨eJ⟩ := hJL
      have h1 : Nat.card (PSimple 3 J) = 9828 := (card_L227_and_aut eJ).1
      have h2 : Nat.card (PSimple 3 J) ≤ Nat.card (barOf 3 J) :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      have h3 : Nat.card (barOf 3 J) ≤ Nat.card J :=
        Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
      omega
    by_cases hKL : IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K)
    · rcases l227_cases hC3 hO hK hq hKL hE hA' hEA hEAp hr hN hC1 with h3 | ⟨h81, hAN, hA27⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h3⟩))))
      ·
        have hKs' : Ks = K := Inputs27.kStar_eq_of_le_normalizer hAN
        have hJK : J ≤ K := hKs' ▸ hJY.1.trans inf_le_left
        obtain ⟨eK⟩ := isLTwoTwentySeven_of_l227 hC3 hq hOK hKL
        have hcardK : Nat.card ↥K = 9828 := (card_L227_and_aut eK).1
        have hJeq : J = K := Subgroup.eq_of_le_of_card_ge hJK (by rw [hcardK]; exact hcJ)
        rw [hJeq] at hJout
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨rfl, h81, hA27 hJout, isLTwoTwentySeven_of_l227 hC3 hq hOK hKL⟩))))
    · exfalso
      by_cases haN : a ∈ Subgroup.normalizer (K : Set X)
      · obtain ⟨g, hg, haL, hJL'⟩ := exists_conj_of_mem_normalizer hp hO hK hA'.2.1 ha haN hJ
        set L : Subgroup X := GLBConj g K with hLdef
        have hLc : GLAPComponent 3 ⊤ L := glaPComponent_conj hK g
        have hLc' : IsComponentOf L ⊤ := isComponentOf_gLBConj hKc g
        obtain ⟨φ, hφA, hφI⟩ := Set.not_subset.1 hJout
        obtain ⟨⟨b, hbN⟩, hbA, rfl⟩ := hφA
        have hbA' : b ∈ A := (Subgroup.mem_subgroupOf.1 hbA).1
        have hbL : b ∈ Subgroup.normalizer (L : Set X) := by
          by_contra hbL
          have hne : GLBConj b L ≠ L := fun h => hbL (mem_normalizer_iff_gLBConj_eq.2 h)
          have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne L (GLBConj b L) hLc'
            (isComponentOf_gLBConj hLc' b) hne.symm
          have hJL1 : J ≤ L := hJL'.1.trans inf_le_left
          have hJL2 : J ≤ GLBConj b L := fun x hx =>
            mem_gLBConj.2 (hJL1 ((Subgroup.mem_normalizer_iff.1 hbN x).1 hx))
          have hJab : ⁅J, J⁆ = ⊥ := le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono hJL1 hJL2)
          have hJbot : J = ⊥ := by rw [← glaPComponent_perfect hJL', hJab]
          have h1 : Nat.card J = 1 := by rw [hJbot, Subgroup.card_bot]
          omega
        obtain ⟨e⟩ := nonempty_conj_center_quot K g
        have hLchev : IsChevSimple 3 (↥L ⧸ Subgroup.center ↥L) :=
          CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv e.symm hchev
        have hLnot : ¬ IsLTwoTwentySeven (↥L ⧸ Subgroup.center ↥L) := fun ⟨f⟩ => hKL ⟨e.symm.trans f⟩
        exact hUp X hO L hLc hLchev hLnot a b haL hbL (Inputs27.elem_mul_comm hA'.2.1 ha hbA')
          (hA'.2.1.2 a ha) (hA'.2.1.2 b hbA') J hJL' hJL hbN hφI
      · obtain ⟨e⟩ := nonempty_pSimple_equiv_of_not_mem_normalizer hp hp2 hO hK hA'.2.1 ha ha1 haN hJ
        exact hKL ⟨e.symm.trans hJL.some⟩
  ·
    refine Or.inr (Or.inr (Or.inl fun a ha ha1 J hJ => ?_))
    have hqJ : CFSG.Open.IsQuasisimple (barOf p J) :=
      CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
    have hOJ : GLAPPrimeCore p (barOf p J) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
    have htJ : IsChevSimple p (PSimple p J) := isChevSimple_of_kstar hp hp2 (hKD p hp hp2) hO hK hchev hA'.2.1 ha ha1 hJ
    by_cases hbal : IsLocallyOTwoBalancedWrtP p 1 (barOf p J)
    · exact Or.inl hbal
    · right
      obtain ⟨B, hB, hnB⟩ : ∃ B : Subgroup (MulAut (barOf p J)), IsElemAbelian p B ∧
          ¬ IsLocallyOTwoBalanced p 1 B :=
        Classical.byContradiction fun h => hbal fun B hB => Classical.byContradiction fun hnB => h ⟨B, hB, hnB⟩
      obtain ⟨rfl, hL, -⟩ := h1964 p hp hp2 (barOf p J) hqJ hOJ htJ B hB hnB
      refine ⟨rfl, isLTwoTwentySeven_of_l227 hC3 hqJ hOJ hL, ?_⟩
      by_contra hnb
      obtain ⟨-, -, hout⟩ := h1964 3 hp hp2 (barOf 3 J) hqJ hOJ htJ (autBar 3 A J)
        (isElemAbelian_autBar hA'.2.1 J) hnb
      exact hbad ⟨a, ha, ha1, J, hJ, rfl, hL, hout⟩

end ChevP4

section L227Up

open CFSG.Yardstones.Md0ec50421ce4 (PSimple PQuot ambiguousChev onLie)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA (chevAut chevTransfer chevQuotHom)

variable {X : Type} [Group X] [Finite X]

theorem coordinator_of_isLTwoTwentySeven {S : Type} [Group S] (h : IsLTwoTwentySeven S) :
    CFSG.HardMathSupport.Solomon.Coordinator.IsLTwoTwentySeven S := by
  obtain ⟨e⟩ := h
  refine ⟨GaloisField 3 3, inferInstance, inferInstance, ?_,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 3 3))⟩⟩
  rw [GaloisField.card 3 3 (by norm_num)]
  norm_num

theorem isPGroup_zpowers_of_pow {p : ℕ} {a : X} (ha : a ^ p = 1) : IsPGroup p (Subgroup.zpowers a) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

theorem barAut_mem_innerAut_of_transfer {p : ℕ} (hp : p.Prime) {L J : Subgroup X} {a b : X}
    (haL : a ∈ Subgroup.normalizer (L : Set X)) (hap : IsPGroup p (Subgroup.zpowers a))
    (hJ : GLAPComponent p (L ⊓ Subgroup.centralizer ({a} : Set X)) J)
    (hbL : b ∈ Subgroup.normalizer (L : Set X)) (hbJ : b ∈ Subgroup.normalizer (J : Set X))
    {i : PSimple p L} (hi : i ∈ chevTransfer p L J)
    (hβ : ∀ x ∈ chevTransfer p L J,
      chevAut p L ⟨b, hbL⟩ x * (i * x * i⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p (chevTransfer p L J)) :
    barAut p J ⟨b, hbJ⟩ ∈ innerAut (barOf p J) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set I : Subgroup (PSimple p L) := chevTransfer p L J with hIdef
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hmemI : ∀ j : ↥J, (chevQuotHom p L).comp (Subgroup.inclusion hJL) j ∈ I := fun j =>
    ⟨Subgroup.inclusion hJL j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
  set πJ : ↥J →* ↥I := ((chevQuotHom p L).comp (Subgroup.inclusion hJL)).codRestrict I hmemI with hπJ
  have hπs : Function.Surjective πJ := by
    rintro ⟨y, k, hk, rfl⟩
    exact ⟨⟨(k : X), Subgroup.mem_subgroupOf.1 hk⟩, rfl⟩
  have hI : GLAPComponent p (fixSubgroup (chevAut p L ⟨a, haL⟩)) I :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer hp haL hap hJ
  have hqJ : CFSG.Open.IsQuasisimple (barOf p J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hqI : CFSG.Open.IsQuasisimple (PQuot p I) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hI
  have hnt : Nontrivial (↥I ⧸ GLAPPrimeCore p ↥I) := by
    haveI : IsSimpleGroup (PQuot p I ⧸ Subgroup.center (PQuot p I)) := hqI.2
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI := h
    have hs : Subsingleton (PQuot p I ⧸ Subgroup.center (PQuot p I)) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p I))).subsingleton
    exact (not_nontrivial_iff_subsingleton.2 hs) inferInstance
  haveI : Group.IsPerfect (barOf p J) := ⟨hqJ.1⟩
  have hΨs := CFSG.LocalAnalysis.GLTheoremA.pQuotMapOfSurjective_surjective hp πJ hπs
  have hker := CFSG.LocalAnalysis.GLTheoremA.ker_pQuotMapOfSurjective_le_center hp πJ hπs hqJ hnt
  refine CFSG.LocalAnalysis.GLTheoremA.chev_mem_inner_of_central_surjective
    (CFSG.LocalAnalysis.GLTheoremA.pQuotMapOfSurjective hp πJ hπs) hΨs hker
    (θ' := MulAut.conj (QuotientGroup.mk (⟨i, hi⟩ : ↥I) : ↥I ⧸ GLAPPrimeCore p ↥I)) ?_ ⟨_, rfl⟩
  intro q
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  have hu : ((πJ (J.normalizerMonoidHom ⟨b, hbJ⟩ j) : ↥I) : PSimple p L) =
      chevAut p L ⟨b, hbL⟩ ((πJ j : ↥I) : PSimple p L) := by
    show chevQuotHom p L (Subgroup.inclusion hJL (J.normalizerMonoidHom ⟨b, hbJ⟩ j)) =
      chevAut p L ⟨b, hbL⟩ (chevQuotHom p L (Subgroup.inclusion hJL j))
    rw [CFSG.LocalAnalysis.GLTheoremA.chevAut_chevQuotHom]
    rfl
  obtain ⟨o, ho, hoeq⟩ : chevAut p L ⟨b, hbL⟩ ((πJ j : ↥I) : PSimple p L) *
      (i * ((πJ j : ↥I) : PSimple p L) * i⁻¹)⁻¹ ∈ (GLAPPrimeCore p ↥I).map I.subtype :=
    hβ _ (πJ j).2
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, CFSG.LocalAnalysis.GLTheoremA.pQuotMapOfSurjective_mk,
    CFSG.LocalAnalysis.GLTheoremA.pQuotMapOfSurjective_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  set u : ↥I := πJ (J.normalizerMonoidHom ⟨b, hbJ⟩ j) with hudef
  set w : ↥I := ⟨i, hi⟩ * πJ j * (⟨i, hi⟩ : ↥I)⁻¹ with hwdef
  have how : o = u * w⁻¹ := by
    apply Subtype.ext
    have h1 : ((u * w⁻¹ : ↥I) : PSimple p L) = chevAut p L ⟨b, hbL⟩ ((πJ j : ↥I) : PSimple p L) *
        (i * ((πJ j : ↥I) : PSimple p L) * i⁻¹)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hu]
      rfl
    rw [h1]
    exact hoeq
  have key : u⁻¹ * w = u⁻¹ * (u * w⁻¹)⁻¹ * u⁻¹⁻¹ := by group
  rw [key, ← how]
  exact (inferInstance : (GLAPPrimeCore p ↥I).Normal).conj_mem _ (Subgroup.inv_mem _ ho) u⁻¹

theorem input27_4L227Up_of (hInner : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3)
    (hAmb : CFSG.LocalAnalysis.GLTheoremA.KDAmbSolv 3)
    (hOC : CFSG.HardMathSupport.Dickson.DefCharOuter.Export.OuterCentAll) : Input27_4L227Up := by
  intro X _ _ hO L hL hLchev hLnot a b haL hbL hab ha3 hb3 J hJ hJL hbJ hout
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp := Nat.prime_three
  obtain ⟨-, hOL⟩ := comp_facts hO hL
  obtain ⟨hSs, hSna⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hL
  haveI : IsSimpleGroup (PSimple 3 L) := hSs
  have eS : PSimple 3 L ≃* ↥L ⧸ Subgroup.center ↥L := Lemma1315b.centerQuotEquiv (barOfEquivOfCore hOL)
  have hSchev : IsChevSimple 3 (PSimple 3 L) :=
    CFSG.HardMathSupport.Dickson.I271.isChevSimple_of_mulEquiv eS.symm hLchev
  have hSnot : ¬ IsLTwoTwentySeven (PSimple 3 L) := fun ⟨f⟩ => hLnot ⟨eS.symm.trans f⟩
  have hap : IsPGroup 3 (Subgroup.zpowers a) := isPGroup_zpowers_of_pow ha3
  set α : MulAut (PSimple 3 L) := chevAut 3 L ⟨a, haL⟩ with hαdef
  set β : MulAut (PSimple 3 L) := chevAut 3 L ⟨b, hbL⟩ with hβdef
  have hα3 : α ^ 3 = 1 := CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one 3 L haL ha3
  have hβ3 : β ^ 3 = 1 := CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one 3 L hbL hb3
  have hβα : β * α = α * β := by
    rw [hαdef, hβdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hab.symm
  set I : Subgroup (PSimple 3 L) := chevTransfer 3 L J with hIdef
  have hI : GLAPComponent 3 (fixSubgroup α) I :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer hp haL hap hJ
  obtain ⟨eJI⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_chevTransfer hp haL hap hJ
  have hIL : IsLTwoTwentySeven (PSimple 3 I) := ⟨eJI.symm.trans hJL.some⟩
  by_cases hα1 : α = 1
  · have hfix : fixSubgroup α = ⊤ := by
      rw [hα1]
      ext x
      simp [mem_fixSubgroup]
    rw [hfix] at hI
    obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp hSna hI
    exact hSnot ⟨e.symm.trans hIL.some⟩
  by_cases hαI : α ∈ innerAut (PSimple 3 L)
  · have hbot := hInner _ hSs hSna hSchev α hα3 hα1 hαI
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hI (le_bot_iff.1 (hbot ▸ le_sSup hI))
  have hαo : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hβI : I.map β.toMonoidHom = I := by
    have hle : I.map β.toMonoidHom ≤ I := by
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨L.normalizerMonoidHom ⟨b, hbL⟩ k, ?_, ?_⟩
      · show L.normalizerMonoidHom ⟨b, hbL⟩ k ∈ J.subgroupOf L
        exact Subgroup.mem_subgroupOf.2
          ((Subgroup.mem_normalizer_iff.1 hbJ (k : X)).1 (Subgroup.mem_subgroupOf.1 hk))
      · exact (CFSG.LocalAnalysis.GLTheoremA.chevAut_chevQuotHom 3 L ⟨b, hbL⟩ k).symm
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective).symm)
  rcases hSchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie idx =>
      have hchar : idx.1.characteristic = 3 := hi
      have hdata := (hOC (CFSG.Yardstones.Md42047359a2a.lieFamily idx.1)).2 _ hSs hSna idx rfl ⟨e⟩ 3 hp
        (by norm_num) hchar.symm α hαo hαI
      obtain ⟨i0, hi0, hi0'⟩ := hdata.l227 rfl I hI (coordinator_of_isLTwoTwentySeven hIL) β hβ3 hβα hβI
      exact hout (barAut_mem_innerAut_of_transfer hp haL hap hJ hbL hbJ hi0 hi0')
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  ·
    haveI : Finite i.Group := Finite.of_equiv _ e.toEquiv
    have hα1' : MulAut.congr e α ≠ 1 := fun h =>
      hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
    have hαp : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
    have hsolv := hAmb i hi (MulAut.congr e α) hαp hα1'
    rw [CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr] at hsolv
    haveI : Group.IsSolvable ↥((fixSubgroup α).map e.toMonoidHom) := hsolv
    have hsolvα : Group.IsSolvable ↥(fixSubgroup α) :=
      Group.isSolvable_of_isSolvable_injective
        (f := ((fixSubgroup α).equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        ((fixSubgroup α).equivMapOfInjective e.toMonoidHom e.injective).injective
    exact CFSG.HardMathSupport.Dickson.DefCharOuter.Export.not_glaPComponent_of_solvable hsolvα hI

end L227Up

section Spor4

open CFSG.Yardstones.Md0ec50421ce4 (PSimple PQuot)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA (chevAut chevTransfer)
open CFSG.HardMathSupport.Timmesfeld.Coordinator (IsLocallyBalancedAbs SporadicLocalOneData SporadicOuterLeTwo)

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem localDeltaTwoIn_le_localDeltaIn {M : Type} [Group M] [Finite M] (hp : p.Prime) (hp2 : p ≠ 2)
    (H D : Subgroup M) :
    localDeltaTwoIn H D ≤ CFSG.HardMathSupport.Solomon.LocalBalance.localDeltaIn p H D :=
  iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ =>
    Inputs123a.pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _

theorem isLocallyOTwoBalancedWrtP_of_abs {S : Type} [Group S] [Finite S] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsLocallyBalancedAbs p 1 S) : IsLocallyOTwoBalancedWrtP p 1 S :=
  fun _ _ D hD H hH hDH => le_bot_iff.1 ((localDeltaTwoIn_le_localDeltaIn hp hp2 H D).trans
    (h D hD.2.1 hD.2.2 H hH hDH).le)

@[expose] def Input27_4SporDown : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ α : MulAut S, α ^ p = 1 → α ≠ 1 →
      ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I →
        IsLocallyOTwoBalancedWrtP p 1 (PSimple p I) ∨
          (CFSG.Open.pRank p (⊤ : Subgroup (MulAut S)) ≤ 2 ∧ (p = 3 ∨ ¬ p ^ 3 ∣ Nat.card S))

theorem input27_4Spor_of (hOne : SporadicLocalOneData) (hCube : SporOneBalanceCube) (hOut : SporadicOuterLeTwo)
    (hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers) (hDown : Input27_4SporDown) :
    Input27_4Spor := by
  intro p hp hp2 X _ _ _ hO K hK hKh hT E A _ hA' _ _ _ _ _ _ _ _ _ hA2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hOK⟩ := comp_facts hO hK
  obtain ⟨s, ⟨e⟩⟩ := hT
  have hq : CFSG.Open.IsQuasisimple ↥K := hKh.1
  have hA2' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2 →
      5 ≤ p ∧ (p ∣ (innerAut ↥K).index ∨ ∃ P : Sylow p ↥K, ¬ IsMulCommutative ↥(P : Subgroup ↥K)) :=
    fun h => ⟨(hA2 h).1, (hA2 h).2.2.2⟩
  have hO2K : IsLocallyOTwoBalancedWrtP p 1 (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOTwoBalancedWrtP_of_abs hp hp2 (spor_balanced hOne hCube hOut hSpM hp hp2 hq hOK e hA2')
  refine Or.inr (Or.inr (Or.inl fun a ha ha1 J hJ => Or.inl ?_))
  have hqJ : CFSG.Open.IsQuasisimple (barOf p J) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  refine Inputs123a.isLocallyOTwoBalancedWrtP_of_quot hqJ.1 ?_
  by_cases haN : a ∈ Subgroup.normalizer (K : Set X)
  · obtain ⟨g, -, haL, hJL⟩ := exists_conj_of_mem_normalizer hp hO hK hA'.2.1 ha haN hJ
    have hLc := glaPComponent_conj hK g
    obtain ⟨-, hOL⟩ := comp_facts hO hLc
    obtain ⟨eLK⟩ := nonempty_conj_center_quot K g
    have eS : PSimple p (GLBConj g K) ≃* ↥K ⧸ Subgroup.center ↥K :=
      (Lemma1315b.centerQuotEquiv (barOfEquivOfCore hOL)).trans eLK
    obtain ⟨hSs, hSna⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hLc
    haveI : IsSimpleGroup (PSimple p (GLBConj g K)) := hSs
    have hap3 : a ^ p = 1 := hA'.2.1.2 a ha
    have hap := isPGroup_zpowers_of_pow hap3
    have hI := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_chevTransfer hp haL hap hJL
    obtain ⟨eJI⟩ := CFSG.LocalAnalysis.GLTheoremA.nonempty_pSimple_equiv_chevTransfer hp haL hap hJL
    refine (Inputs123a.isLocallyOTwoBalancedWrtP_congr eJI).2 ?_
    by_cases hα1 : chevAut p (GLBConj g K) ⟨a, haL⟩ = 1
    · have hfix : fixSubgroup (chevAut p (GLBConj g K) ⟨a, haL⟩) = ⊤ := by
        rw [hα1]
        ext x
        simp [mem_fixSubgroup]
      rw [hfix] at hI
      obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv hp hSna hI
      exact (Inputs123a.isLocallyOTwoBalancedWrtP_congr (e1.trans eS)).2 hO2K
    · rcases hDown _ hSs hSna s ⟨eS.trans e⟩ p hp hp2 _
          (CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one p _ haL hap3) hα1 _ hI with hbal | ⟨hrk, h3⟩
      · exact hbal
      · exfalso
        have hrk' : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K))) ≤ 2 := by
          rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (MulAut.congr eS)]
          exact hrk
        have hcS : Nat.card (PSimple p (GLBConj g K)) = Nat.card (↥K ⧸ Subgroup.center ↥K) :=
          Nat.card_congr eS.toEquiv
        refine spor_false_of_rank hOut hSpM hp hq hOK e hrk' (fun hp5 => ?_) hA2'
        rcases h3 with h3 | h3
        · omega
        · rwa [← hcS]
  · obtain ⟨e'⟩ := nonempty_pSimple_equiv_of_not_mem_normalizer hp hp2 hO hK hA'.2.1 ha ha1 haN hJ
    exact (Inputs123a.isLocallyOTwoBalancedWrtP_congr e').2 hO2K

end Spor4

section AltRegular

open Equiv Equiv.Perm

@[expose] def Input27_3AltRegularTwo : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    GLAPPrimeCore p X = ⊥ → ∀ K : Subgroup X, IsComponentOf K ⊤ →
    ∀ n δ : ℕ, Nonempty (↥K ≃* alternatingGroup (Fin n)) → 1 ≤ δ → δ < p → n = p ^ 2 + δ →
    ∀ E A : Subgroup X, IsSCp p ⊤ E → IsSCp p ⊤ A → E ≠ A → IsPGroup p ↥(E ⊔ A) →
      CFSG.Open.pRank p (E ⊓ A) = 2 →
      Subgroup.centralizer ((GLALayer (⊤ : Subgroup X) : Subgroup X) : Set X) ⊓ (E ⊓ A) ≠ ⊥ →
      ¬ K ≤ GLBCore p 2 E → E ≤ Subgroup.normalizer (K : Set X) →
      CFSG.Open.pRank p (E ⊓ Subgroup.centralizer (K : Set X)) = 1 →
      CFSG.Open.pRank p E = 3 →
      (E ⊓ K) ⊓ (E ⊓ Subgroup.centralizer (K : Set X)) = ⊥ →
      (∃ e1 : ↥K, (e1 : X) ∈ E ∧ e1 ≠ 1 ∧ ∃ ψ : ↥K ≃* ↥(alternatingGroup (Fin n)),
        (ψ e1).1.cycleType = Multiset.replicate p p) →
      (∃ Es : Subgroup X, IsSCp p ⊤ Es ∧ 3 ≤ CFSG.Open.pRank p Es ∧
          IsKConnectedIn p 3 ⊤ E Es ∧ K ≤ GLBCore p 2 Es) ∨
      IsKConnectedIn p 3 ⊤ E A ∨
      (∃ y ∈ GLBCore p 2 E, GLBConj y E = A) ∨
      (CFSG.Open.pRank p E = 3 ∧ 3 < CFSG.Open.pRank p A) ∨
      (p = 3 ∧ CFSG.Open.pRank p E = 3) ∨
      (p = 3 ∧ Nat.card E = 3 ^ 4 ∧ Nat.card A = 3 ^ 3 ∧ IsLTwoTwentySeven ↥K) ∨
      CFSG.HardMathSupport.Solomon.LocalBalance.IsCompLocallyBalanced p 1 A K

theorem input27_3AltRegular_of_two (h23 : Lemma129e.Input23_5) (h2 : Input27_3AltRegularTwo) :
    Input27_3AltRegular := by
  intro p hp hp2 X _ _ hXK hO K hKc n r δ ⟨ψ0⟩ hr2 hδ1 hδp hnr E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hEr hdisj he1
  rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | hr3
  · have he1' : ∃ e1 : ↥K, (e1 : X) ∈ E ∧ e1 ≠ 1 ∧ ∃ ψ : ↥K ≃* ↥(alternatingGroup (Fin n)),
        (ψ e1).1.cycleType = Multiset.replicate p p := by
      obtain ⟨e1, h1, h1', ψ, h3⟩ := he1
      exact ⟨e1, h1, h1', ψ, by simpa using h3⟩
    exact h2 p hp hp2 X hXK hO K hKc n δ ⟨ψ0⟩ hδ1 hδp hnr E A hE hA' hEA hEAp hr hc hKΓ hN hC1 hEr hdisj he1'
  refine Or.inl ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpr : p ^ 3 ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr3
  have h27 : 27 ≤ p ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  have hn5 : 5 ≤ n := by omega
  have hpn : ¬ p ∣ n := by
    intro h
    rw [hnr] at h
    have hd : p ∣ δ := (Nat.dvd_add_right (dvd_pow_self p (by omega))).1 h
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_alt hn5 ψ0
  have hKC := Inputs27.inf_centralizer_self_eq_bot hZK
  have hinner : ∀ e ∈ E, ∃ k ∈ K, ∀ x ∈ K, e * x * e⁻¹ = k * x * k⁻¹ := by
    intro e he
    set σ : MulAut ↥K := K.normalizerMonoidHom ⟨e, hN he⟩ with hσ
    have hσp : σ ^ p = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨e, hN he⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 :=
        Subtype.ext (by simpa using hE.2.1.2 e he)
      rw [this, map_one]
    have hσI : σ ∈ innerAut ↥K := Inputs196.mem_innerAut_of_congr ψ0
      (Inputs196.mem_innerAut_of_not_dvd hp
        (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2)
        (by rw [← map_pow, hσp, map_one]))
    obtain ⟨k, hk⟩ := hσI
    refine ⟨k, k.2, fun x hx => ?_⟩
    have h := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : ↥K) : X)) hk
    simp only [MulAut.conj_apply] at h
    exact h.symm
  have hEsplit := Inputs27.eq_inf_sup_inf_of_inner hE hN hKC hinner
  set C := E ⊓ Subgroup.centralizer (K : Set X) with hCdef
  have hCel : IsElemAbelian p C := CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
  have hCc : Nat.card C = p := by rw [Inputs27.card_eq_pow_pRank hp hCel, hC1, pow_one]
  have hEKel : IsElemAbelian p (E ⊓ K) := CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
  have hcommKC : ∀ x ∈ K, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 x hx
  have hEK : Nat.card (E ⊓ K : Subgroup X) = p ^ r := by
    have h1 := GL83.CompFam.card_sup_of_commute_of_inf_eq_bot
      (fun x hx y hy => hcommKC x (Subgroup.mem_inf.1 hx).2 y hy) hdisj
    rw [← hEsplit, Inputs27.card_eq_pow_pRank hp hE.2.1, hEr, hCc, pow_succ] at h1
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h1).symm
  set perm : ↥K →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp ψ0.toMonoidHom with hperm
  have hperminj : Function.Injective perm :=
    (alternatingGroup (Fin n)).subtype_injective.comp ψ0.injective
  set T' : Subgroup (Perm (Fin n)) := ((E ⊓ K).subgroupOf K).map perm with hT'
  have hT'el : IsElemAbelian p T' :=
    CFSG.SectionRank.isElemAbelian_map (Inputs27.isElemAbelian_subgroupOf hEKel K) perm
  obtain ⟨c₀, hc₀C, hc₀1⟩ : ∃ c₀ ∈ C, c₀ ≠ 1 := by
    obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (ne_bot_of_pRank_eq_one hp hC1)
    exact ⟨c, hc, fun h => hc1 (Subtype.ext h)⟩
  obtain ⟨i, hi⟩ : ∃ i, ∀ β ∈ T', β ≠ 1 → β i ≠ i := by
    by_contra hreg
    push Not at hreg
    apply hKΓ
    set Γ' : Subgroup (Perm (Fin n)) := ((GLBCore p 2 E).comap K.subtype).map perm with hΓ'
    have hcent : ∀ β ∈ T', β ≠ 1 → Claims126.cA β ≤ Γ' := by
      rintro _ ⟨t, ht, rfl⟩ ht1 g hg
      obtain ⟨hgA, hgc⟩ := Claims126.mem_cA.1 hg
      refine ⟨ψ0.symm ⟨g, hgA⟩, ?_, by simp [hperm]⟩
      show ((ψ0.symm ⟨g, hgA⟩ : ↥K) : X) ∈ GLBCore p 2 E
      have htE : (t : X) ∈ E := (Subgroup.mem_subgroupOf.1 ht).1
      have htC : (t : X) ∉ C := by
        intro h
        have h0 : (t : X) ∈ (E ⊓ K) ⊓ C := ⟨Subgroup.mem_subgroupOf.1 ht, h⟩
        rw [hdisj, Subgroup.mem_bot] at h0
        exact ht1 (by rw [show t = 1 from Subtype.ext h0, map_one])
      have hkc : ((ψ0.symm ⟨g, hgA⟩ : ↥K) : X) * t = t * ((ψ0.symm ⟨g, hgA⟩ : ↥K) : X) := by
        have h1 : perm (ψ0.symm ⟨g, hgA⟩ * t) = perm (t * ψ0.symm ⟨g, hgA⟩) := by
          rw [map_mul, map_mul]
          have hg' : perm (ψ0.symm ⟨g, hgA⟩) = g := by simp [hperm]
          rw [hg']
          exact hgc
        exact congrArg Subtype.val (hperminj h1)
      exact AltFacts5.mem_glbCore_of_comm hp hE.2.1 inf_le_left hc₀C hc₀1 htE htC
        (hcommKC _ (ψ0.symm ⟨g, hgA⟩).2 c₀ hc₀C) hkc
    have hA := AltFacts5.alt_le_of_fix' hp2 hpn hn5 hT'el hreg
      (fun β hβ hβ1 _ => (Claims126.altOn_le_cA β).trans (hcent β hβ hβ1))
      (fun β hβ hβ1 h4 g hg => hcent β hβ hβ1 (Claims126.altOn_le_cA β ((Claims126.mem_kleinOn h4).1 hg).1))
    intro k hk
    obtain ⟨x, hx, hxk⟩ := hA (ψ0 ⟨k, hk⟩).2
    have hxk' : x = ⟨k, hk⟩ := ψ0.injective (Subtype.ext hxk)
    rw [hxk'] at hx
    exact hx
  obtain ⟨U₀, hU₀⟩ := Sylow.exists_subgroup_card_pow_prime p (G := ↥(E ⊓ K)) (n := r - 1)
    (by rw [hEK]; exact pow_dvd_pow p (by omega))
  set BX : Subgroup X := U₀.map (E ⊓ K).subtype with hBX
  have hBXEK : BX ≤ E ⊓ K := Subgroup.map_subtype_le U₀
  have hBXK : BX ≤ K := hBXEK.trans inf_le_right
  have hBXc : Nat.card BX = p ^ (r - 1) := by
    rw [hBX, Subgroup.card_map_of_injective (E ⊓ K).subtype_injective, hU₀]
  have hBXel : IsElemAbelian p BX := CFSG.Open.IsElemAbelian.mono hEKel hBXEK
  set κ : ↥BX →* ↥K := Subgroup.inclusion hBXK with hκ
  have hκinj : Function.Injective κ := Subgroup.inclusion_injective hBXK
  have hκT : ∀ b ∈ κ.range, perm b ∈ T' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨κ b, Subgroup.mem_subgroupOf.2 (hBXEK b.2), rfl⟩
  have hκc : Nat.card κ.range = p ^ (r - 1) :=
    (Nat.card_congr (MonoidHom.ofInjective hκinj).toEquiv).symm.trans hBXc
  have hset : ∀ j : Fin n, {j' | ∃ b ∈ κ.range, ((ψ0 b : alternatingGroup (Fin n)) : Perm (Fin n)) j = j'} =
      (fun b : ↥K => perm b j) '' (κ.range : Set ↥K) := fun j => rfl
  have horb1 : ∀ j, Lemma129e.orbitLen ψ0 κ.range j ≤ p ^ (r - 1) := by
    intro j
    unfold Lemma129e.orbitLen
    rw [hset j, ← hκc, ← Nat.card_coe_set_eq]
    exact (Set.ncard_image_le (Set.toFinite _)).trans (le_of_eq (Nat.card_coe_set_eq _).symm)
  have horb2 : ∃ j, Lemma129e.orbitLen ψ0 κ.range j = p ^ (r - 1) := by
    refine ⟨i, ?_⟩
    unfold Lemma129e.orbitLen
    rw [hset i, ← hκc, ← Nat.card_coe_set_eq]
    refine Set.InjOn.ncard_image fun b hb b' hb' hbb' => ?_
    have hmem : b'⁻¹ * b ∈ κ.range := κ.range.mul_mem (κ.range.inv_mem hb') hb
    have hfix : perm (b'⁻¹ * b) i = i := by
      rw [map_mul, map_inv, Perm.mul_apply]
      exact Perm.inv_eq_iff_eq.2 hbb'
    by_contra hne
    have hne' : perm (b'⁻¹ * b) ≠ 1 := by
      intro h1
      apply hne
      have h2 : b'⁻¹ * b = 1 := hperminj (by rw [h1, map_one])
      exact (inv_mul_eq_one.1 h2).symm
    exact hi _ (hκT _ hmem) hne' hfix
  have hκne : κ.range ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hκc
    have : 1 < p ^ (r - 1) := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  obtain ⟨P, hPK, hPel, hPc, hPrk, hKP⟩ := Lemma129e.acl_perm h23 hp hp2 hpn (t := r - 1) (by omega)
    (by rw [show r - 1 + 1 = r by omega, hnr]; omega) ψ0 κ (fun _ _ => rfl) hBXel hκne horb1 horb2
  set E₁ : Subgroup X := BX ⊔ C with hE₁
  have hE₁E : E₁ ≤ E := sup_le (hBXEK.trans inf_le_left) inf_le_left
  have hE₁el : IsElemAbelian p E₁ := Inputs27.isElemAbelian_sup_of_commute hBXel hCel
    fun x hx y hy => hcommKC x (hBXK hx) y hy
  have hE₁c : Nat.card E₁ = p ^ r := by
    have hd : BX ⊓ C = ⊥ := le_bot_iff.1 (hKC ▸ inf_le_inf hBXK inf_le_right)
    have h1 := GL83.CompFam.card_sup_of_commute_of_inf_eq_bot (fun x hx y hy => hcommKC x (hBXK hx) y hy) hd
    rw [h1, hBXc, hCc, ← pow_succ]
    congr 1
    omega
  have hE₁P : E₁ ≤ Subgroup.centralizer (P : Set X) := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hPc x hx y hy).symm) ?_
    exact fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx => hcommKC x (hPK hx) y hy
  have hFel : IsElemAbelian p (P ⊔ E₁) := Inputs27.isElemAbelian_sup_of_commute hPel hE₁el
    fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hE₁P hy) x hx
  obtain ⟨M, ⟨hFM, hMel⟩, hMmax⟩ := (wellFounded_gt (α := Subgroup X)).has_min
    {M' : Subgroup X | P ⊔ E₁ ≤ M' ∧ IsElemAbelian p M'} ⟨P ⊔ E₁, le_rfl, hFel⟩
  have hMSC : IsSCp p ⊤ M := by
    refine ⟨le_top, hMel, fun F' _ hF'el hMF' => ?_⟩
    by_contra hne
    exact hMmax F' ⟨hFM.trans hMF', hF'el⟩ (lt_of_le_of_ne hMF' (Ne.symm hne))
  have hrkle : ∀ {U V : Subgroup X}, IsElemAbelian p U → IsElemAbelian p V → U ≤ V →
      CFSG.Open.pRank p U ≤ CFSG.Open.pRank p V := by
    intro U V hU hV hUV
    have h1 := Subgroup.card_le_of_le hUV
    rw [Inputs27.card_eq_pow_pRank hp hU, Inputs27.card_eq_pow_pRank hp hV] at h1
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have hM3 : 3 ≤ CFSG.Open.pRank p M := by
    have h1 : p ≤ n / p ^ (r - 1) := by
      rw [Nat.le_div_iff_mul_le (pow_pos hp.pos _), ← pow_succ', show r - 1 + 1 = r by omega]
      omega
    have h2 : 2 * 3 ≤ (r - 1) * (n / p ^ (r - 1)) := Nat.mul_le_mul (by omega) (hp3.trans h1)
    have h3 := hrkle hPel hMel (le_sup_left.trans hFM)
    omega
  have hEM3 : 3 ≤ CFSG.Open.pRank p (E ⊓ M) := by
    have hEMel : IsElemAbelian p (E ⊓ M) := CFSG.Open.IsElemAbelian.mono hE.2.1 inf_le_left
    have h1 := Subgroup.card_le_of_le (le_inf hE₁E (le_sup_right.trans hFM) : E₁ ≤ E ⊓ M)
    rw [hE₁c, Inputs27.card_eq_pow_pRank hp hEMel] at h1
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    omega
  have hmono : GLBCore p 2 P ≤ GLBCore p 2 M :=
    sSup_le_sSup fun N ⟨Q, hQP, hQ2, hN⟩ => ⟨Q, hQP.trans (le_sup_left.trans hFM), hQ2, hN⟩
  exact ⟨M, hMSC, hM3, Inputs27.isKConnectedIn_of_inter hp hE.2.1 hMel hEM3, hKP.trans hmono⟩

end AltRegular

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273
