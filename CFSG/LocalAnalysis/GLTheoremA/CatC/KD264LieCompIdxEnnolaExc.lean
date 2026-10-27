module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatDispatch
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaRatTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcEnnolaOrbit
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaTrans
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.StandardType.RecipeExcLang
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped MatrixGroups
open ExcUntw CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem compIdxEnnolaAt_adjointGroup
    {τ : Tag} (hres : ExcUntwRationalCatalogueExpAt τ) (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hinn : ∀ β : MulAut ↥(adjointGroup τ K), β ∈ innAutDerived ↥(adjointGroup τ K) →
      β ^ p = 1 → β ≠ 1 → ∃ h ∈ inndiagGroup τ K,
        (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ p = 1 ∧ h ≠ 1)
    {d : TauCeti.LieTypeIndex} (hdc : d.characteristic = ringChar K)
    (hdf : fieldSize d = Nat.card K) : CompIdxEnnolaAt p d ↥(adjointGroup τ K) := by
  classical
  intro β hβmem hβp hβ1 J hJ
  obtain ⟨h, hh, hβh, hp1, hh1⟩ := hinn β hβmem hβp hβ1
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hcardK⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcardK
  have hpK : ¬ p ∣ Nat.card K := fun hd => hp.not_dvd_one ((Nat.dvd_add_iff_right hd).2 hpq)
  have hpℓ : p ≠ ringChar K := fun h' => hpK (by rw [hK, ← h']; exact dvd_pow_self p f.ne_zero)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ f.pos hp hp2 hpℓ
  have hp₀K : ¬ p₀ ∣ Nat.card K := fun hd =>
    hp₀ℓ ((Nat.prime_dvd_prime_iff_eq hp₀ hℓ).1 (hp₀.dvd_of_dvd_pow (hK ▸ hd)))
  have hq₀' : 5 ≤ p₀ ∨ 4 ≤ Nat.card K := by rw [hK]; exact hq₀
  have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hmon : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with rfl | rfl | rfl <;> simp) hp hp2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h' | h' | h'
    all_goals exact single_edge_perfect τ K (by simp [h'])
  obtain ⟨S, a, ι, hSq, ⟨Fr, hFr1, hFr2⟩, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ5 hp hpK hp₀ hp₀K hq₀' hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  have hℓL : ringChar (AlgebraicClosure K) = ringChar K := ringChar_algebraicClosure K
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hp (by rw [hℓL]; exact hpℓ.symm)
  have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ S.D.q := by
    intro hG2
    rcases hτ with h' | h' | h'
    exacts [absurd (hG2.symm.trans h') (fun hh => by cases hh),
      absurd (hG2.symm.trans h') (fun hh => by cases hh),
      absurd (hG2.symm.trans h') (fun hh => by cases hh)]
  have hTame := langSetup_hTame_of_prime S hp hpL hsmall hT hap h1
  obtain ⟨i, hqs, hJR⟩ := components_of_langSetup S hp ι hinj hrange β hconj hT hap h1 hTame hJ
  obtain ⟨j, hj, hcat⟩ := hres (AlgebraicClosure K) p₀ S
    ⟨Fr, fun c => by rw [hSq]; exact hFr1 c, hFr2⟩ p hp hp2 a hT hap h1 i hqs
  have hodd : Odd (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    obtain ⟨w, hn⟩ := S.D.n_weyl
    rcases hτ with rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.GLTheoremA.I167.ennola_orbitLength_odd_untw (k := .F4) hp hp2
        (Or.inl rfl) (S := S) (w := w)
        (fun γ hγ => S.rho_eq_smul_of_frob (fun c => by rw [hSq]; exact hFr1 c) hFr2 hn hγ)
        hT hap (by rw [hSq]; exact hpq) i
    · exact CFSG.LocalAnalysis.GLTheoremA.I167.ennola_orbitLength_odd_untw (k := .E7) hp hp2
        (Or.inr (Or.inl rfl)) (S := S) (w := w)
        (fun γ hγ => S.rho_eq_smul_of_frob (fun c => by rw [hSq]; exact hFr1 c) hFr2 hn hγ)
        hT hap (by rw [hSq]; exact hpq) i
    · exact CFSG.LocalAnalysis.GLTheoremA.I167.ennola_orbitLength_odd_untw (k := .E8) hp hp2
        (Or.inr (Or.inr rfl)) (S := S) (w := w)
        (fun γ hγ => S.rho_eq_smul_of_frob (fun c => by rw [hSq]; exact hFr1 c) hFr2 hn hγ)
        hT hap (by rw [hSq]; exact hpq) i
  have hjodd : Odd j := by
    rcases hj with hj | hj
    · rw [hj]; exact hodd
    · rw [hj]; exact ⟨0, by norm_num⟩
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  obtain ⟨i', ⟨φ⟩, hidx⟩ := hcat.of_mulEquiv eJ.symm
  refine ⟨i', ⟨φ⟩, j, hjodd, ?_⟩
  rw [hdc, hdf, ← hSq, ← hℓL]
  exact hidx

theorem compIdxEnnolaAt_excUntw_of_rationalCatalogueExpAt
    (d : TauCeti.ValidLieTypeIndex) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ fieldSize d.1 + 1)
    (hF4 : (∃ q, d.1 = .F4 q) → ExcUntwRationalCatalogueExpAt .F4)
    (hE7 : (∃ q, d.1 = .E7 q) → ExcUntwRationalCatalogueExpAt .E7)
    (hE8 : (∃ q, d.1 = .E8 q) → ExcUntwRationalCatalogueExpAt .E8)
    (hP : (∃ q, d.1 = .F4 q) ∨ (∃ q, d.1 = .E7 q) ∨ (∃ q, d.1 = .E8 q)) :
    CompIdxEnnolaAt p d.1 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨e, hv⟩ := d
  cases e with
  | F4 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    haveI := hKc
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hpqK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    exact compIdxEnnolaAt_of_mulEquiv eK.symm
      (compIdxEnnolaAt_adjointGroup (hF4 ⟨q, rfl⟩) (τ := .F4) (Or.inl rfl) hp hp2 hpqK
        (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_F4 β hβ hβp hβ1)
        (by simp [hchar]) (by rw [hK]; rfl))
  | E7 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    haveI := hKc
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hpqK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    exact compIdxEnnolaAt_of_mulEquiv eK.symm
      (compIdxEnnolaAt_adjointGroup (hE7 ⟨q, rfl⟩) (τ := .E7) (Or.inr (Or.inl rfl)) hp hp2 hpqK
        (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_E (Or.inr (Or.inl rfl)) hp β hβ
          hβp hβ1)
        (by simp [hchar]) (by rw [hK]; rfl))
  | E8 q =>
    obtain ⟨K, _, _, hK, hKc, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    haveI := hKc
    have hchar : ringChar K = q.p := ringChar.eq K q.p
    have hpqK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    exact compIdxEnnolaAt_of_mulEquiv eK.symm
      (compIdxEnnolaAt_adjointGroup (hE8 ⟨q, rfl⟩) (τ := .E8) (Or.inr (Or.inr rfl)) hp hp2 hpqK
        (fun β hβ hβp hβ1 => exists_inndiag_of_mem_innAutDerived_E (Or.inr (Or.inr rfl)) hp β hβ
          hβp hβ1)
        (by simp [hchar]) (by rw [hK]; rfl))
  | _ =>
    exfalso
    rcases hP with ⟨q', h'⟩ | ⟨q', h'⟩ | ⟨q', h'⟩ <;> cases h'

theorem compIdxEnnolaAt_cat_twistedE6_of_rational
    (hres : TwistedE6RationalCatalogueExp) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q.card + 1) :
    CompIdxEnnolaAt p (.twistedE6 q) (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  classical
  obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  refine compIdxEnnolaAt_of_mulEquiv eK.symm ?_
  intro β hβ hβp hβ1 J hJ
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK σ
      hσ
  have hKf : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic q.prime_p K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcyc.isMulCommutative.is_comm.comm _ _
  have hmem : β ∈ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj, ← hker]
    exact hΘ hβ
  obtain ⟨h, rfl⟩ := hmem
  have hp1 : h ^ p = 1 := twistedE6InndiagConj_injective q.prime_p q.exponent_pos hK σ hσ
    (by rw [map_pow, hβp, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
  have hpne : p ≠ q.p := by
    intro hpqp
    have hdvd : p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def, hpqp]
      exact dvd_pow_self q.p (by have := q.exponent_pos; omega)
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right hdvd).2 hpq)
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_setup_prime q.prime_p
      q.exponent_pos hp hp2 hpne
  have hmon : MonomialToralAt Tag.E6 p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_exc
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E6_five
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.monomialToralAt_E7_five
      (by simp) hp hp2
  obtain ⟨S, a, ι, hSq, hΦ, hT, hap, h1, hinj, hrange, hconj⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_langSetup_of_inndiag_twE6_of_prime
      q.prime_p q.exponent_pos hK σ hσ hp hpne hp₀ hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ h)
      (h : ModGL TwistTag.E6.tag K) h.2 (twistedE6InndiagConj_apply h)
      (by rw [← Subgroup.coe_pow, hp1]; rfl) (fun h' => hh1 (Subtype.ext h'))
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime S hp
    (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.natCast_ne_zero_algebraicClosure_of_ne
      q.prime_p hp hK hpne) (fun h => absurd h (by decide)) hT hap h1
  obtain ⟨i, hqi, hJR⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup
    S hp ι hinj hrange _ hconj hT hap h1 hTame hJ
  obtain ⟨Fr, hFr, hFΦ⟩ := hΦ
  obtain ⟨j, hj, hcat⟩ := hres (AlgebraicClosure K) p₀ S
    ⟨Fr, fun c => by rw [hSq]; exact hFr c, hFΦ⟩ p hp hp2 a hT hap h1 i hqi
  obtain ⟨w, -, hw⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.d4t2out_rho_eq S
      ⟨TwistTag.E6, rfl, Fr, (fun c => by rw [hSq]; exact hFr c), (fun g => by rw [hFΦ]; rfl)⟩
  have hodd : Odd (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
    CFSG.LocalAnalysis.GLTheoremA.I167.ennola_orbitLength_odd_twE6 hp hp2 (S := S) (w := w) hw hT
      hap (by rw [hSq, ← TauCeti.PrimePower.card_def]; exact hpq) i
  have hjodd : Odd j := by
    rcases hj with hj | hj
    · rw [hj]; exact hodd
    · rw [hj]; exact ⟨0, by norm_num⟩
  let eJ : ↥J ≃* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (J.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hJR)
  obtain ⟨i', ⟨φ⟩, hidx⟩ := hcat.of_mulEquiv eJ.symm
  have hℓL : ringChar (AlgebraicClosure K) = q.p := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_algebraicClosure]
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow
      (n := q.exponent * 2) q.prime_p (by have := q.exponent_pos; omega)
      (by rw [hK, ← pow_mul])
  refine ⟨i', ⟨φ⟩, j, hjodd, ?_⟩
  rw [TauCeti.LieTypeIndex.characteristic_twistedE6, ← hℓL]
  have hfs : fieldSize (.twistedE6 q) = S.D.q := by
    rw [hSq]
    simp only [fieldSize, TauCeti.PrimePower.card_def]
  rw [hfs]
  exact hidx

theorem lieCompIdxEnnola_exc
    : LieCompIdxEnnola isExcEnnolaIdx := by
  intro d p hp hp2 hpq hP
  rcases hP with hF4 | hE7 | hE8 | hE6
  · rcases hF4 with ⟨q, hq⟩
    exact compIdxEnnolaAt_excUntw_of_rationalCatalogueExpAt d hp hp2 hpq
      (fun _ => excUntwRationalCatalogueExpAt_F4)
      (fun _ => excUntwRationalCatalogueExpAt_E7)
      (fun _ => excUntwRationalCatalogueExpAt_E8)
      (Or.inl ⟨q, hq⟩)
  · rcases hE7 with ⟨q, hq⟩
    exact compIdxEnnolaAt_excUntw_of_rationalCatalogueExpAt d hp hp2 hpq
      (fun _ => excUntwRationalCatalogueExpAt_F4)
      (fun _ => excUntwRationalCatalogueExpAt_E7)
      (fun _ => excUntwRationalCatalogueExpAt_E8)
      (Or.inr (Or.inl ⟨q, hq⟩))
  · rcases hE8 with ⟨q, hq⟩
    exact compIdxEnnolaAt_excUntw_of_rationalCatalogueExpAt d hp hp2 hpq
      (fun _ => excUntwRationalCatalogueExpAt_F4)
      (fun _ => excUntwRationalCatalogueExpAt_E7)
      (fun _ => excUntwRationalCatalogueExpAt_E8)
      (Or.inr (Or.inr ⟨q, hq⟩))
  · rcases hE6 with ⟨q, hq⟩
    obtain ⟨e, hv⟩ := d
    subst hq
    exact compIdxEnnolaAt_cat_twistedE6_of_rational twistedE6RationalCatalogueExp_holds q hv hp hp2
      (by simpa only [fieldSize] using hpq)

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
