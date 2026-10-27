module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141f
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.ReeTransport
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.GH74.GLS.Balance.OResidual
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTLargeReeComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141e2
import CFSG.LieType.SeitzGeneration.HeisSmallModel

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2323b
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)

open scoped commutatorElement

theorem card_fixSubfield_pow {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) ^ orderOf σ = Nat.card K := by
  have h : CFSG.LieType.Chevalley.fixSubfield σ = CFSG.GH74.GLS.IVK.fixedField σ := by
    ext x
    rw [CFSG.GH74.GLS.IVK.mem_fixedField_iff]
    exact Iff.rfl
  rw [h]
  exact CFSG.GH74.GLS.IVK.fixedField_card_pow σ

theorem four_le_card_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ≤ Nat.card K) :
    4 ≤ Nat.card K := by
  have h2 := Inputs141e.two_dvd_card_of_charTwo (K := K)
  rcases (show Nat.card K = 3 ∨ 4 ≤ Nat.card K by omega) with h | h
  · rw [h] at h2
    omega
  · exact h

section Untw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.RecipeExcLang

theorem twoInCoreLayer_of_langSetup_congr (hout : LangOuterTwo) {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S' : LangSetup τ (AlgebraicClosure K) p₀) {S C : Type} [Group S]
    [Finite S] [Group C] (e : S ≃* C) (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S'.Γ) (β : MulAut S) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (MulAut.congr e β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S'.D.torus) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (hexc : ¬ (τ = .F4 ∧ S'.D.q = 2 ∧ p = 5)) (hG2 : τ = .G2 → 4 ≤ S'.D.q) :
    TwoInCoreLayer p β := by
  have hrange' : (ι.comp e.toMonoidHom).range = S'.Γ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map, hrange]
  refine twoInCoreLayer_of_langSetup S' hout hK2 (ι.comp e.toMonoidHom) (hι.comp e.injective) hrange' β
    (fun s => ?_) hT hp hp5 hap h1 hexc hG2
  have h := hβ (e s)
  change ι (e (β (e.symm (e s)))) = _ at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h

theorem twoInCoreLayer_untw_inndiag (hout : LangOuterTwo) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hG2 : τ = .G2 → 3 ≤ Nat.card K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hexc5 : ¬ (τ = .F4 ∧ Nat.card K = 2 ∧ p = 5)) (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hh : h ∈ inndiagGroup τ K) (hβh : ∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹)
    (hp1 : h ^ p = 1) (hh1 : h ≠ 1) : TwoInCoreLayer p β := by
  have hp2 : p ≠ 2 := by omega
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h' | h' | h' | h' | h'
    · subst h'
      exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K (hG2 rfl)).commutator_eq_top
    all_goals exact single_edge_perfect τ K (by simp [h'])
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h' | h' | h' | h' | h' <;> simp [h']) hp hp2
  have hpK : ¬ p ∣ Nat.card K := Inputs141e.not_dvd_card_of_charTwo hp hp2
  obtain ⟨S', a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw hτ hp hpK (Or.inl hp5) hmon hperf β h
      (baseChange_mem_adjointGroup_of_mem_inndiag hh) hβh hp1 hh1
  refine twoInCoreLayer_of_langSetup S' hout hK2 ι hinj hrange β hconj hT hp hp5 hap h1 ?_ ?_
  · rw [hSq]
    exact hexc5
  · intro hτG2
    rw [hSq]
    exact four_le_card_of_charTwo (hG2 hτG2)

theorem twoInCoreLayer_untw_field {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hexc7 : ¬ (τ = .G2 ∧ Nat.card K = 2 ^ 7 ∧ p = 7)) (g : adjointGroup τ K)
    (a : Fin τ.rank → Kˣ) (σ : K ≃+* K) (hσ : σ ≠ 1) (hσp : σ ^ p = 1)
    (hα : (MulAut.conj g * exactNormalAut τ K a σ 0) ^ p = 1) :
    TwoInCoreLayer p (MulAut.conj g * exactNormalAut τ K a σ 0) := by
  obtain ⟨ψ, hψ⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_conj_eq_entrywiseAdjointAut τ hp
    g a σ hσ hσp hα
  refine twoInCoreLayer_of_conj ψ hp ?_
  rw [hψ]
  refine twoInCoreLayer_entrywiseAdjointAut τ σ hp hp5 fun hτG2 hk2 hp7 => hexc7 ⟨hτG2, ?_, hp7⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ
  have h1 := card_fixSubfield_pow σ
  rw [hord, hk2, hp7] at h1
  exact h1.symm

theorem twoInCoreLayer_untw (hout : LangOuterTwo) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hG2 : τ = .G2 → 3 ≤ Nat.card K) {S : Type} [Group S] [Finite S] (e : S ≃* ↥(adjointGroup τ K))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hexc5 : ¬ (τ = .F4 ∧ Nat.card K = 2 ∧ p = 5))
    (hexc7 : ¬ (τ = .G2 ∧ Nat.card K = 2 ^ 7 ∧ p = 7)) (β : MulAut S) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    TwoInCoreLayer p β := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hβ' : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  refine twoInCoreLayer_of_congr e hp ?_
  set β' := MulAut.congr e β with hβ'def
  have hFG : τ = .F4 ∨ τ = .G2 → TwoInCoreLayer p β' := by
    intro hτFG
    obtain ⟨g, σ, hβe, hσp⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_form_FG hτFG hG2 hp hp2 β' hβ'
    by_cases hσ : σ = 1
    · subst hσ
      rw [exactNormalAut_one_one_zero, mul_one] at hβe
      have hgp : g ^ p = 1 := by
        have : MulAut.conj (g ^ p) = MulAut.conj 1 := by rw [map_pow, ← hβe, hβ', map_one]
        exact mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot this
      have hg1 : (g : ModGL τ K) ≠ 1 := fun h1 => hβ1' (by
        have : g = 1 := Subtype.ext h1
        rw [hβe, this, map_one])
      refine twoInCoreLayer_untw_inndiag hout hτ hG2 hp hp5 hexc5 β' (g : ModGL τ K)
        (adjointGroup_le_inndiagGroup g.2) (fun c => ?_) ?_ hg1
      · rw [hβe]
        simp [MulAut.conj_apply]
      · rw [← Subgroup.coe_pow, hgp]
        rfl
    · rw [hβe] at hβ' ⊢
      exact twoInCoreLayer_untw_field hp hp5 hexc7 g 1 σ hσ hσp hβ'
  have hE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → TwoInCoreLayer p β' := by
    intro hτE
    obtain ⟨g, a, σ, hβe, hσp⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_form_E hτE hp hp2 β' hβ'
    by_cases hσ : σ = 1
    · subst hσ
      have hβw : ∀ c : adjointGroup τ K, (β' c : ModGL τ K) =
          ((g : ModGL τ K) * rootDiagUnit τ a) * c * ((g : ModGL τ K) * rootDiagUnit τ a)⁻¹ := by
        intro c
        have e1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (c : ModGL τ K) = c :=
          Units.ext (entrywise_id _)
        rw [hβe, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero, inv_one, mul_inv_rev, e1]
        simp only [mul_assoc, mul_one]
      have hw : (g : ModGL τ K) * rootDiagUnit τ a ∈ inndiagGroup τ K :=
        mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
      obtain ⟨h', hh', hβh', hh'p⟩ := exists_inndiag_pow_eq_one hτE hp β' hβ' hw hβw
      have hh1 : h' ≠ 1 := by
        rintro rfl
        apply hβ1'
        refine MulEquiv.ext fun c => Subtype.ext ?_
        rw [hβh' c]
        simp
      exact twoInCoreLayer_untw_inndiag hout hτ hG2 hp hp5 hexc5 β' h' hh' hβh' hh'p hh1
    · rw [hβe] at hβ' ⊢
      exact twoInCoreLayer_untw_field hp hp5 hexc7 g a σ hσ hσp hβ'
  rcases hτ with h | h | h | h | h
  · exact hFG (Or.inr h)
  · exact hFG (Or.inl h)
  · exact hE (Or.inl h)
  · exact hE (Or.inr (Or.inl h))
  · exact hE (Or.inr (Or.inr h))

end Untw

section Twisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.RecipeExcLang

theorem twoInCoreLayer_twE6 (hout : LangOuterTwo) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {S : Type} [Group S]
    [Finite S] (e : S ≃* ↥(twistedE6RootGroup K σ)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (β : MulAut S)
    (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : TwoInCoreLayer p β := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero))
  have hp2 : p ≠ 2 := by omega
  have hK2 : ringChar K = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := f * 2) Nat.prime_two
      (by omega) (by rw [hK, ← pow_mul])
  have hβ' : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  by_cases hΘβ : Θ (MulAut.congr e β) = 1
  ·
    have hmem : MulAut.congr e β ∈ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨h, hh⟩ := hmem
    have hp1 : h ^ p = 1 :=
      twistedE6InndiagConj_injective Nat.prime_two hf hK σ hσ (by rw [map_pow, hh, hβ', map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1' (by rw [← hh, h', map_one])
    have hmon : MonomialToralAt Tag.E6 p :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
    obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two hf hK σ hσ hp hp2 hp hp2 (Or.inl hp5)
        hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
        (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
        (fun h' => hh1 (Subtype.ext h'))
    rw [hh] at hconj
    exact twoInCoreLayer_of_langSetup_congr hout hK2 S' e ι hinj hrange β hconj hT hp hp5 hap h1
      (fun h => absurd h.1 (by decide)) (fun h => absurd h (by decide))
  ·
    exact twoInCoreLayer_of_congr e hp (twoInCoreLayer_twE6_field hf hK σ hσ Θ hΘ hp hp5 _ hβ' hΘβ)

theorem twoInCoreLayer_triD4 (hout : LangOuterTwo) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {S : Type} [Group S]
    [Finite S] (e : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (β : MulAut S) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : TwoInCoreLayer p β := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hK2 : ringChar K = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := f * 3) Nat.prime_two
      (by omega) (by rw [hK, ← pow_mul])
  have hβ' : MulAut.congr e β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨hZ, -, Θ, hΘ, hker⟩ :=
    CFSG.RankThree.Chevalley.triality_normal_form_data Nat.prime_two hf K hK σ hσ
  by_cases hΘβ : Θ (MulAut.congr e β) = 1
  ·
    have hmem : MulAut.congr e β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rw [← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨x, hx⟩ := hmem
    have hxp : x ^ p = 1 :=
      mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hx, hβ', map_one])
    have hx1 : x ≠ 1 := fun h' => hβ1' (by rw [← hx, h', map_one])
    have hmon : MonomialToralAt Tag.D4 p :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
    obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_triD4_of_prime Nat.prime_two hf hK σ hσ hp hp2 hp hp2 (Or.inl hp5) hmon x hxp hx1
    rw [hx] at hconj
    exact twoInCoreLayer_of_langSetup_congr hout hK2 S' e ι hinj hrange β hconj hT hp hp5 hap h1
      (fun h => absurd h.1 (by decide)) (fun h => absurd h (by decide))
  ·
    have hout' : MulAut.congr e β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun hmem =>
      hΘβ (by rw [← MonoidHom.mem_ker, hker]; exact hmem)
    exact twoInCoreLayer_of_congr e hp
      (twoInCoreLayer_triD4_field Nat.prime_two hf hK σ hσ hp hp5 Θ hΘ hβ' hβ1' hout')

end Twisted

section ExcAssembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem input14_1BadSimpleOn_exceptional (hout : LangOuterTwo) :
    Input14_1BadSimpleOn fun p d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional ∧
      ¬ (p = 5 ∧ ∃ q, d = TauCeti.LieTypeIndex.F4 q ∧ q.card = 2) ∧
      ¬ (p = 7 ∧ ∃ q, d = TauCeti.LieTypeIndex.G2 q ∧ q.card = 2 ^ 7) := by
  intro p hp hp5 S _ _ _ _ idx hd hchar he β hβ hβ1
  obtain ⟨hF, hex5, hex7⟩ := hd
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | E6 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_E6 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact twoInCoreLayer_untw hout (τ := .E6) (by simp) (fun h => absurd h (by decide)) (e.trans eK) hp hp5
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide)) β hβ hβ1
  | E7 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_E7 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact twoInCoreLayer_untw hout (τ := .E7) (by simp) (fun h => absurd h (by decide)) (e.trans eK) hp hp5
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide)) β hβ hβ1
  | E8 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_E8 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact twoInCoreLayer_untw hout (τ := .E8) (by simp) (fun h => absurd h (by decide)) (e.trans eK) hp hp5
      (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide)) β hβ hβ1
  | F4 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_F4 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    refine twoInCoreLayer_untw hout (τ := .F4) (by simp) (fun h => absurd h (by decide)) (e.trans eK) hp hp5
      (fun h => hex5 ⟨h.2.2, q, rfl, hK ▸ h.2.1⟩) (fun h => absurd h.1 (by decide)) β hβ hβ1
  | G2 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_G2 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact twoInCoreLayer_untw hout (τ := .G2) (by simp) (fun _ => hK ▸ hr) (e.trans eK) hp hp5
      (fun h => absurd h.1 (by decide)) (fun h => hex7 ⟨h.2.2, q, rfl, hK ▸ h.2.1⟩) β hβ hβ1
  | twistedE6 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_twistedE6 q]; exact hchar
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    rw [hq2] at hK hσ
    exact twoInCoreLayer_twE6 hout q.exponent_pos hK σ hσ (e.trans eK) hp hp5 β hβ hβ1
  | trialityD4 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_trialityD4 q]; exact hchar
    obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
    rw [hq2] at hK hσ
    exact twoInCoreLayer_triD4 hout q.exponent_pos hK σ hσ (e.trans eK) hp hp5 β hβ hβ1
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

end ExcAssembly

section Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem twoInCoreLayer_reeGamma_F4_inner {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = p) : TwoInCoreLayer p (MulAut.conj y) := by
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNC, hN2, -, hcomp, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.largeRee_component_chev ha hK hp (by omega) y hy
  have hC := CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj y
  intro x hx hx2
  rw [hC] at hx ⊢
  have hxN : x ∈ N := by
    refine hN2 x hx ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hx2 ⟨x, Subgroup.mem_zpowers x⟩
    exact ⟨k, (Subgroup.orderOf_mk x (Subgroup.mem_zpowers x)).symm.trans hk⟩
  by_cases hN : N = ⊥
  · rw [hN, Subgroup.mem_bot] at hxN
    rw [hxN]
    exact one_mem _
  · obtain ⟨hle, hq, hsub⟩ := hcomp hN
    exact le_core_sup_layer_of_isComponentOf hp
      ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub,
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hq⟩ hxN

theorem coprime_35942400 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h5 : p ≠ 5) (h13 : p ≠ 13) :
    Nat.Coprime p 35942400 := by
  rw [show (35942400 : ℕ) = (2 ^ 12 * 3 ^ 3) * (5 ^ 2 * 13) by norm_num]
  refine Nat.Coprime.mul_right (coprime_two_pow_mul_three_pow hp hp5 12 3) (Nat.Coprime.mul_right ?_ ?_)
  · exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_five).2 h5)
  · exact (Nat.coprime_primes hp (by norm_num)).2 h13

theorem twoInCoreLayer_reeGamma_F4_field {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hexc : ¬ (2 * a + 1 = p ∧ (p = 5 ∨ p = 13))) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    TwoInCoreLayer p (ReeTag.F4.reeGammaFieldAut K a σ) := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_fieldAut_equiv' hK hp hp2 σ hσ
  haveI := hchar
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL ReeTag.F4.tag (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) := Subtype.finite
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
    have hap : 2 * a + 1 = p := by
      have h1 := card_fixSubfield_pow σ
      rw [hσ, hk2, hK] at h1
      exact (Nat.pow_right_injective le_rfl h1).symm
    have hcard := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion 0
      (fixSubfield σ) (by simpa using hkcard)).1
    refine twoInCoreLayer_of_coprime_fixSubgroup hp ?_
    rw [Nat.card_congr eC.toEquiv, hcard]
    norm_num
    exact coprime_35942400 hp hp5 (fun h => hexc ⟨hap, Or.inl h⟩) (fun h => hexc ⟨hap, Or.inr h⟩)
  ·
    haveI hs : IsSimpleGroup ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hkcard
    have hperf : commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊤ :=
      ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hkcard
    have hnc : ∃ x y : ↥(ReeTag.F4.reeGamma (fixSubfield σ) b), x * y ≠ y * x := by
      by_contra hab
      push Not at hab
      have hc : commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      rw [hperf] at hc
      exact top_ne_bot hc
    haveI : IsSimpleGroup ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := eC.isSimpleGroup
    have hnc' : ∃ x y : ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)), x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := hnc
      exact ⟨eC.symm x, eC.symm y, fun h => hxy (eC.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
    exact twoInCoreLayer_of_isQuasisimple_fixSubgroup hp
      (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hnc')

theorem twoInCoreLayer_reeGamma_F4 {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hexc : ¬ (2 * a + 1 = p ∧ (p = 5 ∨ p = 13))) {β : MulAut (ReeTag.F4.reeGamma K a)} (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) : TwoInCoreLayer p β := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_inner_or_field ha hK hp hβ hβ1 with
    ⟨y, rfl, hy, hy1⟩ | ⟨σ, g, hσ, rfl⟩
  · exact twoInCoreLayer_reeGamma_F4_inner ha hK hp hp5 y (orderOf_eq_prime hy hy1)
  · refine twoInCoreLayer_of_conj (MulAut.conj g)⁻¹ hp ?_
    rw [show (MulAut.conj g)⁻¹ * (MulAut.conj g * ReeTag.F4.reeGammaFieldAut K a σ * (MulAut.conj g)⁻¹) *
      (MulAut.conj g)⁻¹⁻¹ = ReeTag.F4.reeGammaFieldAut K a σ by group]
    exact twoInCoreLayer_reeGamma_F4_field hK hp hp5 hexc σ hσ

theorem input14_1BadSimpleOn_reeF4 :
    Input14_1BadSimpleOn fun p d => ∃ m, d = TauCeti.LieTypeIndex.reeF4 m ∧ ¬ (p = 5 ∧ m = 2) ∧
      ¬ (p = 13 ∧ m = 6) := by
  intro p hp hp5 S _ _ _ _ idx hd _ he β hβ hβ1
  obtain ⟨d, hv⟩ := idx
  obtain ⟨m, rfl, hex5, hex13⟩ := hd
  obtain ⟨e⟩ := he
  have hm : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (GaloisField 2 (2 * m + 1)) ReeTag.F4.prime :=
    (inferInstance : CharP (GaloisField 2 (2 * m + 1)) 2)
  have hK : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) := by
    rw [GaloisField.card 2 (2 * m + 1) (by omega)]
  obtain ⟨eK⟩ := CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeGamma_equiv_cat_of_card hm hv hK
  refine twoInCoreLayer_of_congr (e.trans eK) hp (twoInCoreLayer_reeGamma_F4 hm hK hp hp5 ?_ ?_ ?_)
  · rintro ⟨hpm, h5 | h13⟩
    · exact hex5 ⟨h5, by omega⟩
    · exact hex13 ⟨h13, by omega⟩
  · rw [← map_pow, hβ, map_one]
  · intro h
    exact hβ1 ((MulAut.congr (e.trans eK)).injective (h.trans (map_one _).symm))

end Ree

section BadGroup

theorem eq_one_of_mem_center_of_twoGen {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hgen : ∀ H : Subgroup G, (∀ g : G, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ H) → H = ⊤)
    (P : Sylow p G) (hP : ∀ a b : ↥(P : Subgroup G), a * b = b * a) {c : G}
    (hc : c ∈ Subgroup.center G) {e : ℕ} (hce : c ^ (p ^ e) = 1) : c = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hker : ((Abelianization.of : ↥(P : Subgroup G) →* Abelianization ↥(P : Subgroup G)).transfer).ker =
      ⊤ := by
    refine hgen _ fun g hg => ?_
    obtain ⟨k, hk⟩ := hg
    rw [MonoidHom.mem_ker]
    set V := (Abelianization.of : ↥(P : Subgroup G) →* Abelianization ↥(P : Subgroup G)).transfer
    have h2 : V g ^ (2 ^ k) = 1 := by rw [← map_pow, hk, map_one]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_surjective (V g)
    obtain ⟨n, hn⟩ := P.isPGroup' h
    have hpn : V g ^ (p ^ n) = 1 := by
      rw [← hh]
      change (Abelianization.of h) ^ (p ^ n) = 1
      rw [← map_pow, hn, map_one]
    have hcop : Nat.Coprime (2 ^ k) (p ^ n) :=
      Nat.Coprime.pow k n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one hpn))
  have key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * c ^ k * g₀ ∈ (P : Subgroup G) → g₀⁻¹ * c ^ k * g₀ = c ^ k := by
    intro k g₀ _
    rw [Subgroup.mem_center_iff.mp (pow_mem hc k) g₀⁻¹, inv_mul_cancel_right]
  have h1 := MonoidHom.transfer_eq_pow
    (Abelianization.of : ↥(P : Subgroup G) →* Abelianization ↥(P : Subgroup G)) c key
  have h2 : c ∈ ((Abelianization.of : ↥(P : Subgroup G) →* Abelianization ↥(P : Subgroup G)).transfer).ker := by
    rw [hker]
    exact Subgroup.mem_top c
  rw [MonoidHom.mem_ker, h1, ← MonoidHom.mem_ker, Abelianization.ker_of] at h2
  have hcomm : commutator ↥(P : Subgroup G) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hP y x
  rw [hcomm, Subgroup.mem_bot] at h2
  have hci : c ^ (P : Subgroup G).index = 1 := by
    have := congrArg Subtype.val h2
    simpa using this
  have hnd : ¬ p ∣ (P : Subgroup G).index := P.not_dvd_index
  have hcop : Nat.Coprime (p ^ e) (P : Subgroup G).index :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hce)
    (orderOf_dvd_of_pow_eq_one hci))

theorem eq_top_of_two_elements {E : Type} [Group E] [Finite E] [IsSimpleGroup E] (h2 : 2 ∣ Nat.card E)
    (H : Subgroup E) (hH : ∀ x : E, (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ H) : H = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalClosure {x : E | ∃ k : ℕ, x ^ (2 ^ k) = 1} with hN
  have hNH : N ≤ H := by
    show Subgroup.closure (Group.conjugatesOfSet {x : E | ∃ k : ℕ, x ^ (2 ^ k) = 1}) ≤ H
    rw [Subgroup.closure_le]
    intro y hy
    rw [Group.mem_conjugatesOfSet_iff] at hy
    obtain ⟨x, ⟨k, hk⟩, hxy⟩ := hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
    refine hH _ ⟨k, ?_⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxN : x ∈ N := Subgroup.subset_normalClosure ⟨1, by rw [pow_one, ← hx, pow_orderOf_eq_one]⟩
  haveI : N.Normal := Subgroup.normalClosure_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.mem_bot] at hxN
    rw [hxN, orderOf_one] at hx
    norm_num at hx
  · exact top_le_iff.1 (h ▸ hNH)

theorem commutatorElement_mul_mem_center {G : Type*} [Group G] {a b c d : G} (hc : c ∈ Subgroup.center G)
    (hd : d ∈ Subgroup.center G) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' : ∀ g, c * g = g * c := fun g => (Subgroup.mem_center_iff.1 hc g).symm
  have hd' : ∀ g, d * g = g * d := fun g => (Subgroup.mem_center_iff.1 hd g).symm
  calc ⁅a * c, b * d⁆ = a * (c * (b * d * c⁻¹)) * a⁻¹ * (d⁻¹ * b⁻¹) := by
        rw [commutatorElement_def]; group
    _ = a * (b * d * c⁻¹ * c) * a⁻¹ * (d⁻¹ * b⁻¹) := by rw [hc']
    _ = a * b * (d * (a⁻¹ * d⁻¹)) * b⁻¹ := by group
    _ = a * b * (a⁻¹ * d⁻¹ * d) * b⁻¹ := by rw [hd']
    _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group

theorem conj_mem_commutator_of_normalizes {G : Type*} [Group G] {H : Subgroup G} {g x : G}
    (hg : ∀ y ∈ H, g * y * g⁻¹ ∈ H) (hg' : ∀ y ∈ H, g⁻¹ * y * g ∈ H) (hx : x ∈ ⁅H, H⁆) :
    g * x * g⁻¹ ∈ ⁅H, H⁆ := by
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hg y hy
    · intro y hy
      refine ⟨g⁻¹ * y * g, hg' y hy, ?_⟩
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
  have h1 : (⁅H, H⁆).map (MulAut.conj g).toMonoidHom = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, hmap]
  have h2 : (MulAut.conj g).toMonoidHom x ∈ (⁅H, H⁆).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [h1] at h2
  exact h2

theorem isQuasisimple_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : CFSG.Open.IsQuasisimple G) : CFSG.Open.IsQuasisimple H := by
  obtain ⟨hp, hs⟩ := hG
  have hc : (Subgroup.center G).map (e : G →* H) = Subgroup.center H := Subgroup.map_center_eq e
  refine ⟨?_, (QuotientGroup.congr _ _ e hc).symm.isSimpleGroup⟩
  rw [_root_.commutator_def] at hp ⊢
  rw [← Subgroup.map_top_of_surjective (e : G →* H) e.surjective, ← Subgroup.map_commutator, hp]

theorem conj_mem_oPrimeResidualOf {X : Type*} [Group X] {C : Subgroup X} {g : X}
    (hg : ∀ c ∈ C, g * c * g⁻¹ ∈ C) (hg' : ∀ c ∈ C, g⁻¹ * c * g ∈ C) {l : X}
    (hl : l ∈ CFSG.GH74.GLS.oPrimeResidualOf 2 C) : g * l * g⁻¹ ∈ CFSG.GH74.GLS.oPrimeResidualOf 2 C := by
  have hmap : C.map (MulAut.conj g).toMonoidHom = C := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact hg c hc
    · intro c hc
      refine ⟨g⁻¹ * c * g, hg' c hc, ?_⟩
      show g * (g⁻¹ * c * g) * g⁻¹ = c
      group
  have h1 := CFSG.GH74.GLS.Balance.map_oPrimeResidualOf_le (MulAut.conj g).toMonoidHom C
  rw [hmap] at h1
  exact h1 ⟨l, hl, rfl⟩

theorem le_of_closure_two {G : Type*} [Group G] (C : Subgroup G) :
    Subgroup.closure {x : G | x ∈ C ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1} ≤ C :=
  (Subgroup.closure_le C).2 fun _ hx => hx.1

end BadGroup

@[expose] def BadFix (p : ℕ) {S : Type} [Group S] (β : MulAut S) : Prop :=
  ∃ J E : Subgroup S, J ≤ fixSubgroup β ∧
    (∀ x ∈ fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ J) ∧ ¬ p ^ 2 ∣ Nat.card J ∧
    E ≤ J ∧ (∀ j ∈ J, ∀ e ∈ E, j * e * j⁻¹ ∈ E) ∧ IsSimpleGroup ↥E ∧ (∃ a b : ↥E, a * b ≠ b * a) ∧
    2 ∣ Nat.card E ∧ p ∣ Nat.card E

@[expose] def BadDecomp (p : ℕ) {S : Type} [Group S] (β : MulAut S) : Prop :=
  ∃ B E : Subgroup S, B ≤ fixSubgroup β ∧ (∀ c ∈ fixSubgroup β, ∀ b ∈ B, c * b * c⁻¹ ∈ B) ∧
    (∀ γ : MulAut S, γ * β = β * γ → γ ^ p = 1 → ∀ b ∈ B, γ b ∈ B) ∧ ¬ p ^ 2 ∣ Nat.card B ∧
    E ≤ B ∧ (∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ ∈ E) ∧ IsSimpleGroup ↥E ∧ (∃ a b : ↥E, a * b ≠ b * a) ∧
    2 ∣ Nat.card E ∧ p ∣ Nat.card E ∧
    ∀ g ∈ fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers g) →
      ∃ b ∈ B, IsPGroup 2 ↥(Subgroup.zpowers b) ∧
        ∃ c ∈ GLAPPrimeCoreOf p (fixSubgroup β) ⊔ GLAPLayer p (fixSubgroup β), g = b * c

section BadFactorLift

theorem badFix_of_congr {S T : Type} [Group S] [Group T] (e : S ≃* T) {p : ℕ} {β : MulAut S}
    (h : BadFix p (MulAut.congr e β)) : BadFix p β := by
  obtain ⟨J, E, hJfix, hJ2, hJp, hEJ, hEn, hEs, hEnc, hE2, hEp⟩ := h
  haveI := hEs
  have hfix := Inputs141c.fixSubgroup_congr e β
  set φ : ↥E ≃* ↥(E.map e.symm.toMonoidHom) := E.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  refine ⟨J.map e.symm.toMonoidHom, E.map e.symm.toMonoidHom, ?_, ?_, ?_, Subgroup.map_mono hEJ, ?_,
    φ.symm.isSimpleGroup, ?_, ?_, ?_⟩
  · have := Subgroup.map_mono (f := e.symm.toMonoidHom) (hJfix.trans hfix.le)
    rwa [Inputs141c.map_map_symm] at this
  · intro x hx hx2
    have hex : e x ∈ fixSubgroup (MulAut.congr e β) := by
      rw [hfix]
      exact ⟨x, hx, rfl⟩
    have hex2 : IsPGroup 2 ↥(Subgroup.zpowers (e x)) := by
      have h1 := hx2.map e.toMonoidHom
      rwa [MonoidHom.map_zpowers] at h1
    exact ⟨e x, hJ2 _ hex hex2, by simp⟩
  · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · rintro _ ⟨j, hj, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨j * x * j⁻¹, hEn j hj x hx, by simp⟩
  · obtain ⟨a, b, hab⟩ := hEnc
    exact ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · rwa [Subgroup.card_map_of_injective e.symm.injective]

theorem badFix_of_conj {S : Type} [Group S] (γ : MulAut S) {p : ℕ} {β : MulAut S}
    (h : BadFix p (γ * β * γ⁻¹)) : BadFix p β := by
  refine badFix_of_congr (γ : S ≃* S) ?_
  have e1 : MulAut.congr (γ : S ≃* S) β = γ * β * γ⁻¹ := by
    ext y
    rfl
  rw [e1]
  exact h

theorem badDecomp_of_congr {S T : Type} [Group S] [Group T] [Finite S] [Finite T] (e : S ≃* T) {p : ℕ}
    (hp : p.Prime) {β : MulAut S} (h : BadDecomp p (MulAut.congr e β)) : BadDecomp p β := by
  obtain ⟨B, E, hBfix, hBn, hBγ, hBp, hEB, hEn, hEs, hEnc, hE2, hEp, hdec⟩ := h
  haveI := hEs
  have hfix := Inputs141c.fixSubgroup_congr e β
  set φ : ↥E ≃* ↥(E.map e.symm.toMonoidHom) := E.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  refine ⟨B.map e.symm.toMonoidHom, E.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, Subgroup.map_mono hEB, ?_,
    φ.symm.isSimpleGroup, ?_, ?_, ?_, ?_⟩
  · have := Subgroup.map_mono (f := e.symm.toMonoidHom) (hBfix.trans hfix.le)
    rwa [Inputs141c.map_map_symm] at this
  · rintro c hc _ ⟨b, hb, rfl⟩
    have hec : e c ∈ fixSubgroup (MulAut.congr e β) := by
      rw [hfix]
      exact ⟨c, hc, rfl⟩
    exact ⟨e c * b * (e c)⁻¹, hBn _ hec b hb, by simp⟩
  · rintro γ hγβ hγp _ ⟨b, hb, rfl⟩
    have h1 : MulAut.congr e γ * MulAut.congr e β = MulAut.congr e β * MulAut.congr e γ := by
      rw [← map_mul, ← map_mul, hγβ]
    have h2 : MulAut.congr e γ ^ p = 1 := by rw [← map_pow, hγp, map_one]
    refine ⟨MulAut.congr e γ b, hBγ _ h1 h2 b hb, ?_⟩
    show e.symm (e (γ (e.symm b))) = γ (e.symm b)
    simp
  · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · rintro _ ⟨j, hj, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨j * x * j⁻¹, hEn j hj x hx, by simp⟩
  · obtain ⟨a, b, hab⟩ := hEnc
    exact ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩
  · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · intro g hg hg2
    have heg : e g ∈ fixSubgroup (MulAut.congr e β) := by
      rw [hfix]
      exact ⟨g, hg, rfl⟩
    have heg2 : IsPGroup 2 ↥(Subgroup.zpowers (e g)) := by
      have h1 := hg2.map e.toMonoidHom
      rwa [MonoidHom.map_zpowers] at h1
    obtain ⟨b, hb, hb2, c, hc, hbc⟩ := hdec _ heg heg2
    refine ⟨e.symm b, ⟨b, hb, rfl⟩, ?_, e.symm c, ?_, ?_⟩
    · have h1 := hb2.map e.symm.toMonoidHom
      rwa [MonoidHom.map_zpowers] at h1
    · rw [hfix] at hc
      have h2 := map_core_sup_layer_le hp e.symm.toMonoidHom e.symm.injective _
        (Subgroup.mem_map_of_mem e.symm.toMonoidHom hc)
      rw [Inputs141c.map_map_symm] at h2
      exact h2
    · apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hbc

variable {X : Type} [Group X] [Finite X]

theorem inducedAut_comm {K : Subgroup X} {w z : X} (hw : w ∈ Subgroup.normalizer (K : Set X))
    (hz : z ∈ Subgroup.normalizer (K : Set X)) (hwz : w * z = z * w) :
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) (K.normalizerMonoidHom ⟨w, hw⟩)
        (Subgroup.map_center_eq _) *
      QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) (K.normalizerMonoidHom ⟨z, hz⟩)
        (Subgroup.map_center_eq _) =
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) (K.normalizerMonoidHom ⟨z, hz⟩)
        (Subgroup.map_center_eq _) *
      QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) (K.normalizerMonoidHom ⟨w, hw⟩)
        (Subgroup.map_center_eq _) := by
  have h : K.normalizerMonoidHom ⟨w, hw⟩ * K.normalizerMonoidHom ⟨z, hz⟩ =
      K.normalizerMonoidHom ⟨z, hz⟩ * K.normalizerMonoidHom ⟨w, hw⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hwz
  ext s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) s
  show (QuotientGroup.mk' (Subgroup.center ↥K)
      ((K.normalizerMonoidHom ⟨w, hw⟩ * K.normalizerMonoidHom ⟨z, hz⟩) k) : ↥K ⧸ Subgroup.center ↥K) =
    QuotientGroup.mk' (Subgroup.center ↥K) ((K.normalizerMonoidHom ⟨z, hz⟩ * K.normalizerMonoidHom ⟨w, hw⟩) k)
  rw [h]

theorem inducedAut_pow_eq_one {K : Subgroup X} {w : X} (hw : w ∈ Subgroup.normalizer (K : Set X)) {n : ℕ}
    (hwn : w ^ n = 1) :
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) (K.normalizerMonoidHom ⟨w, hw⟩)
      (Subgroup.map_center_eq _) ^ n = 1 := by
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨w, hw⟩ with hαdef
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) α (Subgroup.map_center_eq α) with hβdef
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπdef
  have hαβ : ∀ x, π (α x) = β (π x) := fun x => rfl
  have hβn : ∀ (m : ℕ) (x : ↥K), (β ^ m) (π x) = π ((α ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih => intro x; rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ← hαβ, ih]
  have hαn : α ^ n = 1 := by
    have e : (⟨w, hw⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ n = 1 := Subtype.ext hwn
    rw [hαdef, ← map_pow, e, map_one]
  ext s
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) s
  rw [hβn, hαn]
  rfl

theorem exists_central_mul_core_sup_layer {K Q : Type} [Group K] [Group Q] [Finite K] [Finite Q]
    (π : K →* Q) (hker : π.ker ≤ Subgroup.center K) (α : MulAut K) (β : MulAut Q)
    (hαβ : ∀ k, π (α k) = β (π k)) (hπ : Function.Surjective π) {p : ℕ} (hp : p.Prime) {h₀ : K}
    (hh₀ : h₀ ∈ fixSubgroup α)
    (hc : π h₀ ∈ GLAPPrimeCoreOf p (fixSubgroup β) ⊔ GLAPLayer p (fixSubgroup β)) :
    ∃ a ∈ Subgroup.center K, (∃ e : ℕ, a ^ (p ^ e) = 1) ∧
      ∃ w ∈ GLAPPrimeCoreOf p (fixSubgroup α) ⊔ GLAPLayer p (fixSubgroup α), h₀ = a * w := by
  classical
  set Cα := fixSubgroup α with hCα
  set Cβ := fixSubgroup β with hCβ
  obtain ⟨y, hy, l, hl, hyl⟩ := exists_mul_of_mem_sup_of_normalizes (fun b hb a ha =>
    CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_conj_mem b
      (CFSG.HardMathSupport.Solomon.Coordinator.glaPLayer_le Cβ hb) a ha) hc
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_glaPLayer_fixSubgroup_eq π hker α β hαβ hπ hp] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  have hl₀C : l₀ ∈ Cα := CFSG.HardMathSupport.Solomon.Coordinator.glaPLayer_le Cα hl₀
  set h₁ := h₀ * l₀⁻¹ with hh₁
  have hh₁C : h₁ ∈ Cα := Cα.mul_mem hh₀ (Cα.inv_mem hl₀C)
  have hπh₁ : π h₁ = y := by
    rw [hh₁, map_mul, map_inv, ← hyl]
    group
  obtain ⟨a, b, e, ha, hb, -, hprod, hord, hcop⟩ :=
    CFSG.TwoRankLowerBound.Helpers.finite_prime_primary_factorization h₁ p hp
  have hzpow : Subgroup.zpowers h₁ ≤ Cα := Subgroup.zpowers_le.2 hh₁C
  have hzpowO : ∀ c ∈ Subgroup.zpowers h₁, π c ∈ GLAPPrimeCoreOf p Cβ := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    rw [map_zpow, hπh₁]
    exact zpow_mem hy k
  have hape : a ^ (p ^ e) = 1 := orderOf_dvd_iff_pow_eq_one.1 hord
  have hπa : π a = 1 :=
    eq_one_of_pow_mem_of_coprime (hzpowO a ha)
      (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp Cβ)
      (by rw [← map_pow, hape, map_one])
  have haZ : a ∈ Subgroup.center K := hker hπa
  have hbO : b ∈ GLAPPrimeCoreOf p Cα :=
    mem_glaPPrimeCoreOf_of_coprime π hker α β hαβ hp (hzpow hb) (hzpowO b hb) hcop.symm
  refine ⟨a, haZ, ⟨e, hape⟩, b * l₀,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hbO) (Subgroup.mem_sup_right hl₀), ?_⟩
  rw [← mul_assoc, hprod, hh₁, inv_mul_cancel_right]

theorem oPrimeResidualOf_le_of_badDecomp {K Z : Subgroup X} (hZN : Z ≤ Subgroup.normalizer (K : Set X))
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hZp : ∀ w ∈ Z, w ^ p = 1)
    {z : X} (hz : z ∈ Z)
    (h : BadDecomp p (QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K)
      (K.normalizerMonoidHom ⟨z, hZN hz⟩) (Subgroup.map_center_eq _))) :
    CFSG.GH74.GLS.oPrimeResidualOf 2 (K ⊓ Subgroup.centralizer ({z} : Set X)) ≤
      GLAPPrimeCoreOf p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
        GLAPLayer p (K ⊓ Subgroup.centralizer ({z} : Set X)) ⊔
        ⨆ (L : Subgroup X) (_ : Inputs2323.BadFactor p K Z z L), L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hzN : z ∈ Subgroup.normalizer (K : Set X) := hZN hz
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨z, hzN⟩ with hαdef
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) α (Subgroup.map_center_eq α) with hβdef
  obtain ⟨B, E, hBfix, hBn, hBγ, hBp, hEB, hEn, hEs, hEnc, hE2, hEp, hdec⟩ := h
  haveI := hEs
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  set C := K ⊓ Subgroup.centralizer ({z} : Set X) with hCdef
  have hCK : C ≤ K := inf_le_left
  set H : Subgroup X := C ⊓ (B.comap π).map K.subtype with hHdef
  set L := CFSG.GH74.GLS.oPrimeResidualOf 2 H with hLdef
  have hHC : H ≤ C := inf_le_left
  have hHK : H ≤ K := hHC.trans hCK
  have hLH : L ≤ H := CFSG.GH74.GLS.Balance.oPrimeResidualOf_le_self H
  have hLC : L ≤ C := hLH.trans hHC
  have hLK : L ≤ K := hLC.trans hCK
  have hfixα : fixSubgroup α = C.subgroupOf K := fixSubgroup_normalizerMonoidHom_eq hzN
  have hβπ : ∀ k : ↥K, β (π k) = π (α k) := fun k => rfl
  have hCfix : ∀ v (hv : v ∈ C), π ⟨v, hCK hv⟩ ∈ fixSubgroup β := by
    intro v hv
    have hk : (⟨v, hCK hv⟩ : ↥K) ∈ fixSubgroup α := by
      rw [hfixα]
      exact hv
    rw [mem_fixSubgroup, hβπ, mem_fixSubgroup.1 hk]
  have hHB : ∀ v (hv : v ∈ H), π ⟨v, hHK hv⟩ ∈ B := by
    intro v hv
    obtain ⟨k, hk, hkv⟩ := (Subgroup.mem_inf.1 hv).2
    have e1 : k = ⟨v, hHK hv⟩ := Subtype.ext hkv
    rw [← e1]
    exact hk
  have hmemH : ∀ v (hv : v ∈ C), π ⟨v, hCK hv⟩ ∈ B → v ∈ H := fun v hv hvB =>
    Subgroup.mem_inf.2 ⟨hv, ⟨⟨v, hCK hv⟩, hvB, rfl⟩⟩
  have hLB : ∀ l (hl : l ∈ L), π ⟨l, hLK hl⟩ ∈ B := fun l hl => hHB l (hLH hl)
  have hlift : ∀ s ∈ fixSubgroup β, ∀ n : ℕ, s ^ (2 ^ n) = 1 →
      ∃ v, ∃ hv : v ∈ C, (∃ m : ℕ, v ^ (2 ^ m) = 1) ∧ π ⟨v, hCK hv⟩ = s := by
    intro s hs n hsn
    have hfix : centerQuotAct K ⟨z, hzN⟩ s = s := by
      have e1 : ∀ s', centerQuotAct K ⟨z, hzN⟩ s' = β s' := by
        intro s'
        induction s' using QuotientGroup.induction_on with
        | H k => rfl
      rw [e1]
      exact mem_fixSubgroup.1 hs
    obtain ⟨k, hks, ⟨m, hkm⟩, hkz⟩ := exists_two_lift_fixed hzN hp hp2 (hZp z hz) hsn hfix
    have hkC : (k : X) ∈ C := by
      refine Subgroup.mem_inf.2 ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc (k : X) * z = z * k * z⁻¹ * z := by rw [hkz]
        _ = z * k := by group
    exact ⟨k, hkC, ⟨m, by simpa using congrArg Subtype.val hkm⟩, hks⟩
  have hwC : ∀ w ∈ Z, ∀ c ∈ C, w * c * w⁻¹ ∈ C := by
    intro w hw c hc
    have hwK := hZN hw
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hwK c).1 hc.1,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).2
    have hwz : w * z = z * w := hZc w hw z hz
    have hwz' : w⁻¹ * z = z * w⁻¹ := by
      calc w⁻¹ * z = w⁻¹ * (z * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * z) * w⁻¹ := by rw [hwz]
        _ = z * w⁻¹ := by group
    calc w * c * w⁻¹ * z = w * c * (w⁻¹ * z) := by group
      _ = w * c * (z * w⁻¹) := by rw [hwz']
      _ = w * (c * z) * w⁻¹ := by group
      _ = w * (z * c) * w⁻¹ := by rw [hcz]
      _ = (w * z) * c * w⁻¹ := by group
      _ = (z * w) * c * w⁻¹ := by rw [hwz]
      _ = z * (w * c * w⁻¹) := by group
  have hwH : ∀ w ∈ Z, ∀ v ∈ H, w * v * w⁻¹ ∈ H := by
    intro w hw v hv
    have hwN := hZN hw
    have h1 := hwC w hw v (hHC hv)
    refine hmemH _ h1 ?_
    have hcomm := inducedAut_comm hwN hzN (hZc w hw z hz)
    have hpow := inducedAut_pow_eq_one hwN (hZp w hw)
    exact hBγ _ hcomm hpow (π ⟨v, hHK hv⟩) (hHB v hv)
  have hHn : ∀ c ∈ C, ∀ v ∈ H, c * v * c⁻¹ ∈ H := by
    intro c hc v hv
    have h1 : c * v * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc (hHC hv)) (C.inv_mem hc)
    refine hmemH _ h1 ?_
    have h2 := hBn _ (hCfix c hc) _ (hHB v hv)
    have e1 : π ⟨c * v * c⁻¹, hCK h1⟩ = π ⟨c, hCK hc⟩ * π ⟨v, hHK hv⟩ * (π ⟨c, hCK hc⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    exact h2
  set πL : ↥L →* ↥K ⧸ Subgroup.center ↥K := π.comp (Subgroup.inclusion hLK) with hπL
  have hπLker : ∀ l : ↥L, πL l = 1 → ∀ l' : ↥L, l * l' = l' * l := by
    intro l hl l'
    have h1 : (Subgroup.inclusion hLK l) ∈ Subgroup.center ↥K := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥K)]
      exact hl
    have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.1 h1 (Subgroup.inclusion hLK l'))
    exact Subtype.ext (by simpa using h2.symm)
  have hgenL : ∀ H' : Subgroup ↥L, (∀ g : ↥L, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ H') → H' = ⊤ := by
    intro H' hH'
    have hle : L ≤ H'.map L.subtype := by
      refine CFSG.GH74.GLS.Balance.oPrimeResidualOf_le_of_two_elements fun v hv hv2 => ?_
      have hvL : v ∈ L := CFSG.GH74.GLS.Balance.mem_oPrimeResidualOf_of_two_element hv hv2
      obtain ⟨k, hk⟩ := hv2
      exact ⟨⟨v, hvL⟩, hH' _ ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩
    rw [eq_top_iff]
    rintro ⟨l, hl⟩ -
    obtain ⟨h', hh', hh'l⟩ := hle hl
    have e1 : h' = ⟨l, hl⟩ := Subtype.ext hh'l
    rw [← e1]
    exact hh'
  have hPJ : ∀ P : Subgroup ↥L, (πL.comp P.subtype).range ≤ B := by
    rintro P _ ⟨x, rfl⟩
    exact hLB _ (x : ↥L).2
  have hPcomm : ∀ P : Sylow p ↥L, ∀ a b : ↥(P : Subgroup ↥L), a * b = b * a := by
    intro P
    set f : ↥(P : Subgroup ↥L) →* ↥K ⧸ Subgroup.center ↥K := πL.comp (P : Subgroup ↥L).subtype with hf
    have hRp : IsPGroup p ↥f.range := P.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hRp
    have hdvd : Nat.card ↥f.range ∣ Nat.card B := Subgroup.card_dvd_of_le (hPJ _)
    have hn1 : n ≤ 1 := by
      by_contra hn1
      apply hBp
      rw [hn] at hdvd
      exact (pow_dvd_pow p (by omega : 2 ≤ n)).trans hdvd
    haveI : IsCyclic ↥f.range := by
      rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · rw [pow_zero] at hn
        haveI : Subsingleton ↥f.range := (Nat.card_eq_one_iff_unique.1 hn).1
        exact isCyclic_of_subsingleton
      · rw [pow_one] at hn
        exact isCyclic_of_prime_card hn
    have hker : f.rangeRestrict.ker ≤ Subgroup.center ↥(P : Subgroup ↥L) := by
      intro x hx
      rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := hπLker (x : ↥L) hx (y : ↥L)
      exact Subtype.ext h1.symm
    exact (f.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm
  obtain ⟨P⟩ : Nonempty (Sylow p ↥L) := inferInstance
  have hcen : ∀ c : ↥L, c ∈ Subgroup.center ↥L → ∀ e : ℕ, c ^ (p ^ e) = 1 → c = 1 :=
    fun c hc e hce => eq_one_of_mem_center_of_twoGen hp hp2 hgenL P (hPcomm P) hc hce
  set LK : Subgroup ↥K := L.comap K.subtype with hLKdef
  set HK : Subgroup ↥K := H.comap K.subtype with hHKdef
  set CK : Subgroup ↥K := C.comap K.subtype with hCKdef
  set MK : Subgroup ↥K := LK ⊓ E.comap π with hMKdef
  set D : Subgroup ↥K := ⁅MK, MK⁆ with hDdef
  have hLBK : ∀ g ∈ LK, π g ∈ B := fun g hg => hLB _ hg
  have hMKE : MK.map π = E := by
    apply le_antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.2
    · have hT : (MK.map π).subgroupOf E = ⊤ := by
        refine eq_top_of_two_elements hE2 _ fun x hx => ?_
        obtain ⟨n, hn⟩ := hx
        have hxs : (x : ↥K ⧸ Subgroup.center ↥K) ^ (2 ^ n) = 1 := by
          simpa using congrArg Subtype.val hn
        obtain ⟨v, hvC, hv2, hvx⟩ := hlift (x : ↥K ⧸ Subgroup.center ↥K) (hBfix (hEB x.2)) n hxs
        have hvH : v ∈ H := hmemH v hvC (by rw [hvx]; exact hEB x.2)
        have hvL : v ∈ L := CFSG.GH74.GLS.Balance.mem_oPrimeResidualOf_of_two_element hvH hv2
        rw [Subgroup.mem_subgroupOf]
        refine ⟨⟨v, hLK hvL⟩, ⟨hvL, ?_⟩, hvx⟩
        show π ⟨v, hLK hvL⟩ ∈ E
        rw [show π ⟨v, hLK hvL⟩ = x from hvx]
        exact x.2
      intro e he
      have h1 : (⟨e, he⟩ : ↥E) ∈ (MK.map π).subgroupOf E := by
        rw [hT]
        exact Subgroup.mem_top _
      exact h1
  have hEperf : ⁅E, E⁆ = E := by
    have hc : commutator ↥E = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥E) with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hEnc
        apply hab
        have h1 : ⁅a, b⁆ ∈ commutator ↥E := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.1 h1
      · exact h
    rw [← Subgroup.map_subtype_commutator, hc, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hDE : D.map π = E := by
    rw [hDdef, Subgroup.map_commutator, hMKE, hEperf]
  have hMKD : ∀ m ∈ MK, ∃ d ∈ D, d⁻¹ * m ∈ Subgroup.center ↥K := by
    intro m hm
    have h1 : π m ∈ D.map π := by
      rw [hDE]
      exact hm.2
    obtain ⟨d, hd, hdm⟩ := h1
    refine ⟨d, hd, ?_⟩
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥K), MonoidHom.mem_ker, map_mul, map_inv]
    change (π d)⁻¹ * π m = 1
    rw [hdm, inv_mul_cancel]
  have hDperf : ⁅D, D⁆ = D := by
    refine le_antisymm (Subgroup.commutator_le_self _) ?_
    conv_lhs => rw [hDdef]
    rw [Subgroup.commutator_le]
    intro m₁ hm₁ m₂ hm₂
    obtain ⟨d₁, hd₁, hc₁⟩ := hMKD m₁ hm₁
    obtain ⟨d₂, hd₂, hc₂⟩ := hMKD m₂ hm₂
    have e1 := commutatorElement_mul_mem_center (a := d₁) (b := d₂) hc₁ hc₂
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at e1
    rw [e1]
    exact Subgroup.commutator_mem_commutator hd₁ hd₂
  have hZE : Subgroup.center ↥E = ⊥ := CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hEnc
  have hDq : CFSG.Open.IsQuasisimple ↥D := by
    refine ⟨?_, ?_⟩
    · apply Subgroup.map_injective D.subtype_injective
      rw [Subgroup.map_subtype_commutator, hDperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · have hρmem : ∀ d : ↥D, (π.comp D.subtype) d ∈ E := fun d => hDE ▸ Subgroup.mem_map_of_mem π d.2
      set ρ : ↥D →* ↥E := (π.comp D.subtype).codRestrict E hρmem with hρ
      have hρs : Function.Surjective ρ := by
        rintro ⟨e, he⟩
        rw [← hDE] at he
        obtain ⟨d, hd, rfl⟩ := he
        exact ⟨⟨d, hd⟩, rfl⟩
      have hρker : ρ.ker = Subgroup.center ↥D := by
        apply le_antisymm
        · intro d hd
          have h1 : (d : ↥K) ∈ Subgroup.center ↥K := by
            rw [← QuotientGroup.ker_mk' (Subgroup.center ↥K), MonoidHom.mem_ker]
            have h2 := congrArg Subtype.val (MonoidHom.mem_ker.1 hd)
            exact h2
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subtype.ext (Subgroup.mem_center_iff.1 h1 g)
        · intro d hd
          have h1 : ρ d ∈ Subgroup.center ↥E := by
            rw [Subgroup.mem_center_iff]
            intro g
            obtain ⟨g', rfl⟩ := hρs g
            rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hd g']
          rw [hZE, Subgroup.mem_bot] at h1
          exact h1
      exact ((QuotientGroup.quotientMulEquivOfEq hρker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)).isSimpleGroup
  have hMKconj : ∀ g ∈ LK, ∀ m ∈ MK, g * m * g⁻¹ ∈ MK := by
    intro g hg m hm
    refine ⟨LK.mul_mem (LK.mul_mem hg hm.1) (LK.inv_mem hg), ?_⟩
    show π (g * m * g⁻¹) ∈ E
    rw [map_mul, map_mul, map_inv]
    exact hEn _ (hLBK g hg) _ hm.2
  have hDconj : ∀ g ∈ LK, ∀ d ∈ D, g * d * g⁻¹ ∈ D := fun g hg d hd =>
    conj_mem_commutator_of_normalizes (hMKconj g hg)
      (fun m hm => by simpa using hMKconj g⁻¹ (LK.inv_mem hg) m hm) hd
  have hDMK : D ≤ MK := Subgroup.commutator_le_self _
  have hMKLK : MK ≤ LK := inf_le_left
  have hLKHK : LK ≤ HK := Subgroup.comap_mono hLH
  have hHKCK : HK ≤ CK := Subgroup.comap_mono hHC
  have hDn : (D.subgroupOf MK).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hDconj _ (hMKLK g.2) _ hn
  have hMKn : (MK.subgroupOf LK).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hMKconj _ g.2 _ hn
  have hLKn : (LK.subgroupOf HK).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hgH : ((g : ↥K) : X) ∈ H := g.2
    show ((g : ↥K) : X) * ((n : ↥K) : X) * ((g : ↥K) : X)⁻¹ ∈ L
    exact conj_mem_oPrimeResidualOf (fun c hc => H.mul_mem (H.mul_mem hgH hc) (H.inv_mem hgH))
      (fun c hc => H.mul_mem (H.mul_mem (H.inv_mem hgH) hc) hgH) hn
  have hHKn : (HK.subgroupOf CK).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hHn _ g.2 _ hn
  have hsubK : CFSG.Open.IsSubnormal D CK :=
    CFSG.Open.IsSubnormal.step hDMK hDn (CFSG.Open.IsSubnormal.step hMKLK hMKn
      (CFSG.Open.IsSubnormal.step hLKHK hLKn (CFSG.Open.IsSubnormal.step hHKCK hHKn
        (CFSG.Open.IsSubnormal.refl _))))
  have hCKmap : CK.map K.subtype = C := by
    rw [hCKdef, Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hCK)]
  have hsubX : CFSG.Open.IsSubnormal (D.map K.subtype) C := by
    have h1 := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSubnormal_map hsubK K.subtype
      K.subtype_injective
    rwa [hCKmap] at h1
  have hL₀L : D.map K.subtype ≤ L := by
    refine (Subgroup.map_mono (hDMK.trans hMKLK)).trans ?_
    rw [hLKdef]
    exact Subgroup.map_comap_le _ _
  have hL₀C : D.map K.subtype ≤ C := hL₀L.trans hLC
  have hL₀q : CFSG.Open.IsQuasisimple ↥(D.map K.subtype) :=
    isQuasisimple_of_mulEquiv' (D.equivMapOfInjective K.subtype K.subtype_injective) hDq
  have hL₀core : D.map K.subtype ≤ GLAPPrimeCoreOf p C ⊔ GLAPLayer p C :=
    le_core_sup_layer_of_isComponentOf hp ⟨hL₀C, hsubX, hL₀q⟩
  have hBad : Inputs2323.BadFactor p K Z z L := by
    refine ⟨hLC, ?_, ?_, ?_, D.map K.subtype, hL₀L, ?_, ?_, Or.inl hL₀core⟩
    · intro w hw
      refine Subgroup.mem_normalizer_fintype fun l hl => ?_
      exact conj_mem_oPrimeResidualOf (hwH w hw)
        (fun c hc => by simpa using hwH w⁻¹ (Z.inv_mem hw) c hc) hl
    · rintro y ⟨hyL, hyc⟩ hyp
      have hc : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyc g g.2)
      have h1 := hcen ⟨y, hyL⟩ hc 1 (Subtype.ext (by simpa using hyp))
      exact congrArg Subtype.val h1
    · intro hdvd
      have hP2 := P.pow_dvd_card_of_pow_dvd_card hdvd
      set f : ↥(P : Subgroup ↥L) →* ↥K ⧸ Subgroup.center ↥K := πL.comp (P : Subgroup ↥L).subtype with hf
      have hinj : Function.Injective f := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        have hxc : (x : ↥L) ∈ Subgroup.center ↥L := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact (hπLker _ (MonoidHom.mem_ker.1 hx) g).symm
        obtain ⟨e, he⟩ := P.isPGroup' x
        have h1 := hcen (x : ↥L) hxc e (by simpa using congrArg Subtype.val he)
        exact Subtype.ext h1
      have hcard : Nat.card ↥(P : Subgroup ↥L) = Nat.card ↥f.range :=
        Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      exact hBp ((hcard ▸ hP2).trans (Subgroup.card_dvd_of_le (hPJ _)))
    · refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨d, hd, hdn⟩ := hn
      have hgK : (g : X) ∈ K := hLK g.2
      refine ⟨⟨g, hgK⟩ * d * ⟨g, hgK⟩⁻¹, hDconj _ (show ((⟨g, hgK⟩ : ↥K) : X) ∈ L from g.2) d hd, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [show (d : X) = (n : X) from hdn]
    · rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact hEp.trans (hDE ▸ Subgroup.card_map_dvd D π)
  have hCmap : (fixSubgroup α).map K.subtype = C := by
    rw [hfixα, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 inf_le_left
  have hαβ' : ∀ k, π (α k) = β (π k) := fun k => rfl
  refine CFSG.GH74.GLS.Balance.oPrimeResidualOf_le_of_two_elements fun g hg hg2 => ?_
  obtain ⟨k₂, hk₂⟩ := hg2
  have hgK : g ∈ K := hCK hg
  have hgKfix : (⟨g, hgK⟩ : ↥K) ∈ fixSubgroup α := by
    rw [hfixα]
    exact hg
  have hs : π ⟨g, hgK⟩ ∈ fixSubgroup β := hCfix g hg
  have hs2 : IsPGroup 2 ↥(Subgroup.zpowers (π ⟨g, hgK⟩)) := by
    refine isPGroup_zpowers_of_pow_eq_one (m := k₂) ?_
    have e1 : (⟨g, hgK⟩ : ↥K) ^ (2 ^ k₂) = 1 := Subtype.ext (by simpa using hk₂)
    rw [← map_pow, e1, map_one]
  obtain ⟨b, hbB, hb2, c, hc, hsbc⟩ := hdec _ hs hs2
  obtain ⟨n, hbn⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hb2
  obtain ⟨v, hvC, hv2, hvb⟩ := hlift b (hBfix hbB) n hbn
  have hvL : v ∈ L :=
    CFSG.GH74.GLS.Balance.mem_oPrimeResidualOf_of_two_element (hmemH v hvC (by rw [hvb]; exact hbB)) hv2
  have hvKfix : (⟨v, hCK hvC⟩ : ↥K) ∈ fixSubgroup α := by
    rw [hfixα]
    exact hvC
  have hh₀fix : (⟨v, hCK hvC⟩ : ↥K)⁻¹ * ⟨g, hgK⟩ ∈ fixSubgroup α :=
    (fixSubgroup α).mul_mem ((fixSubgroup α).inv_mem hvKfix) hgKfix
  have hπh₀ : π ((⟨v, hCK hvC⟩ : ↥K)⁻¹ * ⟨g, hgK⟩) = c := by
    rw [map_mul, map_inv, hsbc, hvb]
    group
  obtain ⟨a, haZ, ⟨e, hae⟩, w, hw, hh₀aw⟩ :=
    exists_central_mul_core_sup_layer π hπker α β hαβ' hπs hp hh₀fix (by rw [hπh₀]; exact hc)
  have hwX : (w : X) ∈ GLAPPrimeCoreOf p C ⊔ GLAPLayer p C := by
    have h1 := map_core_sup_layer_le hp K.subtype K.subtype_injective _ (Subgroup.mem_map_of_mem K.subtype hw)
    rw [hCmap] at h1
    exact h1
  have hgK' : (⟨g, hgK⟩ : ↥K) = a * ((⟨v, hCK hvC⟩ : ↥K) * w) := by
    have h1 : (⟨g, hgK⟩ : ↥K) = (⟨v, hCK hvC⟩ : ↥K) * ((⟨v, hCK hvC⟩ : ↥K)⁻¹ * ⟨g, hgK⟩) := by group
    rw [h1, hh₀aw, ← mul_assoc, Subgroup.mem_center_iff.1 haZ ⟨v, hCK hvC⟩, mul_assoc]
  have hpow : (⟨g, hgK⟩ : ↥K) ^ (p ^ e) = ((⟨v, hCK hvC⟩ : ↥K) * w) ^ (p ^ e) := by
    rw [hgK', Commute.mul_pow (Subgroup.mem_center_iff.1 haZ _).symm, hae, one_mul]
  have hgX : g ^ (p ^ e) = (v * (w : X)) ^ (p ^ e) := by
    have := congrArg Subtype.val hpow
    simpa using this
  have hmem : v * (w : X) ∈ (GLAPPrimeCoreOf p C ⊔ GLAPLayer p C) ⊔ L :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right hvL) (Subgroup.mem_sup_left hwX)
  have hcop2 : Nat.Coprime (p ^ e) (orderOf g) := by
    have h1 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk₂) (Nat.Coprime.pow e k₂ h1)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop2
  have hgmem : g ∈ (GLAPPrimeCoreOf p C ⊔ GLAPLayer p C) ⊔ L := by
    rw [← hm, hgX]
    exact pow_mem (pow_mem hmem _) _
  have hle : (GLAPPrimeCoreOf p C ⊔ GLAPLayer p C) ⊔ L ≤
      GLAPPrimeCoreOf p C ⊔ GLAPLayer p C ⊔ ⨆ (L' : Subgroup X) (_ : Inputs2323.BadFactor p K Z z L'), L' :=
    sup_le_sup_left (le_iSup₂_of_le (f := fun (L' : Subgroup X) (_ : Inputs2323.BadFactor p K Z z L') => L') L
      hBad le_rfl) _
  exact hle hgmem

@[expose] def Input14_1BadSimpleOrDecompOn (R : ℕ → TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, R p d.1 → d.1.characteristic = 2 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → TwoInCoreLayer p β ∨ BadDecomp p β

theorem input14_1BadOn_of_simpleOrDecomp {R : ℕ → TauCeti.LieTypeIndex → Prop}
    (h : Input14_1BadSimpleOrDecompOn R) : Input14_1BadOn R := by
  intro p hp hp5 X _ _ K Z hKq d hR hchar he hZel _ hZN hfaith _ z hz hz1
  classical
  have hzN : z ∈ Subgroup.normalizer (K : Set X) := hZN hz
  set α : MulAut ↥K := K.normalizerMonoidHom ⟨z, hzN⟩ with hαdef
  have hαx : ∀ x : ↥K, ((α x : ↥K) : X) = z * x * z⁻¹ := fun x => rfl
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπdef
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) :=
    QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥K) α (Subgroup.map_center_eq α) with hβdef
  have hαβ : ∀ x, π (α x) = β (π x) := fun x => rfl
  have hzp : z ^ p = 1 := hZel.2 z hz
  have hβp : β ^ p = 1 := inducedAut_pow_eq_one hzN hzp
  have hβ1 : β ≠ 1 := by
    intro hβ
    apply hz1
    have hα1 : α = 1 := Inputs141c.eq_one_of_mul_inv_mem_center hKq.1 α fun x => hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαβ, hβ, MulAut.one_apply, mul_inv_cancel])
    have hzC : z ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have e1 : α ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hα1, MulAut.one_apply]
      have e : z * y * z⁻¹ = y := by
        have := congrArg Subtype.val e1
        rw [hαx] at this
        exact this
      calc y * z = z * y * z⁻¹ * z := by rw [e]
        _ = z * y := by group
    have hmem : z ∈ Z ⊓ Subgroup.centralizer (K : Set X) := Subgroup.mem_inf.2 ⟨hz, hzC⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact hmem
  have hSs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKq.2
  have hSnc : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hKq
  have hp2 : p ≠ 2 := by omega
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hZel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  rcases h p hp hp5 _ hSs hSnc d hR hchar he β hβp hβ1 with hT | hB
  · exact le_sup_of_le_left (oPrimeResidualOf_le_of_twoInCoreLayer hzN hp hp2 hT)
  · exact oPrimeResidualOf_le_of_badDecomp hZN hZc hp hp2 hZel.2 hz hB

theorem twoInCoreLayerOrDecomp_of_congr {S T : Type} [Group S] [Group T] [Finite S] [Finite T] (e : S ≃* T)
    {p : ℕ} (hp : p.Prime) {β : MulAut S}
    (h : TwoInCoreLayer p (MulAut.congr e β) ∨ BadDecomp p (MulAut.congr e β)) :
    TwoInCoreLayer p β ∨ BadDecomp p β :=
  h.imp (twoInCoreLayer_of_congr e hp) (badDecomp_of_congr e hp)

theorem badDecomp_of_badFix {S : Type} [Group S] [Finite S] {p : ℕ} {β : MulAut S} (h : BadFix p β) :
    BadDecomp p β := by
  classical
  obtain ⟨J, E, hJfix, hJ2, hJp, hEJ, hEn, hEs, hEnc, hE2, hEp⟩ := h
  haveI := hEs
  set B := Subgroup.closure {x : S | x ∈ fixSubgroup β ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1} with hBdef
  have hBfix : B ≤ fixSubgroup β := le_of_closure_two _
  have hBJ : B ≤ J := (Subgroup.closure_le J).2 fun x hx => by
    obtain ⟨hx, k, hk⟩ := hx
    exact hJ2 x hx (isPGroup_zpowers_of_pow_eq_one (m := k) hk)
  have hBaut : ∀ φ : MulAut S, (∀ x ∈ fixSubgroup β, φ x ∈ fixSubgroup β) → ∀ b ∈ B, φ b ∈ B := by
    intro φ hφ b hb
    have hle : B ≤ B.comap φ.toMonoidHom := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨hx, k, hk⟩
      exact Subgroup.subset_closure ⟨hφ x hx, k, by rw [← map_pow, hk, map_one]⟩
    exact hle hb
  refine ⟨B, E, hBfix, fun c hc b hb => ?_, fun γ hγ _ b hb => ?_, ?_, ?_,
    fun b hb e he => hEn b (hBJ hb) e he, hEs, hEnc, hE2, hEp, fun g hg hg2 => ?_⟩
  · exact hBaut (MulAut.conj c) (fun x hx => (fixSubgroup β).mul_mem ((fixSubgroup β).mul_mem hc hx)
      ((fixSubgroup β).inv_mem hc)) b hb
  · refine hBaut γ (fun x hx => ?_) b hb
    rw [mem_fixSubgroup] at hx ⊢
    have h1 := congrArg (fun φ : MulAut S => φ x) hγ
    simp only [MulAut.mul_apply] at h1
    rw [← h1, hx]
  · exact fun hdvd => hJp (hdvd.trans (Subgroup.card_dvd_of_le hBJ))
  · have hT : B.subgroupOf E = ⊤ := eq_top_of_two_elements hE2 _ fun x hx => by
      obtain ⟨k, hk⟩ := hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure ⟨hJfix (hEJ x.2), k, by simpa using congrArg Subtype.val hk⟩
    intro e he
    have h1 : (⟨e, he⟩ : ↥E) ∈ B.subgroupOf E := by
      rw [hT]
      exact Subgroup.mem_top _
    exact h1
  · obtain ⟨k, hk⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hg2
    exact ⟨g, Subgroup.subset_closure ⟨hg, k, hk⟩, hg2, 1, one_mem _, (mul_one g).symm⟩

@[expose] def Input14_1BadSimpleOrBadOn (R : ℕ → TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, R p d.1 → d.1.characteristic = 2 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → TwoInCoreLayer p β ∨ BadFix p β

theorem input14_1BadOn_of_simpleOrBad {R : ℕ → TauCeti.LieTypeIndex → Prop}
    (h : Input14_1BadSimpleOrBadOn R) : Input14_1BadOn R :=
  input14_1BadOn_of_simpleOrDecomp fun p hp hp5 S _ _ hs hna d hR hchar he β hβ hβ1 =>
    (h p hp hp5 S hs hna d hR hchar he β hβ hβ1).imp id badDecomp_of_badFix

end BadFactorLift

section BadInstances

theorem badFix_of_equiv {S : Type} [Group S] [Finite S] {β : MulAut S} {p : ℕ} (J : Subgroup S)
    (hJ : J ≤ fixSubgroup β) (hJ2 : ∀ x ∈ fixSubgroup β, IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ J)
    (hJp : ¬ p ^ 2 ∣ Nat.card J) {T : Type} [Group T] [IsSimpleGroup T] (eT : ↥⁅J, J⁆ ≃* T)
    (h2 : 2 ∣ Nat.card T) (hpT : p ∣ Nat.card T) (hT : ¬ (Nat.card T).Prime) : BadFix p β := by
  haveI : IsSimpleGroup ↥⁅J, J⁆ := eT.isSimpleGroup
  refine ⟨J, ⁅J, J⁆, hJ, hJ2, hJp, Subgroup.commutator_le_self _, fun j hj e he => ?_, inferInstance,
    ?_, ?_, ?_⟩
  · exact conj_mem_commutator_of_normalizes (fun y hy => J.mul_mem (J.mul_mem hj hy) (J.inv_mem hj))
      (fun y hy => J.mul_mem (J.mul_mem (J.inv_mem hj) hy) hj) he
  · by_contra hcon
    push Not at hcon
    letI : CommGroup ↥⁅J, J⁆ := { (inferInstance : Group ↥⁅J, J⁆) with mul_comm := fun a b => hcon a b }
    have hprime : (Nat.card ↥⁅J, J⁆).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_congr eT.toEquiv] at hprime
    exact hT hprime
  · rwa [Nat.card_congr eT.toEquiv]
  · rwa [Nat.card_congr eT.toEquiv]

theorem twoInCoreLayerOrBad_of_congr {S T : Type} [Group S] [Group T] [Finite S] [Finite T] (e : S ≃* T)
    {p : ℕ} (hp : p.Prime) {β : MulAut S}
    (h : TwoInCoreLayer p (MulAut.congr e β) ∨ BadFix p (MulAut.congr e β)) :
    TwoInCoreLayer p β ∨ BadFix p β :=
  h.imp (twoInCoreLayer_of_congr e hp) (badFix_of_congr e)

theorem twoInCoreLayerOrBad_of_conj {S : Type} [Group S] [Finite S] (γ : MulAut S) {p : ℕ} (hp : p.Prime)
    {β : MulAut S} (h : TwoInCoreLayer p (γ * β * γ⁻¹) ∨ BadFix p (γ * β * γ⁻¹)) :
    TwoInCoreLayer p β ∨ BadFix p β :=
  h.imp (twoInCoreLayer_of_conj γ hp) (badFix_of_conj γ)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut spLinearAutGroup spSemilinearAutGroup)

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem badFix_fieldAut_sp4 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 5) (σ : K ≃+* K)
    (hσ : orderOf σ = 5) : BadFix 5 (fieldAut 2 K σ) := by
  obtain ⟨-, -, -, -, -, hfixiff, -, -, hA6, -⟩ :=
    CFSG.RankThree.CASymplecticSubfield.symplectic_prime_subfield_fixed_group_and_full_centralizer
      (K := K) (r := 2) Nat.prime_two Nat.prime_five (by norm_num) (by norm_num) (by norm_num) le_rfl hK σ hσ
  obtain ⟨-, ⟨eA⟩, h720⟩ := hA6 ⟨rfl, by norm_num⟩
  have hJ : fixSubgroup (fieldAut 2 K σ) = CFSG.RankThree.CASymplecticSubfield.subfieldFixedGroup K 2 σ :=
    Subgroup.ext fun x => (hfixiff x).symm
  have h5 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_fin]; norm_num
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h5
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  refine badFix_of_equiv _ hJ.ge (fun x hx _ => hJ ▸ hx) ?_ eA ?_ ?_ ?_
  · rw [h720]; norm_num
  · rw [hcardA]; norm_num
  · rw [hcardA]; norm_num
  · rw [hcardA]; norm_num

theorem input14_1BadSimpleOrBadOn_B2_32 :
    Input14_1BadSimpleOrBadOn fun p d => p = 5 ∧ ∃ q, d = TauCeti.LieTypeIndex.B 2 q ∧ q.card = 32 := by
  intro p hp hp5 S _ _ hs hna idx hd hchar he β hβ hβ1
  haveI := hs
  obtain ⟨d, hv⟩ := idx
  obtain ⟨rfl, q, rfl, hq32⟩ := hd
  have hq2 : q.p = 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_B 2 q]
    exact hchar
  obtain ⟨e⟩ := he
  have hM : CFSG.Open.StatedClassicalModel S .PSp 2 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  obtain ⟨⟨-, hf, hr, -⟩, K, _, _, hK, ⟨e'⟩⟩ := hM
  rw [hq2] at hK
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  refine twoInCoreLayerOrBad_of_congr e' hp ?_
  have hβ' : MulAut.congr e' β ^ 5 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h1 =>
    hβ1 ((MulAut.congr e').injective (h1.trans (map_one _).symm))
  generalize MulAut.congr e' β = β' at hβ' hβ1' ⊢
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) Nat.prime_two hf hr hK
  haveI : Fact (Nat.Prime 5) := ⟨hp⟩
  have hodd : Odd (orderOf β') :=
    (hp.odd_of_ne_two (by norm_num)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ')
  have hE : β' ∈ spSemilinearAutGroup 2 K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : β' ∈ spLinearAutGroup 2 K
  ·
    left
    have : (inner (StatedProj (StatedSp 2 K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp 2 K))).relIndex (spLinearAutGroup 2 K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp
      (by norm_num) hD hβ'
    have hna' : ∃ a b : StatedProj (StatedSp 2 K), a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hna
      exact ⟨e' a, e' b, fun h => hab (e'.injective (by rw [map_mul, map_mul, h]))⟩
    haveI : IsSimpleGroup (StatedProj (StatedSp 2 K)) := e'.symm.isSimpleGroup
    have htp : t ^ 5 = 1 := pow_eq_one_of_conj_pow_eq_one hna' (by rw [ht]; exact hβ')
    obtain ⟨x, hx, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
      (by norm_num) hp (by norm_num) htp
    have hx1 : proj 2 K x ≠ 1 := by
      rw [hx]
      intro h1
      apply hβ1'
      rw [← ht, h1, map_one]
    have hpK : 7 ≤ 5 ∨ 4 ≤ 2 ^ q.exponent := by
      right
      rw [← hqc, hq32]
      norm_num
    rw [← ht, ← hx]
    exact twoInCoreLayer_conj_sp hK hf (by norm_num) hp hp5 hpK x hxp hx1
  ·
    right
    have hord : orderOf β' = 5 := orderOf_eq_prime hβ' hβ1'
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent 5 hp _ hE hD hord
    refine badFix_of_conj h⁻¹ ?_
    rw [hβeq, show h⁻¹ * (h * fieldAut 2 K σ * h⁻¹) * h⁻¹⁻¹ = fieldAut 2 K σ by group]
    have hK32 : Nat.card K = 2 ^ 5 := by
      rw [hK, ← hqc, hq32]
      norm_num
    exact badFix_fieldAut_sp4 hK32 σ hσ

end BadInstances

section BadG2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.RecipeExcLang

theorem badFix_entrywise_G2 {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hk2 : Nat.card (fixSubfield σ) = 2) : BadFix 7 (entrywiseAdjointAut .G2 σ) := by
  classical
  obtain ⟨J, hJle, -, ⟨eJ⟩, hJ2⟩ := exists_fixed_normal_two .G2 σ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  obtain ⟨hDs, hDcard⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.g2Two_derived_exc hk2
  haveI := hDs
  obtain ⟨e1⟩ := nonempty_commutator_sub_equiv J
  obtain ⟨e2⟩ := nonempty_commutator_congr eJ
  refine badFix_of_equiv J hJle hJ2 ?_ (e1.trans e2) ?_ ?_ ?_
  · rw [Nat.card_congr eJ.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk2]
    unfold ordG2
    norm_num
  · rw [hDcard]; norm_num
  · rw [hDcard]; norm_num
  · rw [hDcard]; norm_num

theorem input14_1BadSimpleOrBadOn_G2_128 (hout : LangOuterTwo) :
    Input14_1BadSimpleOrBadOn fun p d => p = 7 ∧ ∃ q, d = TauCeti.LieTypeIndex.G2 q ∧ q.card = 2 ^ 7 := by
  intro p hp hp5 S _ _ _ _ idx hd hchar he β hβ hβ1
  obtain ⟨d, hv⟩ := idx
  obtain ⟨rfl, q, rfl, hq7⟩ := hd
  obtain ⟨e⟩ := he
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_G2 q]; exact hchar
  obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
  haveI : CharP K 2 := hq2 ▸ hKchar
  have hG2 : Tag.G2 = .G2 → 3 ≤ Nat.card K := fun _ => hK ▸ hr
  refine twoInCoreLayerOrBad_of_congr (e.trans eK) hp ?_
  have hβ' : MulAut.congr (e.trans eK) β ^ 7 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr (e.trans eK) β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr (e.trans eK)).injective (h.trans (map_one _).symm))
  generalize MulAut.congr (e.trans eK) β = β' at hβ' hβ1' ⊢
  obtain ⟨g, σ, hβe, hσp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_form_FG (Or.inr rfl) hG2 hp (by norm_num) β'
      hβ'
  by_cases hσ : σ = 1
  · left
    subst hσ
    rw [exactNormalAut_one_one_zero, mul_one] at hβe
    have hgp : g ^ 7 = 1 := by
      have : MulAut.conj (g ^ 7) = MulAut.conj 1 := by rw [map_pow, ← hβe, hβ', map_one]
      exact mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot this
    have hg1 : (g : ModGL Tag.G2 K) ≠ 1 := fun h1 => hβ1' (by
      have : g = 1 := Subtype.ext h1
      rw [hβe, this, map_one])
    refine twoInCoreLayer_untw_inndiag hout (Or.inl rfl) hG2 hp hp5 (fun h => absurd h.1 (by decide)) β'
      (g : ModGL Tag.G2 K) (adjointGroup_le_inndiagGroup g.2) (fun c => ?_) ?_ hg1
    · rw [hβe]
      simp [MulAut.conj_apply]
    · rw [← Subgroup.coe_pow, hgp]
      rfl
  · subst hβe
    obtain ⟨ψ, hψ⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_conj_eq_entrywiseAdjointAut
      Tag.G2 hp g 1 σ hσ hσp hβ'
    refine twoInCoreLayerOrBad_of_conj ψ hp ?_
    rw [hψ]
    by_cases hk2 : Nat.card (fixSubfield σ) = 2
    · exact Or.inr (badFix_entrywise_G2 σ hk2)
    · exact Or.inl (twoInCoreLayer_entrywiseAdjointAut .G2 σ hp hp5 fun _ h => absurd h hk2)

end BadG2

section BadRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem badFix_of_fixSubgroup_equiv_reeTwo {S : Type} [Group S] [Finite S] {β : MulAut S} {k : Type}
    [Field k] [Finite k] [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2)
    (eC : ↥(fixSubgroup β) ≃* ↥(ReeTag.F4.reeGamma k 0)) : BadFix 13 β := by
  classical
  obtain ⟨e1⟩ := nonempty_commutator_sub_equiv (fixSubgroup β)
  obtain ⟨e2⟩ := nonempty_commutator_congr (eC.trans (CFSG.LieType.Ree.ReeTag.reeFixedEquivReeGamma k 0).symm)
  haveI := CFSG.ComponentClassification.ExcSelector.isSimpleGroup_commutator_reeFixed_tits hk
  have hidx := CFSG.ComponentClassification.ExcSelector.index_commutator_reeFixed_tits_le hk
  have hcardΓ : Nat.card ↥(ReeTag.F4.reeGamma k 0) = 35942400 := by
    rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion 0 k
      (by simpa using hk)).1]
    norm_num
  have hmul := Subgroup.card_mul_index (commutator ↥(reeFixed ReeTag.F4 k 0))
  rw [Nat.card_congr (CFSG.LieType.Ree.ReeTag.reeFixedEquivReeGamma k 0).toEquiv, hcardΓ] at hmul
  have hidx0 : (commutator ↥(reeFixed ReeTag.F4 k 0)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨i, hi⟩ : ∃ i, (commutator ↥(reeFixed ReeTag.F4 k 0)).index = i := ⟨_, rfl⟩
  rw [hi] at hmul hidx hidx0
  have h2 : 2 ∣ Nat.card ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) := by
    interval_cases i <;> omega
  refine badFix_of_equiv (fixSubgroup β) le_rfl (fun x hx _ => hx) ?_ (e1.trans e2) h2 ?_ ?_
  · rw [Nat.card_congr eC.toEquiv, hcardΓ]
    norm_num
  · interval_cases i <;> omega
  · intro hpr
    have := hpr.eq_one_or_self_of_dvd 2 h2
    interval_cases i <;> omega

theorem input14_1BadSimpleOrBadOn_reeF4_13 :
    Input14_1BadSimpleOrBadOn fun p d => p = 13 ∧ d = TauCeti.LieTypeIndex.reeF4 6 := by
  intro p hp hp5 S _ _ _ _ idx hd _ he β hβ hβ1
  obtain ⟨d, hv⟩ := idx
  obtain ⟨rfl, rfl⟩ := hd
  obtain ⟨e⟩ := he
  have hm : 1 ≤ 6 := by norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (GaloisField 2 (2 * 6 + 1)) ReeTag.F4.prime :=
    (inferInstance : CharP (GaloisField 2 (2 * 6 + 1)) 2)
  have hK : Nat.card (GaloisField 2 (2 * 6 + 1)) = 2 ^ (2 * 6 + 1) := by
    rw [GaloisField.card 2 (2 * 6 + 1) (by omega)]
  obtain ⟨eK⟩ := CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeGamma_equiv_cat_of_card hm hv hK
  haveI : Finite (ModGL ReeTag.F4.tag (GaloisField 2 (2 * 6 + 1))) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma (GaloisField 2 (2 * 6 + 1)) 6) := Subtype.finite
  refine twoInCoreLayerOrBad_of_congr (e.trans eK) hp ?_
  have hβ' : MulAut.congr (e.trans eK) β ^ 13 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr (e.trans eK) β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr (e.trans eK)).injective (h.trans (map_one _).symm))
  generalize MulAut.congr (e.trans eK) β = β' at hβ' hβ1' ⊢
  haveI : Fact (Nat.Prime 13) := ⟨hp⟩
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_inner_or_field hm hK hp hβ' hβ1' with
    ⟨y, rfl, hy, hy1⟩ | ⟨σ, g, hσ, rfl⟩
  · exact Or.inl (twoInCoreLayer_reeGamma_F4_inner hm hK hp hp5 y (orderOf_eq_prime hy hy1))
  · refine twoInCoreLayerOrBad_of_conj (MulAut.conj g)⁻¹ hp ?_
    rw [show (MulAut.conj g)⁻¹ * (MulAut.conj g * ReeTag.F4.reeGammaFieldAut _ 6 σ * (MulAut.conj g)⁻¹) *
      (MulAut.conj g)⁻¹⁻¹ = ReeTag.F4.reeGammaFieldAut _ 6 σ by group]
    obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_fixSubgroup_fieldAut_equiv' hK hp (by norm_num) σ hσ
    have hb : b = 0 := by
      have h1 := card_fixSubfield_pow σ
      rw [hσ, hkcard, hK, ← pow_mul] at h1
      have := Nat.pow_right_injective le_rfl h1
      omega
    subst hb
    haveI := hchar
    haveI : Finite (fixSubfield σ) := Subtype.finite
    exact Or.inr (badFix_of_fixSubgroup_equiv_reeTwo (by simpa using hkcard) eC)

end BadRee

section BadDecompFamily

theorem badDecomp_conj_of_family {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (x : X)
    (hlay : PerfectInLayer (MulAut.conj x)) {ι : Type} [Finite ι] (A : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set X)) (i₀ : ι)
    (hind : Disjoint (A i₀) (⨆ (j) (_ : j ≠ i₀), A j)) (h2 : ∀ i, i ≠ i₀ → TwoGood p ↥(A i))
    (hBp : ¬ p ^ 2 ∣ Nat.card (A i₀)) (hEs : IsSimpleGroup ↥⁅A i₀, A i₀⁆)
    (hEnc : ∃ a b : ↥⁅A i₀, A i₀⁆, a * b ≠ b * a) (hE2 : 2 ∣ Nat.card ↥⁅A i₀, A i₀⁆)
    (hEp : p ∣ Nat.card ↥⁅A i₀, A i₀⁆)
    (hγ : ∀ γ : MulAut X, γ * MulAut.conj x = MulAut.conj x * γ → γ ^ p = 1 → ∀ b ∈ A i₀, γ b ∈ A i₀) :
    BadDecomp p (MulAut.conj x) := by
  classical
  have hfix : fixSubgroup (MulAut.conj x) = ⨆ i, A i := by
    rw [hjoin, fixSubgroup_conj_eq_centralizer']
  have hAfix : ∀ i, A i ≤ fixSubgroup (MulAut.conj x) := fun i => hfix ▸ le_iSup A i
  have hAn : ∀ i, ∀ c ∈ fixSubgroup (MulAut.conj x), ∀ b ∈ A i, c * b * c⁻¹ ∈ A i := by
    intro i c hc' b hb
    rw [hfix] at hc'
    have h1 := conj_mem_map_of_family A hc (M := (⊤ : Subgroup ↥(A i))) Subgroup.normal_top hc'
      (b := b) ⟨⟨b, hb⟩, Subgroup.mem_top _, rfl⟩
    obtain ⟨y, -, hy⟩ := h1
    rw [← hy]
    exact y.2
  have h2' : ∀ i, ∃ M : Subgroup X, M ≤ A i ∧ (∀ g ∈ A i, IsPGroup 2 ↥(Subgroup.zpowers g) → g ∈ M) ∧
      (i ≠ i₀ → (⁅M, M⁆ = M ∨ (Nat.Coprime p (Nat.card M) ∧
        ∀ c ∈ fixSubgroup (MulAut.conj x), ∀ m ∈ M, c * m * c⁻¹ ∈ M))) := by
    intro i
    by_cases hi : i = i₀
    · exact ⟨A i, le_rfl, fun g hg _ => hg, fun h => absurd hi h⟩
    · obtain ⟨M, hMn, hM2, hM⟩ := h2 i hi
      refine ⟨M.map (A i).subtype, Subgroup.map_subtype_le _, fun g hg hg2 => ?_, fun _ => ?_⟩
      · obtain ⟨m, hm⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hg2
        have hg2' : IsPGroup 2 ↥(Subgroup.zpowers (⟨g, hg⟩ : ↥(A i))) :=
          Inputs141d.isPGroup_zpowers_of_pow (m := m) (Subtype.ext (by simpa using hm))
        exact ⟨⟨g, hg⟩, hM2 _ hg2', rfl⟩
      · rcases hM with hperf | hcop
        · left
          rw [← Subgroup.map_commutator, hperf]
        · right
          refine ⟨by rwa [Subgroup.card_map_of_injective (A i).subtype_injective], fun c hc' m hm => ?_⟩
          rw [hfix] at hc'
          exact conj_mem_map_of_family A hc hMn hc' hm
  choose M hMA hM2 hM using h2'
  set N : Subgroup X := ⨆ (i) (_ : i ≠ i₀), M i with hNdef
  have hNle : N ≤ ⨆ (j) (_ : j ≠ i₀), A j := iSup₂_mono fun i _ => hMA i
  have hNcore : N ≤ GLAPPrimeCoreOf p (fixSubgroup (MulAut.conj x)) ⊔ GLAPLayer p (fixSubgroup (MulAut.conj x)) := by
    refine iSup₂_le fun i hi => ?_
    have hMfix : M i ≤ fixSubgroup (MulAut.conj x) := (hMA i).trans (hAfix i)
    rcases hM i hi with hperf | ⟨hcop, hnorm⟩
    · exact (hlay _ hMfix hperf).trans (glaLayer_le_core_sup_layer hp _)
    · refine le_sup_of_le_left (le_glaPPrimeCoreOf_of_isSubnormal hp (isSubnormal_of_normal hMfix ?_) hcop)
      refine ⟨fun n hn c => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hnorm c c.2 n hn
  have hcommBN : ∀ b ∈ A i₀, ∀ n ∈ N, b * n = n * b := by
    have hle : N ≤ Subgroup.centralizer (A i₀ : Set X) := by
      refine iSup₂_le fun i hi => ?_
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hc i i₀ hi m (hMA i hm) b hb).eq.symm
    intro b hb n hn
    exact Subgroup.mem_centralizer_iff.1 (hle hn) b hb
  refine ⟨A i₀, ⁅A i₀, A i₀⁆, hAfix i₀, hAn i₀, hγ, hBp, Subgroup.commutator_le_self _, fun b hb e he => ?_,
    hEs, hEnc, hE2, hEp, fun g hg hg2 => ?_⟩
  · exact conj_mem_commutator_of_normalizes (fun y hy => (A i₀).mul_mem ((A i₀).mul_mem hb hy) ((A i₀).inv_mem hb))
      (fun y hy => (A i₀).mul_mem ((A i₀).mul_mem ((A i₀).inv_mem hb) hy) hb) he
  · rw [hfix] at hg
    have hgM : g ∈ ⨆ i, M i := Inputs141d.mem_iSup_of_two A M hc (fun i y hy hy2 => hM2 i y hy hy2) hg hg2
    rw [iSup_split_single M i₀] at hgM
    have hgBN : g ∈ A i₀ ⊔ N := (sup_le_sup_right (hMA i₀) N) hgM
    obtain ⟨b, hb, n, hn, rfl⟩ := Input183.mem_sup_of_commute hcommBN hgBN
    obtain ⟨k, hk⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hg2
    have hbk : b ^ (2 ^ k) = 1 := by
      have h1 : b ^ (2 ^ k) * n ^ (2 ^ k) = 1 := by
        rw [← (Commute.mul_pow (hcommBN b hb n hn)), hk]
      have h2 : b ^ (2 ^ k) = (n ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hmem : b ^ (2 ^ k) ∈ A i₀ ⊓ ⨆ (j) (_ : j ≠ i₀), A j := by
        refine Subgroup.mem_inf.2 ⟨pow_mem hb _, ?_⟩
        rw [h2]
        exact inv_mem (pow_mem (hNle hn) _)
      rw [hind.eq_bot, Subgroup.mem_bot] at hmem
      exact hmem
    exact ⟨b, hb, isPGroup_zpowers_of_pow_eq_one hbk, n, hNcore hn, rfl⟩

end BadDecompFamily

section SympTwo

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut spLinearAutGroup spSemilinearAutGroup)

open CFSG.RankThree.PartOne.KCSpIsotypic (exists_mulEquiv_sesqUnitaryGroup_statedSp)

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (exists_finset_card_four_of_paired)

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {r : ℕ} {K : Type} [Field K]

theorem exists_conj_of_pow_eq_one_sp_two [Finite K] (hK : Nat.card K = 2) (hr : 2 ≤ r) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (γ : MulAut (StatedProj (StatedSp r K))) (hγ : γ ^ p = 1) :
    ∃ t : StatedProj (StatedSp r K), γ = MulAut.conj t := by
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) Nat.prime_two le_rfl hr hK'
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hγ1 : γ = 1
  · exact ⟨1, by rw [hγ1, map_one]⟩
  have hodd : Odd (orderOf γ) := (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hγ)
  have hE : γ ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : γ ∈ spLinearAutGroup r K
  · have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp hp2 hD hγ
    exact ⟨t, ht.symm⟩
  · exfalso
    obtain ⟨h5, -⟩ := hO.descent p hp γ hE hD (orderOf_eq_prime hγ hγ1)
    have := Nat.le_of_dvd one_pos h5
    have := hp.two_le
    omega

theorem twoGood_statedSp_of_ne (s : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hK : 7 ≤ p ∨ 4 ≤ Nat.card K ∨ s ≠ 2) : TwoGood p ↥(StatedSp s K) := by
  have hcard := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) s
  have hK2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hK3 : Nat.card K ≠ 3 := by
    intro h
    haveI : Fintype K := Fintype.ofFinite K
    have h2 := FiniteField.cast_card_eq_zero K
    rw [Fintype.card_eq_nat_card, h] at h2
    have h3' : ((3 : ℕ) : K) = 1 := by
      have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
      rw [show (3 : ℕ) = 2 + 1 by norm_num, Nat.cast_add, this, zero_add, Nat.cast_one]
    rw [h3'] at h2
    exact one_ne_zero h2
  by_cases hs : 1 ≤ s
  · by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨ (Nat.card K = 2 ∧ 3 ≤ s)
    · exact twoGood_of_perfect (Group.isPerfect_def.mp (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hq).1)
    · apply twoGood_of_coprime
      have hK4 : Nat.card K = 2 := by
        by_contra h
        exact hq (Or.inl (Or.inr (by omega)))
      rcases (show s = 1 ∨ s = 2 by
          by_contra h
          exact hq (Or.inr (Or.inr ⟨hK4, by omega⟩))) with rfl | rfl
      · rw [hcard, hK4, show 2 ^ 1 ^ 2 * ∏ j ∈ Finset.Icc 1 1, (2 ^ (2 * j) - 1) = 2 ^ 1 * 3 ^ 1 by decide]
        exact coprime_two_pow_mul_three_pow hp hp5 1 1
      · have hp7 : 7 ≤ p := by
          rcases hK with h7 | h4 | hs2
          · exact h7
          · omega
          · exact absurd rfl hs2
        rw [hcard, hK4, show 2 ^ 2 ^ 2 * ∏ j ∈ Finset.Icc 1 2, (2 ^ (2 * j) - 1) = 720 by decide]
        rw [show (720 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 by norm_num]
        refine Nat.Coprime.mul_right (coprime_two_pow_mul_three_pow hp hp5 4 2) ?_
        exact (Nat.coprime_primes hp Nat.prime_five).2 (by omega)
  · apply twoGood_of_coprime
    obtain rfl : s = 0 := by omega
    rw [hcard]
    simp

theorem twoGood_spSupported_of [Finite K] [CharP K 2] {f p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : 2 ≤ 2 ^ f)
    {x : StatedSp r K} {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks 2 f p x a)
    (O : reciprocalOrbits (spEnd x))
    (hX1 : (X - 1 : K[X]) ∈ (O : Set K[X]) →
      7 ≤ p ∨ 4 ≤ Nat.card K ∨ Module.finrank K (primaryComponent (spEnd x) (X - 1)) ≠ 4) :
    TwoGood p ↥(spSupported x (O : Set K[X])) := by
  obtain ⟨O, h, hh, rfl⟩ := O
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h = h
  · have hO : ({h, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h} : Set K[X]) = {h} := by
      rw [hself, Set.pair_eq_singleton]
    show TwoGood p ↥(spSupported x {h, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h})
    rw [hO]
    by_cases h1 : h = X - 1
    · subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hh
      obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
      refine twoGood_of_mulEquiv (φ.trans e) (twoGood_statedSp_of_ne s K hp hp5 ?_)
      rcases hX1 (Set.mem_insert _ _) with h7 | h4 | hfin
      · exact Or.inl h7
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr fun hs2 => hfin (by rw [hs, hs2]))
    · obtain ⟨d, -, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
        (blocks.selfDual ⟨h, hh⟩ h1 hself).exists_half
      exact twoGood_of_mulEquiv φ (twoGood_sesqUnitaryGroup hE hHf hHfl hp hp5)
  · have hP := blocks.paired ⟨h, hh⟩ (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    haveI : CharP (AdjoinRoot ((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])) 2 :=
      charP_of_injective_algebraMap
        (algebraMap K (AdjoinRoot ((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X]))).injective 2
    haveI : Finite (AdjoinRoot ((⟨h, hh⟩ : primaryFactors (spEnd x)) : K[X])) := Module.finite_of_finite K
    exact twoGood_of_mulEquiv φ
      (twoGood_generalLinearGroup p (Or.inr (exists_finset_card_four_of_paired (by omega) hq hP)))

theorem mem_primaryFactors_of_mem_orbit {f p : ℕ} {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (blocks : SpPrimaryBlocks 2 f p x a) (O : reciprocalOrbits (spEnd x))
    (hO : (X - 1 : K[X]) ∈ (O : Set K[X])) : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
  obtain ⟨O, h, hh, rfl⟩ := O
  rcases hO with hO | hO
  · rw [hO]
    exact hh
  · have h1 := blocks.bijOn.mapsTo hh
    rw [Set.mem_singleton_iff.1 hO]
    exact h1

theorem twoInCoreLayer_conj_sp_of [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hr : 1 ≤ r) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (x : StatedSp r K) (hx : x ^ p = 1) (hx1 : proj r K x ≠ 1)
    (hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) →
      7 ≤ p ∨ 4 ≤ 2 ^ f ∨ Module.finrank K (primaryComponent (spEnd x) (X - 1)) ≠ 4) :
    TwoInCoreLayer p (MulAut.conj (proj r K x)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have ha : orderOf (proj r K x) = p := orderOf_eq_prime (by rw [← map_pow, hx, map_one]) hx1
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hxp : orderOf x = p := orderOf_eq_prime hx hx1'
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hf hK hp
    (by omega) (by omega) hr _ ha).2 x rfl hxp
  have hpK' : ((p : ℕ) : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0
    omega
  have hsq := (altPrimaryData_spLin hpK' hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) := (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hker : (proj r K).ker ≤ Subgroup.center ↥(StatedSp r K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have hodd : Nat.Coprime 2 (Nat.card (proj r K).ker) := by
    rw [CFSG.RankThree.PartOne.KCSpFull.ker_proj_eq_bot_of_even hr (by rw [hK]; exact dvd_pow_self 2 (by omega)),
      Subgroup.card_bot]
    exact Nat.coprime_one_right 2
  have hA := fun O : reciprocalOrbits (spEnd x) =>
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported (by omega) hq hsq
      blocks O
  have hlay := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_of_orbit_family (proj r K)
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective hker x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb) hjoin hA
  refine twoInCoreLayer_conj_of_family (proj r K) CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
    hker hodd hp x hlay (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb) hjoin
    (fun O => twoGood_spSupported_of hp hp5 hq blocks O fun hO => ?_)
  rw [hK]
  exact hX1 (mem_primaryFactors_of_mem_orbit blocks O hO)

theorem badDecomp_conj_sp_two [Finite K] (hK2 : Nat.card K = 2) (hr : 2 ≤ r)
    (hZ : Subgroup.center ↥(StatedSp r K) = ⊥)
    (hinn : ∀ γ : MulAut ↥(StatedSp r K), γ ^ 5 = 1 → ∃ y, γ = MulAut.conj y)
    (x : StatedSp r K) (hx : x ^ 5 = 1) (hx1 : proj r K x ≠ 1)
    (hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x))
    (hfin : Module.finrank K (primaryComponent (spEnd x) (X - 1)) = 4) :
    BadDecomp 5 (MulAut.conj x) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
  have ha : orderOf (proj r K x) = 5 := orderOf_eq_prime (by rw [← map_pow, hx, map_one]) hx1
  have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hxp : orderOf x = 5 := orderOf_eq_prime hx hx1'
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two le_rfl hK Nat.prime_five
    (by norm_num) (by norm_num) (by omega) _ ha).2 x rfl hxp
  have hpK' : ((5 : ℕ) : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    norm_num at h0
  have hsq := (altPrimaryData_spLin hpK' hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) := (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, hindep, hjoin⟩ := blocks.directProduct
  have hq : 2 ≤ 2 ^ 1 := by norm_num
  set A : reciprocalOrbits (spEnd x) → Subgroup ↥(StatedSp r K) := fun O => spSupported x (O : Set K[X])
    with hAdef
  have hc : ∀ i j : reciprocalOrbits (spEnd x), i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b :=
    fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  have hlay : PerfectInLayer (MulAut.conj x) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_of_orbit_family
      (MonoidHom.id _) Function.surjective_id (fun g hg => by
        rw [MonoidHom.mem_ker] at hg
        rw [show g = 1 from hg]
        exact one_mem _) x A hc hjoin
      (fun O => CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
        (by omega) hq hsq blocks O)
  set O₁ : reciprocalOrbits (spEnd x) :=
    ⟨{X - 1, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial (X - 1)}, X - 1, hX1, rfl⟩ with hO₁
  have hAO₁ : A O₁ = spSupported x {X - 1} := by
    show spSupported x {X - 1, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial (X - 1)} = _
    rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
  have hmemO : ∀ O : reciprocalOrbits (spEnd x), (X - 1 : K[X]) ∈ (O : Set K[X]) → O = O₁ := by
    rintro ⟨O, h, hh, rfl⟩ hO
    have hh' : h = X - 1 := by
      rcases hO with hO | hO
      · exact hO.symm
      · have h1 : CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h =
            CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial (X - 1) := by
          rw [reciprocalPolynomial_X_sub_one]
          exact (Set.mem_singleton_iff.1 hO).symm
        exact blocks.bijOn.injOn hh hX1 h1
    subst hh'
    rfl
  obtain ⟨φ, -⟩ := blocks.fixedFactor hX1
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp
    (B := (spForm r K).restrict (primaryComponent (spEnd x) (X - 1)))
    (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
  have hs2 : s = 2 := by omega
  subst hs2
  have ψ : ↥(A O₁) ≃* ↥(StatedSp 2 K) := (MulEquiv.subgroupCongr hAO₁).trans (φ.trans e)
  have hcardB : Nat.card ↥(A O₁) = 720 := by
    rw [Nat.card_congr ψ.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK2]
    decide
  obtain ⟨e1⟩ := nonempty_commutator_sub_equiv (A O₁)
  obtain ⟨e2⟩ := nonempty_commutator_congr ψ
  have eA := (e1.trans e2).trans (CFSG.SignalizerFunctorTheorem.NonLocal.commutatorSpTwoEquiv hK2)
  have h6 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_fin]; norm_num
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h6
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  haveI hEs : IsSimpleGroup ↥⁅A O₁, A O₁⁆ := eA.isSimpleGroup
  have hcardE : Nat.card ↥⁅A O₁, A O₁⁆ = 360 := by rw [Nat.card_congr eA.toEquiv, hcardA]
  have hEnc : ∃ a b : ↥⁅A O₁, A O₁⁆, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup ↥⁅A O₁, A O₁⁆ :=
      { (inferInstance : Group ↥⁅A O₁, A O₁⁆) with mul_comm := fun a b => hcon a b }
    have hprime : (Nat.card ↥⁅A O₁, A O₁⁆).Prime := IsSimpleGroup.prime_card
    rw [hcardE] at hprime
    exact absurd hprime (by norm_num)
  have hγ : ∀ γ : MulAut ↥(StatedSp r K), γ * MulAut.conj x = MulAut.conj x * γ → γ ^ 5 = 1 →
      ∀ b ∈ A O₁, γ b ∈ A O₁ := by
    intro γ hγx hγ5 b hb
    obtain ⟨y, rfl⟩ := hinn γ hγ5
    have hyx : y * x = x * y := by
      apply CFSG.SeitzReduction.mulAut_conj_injective_of_center_eq_bot hZ
      rw [map_mul, map_mul]
      exact hγx
    have hyC : y ∈ ⨆ O, A O := by
      rw [hjoin]
      exact Subgroup.mem_centralizer_singleton_iff.2 hyx
    obtain ⟨y', -, hy'⟩ := conj_mem_map_of_family A hc (M := (⊤ : Subgroup ↥(A O₁))) Subgroup.normal_top hyC
      (b := b) ⟨⟨b, hb⟩, Subgroup.mem_top _, rfl⟩
    rw [MulAut.conj_apply, ← hy']
    exact y'.2
  have h2 : ∀ O, O ≠ O₁ → TwoGood 5 ↥(A O) := fun O hO =>
    twoGood_spSupported_of Nat.prime_five le_rfl hq blocks O (fun hX => absurd (hmemO O hX) hO)
  exact badDecomp_conj_of_family Nat.prime_five x hlay A hc hjoin O₁ (hindep O₁) h2
    (by rw [hcardB]; norm_num) hEs hEnc (by rw [hcardE]; norm_num) (by rw [hcardE]; norm_num) hγ

theorem twoInCoreLayerOrDecomp_conj_sp_two [Finite K] (hK2 : Nat.card K = 2) (hr : 2 ≤ r)
    (hna : ∃ a b : StatedProj (StatedSp r K), a * b ≠ b * a) [IsSimpleGroup (StatedProj (StatedSp r K))]
    (x : StatedSp r K) (hx : x ^ 5 = 1) (hx1 : proj r K x ≠ 1) :
    TwoInCoreLayer 5 (MulAut.conj (proj r K x)) ∨ BadDecomp 5 (MulAut.conj (proj r K x)) := by
  classical
  by_cases hbad : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) ∧
      Module.finrank K (primaryComponent (spEnd x) (X - 1)) = 4
  · right
    have hker : (proj r K).ker = ⊥ :=
      CFSG.RankThree.PartOne.KCSpFull.ker_proj_eq_bot_of_even (by omega) (by rw [hK2])
    have hinj : Function.Injective (proj r K) := (MonoidHom.ker_eq_bot_iff _).1 hker
    set ε : ↥(StatedSp r K) ≃* StatedProj (StatedSp r K) :=
      MulEquiv.ofBijective (proj r K) ⟨hinj, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective⟩
      with hε
    refine badDecomp_of_congr ε.symm Nat.prime_five ?_
    have e1 : MulAut.congr ε.symm (MulAut.conj (proj r K x)) = MulAut.conj x := by
      refine MulEquiv.ext fun g => ?_
      apply ε.injective
      show ε (ε.symm (proj r K x * ε.symm.symm g * (proj r K x)⁻¹)) = ε (x * g * x⁻¹)
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv]
      rfl
    rw [e1]
    have hZS : Subgroup.center (StatedProj (StatedSp r K)) = ⊥ :=
      CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hna
    have hZ : Subgroup.center ↥(StatedSp r K) = ⊥ := by
      have h1 : (Subgroup.center ↥(StatedSp r K)).map (ε : ↥(StatedSp r K) →* StatedProj (StatedSp r K)) = ⊥ := by
        rw [Subgroup.map_center_eq ε, hZS]
      exact (Subgroup.map_eq_bot_iff_of_injective _ ε.injective).1 h1
    refine badDecomp_conj_sp_two hK2 hr hZ (fun γ hγ => ?_) x hx hx1 hbad.1 hbad.2
    have hγ' : MulAut.congr ε γ ^ 5 = 1 := by rw [← map_pow, hγ, map_one]
    obtain ⟨t, ht⟩ := exists_conj_of_pow_eq_one_sp_two hK2 hr Nat.prime_five (by norm_num) _ hγ'
    refine ⟨ε.symm t, ?_⟩
    refine MulEquiv.ext fun g => ?_
    apply ε.injective
    have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ (ε g)) ht
    change ε (γ (ε.symm (ε g))) = t * ε g * t⁻¹ at h1
    rw [MulEquiv.symm_apply_apply] at h1
    show ε (γ g) = ε (ε.symm t * g * (ε.symm t)⁻¹)
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · left
    have hK : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
    exact twoInCoreLayer_conj_sp_of hK le_rfl (by omega) Nat.prime_five le_rfl x hx hx1
      fun hX => Or.inr (Or.inr fun h4 => hbad ⟨hX, h4⟩)

theorem input14_1BadSimpleOrDecompOn_B_two :
    Input14_1BadSimpleOrDecompOn fun p d => p = 5 ∧ ∃ r q, d = TauCeti.LieTypeIndex.B r q ∧ q.card = 2 := by
  intro p hp hp5 S _ _ hs hna idx hd hchar he β hβ hβ1
  haveI := hs
  obtain ⟨d, hv⟩ := idx
  obtain ⟨rfl, r, q, rfl, hq2c⟩ := hd
  have hq2 : q.p = 2 := by
    rw [← TauCeti.LieTypeIndex.characteristic_B r q]
    exact hchar
  obtain ⟨e⟩ := he
  have hr0 := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hM : CFSG.Open.StatedClassicalModel S .PSp r q.p q.exponent := by
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    · exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2 hr3 e
  obtain ⟨⟨-, hf, hr, -⟩, K, _, _, hK, ⟨e'⟩⟩ := hM
  rw [hq2] at hK
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hK2 : Nat.card K = 2 := by rw [hK, ← hqc, hq2c]
  refine twoInCoreLayerOrDecomp_of_congr e' hp ?_
  have hβ' : MulAut.congr e' β ^ 5 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e' β ≠ 1 := fun h1 =>
    hβ1 ((MulAut.congr e').injective (h1.trans (map_one _).symm))
  generalize MulAut.congr e' β = β' at hβ' hβ1' ⊢
  haveI : IsSimpleGroup (StatedProj (StatedSp r K)) := e'.symm.isSimpleGroup
  have hna' : ∃ a b : StatedProj (StatedSp r K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e' a, e' b, fun h => hab (e'.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨t, rfl⟩ := exists_conj_of_pow_eq_one_sp_two hK2 hr hp (by norm_num) β' hβ'
  have htp : t ^ 5 = 1 := pow_eq_one_of_conj_pow_eq_one hna' hβ'
  obtain ⟨x, hx, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
    (by omega) hp (by norm_num) htp
  have hx1 : proj r K x ≠ 1 := by
    rw [hx]
    intro h1
    apply hβ1'
    rw [h1, map_one]
  rw [← hx]
  exact twoInCoreLayerOrDecomp_conj_sp_two hK2 hr hna' x hxp hx1

end SympTwo

theorem not_sq_dvd_card_closure_two {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hG : ¬ p ^ 3 ∣ Nat.card G) {h : G} (hh : orderOf h = p) :
    ¬ p ^ 2 ∣ Nat.card (Subgroup.closure
      {x : G | x ∈ Subgroup.centralizer ({h} : Set G) ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set J := Subgroup.closure {x : G | x ∈ Subgroup.centralizer ({h} : Set G) ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}
    with hJdef
  have hJC : J ≤ Subgroup.centralizer ({h} : Set G) := le_of_closure_two _
  intro hdvd
  obtain ⟨P⟩ : Nonempty (Sylow p ↥J) := inferInstance
  have hP2 : p ^ 2 ∣ Nat.card ↥(P : Subgroup ↥J) := P.pow_dvd_card_of_pow_dvd_card hdvd
  set P' : Subgroup G := (P : Subgroup ↥J).map J.subtype with hP'def
  have hP'card : Nat.card ↥P' = Nat.card ↥(P : Subgroup ↥J) :=
    Subgroup.card_map_of_injective J.subtype_injective
  have hP'p : IsPGroup p ↥P' := P.isPGroup'.map J.subtype
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP'p
  have hdvdG : ∀ (H : Subgroup G) (m : ℕ), Nat.card H = p ^ m → m ≤ 2 := by
    intro H m hm
    by_contra hm2
    apply hG
    exact (pow_dvd_pow p (by omega : 3 ≤ m)).trans (hm ▸ Subgroup.card_subgroup_dvd_card H)
  have hn2 : n = 2 := by
    have h1 := hdvdG P' n hn
    have h2 : p ^ 2 ∣ p ^ n := by rw [← hn, hP'card]; exact hP2
    have h3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2
    omega
  have hhN : Subgroup.zpowers h ≤ Subgroup.normalizer (P' : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨j, hjP, rfl⟩ := hy
    have hjh : (j : G) * h = h * j :=
      Subgroup.mem_centralizer_singleton_iff.1 (hJC j.2)
    have e : h * J.subtype j * h⁻¹ = J.subtype j := by
      show h * (j : G) * h⁻¹ = j
      rw [← hjh]
      group
    rw [e]
    exact ⟨j, hjP, rfl⟩
  have hzp : IsPGroup p ↥(Subgroup.zpowers h) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hh, pow_one])
  have hQ := IsPGroup.to_sup_of_normal_right' hzp hP'p hhN
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hQ
  have hm2 := hdvdG _ m hm
  have hQP : Subgroup.zpowers h ⊔ P' = P' := by
    symm
    refine Subgroup.eq_of_le_of_card_ge le_sup_right ?_
    rw [hm, hn, hn2]
    exact Nat.pow_le_pow_right hp.pos hm2
  have hhP' : h ∈ P' := hQP ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  obtain ⟨j, hjP, hjh⟩ := hhP'
  have hjc : j ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hJC g.2)
    show (g : G) * (j : G) = (j : G) * (g : G)
    have hj' : (j : G) = h := hjh
    rw [hj']
    exact h1
  have hjp : j ^ (p ^ 1) = 1 := by
    apply Subtype.ext
    show (j : G) ^ (p ^ 1) = 1
    have hj' : (j : G) = h := hjh
    rw [hj', pow_one, ← hh, pow_orderOf_eq_one]
  have hgen : ∀ H : Subgroup ↥J, (∀ g : ↥J, (∃ k : ℕ, g ^ (2 ^ k) = 1) → g ∈ H) → H = ⊤ := by
    intro H hH
    have hle : J ≤ H.map J.subtype := by
      refine (Subgroup.closure_le (H.map J.subtype)).2 ?_
      intro x hx
      have hxJ : x ∈ J := Subgroup.subset_closure hx
      obtain ⟨k, hk⟩ := hx.2
      exact ⟨⟨x, hxJ⟩, hH _ ⟨k, Subtype.ext (by simpa using hk)⟩, rfl⟩
    rw [eq_top_iff]
    rintro ⟨l, hl⟩ -
    obtain ⟨h', hh', hh'l⟩ := hle hl
    have e1 : h' = ⟨l, hl⟩ := Subtype.ext hh'l
    rw [← e1]
    exact hh'
  have hPcard : Nat.card ↥(P : Subgroup ↥J) = p ^ 2 := by rw [← hP'card, hn, hn2]
  have hPc : ∀ a b : ↥(P : Subgroup ↥J), a * b = b * a := IsPGroup.commutative_of_card_eq_prime_sq hPcard
  have hj1 := eq_one_of_mem_center_of_twoGen hp hp2 hgen P hPc hjc hjp
  have hh1 : h = 1 := by rw [← hjh, hj1]; rfl
  rw [hh1, orderOf_one] at hh
  exact hp.one_lt.ne hh

theorem eq_zero_or_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  by_contra hx
  push Not at hx
  have h3 : ({0, 1, x} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hx.2.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, hx.1.symm⟩
  have h4 := Finset.card_le_univ ({0, 1, x} : Finset K)
  rw [h3, Fintype.card_eq_nat_card, hK] at h4
  omega

theorem ringEquiv_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (σ : K ≃+* K) :
    σ = 1 := by
  ext x
  rcases eq_zero_or_eq_one_of_card_two hK x with rfl | rfl
  · simp
  · simp

section BadF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.RecipeExcLang

theorem badFix_of_langSetup {τ : Tag} {K : Type} [Field K] [Finite K] (hK2 : ringChar K = 2) {p₀ : ℕ}
    (S' : LangSetup τ (AlgebraicClosure K) p₀) {C : Type} [Group C] [Finite C]
    (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι) (hrange : ι.range = S'.Γ)
    (β : MulAut C) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) (hT : rootDiagUnit τ a ∈ S'.D.torus)
    {p : ℕ} (hp : p.Prime) (hp5 : p = 5) (hap : ∀ i, a i ^ p = 1) (i : KernelComponent (rootCharHom a))
    (eA : ↥⁅ratTwo (rationalRoots S'.ρ (rootCharHom a) i) S'.D.model,
        ratTwo (rationalRoots S'.ρ (rootCharHom a) i) S'.D.model⁆ ≃* alternatingGroup (Fin 6))
    (hJ : ¬ p ^ 2 ∣ Nat.card (Subgroup.closure {x : C | x ∈ fixSubgroup β ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1})) :
    BadFix p β := by
  classical
  subst hp5
  set M := S'.D.model with hMdef
  set d := rootDiagUnit τ a with hd
  set Ti := ratTwo (rationalRoots S'.ρ (rootCharHom a) i) M with hTi
  set J := Subgroup.closure {x : C | x ∈ fixSubgroup β ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1} with hJdef
  have hker := rho_mem_kernelRoots_of_mem_torus S' hT
  have hform := S'.frob.iform_eq
  have hTA : ∀ Ψ : Set (Fin τ.rank → ℤ), ratTwo Ψ M ≤ rootSpan τ (AlgebraicClosure K) Ψ ⊓ M := by
    intro Ψ
    rw [ratTwo, Subgroup.closure_le]
    rintro g ⟨hgA, hgM, -⟩
    exact ⟨hgA, hgM⟩
  have hTiC : Ti ≤ Subgroup.centralizer {d} :=
    (hTA _).trans (inf_le_left.trans (rootSpan_le_centralizer a (rationalRoots_subset_kernelRoots hker i)))
  have hDΓ : ⁅Ti, Ti⁆ ≤ S'.Γ :=
    Subgroup.commutator_mono ((hTA _).trans inf_le_right) ((hTA _).trans inf_le_right)
  set E : Subgroup C := ⁅Ti, Ti⁆.comap ι with hEdef
  have hEmap : E.map ι = ⁅Ti, Ti⁆ := Subgroup.map_comap_eq_self (by rw [hrange]; exact hDΓ)
  have eE : ↥E ≃* alternatingGroup (Fin 6) :=
    ((E.equivMapOfInjective ι hι).trans (MulEquiv.subgroupCongr hEmap)).trans eA
  have hEfix : E ≤ fixSubgroup β := by
    intro e he
    rw [mem_fixSubgroup]
    apply hι
    rw [hβ]
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (hTiC (Subgroup.commutator_le_self Ti he))
    rw [← hc, mul_inv_cancel_right]
  have h6 : 5 ≤ Nat.card (Fin 6) := by rw [Nat.card_fin]; norm_num
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h6
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  haveI hEs : IsSimpleGroup ↥E := eE.isSimpleGroup
  have hcardE : Nat.card ↥E = 360 := by rw [Nat.card_congr eE.toEquiv, hcardA]
  have hEJ : E ≤ J := by
    have hTop : J.subgroupOf E = ⊤ := eq_top_of_two_elements (by rw [hcardE]; norm_num) _ fun x hx => by
      obtain ⟨k, hk⟩ := hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure ⟨hEfix x.2, k, by simpa using congrArg Subtype.val hk⟩
    intro e he
    have h1 : (⟨e, he⟩ : ↥E) ∈ J.subgroupOf E := by
      rw [hTop]
      exact Subgroup.mem_top _
    exact h1
  have hJT : J ≤ (⨆ O : Set.range (rationalRoots S'.ρ (rootCharHom a)), ratTwo O.1 M).comap ι := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyfix, k, hk⟩
    have hyΓ : ι y ∈ S'.Γ ⊓ Subgroup.centralizer {d} := by
      have h1 := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj ι hι β d hβ
      rw [hrange] at h1
      rw [← h1]
      exact ⟨y, hyfix, rfl⟩
    exact mem_iSup_ratTwo S' hK2 hp (by norm_num) hT hap hyΓ
      (isPGroup_zpowers_of_pow_eq_one (m := k) (by rw [← map_pow, hk, map_one]))
  have hnorm : ∀ t ∈ ⨆ O : Set.range (rationalRoots S'.ρ (rootCharHom a)), ratTwo O.1 M,
      ∀ u ∈ ⁅Ti, Ti⁆, t * u * t⁻¹ ∈ ⁅Ti, Ti⁆ := by
    intro t ht
    refine Subgroup.iSup_induction (fun O : Set.range (rationalRoots S'.ρ (rootCharHom a)) => ratTwo O.1 M)
      (C := fun t => ∀ u ∈ ⁅Ti, Ti⁆, t * u * t⁻¹ ∈ ⁅Ti, Ti⁆) ht ?_ ?_ ?_
    · rintro ⟨_, j, rfl⟩ t htj u hu
      by_cases hij : rationalRoots S'.ρ (rootCharHom a) j = rationalRoots S'.ρ (rootCharHom a) i
      · have htTi : t ∈ Ti := by
          rw [hTi, ← hij]
          exact htj
        exact conj_mem_commutator_of_normalizes (fun y hy => Ti.mul_mem (Ti.mul_mem htTi hy) (Ti.inv_mem htTi))
          (fun y hy => Ti.mul_mem (Ti.mul_mem (Ti.inv_mem htTi) hy) htTi) hu
      · have hcomm : ∀ y ∈ Ti, Commute t y := fun y hy =>
          commute_rootSpan_rationalRoots hker hform hij t ((hTA _ htj).1) y ((hTA _ hy).1)
        have hcen : ⁅Ti, Ti⁆ ≤ Subgroup.centralizer {t} := (Subgroup.commutator_le_self Ti).trans
          fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hcomm y hy).eq.symm
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hcen hu)
        rw [← h1, mul_inv_cancel_right]
        exact hu
    · intro u hu
      simpa using hu
    · intro t₁ t₂ h₁ h₂ u hu
      have e : t₁ * t₂ * u * (t₁ * t₂)⁻¹ = t₁ * (t₂ * u * t₂⁻¹) * t₁⁻¹ := by group
      rw [e]
      exact h₁ _ (h₂ u hu)
  have hEn : ∀ j ∈ J, ∀ e ∈ E, j * e * j⁻¹ ∈ E := by
    intro j hj e he
    show ι (j * e * j⁻¹) ∈ ⁅Ti, Ti⁆
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (hJT hj) _ he
  have hEnc : ∃ a b : ↥E, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    letI : CommGroup ↥E := { (inferInstance : Group ↥E) with mul_comm := fun a b => hcon a b }
    have hprime : (Nat.card ↥E).Prime := IsSimpleGroup.prime_card
    rw [hcardE] at hprime
    exact absurd hprime (by norm_num)
  refine ⟨J, E, le_of_closure_two _, fun x hx hx2 => ?_, hJ, hEJ, hEn, hEs, hEnc,
    by rw [hcardE]; norm_num, by rw [hcardE]; norm_num⟩
  obtain ⟨k, hk⟩ := Inputs141d.exists_pow_eq_one_of_isPGroup hx2
  exact Subgroup.subset_closure ⟨hx, k, hk⟩

theorem input14_1BadSimpleOrBadOn_F4_two (hout : LangOuterTwo) :
    Input14_1BadSimpleOrBadOn fun p d => p = 5 ∧ ∃ q, d = TauCeti.LieTypeIndex.F4 q ∧ q.card = 2 := by
  intro p hp hp5 S _ _ _ _ idx hd hchar he β hβ hβ1
  obtain ⟨d, hv⟩ := idx
  obtain ⟨rfl, q, rfl, hq2c⟩ := hd
  obtain ⟨e⟩ := he
  have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_F4 q]; exact hchar
  obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
  haveI : CharP K 2 := hq2 ▸ hKchar
  have hK2 : Nat.card K = 2 := hK.trans hq2c
  refine twoInCoreLayerOrBad_of_congr (e.trans eK) hp ?_
  have hβ' : MulAut.congr (e.trans eK) β ^ 5 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr (e.trans eK) β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr (e.trans eK)).injective (h.trans (map_one _).symm))
  generalize MulAut.congr (e.trans eK) β = β' at hβ' hβ1' ⊢
  obtain ⟨g, σ, hβe, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.exists_form_FG (Or.inl rfl)
      (fun h => absurd h (by decide)) hp (by norm_num) β' hβ'
  have hσ1 : σ = 1 := ringEquiv_eq_one_of_card_two hK2 σ
  subst hσ1
  rw [exactNormalAut_one_one_zero, mul_one] at hβe
  subst hβe
  have hgp : g ^ 5 = 1 := by
    have : MulAut.conj (g ^ 5) = MulAut.conj 1 := by rw [map_pow, hβ', map_one]
    exact mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot this
  have hg1 : g ≠ 1 := fun h1 => hβ1' (by rw [h1, map_one])
  have hgord : orderOf g = 5 := orderOf_eq_prime hgp hg1
  have hK2r : ringChar K = 2 := ringChar.eq K 2
  have hperf : commutator ↥(adjointGroup .F4 K) = ⊤ := single_edge_perfect .F4 K (by decide)
  have hmon : MonomialToralAt Tag.F4 5 :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp (by norm_num)
  have hpK : ¬ 5 ∣ Nat.card K := by rw [hK2]; norm_num
  obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_untw (τ := .F4) (Or.inr (Or.inl rfl)) hp hpK (Or.inl hp5) hmon hperf
      (MulAut.conj g) (g : ModGL Tag.F4 K)
      (baseChange_mem_adjointGroup_of_mem_inndiag (adjointGroup_le_inndiagGroup g.2))
      (fun c => by simp [MulAut.conj_apply]) (by rw [← Subgroup.coe_pow, hgp]; rfl)
      (fun h' => hg1 (Subtype.ext h'))
  by_cases hgood : ∀ i : KernelComponent (rootCharHom a), twistKind S'.ρ (rootCharHom a) i = .inner →
      ⁅ratTwo (rationalRoots S'.ρ (rootCharHom a) i) S'.D.model,
          ratTwo (rationalRoots S'.ρ (rootCharHom a) i) S'.D.model⁆ =
          ratTwo (rationalRoots S'.ρ (rootCharHom a) i) S'.D.model ∨
        Nat.Coprime 5 (Nat.card (ratTwo (rationalRoots S'.ρ (rootCharHom a) i) S'.D.model))
  · exact Or.inl (twoInCoreLayer_of_langSetup_of_inner S' hout hK2r ι hinj hrange (MulAut.conj g) hconj hT hp
      hp5 hap h1 hgood)
  · right
    push Not at hgood
    obtain ⟨i, hkind, hnp, hnc⟩ := hgood
    rcases ratTwo_inner_or S' hK2r hp hp5 hT i hkind (fun h => absurd h (by decide)) with h' | h' | ⟨-, -, -, ⟨eA⟩⟩
    · exact absurd h' hnp
    · exact absurd h' hnc
    · refine badFix_of_langSetup hK2r S' ι hinj hrange (MulAut.conj g) hconj hT hp rfl hap i eA ?_
      rw [fixSubgroup_conj_eq_centralizer' g]
      refine not_sq_dvd_card_closure_two hp (by norm_num) ?_ hgord
      rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK2]
      unfold ordF4
      norm_num

end BadF4

section Final

theorem input14_1BadRest_of_langOuterTwo (h : LangOuterTwo) : Inputs2323b.Input14_1BadRest := by
  have hE := input14_1BadOn_of_simple (input14_1BadSimpleOn_exceptional h)
  have hR := input14_1BadOn_of_simple input14_1BadSimpleOn_reeF4
  have hG2 := input14_1BadOn_of_simpleOrBad (input14_1BadSimpleOrBadOn_G2_128 h)
  have hF4 := input14_1BadOn_of_simpleOrBad (input14_1BadSimpleOrBadOn_F4_two h)
  have hB2 := input14_1BadOn_of_simpleOrBad input14_1BadSimpleOrBadOn_B2_32
  have hR13 := input14_1BadOn_of_simpleOrBad input14_1BadSimpleOrBadOn_reeF4_13
  have hBr := input14_1BadOn_of_simpleOrDecomp input14_1BadSimpleOrDecompOn_B_two
  have hall := input14_1BadOn_or (input14_1BadOn_or (input14_1BadOn_or hE hR)
    (input14_1BadOn_or hG2 (input14_1BadOn_or hB2 hR13))) (input14_1BadOn_or hBr hF4)
  refine Input14_1BadOn.mono (fun p d hd => ?_) hall
  rcases hd with hd | ⟨m, rfl, hm⟩ | ⟨h5, r, q, rfl, hq⟩
  · by_cases h5 : p = 5 ∧ ∃ q, d = TauCeti.LieTypeIndex.F4 q ∧ q.card = 2
    · exact Or.inr (Or.inr h5)
    · by_cases h7 : p = 7 ∧ ∃ q, d = TauCeti.LieTypeIndex.G2 q ∧ q.card = 2 ^ 7
      · exact Or.inl (Or.inr (Or.inl h7))
      · exact Or.inl (Or.inl (Or.inl ⟨hd, h5, h7⟩))
  · by_cases h13 : p = 13 ∧ m = 6
    · obtain ⟨h13, rfl⟩ := h13
      exact Or.inl (Or.inr (Or.inr (Or.inr ⟨h13, rfl⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨m, rfl, hm, h13⟩))
  · rcases hq with hq | ⟨rfl, hq⟩
    · exact Or.inr (Or.inl ⟨h5, r, q, rfl, hq⟩)
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨h5, q, rfl, hq⟩)))

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f

end
