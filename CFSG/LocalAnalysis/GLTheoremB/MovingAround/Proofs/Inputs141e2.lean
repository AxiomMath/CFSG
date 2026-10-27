module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141e
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Field
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyExc
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuN
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedHigh
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedE6

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141c CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141d
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.RecipeExcLang

set_option linter.unusedSectionVars false

section Transport


theorem structAt_of_langSetup_congr (hres : LangInnerTwo) {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S' : LangSetup τ (AlgebraicClosure K) p₀) {S C : Type} [Group S]
    [Finite S] [Group C] (e : S ≃* C) (ι : C →* ModGL τ (AlgebraicClosure K)) (hι : Function.Injective ι)
    (hrange : ι.range = S'.Γ) (β : MulAut S) {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (hβ : ∀ c, ι (MulAut.congr e β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S'.D.torus) (hap : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S'.ρ S'.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S'.ρ S'.Γ (rootCharHom a) i))
    {J : Subgroup S} (hJ : IsComponentOf J (fixSubgroup β))
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) :
    StructAt β J := by
  have hrange' : (ι.comp e.toMonoidHom).range = S'.Γ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, ← MonoidHom.range_eq_map, hrange]
  refine structAt_of_langSetup hres hK2 S' (ι.comp e.toMonoidHom) (hι.comp e.injective) hrange' β
    (fun s => ?_) hT hap h1 hTame hJ hJt
  have h := hβ (e s)
  change ι (e (β (e.symm (e s)))) = _ at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h

end Transport

section Untw

theorem not_dvd_card_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem two_dvd_card_of_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] : 2 ∣ Nat.card K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.pos.ne'


theorem structAt_untw (hres : LangInnerTwo) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hG2 : τ = .G2 → 3 ≤ Nat.card K) {S : Type} [Group S] [Finite S] (e : S ≃* ↥(adjointGroup τ K))
    (β : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) (hlay : PerfectInLayer β) {J : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) : StructAt β J := by
  classical
  have hJ20 := card_dvd_of_isLThreeFour hJt
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hJc := isComponentOf_of_perfectInLayer hlay hJ
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have hpK : ¬ 3 ∣ Nat.card K := not_dvd_card_of_charTwo Nat.prime_three (by norm_num)
  have hdisp : (∃ (σ : K ≃+* K) (ψ : MulAut ↥(adjointGroup τ K)),
      σ ≠ 1 ∧ ψ * MulAut.congr e β * ψ⁻¹ = entrywiseAdjointAut τ σ) ∨
    (∃ h ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K,
        ((MulAut.congr e β) c : ModGL τ K) = h * c * h⁻¹) ∧ h ^ 3 = 1 ∧ h ≠ 1) := by
    rcases hτ with h | h | h | h | h
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inr h) hG2
        Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_FG (Or.inl h) hG2
        Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inl h)
        Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inr (Or.inl h))
        Nat.prime_three (by norm_num) _ hβ' hβ1'
    · exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_field_or_inndiag_E (Or.inr (Or.inr h))
        Nat.prime_three (by norm_num) _ hβ' hβ1'
  rcases hdisp with ⟨σ, ψ, -, hψ⟩ | ⟨h, hh, hβh, hp1, hh1⟩
  ·
    exact structAt_of_goodFixed
      (goodFixed_of_congr e (goodFixed_of_conj_eq hψ (goodFixed_entrywiseAdjointAut_two τ σ))) hJ hJ20
  ·
    have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
      rcases hτ with h | h | h | h | h
      · subst h
        exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K
          (hG2 rfl)).commutator_eq_top
      all_goals exact single_edge_perfect τ K (by simp [h])
    have hmon : MonomialToralAt τ 3 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
        (by rcases hτ with h | h | h | h | h <;> simp [h]) Nat.prime_three (by norm_num)
    have hhL := baseChange_mem_adjointGroup_of_mem_inndiag hh
    by_cases hq : 4 ≤ Nat.card K
    · obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
        exists_langSetup_of_inner_untw hτ Nat.prime_three hpK (Or.inr hq) hmon hperf _ h hhL hβh hp1 hh1
      exact structAt_of_langSetup_congr hres hK2 S' e ι hinj hrange β hconj hT hap h1
        (langSetup_hTame S' hT hap h1) hJc hJt
    · have hK1 : 0 < Nat.card K := Nat.card_pos
      have h5K : ¬ 5 ∣ Nat.card K := fun h5 => by
        have := Nat.le_of_dvd hK1 h5
        omega
      obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
        exists_langSetup_of_inner_untw_of_prime hτ Nat.prime_three hpK Nat.prime_five h5K (Or.inl le_rfl)
          hmon hperf _ h hhL hβh hp1 hh1
      have hsmall : τ = .G2 → 5 ≤ 3 ∨ 4 ≤ S'.D.q := fun hg => by
        exfalso
        have h3 := hG2 hg
        have h2 := two_dvd_card_of_charTwo (K := K)
        have : Nat.card K = 3 := by omega
        rw [this] at h2
        omega
      exact structAt_of_langSetup_congr hres hK2 S' e ι hinj hrange β hconj hT hap h1
        (langSetup_hTame_of_prime S' Nat.prime_three (natCast_ne_zero_algebraicClosure Nat.prime_three hpK)
          hsmall hT hap h1) hJc hJt

theorem structAt_twE6 (hres : LangInnerTwo) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {S : Type} [Group S]
    [Finite S] (e : S ≃* ↥(twistedE6RootGroup K σ)) (β : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1)
    (hlay : PerfectInLayer β) {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) : StructAt β J := by
  classical
  have hJ20 := card_dvd_of_isLThreeFour hJt
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero))
  have hK2 : ringChar K = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := f * 2) Nat.prime_two
      (by omega) (by rw [hK, ← pow_mul])
  have hJc := isComponentOf_of_perfectInLayer hlay hJ
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
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
    have hp1 : h ^ 3 = 1 :=
      twistedE6InndiagConj_injective Nat.prime_two hf hK σ hσ (by rw [map_pow, hh, hβ', map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1' (by rw [← hh, h', map_one])
    obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
      exists_setup_prime Nat.prime_two hf Nat.prime_three (by norm_num) (by norm_num)
    have hmon : MonomialToralAt Tag.E6 3 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
        (by norm_num)
    obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two hf hK σ hσ Nat.prime_three (by norm_num) hp₀
        hp₀ℓ hq₀ hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
        (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
        (fun h' => hh1 (Subtype.ext h'))
    rw [hh] at hconj
    exact structAt_of_langSetup_congr hres hK2 S' e ι hinj hrange β hconj hT hap h1
      (langSetup_hTame_of_prime S' Nat.prime_three
        (natCast_ne_zero_algebraicClosure_of_ne Nat.prime_two Nat.prime_three hK (by norm_num))
        (fun h => absurd h (by decide)) hT hap h1) hJc hJt
  ·
    exact structAt_of_goodFixed
      (goodFixed_of_congr e (goodFixed_twE6_field hf hK σ hσ Θ hΘ _ hβ' hΘβ)) hJ hJ20

theorem structAt_triD4 (hres : LangInnerTwo) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K))
    (hΘker : Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    {S : Type} [Group S] [Finite S] (e : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (β : MulAut S) (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) (hlay : PerfectInLayer β) {J : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup β) J)
    (hJt : IsLThreeFour (barOf 3 J ⧸ Subgroup.center (barOf 3 J))) : StructAt β J := by
  classical
  have hJ20 := card_dvd_of_isLThreeFour hJt
  have hK2 : ringChar K = 2 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_eq_of_card_eq_pow (n := f * 3) Nat.prime_two
      (by omega) (by rw [hK, ← pow_mul])
  have hJc := isComponentOf_of_perfectInLayer hlay hJ
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  by_cases hΘβ : Θ (MulAut.congr e β) = 1
  ·
    have hmem : MulAut.congr e β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rw [← hΘker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨x, hx⟩ := hmem
    have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
      center_graphFixedRootGroup_eq_bot σ.surjective
    have hxp : x ^ 3 = 1 :=
      mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hx, hβ', map_one])
    have hx1 : x ≠ 1 := fun h' => hβ1' (by rw [← hx, h', map_one])
    obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
      exists_setup_prime Nat.prime_two hf Nat.prime_three (by norm_num) (by norm_num)
    have hmon : MonomialToralAt Tag.D4 3 :=
      monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) Nat.prime_three
        (by norm_num)
    obtain ⟨S', a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_triD4_of_prime Nat.prime_two hf hK σ hσ Nat.prime_three (by norm_num) hp₀
        hp₀ℓ hq₀ hmon x hxp hx1
    rw [hx] at hconj
    exact structAt_of_langSetup_congr hres hK2 S' e ι hinj hrange β hconj hT hap h1
      (langSetup_hTame_of_prime S' Nat.prime_three
        (natCast_ne_zero_algebraicClosure_of_ne Nat.prime_two Nat.prime_three hK (by norm_num))
        (fun h => absurd h (by decide)) hT hap h1) hJc hJt
  ·
    have hout : MulAut.congr e β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun hmem =>
      hΘβ (by rw [← MonoidHom.mem_ker, hΘker]; exact hmem)
    exact structAt_of_goodFixed
      (goodFixed_of_congr e (goodFixed_triality_outer_even hf hK σ hσ _ hβ' hout)) hJ hJ20

end Untw

section Outer

open CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem isLThreeFour_center_of_barOf {G : Type} [Group G] {R : Subgroup G} (hq : CFSG.IsQuasisimple ↥R)
    (h : IsLThreeFour (barOf 3 R ⧸ Subgroup.center (barOf 3 R))) :
    IsLThreeFour (↥R ⧸ Subgroup.center ↥R) := by
  have hperf : Group.IsPerfect ↥R := hq.1
  have hq' : CFSG.Open.IsQuasisimple ↥R := ⟨hperf.commutator_eq_top, hq.2.1⟩
  have hN : GLAPPrimeCore 3 ↥R ≤ Subgroup.center ↥R := by
    refine CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq' _ ?_
    intro htop
    have h1 : Nat.card (barOf 3 R) = 1 := by
      show (GLAPPrimeCore 3 ↥R).index = 1
      rw [htop, Subgroup.index_top]
    have h2 : Nat.card (barOf 3 R) = Nat.card (barOf 3 R ⧸ Subgroup.center (barOf 3 R)) *
        Nat.card (Subgroup.center (barOf 3 R)) := Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [card_eq_of_isLThreeFour h, h1] at h2
    omega
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥R)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact hN)
  exact IsLThreeFour.of_mulEquiv e.symm h


theorem not_isLThreeFour_suN {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .suN)
    (hL34 : IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
  classical
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  obtain ⟨h2', hn⟩ := suN_rank_ncard hk
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
    have h3 : ((3 : ℕ) : L) = 1 := by
      have : (3 : ℕ) = 2 + 1 := rfl
      rw [this, Nat.cast_add, h2, zero_add, Nat.cast_one]
    rw [h3]
    exact one_ne_zero
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S Nat.prime_three h3L hTp i h2' hn
  obtain ⟨π, hπ⟩ := two_suN_perm S hT i hk hν hψ hκ hnorm hΨ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq L hchar (by assumption)
  subst hr2
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  haveI : Fact (Nat.Prime 2) := ⟨hr⟩
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨hfin, hqsC, hc216⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  haveI := hfin
  have hR20160 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 20160 :=
    card_eq_of_isLThreeFour hL34
  by_cases h32 : (ν, 2 ^ (e * s)) = (3, 2)
  ·
    have h216 := hc216 h32
    haveI : Finite ↥f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Finite.of_injective (Subgroup.inclusion hf1) (Subgroup.inclusion_injective hf1)
    have h1 : 20160 ≤ Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
      rw [← hR20160]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    have h2 : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ Nat.card ↥f.range :=
      Subgroup.card_le_of_le hf1
    have h3 : Nat.card ↥f.range ≤ 216 := by
      rw [← h216]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd f)
    omega
  · have hCperf : Group.IsPerfect ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := (hqsC h32).1
    have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i := le_antisymm (hf2 hCperf) hf1
    let g : ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
    have hgsurj : Function.Surjective g := by
      rintro ⟨x, hx⟩
      obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
      exact ⟨c, Subtype.ext hc⟩
    have hgker : g.ker ≤ Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) := by
      intro c hc
      apply hfker
      rw [MonoidHom.mem_ker] at hc ⊢
      exact congrArg Subtype.val hc
    have hCL := two_isLThreeFour_of_surjective_central hCperf g hgsurj hgker hL34
    have hcardCL : Nat.card (↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) ⧸
        Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))) = 20160 :=
      card_eq_of_isLThreeFour hCL
    have hcardC : Nat.card ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) =
        20160 * Nat.card ↥(Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ))), hcardCL]
    obtain ⟨F, hFcard, ⟨eC⟩⟩ := two_suN_exists_equiv hr hes σQ hσc hν
    haveI : Finite ↥F := Nat.finite_of_card_ne_zero (by
      rw [hFcard]
      exact (pow_pos (pow_pos Nat.two_pos _) 2).ne')
    haveI : CharP ↥F 2 := inferInstance
    have hU : UnitaryFieldData 2 (e * s) ↥F := ⟨hr, hes, by rw [hFcard, ← pow_mul, mul_comm]⟩
    have hint := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := ν) (by omega)
    have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2)
      (f := e * s) hFcard hν h32).2
    have hodd : Odd (Nat.card
        ↥(Subgroup.center ↥(CFSG.RankThree.Classical2.fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)))) := by
      rw [← Nat.card_congr (Subgroup.centerCongr eC).toEquiv]
      exact two_suN_center_odd (by omega) hZ
    refine two_suN_arith (ν := ν) (t := e * s) hν hes (fun h => h32 ?_) hodd ?_
    · obtain ⟨h1, h2⟩ := h
      rw [h1, h2]
      norm_num
    · rw [Nat.card_congr eC.toEquiv, hcardC] at hint
      push_cast at hint
      exact hint.symm

theorem not_isLThreeFour_outer {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i ≠ .inner)
    (hL34 : IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
  haveI := ssTw_finite_rationalComponent S i
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  cases hkind : twistKind S.ρ (rootCharHom a) i with
  | inner => exact hk hkind
  | suN => exact not_isLThreeFour_suN S hT hap i hkind hL34
  | twoD =>
    obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hkind
    by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · have hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        have hle := h5.trans (compRank_le_rank (componentRoots (rootCharHom a) i))
        cases τ with
        | G2 => exact absurd hle (by decide)
        | F4 => exact absurd hle (by decide)
        | D4 => exact Or.inl rfl
        | E6 => exact Or.inr (Or.inl rfl)
        | E7 => exact Or.inr (Or.inr (Or.inl rfl))
        | E8 => exact Or.inr (Or.inr (Or.inr rfl))
      exact Up34Chev2.not_isLThreeFour_of_bad3 (Up34Chev2.bad3_twoD_high S hτ hT i hkind h5) hL34
    · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
      exact Up34Chev2.not_isLThreeFour_d4class S hT hTp h1 i hr (by rw [hcard, hr]) hnin hL34
  | exc =>
    obtain ⟨hnin, h⟩ := exc_kind hkind
    rcases h with h6 | ⟨h4, h24, -⟩
    · exact Up34Chev2.not_isLThreeFour_of_bad3 (Up34Chev2.bad3_e6class S hT hTp h1 i h6.1 h6.2) hL34
    · exact Up34Chev2.not_isLThreeFour_d4class S hT hTp h1 i h4 h24 hnin hL34

theorem langOrbitTwo_holds : LangOrbitTwo := by
  intro τ K _ _ hK2 p₀ S a hT hap h1 i hq hRt g hg hgF hg2 _
  by_cases hk : twistKind S.ρ (rootCharHom a) i = .inner
  · exact langOrbitTwo_inner hK2 S hT i hk hq hRt hg hgF hg2
  · haveI : CharP K 2 := ringChar.of_eq hK2
    haveI : CharP (AlgebraicClosure K) 2 :=
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
    exact (not_isLThreeFour_outer S hT hap h1 i hk (isLThreeFour_center_of_barOf hq hRt)).elim

theorem langInnerTwo_holds : LangInnerTwo :=
  langInnerTwo_of_orbitTwo langOrbitTwo_holds

end Outer

section Assembly


theorem input14_1StructFor_exceptional (hres : LangInnerTwo) :
    Input14_1StructFor fun d =>
      CFSG.Yardstones.Md42047359a2a.lieFamily d = CFSG.Yardstones.Md42047359a2a.LieFamily.exceptional := by
  intro S _ _ hS hnc idx hF hchar he β hβ hβ1 J hJ hJt
  obtain ⟨e⟩ := he
  have hlay : PerfectInLayer β :=
    lieSemisimpleCentExceptional S hS hnc idx hF ⟨e⟩ 3 Nat.prime_three (by norm_num)
      (by rw [hchar]; norm_num) β hβ hβ1
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | E6 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_E6 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact structAt_untw hres (τ := .E6) (by simp) (fun h => absurd h (by decide)) (e.trans eK) β hβ hβ1 hlay
      hJ hJt
  | E7 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_E7 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact structAt_untw hres (τ := .E7) (by simp) (fun h => absurd h (by decide)) (e.trans eK) β hβ hβ1 hlay
      hJ hJt
  | E8 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_E8 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact structAt_untw hres (τ := .E8) (by simp) (fun h => absurd h (by decide)) (e.trans eK) β hβ hβ1 hlay
      hJ hJt
  | F4 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_F4 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact structAt_untw hres (τ := .F4) (by simp) (fun h => absurd h (by decide)) (e.trans eK) β hβ hβ1 hlay
      hJ hJt
  | G2 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_G2 q]; exact hchar
    obtain ⟨K, _, _, hK, hKchar, ⟨eK⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv
    haveI : CharP K 2 := hq2 ▸ hKchar
    exact structAt_untw hres (τ := .G2) (by simp) (fun _ => hK ▸ hr) (e.trans eK) β hβ hβ1 hlay hJ hJt
  | twistedE6 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_twistedE6 q]; exact hchar
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    rw [hq2] at hK hσ
    exact structAt_twE6 hres q.exponent_pos hK σ hσ (e.trans eK) β hβ hβ1 hlay hJ hJt
  | trialityD4 q =>
    have hq2 : q.p = 2 := by rw [← TauCeti.LieTypeIndex.characteristic_trialityD4 q]; exact hchar
    obtain ⟨K, _, _, σ, hK, hσ, ⟨Θ, hΘker⟩, ⟨eK⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
    rw [hq2] at hK hσ
    exact structAt_triD4 hres q.exponent_pos hK σ hσ Θ hΘker (e.trans eK) β hβ hβ1 hlay hJ hJt
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

theorem input14_1CoreExc_of_langInnerTwo (hres : LangInnerTwo) : Inputs141d.Input14_1CoreExc :=
  input14_1CoreFor_of_struct (input14_1StructFor_exceptional hres)

theorem input14_1CoreExc_holds : Inputs141d.Input14_1CoreExc :=
  input14_1CoreExc_of_langInnerTwo langInnerTwo_holds

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141e

end
