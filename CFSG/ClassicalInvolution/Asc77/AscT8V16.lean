module

public import CFSG.ClassicalInvolution.Asc77.AscT8V13
public import CFSG.ClassicalInvolution.Asc77.AscT8V14
public import CFSG.ClassicalInvolution.Asc77.AscT8V15
public import CFSG.ClassicalInvolution.Asc77.AscT8V3
public import CFSG.ClassicalInvolution.Asc77.AscT8V10

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace T8V

section Transport

theorem E4Pair.map_equiv {S S' X : Type} [Group S] [Group S'] [Group X] {ψ : S →* X}
    {R R' : Subgroup S} {y y' : S} (hP : E4Pair ψ R R' y y') (e : S ≃* S') :
    E4Pair (ψ.comp e.symm.toMonoidHom) (R.map e.toMonoidHom) (R'.map e.toMonoidHom) (e y)
      (e y') := by
  have hcen : ∀ z : S, e z ∈ Subgroup.center S' ↔ z ∈ Subgroup.center S := by
    intro z
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h g
      apply e.injective
      rw [map_mul, map_mul]
      exact h (e g)
    · intro h g'
      obtain ⟨g, rfl⟩ := e.surjective g'
      rw [← map_mul, ← map_mul, h g]
  refine ⟨hP.surj.comp e.symm.surjective, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro z hz
    rw [MonoidHom.mem_ker] at hz
    have h1 : e.symm z ∈ Subgroup.center S := hP.ker (by rw [MonoidHom.mem_ker]; exact hz)
    have := (hcen (e.symm z)).mpr h1
    rwa [MulEquiv.apply_symm_apply] at this
  · rw [Group.isPerfect_def]
    have h := top_le_commutator_of_perfect hP.perf
    have h' := Subgroup.map_mono (f := e.toMonoidHom) h
    rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective] at h'
    rw [commutator_def]
    exact top_le_iff.mp h'
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hP.perfR
  · rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hP.perfR'
  · intro h
    exact hP.ne (Subgroup.map_injective e.injective h)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show e a * e b = e b * e a
    rw [← map_mul, ← map_mul, hP.comm a ha b hb]
  · exact Subgroup.mem_map_of_mem _ hP.hy
  · rw [← map_mul, hP.hy2, map_one]
  · intro h
    exact hP.hy1 (e.injective (by rw [h, map_one]))
  · exact Subgroup.mem_map_of_mem _ hP.hy'
  · rw [← map_mul, hP.hy'2, map_one]
  · intro h
    exact hP.hy'1 (e.injective (by rw [h, map_one]))
  · rw [← map_mul]
    exact (hcen _).mpr hP.cen
  · intro h
    apply hP.nontwin
    rw [MonoidHom.mem_ker] at h ⊢
    simpa [← map_mul] using h
  · intro h
    apply hP.nc
    simpa using h

theorem not_isSquare_neg_one_of_mod_four {p e : ℕ} [Fact p.Prime] (hq : p ^ e % 4 = 3)
    (he : e ≠ 0) : ¬ IsSquare (-1 : GaloisField p e) := by
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, GaloisField.card p e he]
  omega

end Transport

section Final

variable {p f : ℕ} [Fact p.Prime]


theorem e4_concl_sp (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hΦ : HypOmegaMod p f Φ) {e : ℕ} (M : Ih8Model p f Φ .PSp 2 e)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X) :
    (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
      (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
    (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
      e * e ≠ x * x') := by
  have hG2 : StatedLieTag.PSp ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSp ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSp = .PSL ∧ (2 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSp 2 p e Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSp 2 p e Fact.out trivial M.admissible).1.1
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    e4_pair_of_model hp2 hq hΦ M hG2 hD4 hnpsl hSperf hnt htrans hA hB hxA hxB hcen
  have hA0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR
  have hB0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR'
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have h4 : 4 ≤ Nat.card (GaloisField p e) := M.four_le_natCard_galoisField hD4 hq
  have hRl := (ModelFacts.fund_iff_isLongRootSp2 M.admissible h2 R).mp (M.cls_sub hR)
  have hRl' := (ModelFacts.fund_iff_isLongRootSp2 M.admissible h2 R').mp (M.cls_sub hR')
  have key := e4_assemble hP (e4_sp_sigma h2 h4 M.ψ hP hRl hRl') (e4_sp_inner h2 M.ψ hP hRl hRl')
    hA0 hB0
  subst hAR hBR hy hy'
  exact key

theorem e4_concl_sl4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq3 : p ^ f % 4 = 3) {X : Type} [Group X]
    [Finite X] {Φ : Set (Subgroup X)} (hΦ : HypOmegaMod p f Φ) {e : ℕ}
    (M : Ih8Model p f Φ .PSL 4 e) (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X) :
    (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
      (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
    (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
      e * e ≠ x * x') := by
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSL 4 p e Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSL 4 p e Fact.out trivial M.admissible).1.1
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    e4_pair_of_model hp2 hq hΦ M hG2 hD4 hnpsl hSperf hnt htrans hA hB hxA hxB hcen
  have hA0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR
  have hB0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR'
  have he : e = f := M.exp_eq_f hD4
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hneg : ¬ IsSquare (-1 : GaloisField p e) :=
    not_isSquare_neg_one_of_mod_four (he ▸ hq3) (by have := M.admissible.2.1; omega)
  have hRl := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR)
  have hRl' := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR')
  have key := e4_assemble hP (e4_sl4_sigma h2 hneg M.ψ hP hRl hRl')
    (e4_sl4_inner h2 hneg M.ψ hP hRl hRl') hA0 hB0
  subst hAR hBR hy hy'
  exact key

theorem e4_concl_su4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq1 : p ^ f % 4 = 1) {X : Type} [Group X]
    [Finite X] {Φ : Set (Subgroup X)} (hΦ : HypOmegaMod p f Φ) {e : ℕ}
    (M : Ih8Model p f Φ .PSU 4 e) (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X) :
    (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
      (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
    (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
      e * e ≠ x * x') := by
  have hG2 : StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSU ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSU = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSU 4 p e Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSU 4 p e Fact.out trivial M.admissible).1.1
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    e4_pair_of_model hp2 hq hΦ M hG2 hD4 hnpsl hSperf hnt htrans hA hB hxA hxB hcen
  have hA0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR
  have hB0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR'
  have he : e = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ e := he ▸ hq
  have hq4 : p ^ e % 4 = 1 := he ▸ hq1
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 M.admissible
  have hP' := hP.map_equiv φ
  have hRl := (hφ R).mp (M.cls_sub hR)
  have hRl' := (hφ R').mp (M.cls_sub hR')
  have hσ1 : ∀ σ : MulAut X, (∀ r ∈ R, σ (M.ψ r) = M.ψ r) → (∀ r ∈ R', σ (M.ψ r) = M.ψ r) →
      σ * σ * (σ * σ) = 1 → σ * σ = 1 := by
    intro σ h1 h2 h4
    refine e4_su_sigma hK hp2 hq' hq4 _ hP' hRl hRl' σ ?_ ?_ h4
    · rintro _ ⟨r, hr, rfl⟩
      simpa using h1 r hr
    · rintro _ ⟨r, hr, rfl⟩
      simpa using h2 r hr
  have he1 : ∀ s : (modelUniv .PSU 4 p e Fact.out).K, (∀ r ∈ R, s * r = r * s) →
      (∀ r ∈ R', s * r = r * s) → ∀ k ∈ M.ψ.ker, s * s ≠ y * y' * k := by
    intro s hs hs' k hk hsk
    refine e4_su_inner hK hp2 hq4 _ hP' hRl hRl' (φ s) ?_ ?_ (φ k) ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      show φ s * φ r = φ r * φ s
      rw [← map_mul, ← map_mul, hs r hr]
    · rintro _ ⟨r, hr, rfl⟩
      show φ s * φ r = φ r * φ s
      rw [← map_mul, ← map_mul, hs' r hr]
    · rw [MonoidHom.mem_ker] at hk ⊢
      simpa using hk
    · rw [← map_mul, ← map_mul, ← map_mul, hsk]
  have key := e4_assemble hP hσ1 he1 hA0 hB0
  subst hAR hBR hy hy'
  exact key

theorem e4SecNoRoot : E4SecNoRoot p f := by
  intro hp2 hq n hn X _ _ hlt Φ hΦ hO hgen hnt hdisc A hA B hB x x' hxA hxB hcen
  rcases e4_tag hp2 hq hn hlt hΦ hO hgen hnt hdisc hA hB with ⟨e, ⟨M⟩⟩ | ⟨hq3, e, ⟨M⟩⟩ |
    ⟨hq1, e, ⟨M⟩⟩
  · exact e4_concl_sp hp2 hq hΦ M hnt (M.exists_conj_of_fund (by decide) (by decide)) hA hB hxA
      hxB hcen
  · exact e4_concl_sl4 hp2 hq hq3 hΦ M hnt (M.exists_conj_of_fund (by decide) (by decide)) hA hB
      hxA hxB hcen
  · exact e4_concl_su4 hp2 hq hq1 hΦ M hnt (M.exists_conj_of_fund (by decide) (by decide)) hA hB
      hxA hxB hcen

end Final

end T8V

end CFSG.ClassicalInvolution.Asc77
