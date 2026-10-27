module

public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRSp
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NR
public import CFSG.ClassicalInvolution.Q3.Q3T8E4NRDef
public import CFSG.ClassicalInvolution.Q3.Q3T8E4Gen

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1

namespace E4NR3

section Pair

variable {S X : Type} [Group S] [Group X]

theorem nontwin_of_adj {Φ : Set (Subgroup X)} (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ omegaNbr Φ A) {ψ : S →* X} {y y' : S}
    (hy2 : y * y = 1) (hxA : IsUniqueInvolution A (ψ y)) (hxB : IsUniqueInvolution B (ψ y')) :
    y * y' ∉ ψ.ker := by
  intro h
  have h1 : ψ y * ψ y' = 1 := by rw [← map_mul]; exact h
  have h2 : ψ y * ψ y = 1 := by rw [← map_mul, hy2, map_one]
  have h3 : ψ y' = ψ y := by
    calc ψ y' = (ψ y)⁻¹ := eq_inv_of_mul_eq_one_right h1
      _ = ψ y := inv_eq_of_mul_eq_one_right h2
  rw [h3] at hxB
  exact hB.2.1 (hnt A hA B ⟨hB.1, ψ y, hxA, hxB⟩)

theorem not_mem_center_of_adj3 [Finite X] {Φ : Set (Subgroup X)} (hΦ : HypOmegaModU (.sl2 3 1) Φ)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x : X} (hx : IsUniqueInvolution A x) : x ∉ Subgroup.center X := by
  intro hc
  have hΩg := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΦ
  have hN : Subgroup.centralizer ({x} : Set X) ≤ Subgroup.normalizer (A : Set X) :=
    T8.centralizer_le_normalizer_of_noTwins hΩg.conjInvariant hA (hnt _ hA) hx
  have hall : ∀ g : X, conjSub g A = A := fun g => by
    have : g ∈ Subgroup.centralizer ({x} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_center_iff.mp hc g
    exact mem_normalizer_iff_conjSub_eq.mp (hN this)
  obtain ⟨g, hg⟩ := htrans A hA B hB.1
  exact hB.2.1 (by rw [← hg, hall g])

theorem gen3_of_equiv_sl2 {R : Subgroup S} (e : ↥R ≃* SL(2, 𝔽₃)) : ModelFacts.Gen3 R := by
  have h1 := (ModelFacts.gen3_top_sl2 (F := 𝔽₃)).map e.symm.toMonoidHom
  have h2 := h1.map R.subtype
  have e1 : (⊤ : Subgroup SL(2, 𝔽₃)).map e.symm.toMonoidHom = ⊤ := by
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.symm.surjective
  rw [e1, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2

end Pair

section Sp

open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (twin_std_sp)

theorem e4_sp_sigma3 {X : Type} [Group X] (ψ : StatedSp 2 𝔽₃ →* X)
    {R R' : Subgroup (StatedSp 2 𝔽₃)} {y y' : StatedSp 2 𝔽₃} (hP : E4Pair3N ψ R R' y y')
    (hR : ∃ i, IsLongRootSp2 R i) (hR' : ∃ i, IsLongRootSp2 R' i) :
    ∀ σ : MulAut X, (∀ r ∈ R, σ (ψ r) = ψ r) → (∀ r ∈ R', σ (ψ r) = ψ r) →
      σ * σ * (σ * σ) = 1 → σ * σ = 1 := by
  intro σ hσR hσR' _
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hc : y' * y⁻¹ ∈ Subgroup.center (StatedSp 2 𝔽₃) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, k, hRg, hR'g⟩ := twin_std_sp h2 hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2
    hP.hy'1 hc
  set ψ₀ : StatedSp 2 𝔽₃ →* X := ψ.comp (MulAut.conj g).toMonoidHom with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := hP.surj.comp (MulAut.conj g).surjective
  have hker₀ : ψ₀.ker ≤ Subgroup.center (StatedSp 2 𝔽₃) := by
    intro z hz
    have h1 : g * z * g⁻¹ ∈ Subgroup.center (StatedSp 2 𝔽₃) := hP.ker hz
    have h2' := (Subgroup.center (StatedSp 2 𝔽₃)).normal_of_characteristic.conj_mem
      (g * z * g⁻¹) h1 g⁻¹
    simpa [mul_assoc] using h2'
  refine sp4_sq_one3 ψ₀ hψ₀s hker₀ k σ ?_ ?_
  · intro r hr
    apply hσR
    rw [hRg]
    exact ⟨r, hr, rfl⟩
  · intro r hr
    apply hσR'
    rw [hR'g]
    exact ⟨r, hr, rfl⟩

end Sp

end E4NR3

section Tags

open CFSG.ClassicalInvolution.Models (longRootSet)
open E4NR3


variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem e4_concl_sp3 (hΦ : HypOmegaModU (.sl2 3 1) Φ) (M : Ih8Model 3 1 Φ .PSp 2 1)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X) :
    (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
      (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
    (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
      e * e ≠ x * x') := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hG2 : StatedLieTag.PSp ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSp ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSp = .PSL ∧ (2 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSp 2 3 1 Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSp 2 3 1 Fact.out trivial M.admissible).1.1
  have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
  have htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L :=
    M.exists_conj_of_fund hG2 hD4
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    E4G3.e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hA hB hxA hxB hcen
  have hA0 : oddCoreOf A = ⊥ := oddCoreOf_eq_bot_of_exact hex hA
  have hB0 : oddCoreOf B = ⊥ := oddCoreOf_eq_bot_of_exact hex hB.1
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hRl := (ModelFacts.fund_iff_isLongRootSp2 M.admissible h2 R).mp (M.cls_sub hR)
  have hRl' := (ModelFacts.fund_iff_isLongRootSp2 M.admissible h2 R').mp (M.cls_sub hR')
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨eR'⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR'
  have hnc : M.ψ y ∉ Subgroup.center X := by
    rw [hy]
    exact not_mem_center_of_adj3 hΦ hnt htrans hA hB hxA
  have hnt' : y * y' ∉ M.ψ.ker := by
    refine nontwin_of_adj hnt hA hB hP.hy2 ?_ ?_
    · rw [hy]
      exact hxA
    · rw [hy']
      exact hxB
  subst hAR hBR hy hy'
  have hP' : E4Pair3N M.ψ R R' y y' := ⟨hP, hnt', hnc⟩
  have key := e4_assemble3 hP' (gen3_of_equiv_sl2 eR) (gen3_of_equiv_sl2 eR')
    (e4_sp_sigma3 M.ψ hP' hRl hRl') (e4_sp_inner3 M.ψ hP' hRl hRl') hA0 hB0
  exact key

theorem e4_concl_sl43 (hΦ : HypOmegaModU (.sl2 3 1) Φ) (M : Ih8Model 3 1 Φ .PSL 4 1)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X) :
    (∀ σ : MulAut X, (∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A) →
      (∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) → σ * σ ≠ MulAut.conj x) ∧
    (∀ e : X, (∀ k ∈ A, ⁅e, k⁆ ∈ oddCoreOf A) → (∀ k ∈ B, ⁅e, k⁆ ∈ oddCoreOf B) →
      e * e ≠ x * x') := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSL 4 3 1 Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSL 4 3 1 Fact.out trivial M.admissible).1.1
  have hex := exactMembers_of_ih8Model M hΦ hG2 hD4
  have htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L :=
    M.exists_conj_of_fund hG2 hD4
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    E4G3.e4_pair_of_model3 hΦ M hG2 hD4 hnpsl hSperf hA hB hxA hxB hcen
  have hA0 : oddCoreOf A = ⊥ := oddCoreOf_eq_bot_of_exact hex hA
  have hB0 : oddCoreOf B = ⊥ := oddCoreOf_eq_bot_of_exact hex hB.1
  have h2 : (2 : 𝔽₃) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hneg : ¬ IsSquare (-1 : 𝔽₃) :=
    CFSG.ClassicalInvolution.Asc77.T8V.not_isSquare_neg_one_of_mod_four (p := 3) (e := 1)
      (by norm_num) (by norm_num)
  have hRl := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR)
  have hRl' := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR')
  obtain ⟨eR⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  obtain ⟨eR'⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR'
  have hnc : M.ψ y ∉ Subgroup.center X := by
    rw [hy]
    exact not_mem_center_of_adj3 hΦ hnt htrans hA hB hxA
  have hnt' : y * y' ∉ M.ψ.ker := by
    refine nontwin_of_adj hnt hA hB hP.hy2 ?_ ?_
    · rw [hy]
      exact hxA
    · rw [hy']
      exact hxB
  subst hAR hBR hy hy'
  have hP' : E4Pair3N M.ψ R R' y y' := ⟨hP, hnt', hnc⟩
  have key := e4_assemble3 hP' (gen3_of_equiv_sl2 eR) (gen3_of_equiv_sl2 eR')
    (e4_sl4_sigma3 h2 hneg M.ψ hP' hRl hRl') (e4_sl4_inner3 h2 hneg M.ψ hP' hRl hRl') hA0 hB0
  exact key

end Tags

section Final


theorem e4SecNoRoot3 : E4SecNoRoot3 := by
  intro n hn hih X _ _ hlt Φ hΦ hO hgen hA hnt hdisc A hAΦ B hB x x' hxA hxB hcen
  obtain ⟨t, k, htag, ⟨M⟩⟩ := E4G3.e4_tag3 hn hih hlt hΦ hO hgen hA hdisc hAΦ hB
  rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h4 | ⟨rfl, rfl⟩ | h6
  · exact e4_concl_sp3 hΦ M hnt hAΦ hB hxA hxB hcen
  · exact e4_concl_sl43 hΦ M hnt hAΦ hB hxA hxB hcen
  · exact absurd (E4G3.dstarConnected_psu43 hΦ M) hdisc
  · exact absurd (E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inl h4) hAΦ hB hxA hxB hcen) hdisc
  · exact absurd (E4G3.dstarConnected_spin8plus3 hΦ M) hdisc
  · exact absurd (E4G3.dstarConnected_spin_of_pair3 hΦ M (Or.inr h6) hAΦ hB hxA hxB hcen) hdisc

end Final

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
