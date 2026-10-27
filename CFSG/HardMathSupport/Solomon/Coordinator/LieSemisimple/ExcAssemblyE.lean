module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Untw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcField
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.RecipeExcLang

set_option linter.unusedSectionVars false


theorem natCast_ne_zero_algebraicClosure {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K)]
  intro h
  have hpe : ringChar K = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 h
  apply hpK
  rw [Nat.card_eq_fintype_card, hn, hpe]
  exact dvd_pow_self p n.pos.ne'

theorem perfectInLayer_exc_inner_untw {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ Nat.card K) (hmon : MonomialToralAt τ p)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤)
    (β : MulAut ↥(adjointGroup τ K)) (h : ModGL τ K)
    (hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈
      adjointGroup τ (AlgebraicClosure K))
    (hβ : ∀ c, (β c : ModGL τ K) = h * c * h⁻¹) (hp1 : h ^ p = 1) (hh1 : h ≠ 1) :
    PerfectInLayer β := by
  by_cases hq : 5 ≤ p ∨ 4 ≤ Nat.card K
  · obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ := exists_langSetup_of_inner_untw hτ
      hp hpK hq hmon hperf β h hhL hβ hp1 hh1
    exact perfectInLayer_of_langSetup S ι hinj hrange β hconj hT hap h1
      (langSetup_hTame S hT hap h1)
  ·
    have hK1 : 0 < Nat.card K := Nat.card_pos
    have h5K : ¬ 5 ∣ Nat.card K := fun h5 => by
      have := Nat.le_of_dvd hK1 h5
      omega
    obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_untw_of_prime hτ hp hpK Nat.prime_five h5K (Or.inl le_rfl) hmon
        hperf β h hhL hβ hp1 hh1
    exact perfectInLayer_of_langSetup_of_prime S hp ι hinj hrange β hconj hT hap h1
      (langSetup_hTame_of_prime S hp (natCast_ne_zero_algebraicClosure hp hpK)
        (fun hG2 => (hq (hsmall hG2)).elim) hT hap h1)

theorem baseChange_mem_adjointGroup_of_mem_inndiag {τ : Tag} {K : Type} [Field K]
    {h : ModGL τ K} (hh : h ∈ inndiagGroup τ K) :
    baseChangeGL (algebraMap K (AlgebraicClosure K)) h ∈ adjointGroup τ (AlgebraicClosure K) :=
  baseChangeGL_mem_adjointGroup_of_mem_inndiag _ hh

private theorem pow_card_sub_one_mem_adjointGroup {τ : Tag} {K : Type} [Field K] [Finite K]
    {w : ModGL τ K} (hw : w ∈ inndiagGroup τ K) :
    w ^ (Nat.card K - 1) ∈ adjointGroup τ K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨b, j, hj, rfl⟩ := hw
  have key : ∀ n : ℕ, ∃ j' ∈ adjointGroup τ K,
      (rootDiagUnit τ b * j) ^ n = rootDiagUnit τ b ^ n * j' := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨j', hj', hn⟩ := ih
      have h1 := conj_rootDiagUnit_mem_adjointGroup (τ := τ) b⁻¹ hj'
      rw [← rootDiagUnit_inv, inv_inv] at h1
      refine ⟨(rootDiagUnit τ b)⁻¹ * j' * rootDiagUnit τ b * j, mul_mem h1 hj, ?_⟩
      rw [pow_succ, hn, pow_succ]
      group
  obtain ⟨j', hj', hn⟩ := key (Nat.card K - 1)
  have hd : rootDiagUnit τ b ^ (Nat.card K - 1) = 1 := by
    refine rootDiagUnit_pow_eq_one_of_forall fun i => Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ (b i).ne_zero
  rw [hn, hd, one_mul]
  exact hj'

theorem exists_inndiag_pow_eq_one {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (β : MulAut ↥(adjointGroup τ K)) (hβ : β ^ p = 1)
    {h : ModGL τ K} (hh : h ∈ inndiagGroup τ K)
    (hβh : ∀ c : adjointGroup τ K, (β c : ModGL τ K) = h * c * h⁻¹) :
    ∃ h' ∈ inndiagGroup τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = h' * c * h'⁻¹) ∧
      h' ^ p = 1 := by
  classical
  clear hτ
  have hpow : ∀ w : ModGL τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = w * c * w⁻¹) →
      ∀ (n : ℕ) (c : adjointGroup τ K), ((β ^ n) c : ModGL τ K) = w ^ n * c * (w ^ n)⁻¹ := by
    intro w hw n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ', MulAut.mul_apply, hw, ih, pow_succ']
      group
  have hcomm : ∀ w : ModGL τ K, (∀ c : adjointGroup τ K, (β c : ModGL τ K) = w * c * w⁻¹) →
      ∀ c ∈ adjointGroup τ K, w ^ p * c = c * w ^ p := by
    intro w hw c hc
    have h1 := hpow w hw p ⟨c, hc⟩
    rw [hβ, MulAut.one_apply] at h1
    change c = w ^ p * c * (w ^ p)⁻¹ at h1
    rw [eq_mul_inv_iff_mul_eq] at h1
    exact h1.symm
  have hCz : ∀ x ∈ adjointGroup τ K, (∀ c ∈ adjointGroup τ K, x * c = c * x) → x = 1 := by
    intro x hx hc
    have hxc : (⟨x, hx⟩ : adjointGroup τ K) ∈ Subgroup.center (adjointGroup τ K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hxc
    exact congrArg Subtype.val hxc
  by_cases hK4 : 4 ≤ Nat.card K
  · exact ⟨h, hh, hβh, eq_one_of_commute_adjointGroup hK4 (pow_mem hh p) (hcomm h hβh)⟩
  have hcard : Nat.card K = 2 ∨ Nat.card K = 3 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hm := pow_card_sub_one_mem_adjointGroup hh
  by_cases hA : h ^ p ∈ adjointGroup τ K
  · exact ⟨h, hh, hβh, hCz _ hA (hcomm h hβh)⟩
  have h3 : Nat.card K = 3 := by
    rcases hcard with hc | hc
    · rw [hc] at hm
      exact absurd (pow_mem hm p) (by simpa using hA)
    · exact hc
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [h3] at hm
    exact hA hm
  rw [h3] at hm
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have hmem : h ^ (p + 1) ∈ adjointGroup τ K := by
    have e : h ^ (p + 1) = (h ^ (3 - 1)) ^ (k + 1) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [e]
    exact pow_mem hm _
  have hβ' : ∀ c : adjointGroup τ K, (β c : ModGL τ K) = h ^ (p + 1) * c * (h ^ (p + 1))⁻¹ := by
    intro c
    have := hpow h hβh (p + 1) c
    rwa [pow_succ, hβ, one_mul] at this
  exact ⟨h ^ (p + 1), adjointGroup_le_inndiagGroup hmem, hβ',
    hCz _ (pow_mem hmem p) (hcomm _ hβ')⟩

theorem perfectInLayer_exc_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hmon : MonomialToralAt τ p)
    (β : MulAut ↥(adjointGroup τ K)) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : PerfectInLayer β := by
  classical
  have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    single_edge_perfect τ K (by rcases hτ with h | h | h <;> simp [h])
  obtain ⟨Θ, -, hΘ, -, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form τ hτ K
  obtain ⟨g, a, σ, ε, hform⟩ := hnf β
  have hΘp : Θ β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  rw [hΘ β g a σ ε hform] at hΘp
  have hσp : σ ^ p = 1 := by simpa using congrArg Prod.fst hΘp
  have hεp : exactE τ ∣ p * (ε : ℕ) := by
    have h2 : (Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE τ))) ^ p = 1 :=
      congrArg Prod.snd hΘp
    rw [← ofAdd_nsmul, ofAdd_eq_one] at h2
    rw [← ZMod.natCast_eq_zero_iff]
    simpa using h2
  have hcop : Nat.Coprime (exactE τ) p := by
    rcases hτ with h | h | h
    · rw [h]
      exact (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    · rw [h]
      exact Nat.coprime_one_left p
    · rw [h]
      exact Nat.coprime_one_left p
  have hε : (ε : ℕ) = 0 :=
    Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_left hεp) ε.2
  rw [hε] at hform
  have hβe : β = MulAut.conj g * exactNormalAut τ K a σ 0 :=
    eq_conj_mul_exactNormalAut_of_apply hform
  by_cases hσ : σ = 1
  · subst hσ
    have hβw : ∀ c : adjointGroup τ K, (β c : ModGL τ K) =
        ((g : ModGL τ K) * rootDiagUnit τ a) * c * ((g : ModGL τ K) * rootDiagUnit τ a)⁻¹ := by
      intro c
      have e : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (c : ModGL τ K) = c :=
        Units.ext (entrywise_id _)
      rw [hform c, exactQ_zero, inv_one, mul_inv_rev, e]
      simp only [mul_assoc, mul_one]
    have hw : (g : ModGL τ K) * rootDiagUnit τ a ∈ inndiagGroup τ K :=
      mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
    obtain ⟨h', hh', hβh', hh'p⟩ := exists_inndiag_pow_eq_one hτ hp β hβ hw hβw
    have hh1 : h' ≠ 1 := by
      rintro rfl
      apply hβ1
      refine MulEquiv.ext fun c => Subtype.ext ?_
      rw [hβh' c]
      simp
    have hsmall : τ = .G2 → 5 ≤ p ∨ 4 ≤ Nat.card K := fun hG2 => by
      rcases hτ with h | h | h <;> rw [h] at hG2 <;> exact absurd hG2 (by decide)
    exact perfectInLayer_exc_inner_untw hτ5 hp hpK hsmall hmon hperf β h'
      (baseChange_mem_adjointGroup_of_mem_inndiag hh') hβh' hh'p hh1
  · rw [hβe]
    exact perfectInLayer_exc_field τ hp g a σ hσ hσp (by rw [← hβe]; exact hβ)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
