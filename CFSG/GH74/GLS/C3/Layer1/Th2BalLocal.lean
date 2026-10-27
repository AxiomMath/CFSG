module

public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Fixed
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Normalizes

public section

namespace CFSG.GH74.GLS.Th2.Bal

open CFSG CFSG.LocalCores CFSG.Open CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance

@[expose] def IsLocallyKBalanced (k : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ H : Subgroup (MulAut K), (MulAut.conj : K →* MulAut K).range ≤ H →
    ∀ F : Subgroup H, 2 ^ k ≤ Nat.card F → (∀ f ∈ F, f * f = 1) → deltaCore F = ⊥

section Faithful

variable {X : Type*} [Group X] [Finite X]

@[expose] noncomputable def canonicalNormalizerAction (L : Subgroup X) [Group.IsPerfect L] :
    Subgroup.normalizer (L : Set X) →* MulAut (L ⧸ Subgroup.center L) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L).comp
    (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L)

@[simp] theorem canonicalNormalizerAction_apply (L : Subgroup X) [Group.IsPerfect L]
    (x : Subgroup.normalizer (L : Set X)) :
    canonicalNormalizerAction L x =
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom L)
        (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L x) := rfl

@[simp] theorem canonicalNormalizerAction_rangeRestrict_apply
    (L : Subgroup X) [Group.IsPerfect L]
    (x : Subgroup.normalizer (L : Set X)) :
    ((canonicalNormalizerAction L).rangeRestrict x :
      MulAut (L ⧸ Subgroup.center L)) = canonicalNormalizerAction L x := rfl

structure CoupledActionData (L : Subgroup X) [Group.IsPerfect L]
    (F D : Subgroup X) where
  hker : (canonicalNormalizerAction L).ker =
    (Subgroup.centralizer (L : Set X)).subgroupOf (Subgroup.normalizer (L : Set X))
  hInn : (MulAut.conj : (L ⧸ Subgroup.center L) →*
      MulAut (L ⧸ Subgroup.center L)).range ≤ (canonicalNormalizerAction L).range
  A : Subgroup (canonicalNormalizerAction L).range
  hA : A = (F.subgroupOf (Subgroup.normalizer (L : Set X))).map
    (canonicalNormalizerAction L).rangeRestrict
  hAcard : Nat.card A = Nat.card F
  hA2 : ∀ a ∈ A, a * a = 1
  hFinj : ∀ (f : X) (hf : f ∈ F) (hfM : f ∈ Subgroup.normalizer (L : Set X)),
    canonicalNormalizerAction L ⟨f, hfM⟩ = 1 → f = 1
  D0 : Subgroup (canonicalNormalizerAction L).range
  hD0 : D0 = (D.subgroupOf (Subgroup.normalizer (L : Set X))).map
    (canonicalNormalizerAction L).rangeRestrict
  hD0le : D0 ≤ deltaCore A
  hActive : ∀ (d : X) (hdM : d ∈ Subgroup.normalizer (L : Set X)),
    (¬ ∀ x ∈ L, d * x = x * d) → canonicalNormalizerAction L ⟨d, hdM⟩ ≠ 1

noncomputable def coupled_action_data {L : Subgroup X} (hL : IsComponent L) [Group.IsPerfect L]
    {F : Subgroup X} (hF2 : ∀ f ∈ F, f * f = 1)
    (hFL : ∀ f ∈ F, conjSub f L = L)
    (hFfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f)
    {D : Subgroup X} (hD : ∀ d ∈ D, conjSub d L = L)
    (hDF : ∀ f ∈ F, f ≠ 1 → D ≤ CFSG.Assembly.Dichotomy.involutionOddCore f) :
    CoupledActionData L F D := by
  set M : Subgroup X := Subgroup.normalizer (L : Set X) with hM
  have hFM : F ≤ M := fun f hf => mem_normalizer_of_conjSub_eq (hFL f hf)
  have hDM : D ≤ M := fun d hd => mem_normalizer_of_conjSub_eq (hD d hd)
  let ρ : M →* MulAut (L ⧸ Subgroup.center L) := canonicalNormalizerAction L
  have hker : ρ.ker = (Subgroup.centralizer (L : Set X)).subgroupOf M :=
    CFSG.LocalAnalysis.ComponentInitial.ker_centerQuotient_comp_normalizerConjHom L
  have hInn : (MulAut.conj : (L ⧸ Subgroup.center L) →*
      MulAut (L ⧸ Subgroup.center L)).range ≤ ρ.range :=
    CFSG.LocalAnalysis.ComponentInitial.inner_le_range_centerQuotient_comp L
  let φ : M →* ρ.range := ρ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  have hφker : φ.ker = ρ.ker := MonoidHom.ker_rangeRestrict ρ
  set F' : Subgroup M := F.subgroupOf M with hF'
  have hFinj : ∀ m ∈ F', φ m = 1 → m = 1 := by
    intro m hm hm1
    have h1 : m ∈ ρ.ker := by rw [← hφker]; exact hm1
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    by_contra hne
    refine hFfaith (m : X) ((Subgroup.mem_subgroupOf).mp hm)
      (fun h => hne (Subtype.ext h)) ?_
    intro x hx
    exact (h1 x hx).symm
  have hbij : Function.Bijective (φ.subgroupMap F') := by
    refine ⟨?_, φ.subgroupMap_surjective F'⟩
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro m hm
    have := hFinj m m.2 (by
      have h2 := (MonoidHom.mem_ker.mp hm)
      have h3 := congrArg Subtype.val h2
      exact h3)
    exact Subtype.ext this
  have hAcard : Nat.card (F'.map φ) = Nat.card F := by
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv
  have hA2 : ∀ g ∈ F'.map φ, g * g = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hF2 m ((Subgroup.mem_subgroupOf).mp hm))
    rw [this, map_one]
  have hD0le : (D.subgroupOf M).map φ ≤ deltaCore (F'.map φ) := by
    refine le_deltaCore fun g hg hg1 => ?_
    obtain ⟨m, hm, rfl⟩ := hg
    have hmF : (m : X) ∈ F := (Subgroup.mem_subgroupOf).mp hm
    have hm1 : (m : X) ≠ 1 := by
      intro h
      have hm1' : m = 1 := Subtype.ext h
      exact hg1 (by rw [hm1']; exact map_one φ)
    have hDm : D.subgroupOf M ≤ CFSG.Assembly.Dichotomy.involutionOddCore m := fun u hu =>
      subgroupOf_involutionOddCore_le m
        ((Subgroup.mem_subgroupOf).mpr (hDF (m : X) hmF hm1 ((Subgroup.mem_subgroupOf).mp hu)))
    exact (Subgroup.map_mono hDm).trans
      (map_involutionOddCore_le φ hφ (isPGroup_zpowers_of_mul_self_eq_one
        (Subtype.ext (hF2 (m : X) hmF) : m * m = 1)))
  refine
    { hker := hker
      hInn := hInn
      A := F'.map φ
      hA := rfl
      hAcard := hAcard
      hA2 := hA2
      hFinj := ?_
      D0 := (D.subgroupOf M).map φ
      hD0 := rfl
      hD0le := hD0le
      hActive := ?_ }
  · intro f hf hfM hρ
    have h1 : (⟨f, hfM⟩ : M) ∈ ρ.ker := MonoidHom.mem_ker.mpr hρ
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    by_contra hne
    refine hFfaith f hf hne ?_
    intro x hx
    exact (h1 x hx).symm
  · intro d hdM hdnc hρ1
    apply hdnc
    intro x hx
    have hdker : (⟨d, hdM⟩ : M) ∈ ρ.ker := MonoidHom.mem_ker.mpr hρ1
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hdker
    exact (hdker x hx).symm

theorem commute_of_faithful_k {L : Subgroup X} (hL : IsComponent L) {k : ℕ}
    (hbal : IsLocallyKBalanced k (L ⧸ Subgroup.center L))
    {F : Subgroup X} (hFk : 2 ^ k ≤ Nat.card F) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFL : ∀ f ∈ F, conjSub f L = L)
    (hFfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f)
    {D : Subgroup X} (hD : ∀ d ∈ D, conjSub d L = L)
    (hDF : ∀ f ∈ F, f ≠ 1 → D ≤ CFSG.Assembly.Dichotomy.involutionOddCore f) :
    ∀ d ∈ D, ∀ x ∈ L, d * x = x * d := by
  haveI : Group.IsPerfect L := hL.1.1
  obtain ⟨hker, hInn, A, hA, hAcard, hA2, hFinj, D0, hD0, hD0le, hActive⟩ :=
    coupled_action_data hL hF2 hFL hFfaith hD hDF
  let ρ := canonicalNormalizerAction L
  let φ := ρ.rangeRestrict
  have hAcard' : 2 ^ k ≤ Nat.card A := by rw [hAcard]; exact hFk
  have hdelta : deltaCore A = ⊥ := hbal ρ.range hInn A hAcard' hA2
  rw [hdelta] at hD0le
  intro d hd x hx
  have hdM : d ∈ Subgroup.normalizer (L : Set X) := mem_normalizer_of_conjSub_eq (hD d hd)
  have hmem : φ ⟨d, hdM⟩ ∈ D0 := by
    rw [hD0]
    exact ⟨⟨d, hdM⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  have h1 : φ ⟨d, hdM⟩ = 1 := Subgroup.mem_bot.mp (hD0le hmem)
  have h2 : (⟨d, hdM⟩ : Subgroup.normalizer (L : Set X)) ∈ φ.ker :=
    MonoidHom.mem_ker.mpr h1
  rw [MonoidHom.ker_rangeRestrict, hker, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_iff] at h2
  exact (h2 x hx).symm

end Faithful

section Existence

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem exists_ne_one_of_two_pow_le {F : Subgroup X} {k : ℕ} (hk : 1 ≤ k)
    (hFk : 2 ^ k ≤ Nat.card F) : ∃ f ∈ F, f ≠ 1 := by
  by_contra h
  push Not at h
  have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr h
  rw [hbot, Subgroup.card_bot] at hFk
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem exists_component_of_deltaCore (hO : CFSG.pPrimeCore 2 X = ⊥) {F : Subgroup X}
    (hF2 : ∀ f ∈ F, f * f = 1) {f₀ : X} (hf₀F : f₀ ∈ F) (hf₀1 : f₀ ≠ 1) {N : Subgroup X}
    (hNF : N ≤ deltaCore F) (hN1 : N ≠ ⊥) :
    ∃ L : Subgroup X, IsComponent L ∧ (∀ f ∈ F, conjSub f L = L) ∧
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) ∧ (∀ n ∈ N, conjSub n L = L) ∧
      ¬ ∀ n ∈ N, ∀ x ∈ L, n * x = x * n := by
  classical
  by_contra hno
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDodd : Odd (Nat.card N) :=
    (odd_card_deltaCore hf₀F hf₀1).of_dvd_nat (Subgroup.card_dvd_of_le hNF)
  have hord : orderOf f₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hF2 f₀ hf₀F) hf₀1
  have hNF' : ∀ f ∈ F, f ≠ 1 → N ≤ CFSG.Assembly.Dichotomy.involutionOddCore f :=
    fun f hf hf1 => hNF.trans (deltaCore_le_involutionOddCore hf hf1)
  have hQ : N ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have := commute_pCore_of_mem_involutionOddCore hord (hNF' f₀ hf₀F hf₀1 hd) q hq
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hL : ∀ L : Subgroup X, IsComponent L → N ≤ Subgroup.centralizer (L : Set X) := by
    intro L hL
    have key : ∀ d ∈ N, ∀ x ∈ L, d * x = x * d := by
      by_cases hcen : ∃ f ∈ F, f ≠ 1 ∧ ∀ x ∈ L, f * x = x * f
      · obtain ⟨f, hfF, hf1, hfL⟩ := hcen
        have hLC : L ≤ Subgroup.centralizer ({f} : Set X) := fun x hx =>
          Subgroup.mem_centralizer_singleton_iff.mpr (hfL x hx).symm
        intro d hd
        exact commute_of_isComponent_centralizer (hNF' f hfF hf1 hd) hLC
          (CFSG.LocalCores.component_overgroup hL hLC)
      · by_cases hmov : ∃ f ∈ F, conjSub f L ≠ L
        · obtain ⟨f, hfF, hfne⟩ := hmov
          have hf1 : f ≠ 1 := fun h => hfne (by rw [h, conjSub_one])
          intro d hd
          exact commute_of_moved hL (hF2 f hfF) hfne (hNF' f hfF hf1 hd)
        · push Not at hcen hmov
          by_contra hnc
          apply hno
          refine ⟨L, hL, hmov, fun f hf hf1 h => ?_, fun d hd => ?_, hnc⟩
          · obtain ⟨x, hx, hxne⟩ := hcen f hf hf1
            exact hxne (h x hx)
          · exact conjSub_eq_of_mem_involutionOddCore hL (hF2 f₀ hf₀F) (hmov f₀ hf₀F)
              (hNF' f₀ hf₀F hf₀1 hd)
    intro d hd x hx
    exact (key d hd x hx).symm
  exact hN1 (eq_bot_of_centralizes_pCore_of_centralizes_components hO hDodd hQ hL)

theorem exists_component_not_locallyKBalanced (hO : CFSG.pPrimeCore 2 X = ⊥) {F : Subgroup X}
    {k : ℕ} (hFk : 2 ^ k ≤ Nat.card F) (hF2 : ∀ f ∈ F, f * f = 1) {f₀ : X} (hf₀F : f₀ ∈ F)
    (hf₀1 : f₀ ≠ 1) {N : Subgroup X} (hNF : N ≤ deltaCore F) (hN1 : N ≠ ⊥) :
    ∃ L : Subgroup X, IsComponent L ∧ (∀ f ∈ F, conjSub f L = L) ∧
      (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) ∧ (∀ n ∈ N, conjSub n L = L) ∧
      (¬ ∀ n ∈ N, ∀ x ∈ L, n * x = x * n) ∧ ¬ IsLocallyKBalanced k (L ⧸ Subgroup.center L) := by
  obtain ⟨L, hL, hFL, hfaith, hNL, hnc⟩ := exists_component_of_deltaCore hO hF2 hf₀F hf₀1 hNF hN1
  refine ⟨L, hL, hFL, hfaith, hNL, hnc, fun hbal => hnc ?_⟩
  intro n hn x hx
  exact commute_of_faithful_k hL hbal hFk hF2 hFL hfaith (D := N) hNL
    (fun f hf hf1 => hNF.trans (deltaCore_le_involutionOddCore hf hf1)) n hn x hx

end Existence

end CFSG.GH74.GLS.Th2.Bal
