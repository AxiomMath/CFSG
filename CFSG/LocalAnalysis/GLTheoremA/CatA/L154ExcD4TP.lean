module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcD4TPInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcD4TPOuter
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoKac
import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoE6D4
import CFSG.LocalAnalysis.StandardType.GGLangSmallLat
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallPerfect

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)

open CFSG.LocalAnalysis.GLTheoremA.S10 (twoPart)

open CFSG.LocalAnalysis.GLTheoremA.FP (fixNum)

open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem l154d4tp_twoPart_sandwich {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ∣ b) (hbc : b ∣ c) (h : twoPart a = twoPart c) : twoPart b = twoPart a := by
  have h1 : twoPart a ≤ twoPart b := by
    unfold twoPart
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.factorization_le_iff_dvd ha hb).2 hab 2)
  have h2 : twoPart b ≤ twoPart c := by
    unfold twoPart
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.factorization_le_iff_dvd hb hc).2 hbc 2)
  omega

theorem l154d4tp_closure_smul_mem
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    ∀ γ ∈ Ψ, w • γ ∈ Ψ ∧ w⁻¹ • γ ∈ Ψ := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    intro γ hγ
    refine ⟨hΨ.reflection_mem γ hγ β hβ, ?_⟩
    rw [rootReflection_inv (hΨ.isRoot β hβ)]
    exact hΨ.reflection_mem γ hγ β hβ
  | one => exact fun γ hγ => ⟨by rwa [one_smul], by rwa [inv_one, one_smul]⟩
  | mul x y _ _ hx hy =>
    intro γ hγ
    refine ⟨by rw [mul_smul]; exact (hx _ (hy γ hγ).1).1, ?_⟩
    rw [mul_inv_rev, mul_smul]
    exact (hy _ (hx γ hγ).2).2
  | inv x _ hx =>
    intro γ hγ
    exact ⟨(hx γ hγ).2, by rw [inv_inv]; exact (hx γ hγ).1⟩

theorem l154d4tp_twistInner_of_two_three
    {τ : Tag}
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (h2 : twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → _)^[2]))
    (h3 : twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → _)^[3])) :
    twistInner Ψ (ρ : (Fin τ.rank → ℤ) → _) := by
  obtain ⟨w₂, hw₂, h2'⟩ := h2
  obtain ⟨w₃, hw₃, h3'⟩ := h3
  refine ⟨w₃ * w₂⁻¹, mul_mem hw₃ (inv_mem hw₂), fun γ' hγ' => ?_⟩
  have hγ : w₂⁻¹ • γ' ∈ Ψ := (l154d4tp_closure_smul_mem hΨ hw₂ γ' hγ').2
  have e3 := h3' _ hγ
  have e2 := h2' _ hγ
  rw [Function.iterate_succ_apply', e2, smul_inv_smul] at e3
  rw [e3, mul_smul]

theorem l154d4tp_commutator_le_self {G : Type*} [Group G] (X : Subgroup G) : ⁅X, X⁆ ≤ X := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem l154d4tp_twoPart_card_sandwich {G : Type*} [Group G] {A B C : Subgroup G} [Finite C]
    (hAB : A ≤ B) (hBC : B ≤ C) (h : twoPart (Nat.card A) = twoPart (Nat.card C)) :
    twoPart (Nat.card B) = twoPart (Nat.card A) := by
  haveI : Finite B := Finite.of_injective _ (Subgroup.inclusion_injective hBC)
  haveI : Finite A := Finite.of_injective _ (Subgroup.inclusion_injective hAB)
  exact l154d4tp_twoPart_sandwich Nat.card_pos.ne' Nat.card_pos.ne' Nat.card_pos.ne'
    (Subgroup.card_dvd_of_le hAB) (Subgroup.card_dvd_of_le hBC) h

theorem l154d4tp_fixNum_eq {G : Type*} [Group G] {R : Subgroup G} (σ : MulAut ↥R) (f : G →* G)
    (hσ : ∀ r : ↥R, ((σ r : ↥R) : G) = f r) :
    fixNum σ = Nat.card ↥(R ⊓ f.eqLocus (MonoidHom.id G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : G), x.1.2, by
        change f (x.1 : G) = (x.1 : G)
        rw [← hσ x.1, x.2]⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext (by
        have h : f y.1 = y.1 := y.2.2
        rw [hσ]
        exact h)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem l154d4tp_model_le
    {τ : Tag} {L : Type} [Field L] {D : LangDatum τ L} (R : FrobRoot D 3) (D₀ : LangDatum τ L)
    (hD₀ : ∀ g, D₀.step g = R.step0 g) : D₀.model ≤ D.model := by
  intro x hx
  rw [LangDatum.mem_model] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have h1 : R.step0 x = x := by rw [← hD₀]; exact hx.2
  have h2 := R.step0_iterate x
  rw [Function.iterate_fixed h1 3] at h2
  exact h2.symm

section Rational

variable {τ : Tag} {L : Type}
  [Field L] [IsAlgClosed L] {p p' : ℕ}

theorem l154d4tp_rationalComponent_le (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
  have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
    unfold rationalSpan
    rw [CFSG.StandardType.LangRat.rationalRoots_eq_componentRoots_of_mapsTo S.ρ (rootCharHom a)
      i hρ]
    exact inf_le_inf_left _ (l154d4tp_commutator_le_self _)
  exact (l154d4tp_commutator_le_self _).trans hspan

theorem l154d4tp_rationalComponent_mono (S : LangSetup τ L p) (S₀ : LangSetup τ L p')
    (hM : S₀.D.model ≤ S.D.model) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hρ₀ : ∀ γ ∈ componentRoots (rootCharHom a) i, S₀.ρ γ ∈ componentRoots (rootCharHom a) i) :
    rationalComponent S₀.ρ S₀.Γ (rootCharHom a) i ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  have hΓ : S₀.Γ ≤ S.Γ := Subgroup.commutator_mono hM hM
  have hspan : rationalSpan S₀.ρ S₀.Γ (rootCharHom a) i ≤
      rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    unfold rationalSpan
    rw [CFSG.StandardType.LangRat.rationalRoots_eq_componentRoots_of_mapsTo S.ρ (rootCharHom a)
      i hρ, CFSG.StandardType.LangRat.rationalRoots_eq_componentRoots_of_mapsTo S₀.ρ
      (rootCharHom a) i hρ₀]
    exact inf_le_inf_left _ hΓ
  exact Subgroup.commutator_mono hspan hspan

theorem l154d4tp_twoPart_fixed (S : LangSetup τ L p) (S₀ : LangSetup τ L p')
    (hM : S₀.D.model ≤ S.D.model) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hρ₀ : ∀ γ ∈ componentRoots (rootCharHom a) i, S₀.ρ γ ∈ componentRoots (rootCharHom a) i)
    {m : ℕ} (h₀ : twoPart (Nat.card ↥(rationalComponent S₀.ρ S₀.Γ (rootCharHom a) i)) = 2 ^ m)
    (hH : twoPart (Nat.card ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S₀.D.model)) =
      2 ^ m) :
    twoPart (Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓ S₀.D.model)) = 2 ^ m := by
  haveI := S₀.finite
  haveI : Finite ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S₀.D.model) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_right :
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S₀.D.model ≤ S₀.D.model))
      (Subgroup.inclusion_injective _)
  have hR₀H := l154d4tp_rationalComponent_le S₀ i hρ₀
  have hR₀R := l154d4tp_rationalComponent_mono S S₀ hM i hρ hρ₀
  have hlow : rationalComponent S₀.ρ S₀.Γ (rootCharHom a) i ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓ S₀.D.model :=
    le_inf hR₀R (hR₀H.trans inf_le_right)
  have hup : rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓ S₀.D.model ≤
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S₀.D.model :=
    inf_le_inf_right _ ((l154d4tp_rationalComponent_le S i hρ).trans inf_le_left)
  rw [l154d4tp_twoPart_card_sandwich hlow hup (h₀.trans hH.symm), h₀]

theorem l154d4tp_rationalComponent_eq_of_layer (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hqs : CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i =
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model := by
  set P := rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model with hP
  refine le_antisymm (l154d4tp_rationalComponent_le S i hρ) ?_
  have hPP : ⁅P, P⁆ = P := by
    have h1 := Group.isPerfect_def.1 hqs.1
    rw [_root_.commutator_def] at h1
    have h2 := congrArg (Subgroup.map P.subtype) h1
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  have hPΓ : P ≤ S.Γ := by
    rw [← hPP]
    exact Subgroup.commutator_mono inf_le_right inf_le_right
  have hspan : P ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    unfold rationalSpan
    rw [CFSG.StandardType.LangRat.rationalRoots_eq_componentRoots_of_mapsTo S.ρ (rootCharHom a)
      i hρ]
    exact le_inf inf_le_left hPΓ
  calc P = ⁅P, P⁆ := hPP.symm
    _ ≤ _ := Subgroup.commutator_mono hspan hspan

end Rational

theorem l154d4tp_exists_ne_neg {α : Type*} [Neg α] {Ψ : Set α} (h : 2 < Ψ.ncard) :
    ∃ x ∈ Ψ, ∃ y ∈ Ψ, y ≠ x ∧ y ≠ -x := by
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (by omega : Ψ.ncard ≠ 0)
  by_contra hcon
  push Not at hcon
  have hsub : Ψ ⊆ {x, -x} := fun y hy => by
    by_cases h1 : y = x
    · exact Or.inl h1
    · exact Or.inr (hcon x hx y hy h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({x, -x} : Set α).ncard ≤ 2 := (Set.ncard_insert_le x {-x}).trans (by simp)
  omega

section D0

open CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.StandardType.ExcThreeAtTwo
open CFSG.RankThree.PartOne.KE (d4Nodes)


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ}

theorem l154d4tp_outer_counts
    (S : LangSetup Tag.E6 L p) {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) {e : ℕ} (hq : S.D.q = 2 ^ e) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i =
        rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model ∧
      twoPart (Nat.card ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) =
        2 ^ (e * 12) := by
  classical
  have key : ∀ f : ℕ, S.D.q = 2 ^ f →
      CFSG.IsQuasisimple ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) →
      L154D4TPLay (2 ^ f) (rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model) →
      rationalComponent S.ρ S.Γ (rootCharHom a) i =
          rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model ∧
        twoPart (Nat.card ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S.D.model)) =
          2 ^ (e * 12) := by
    intro f hqf hqs hlay
    have hfe : f = e := Nat.pow_right_injective (le_refl 2) (hqf.symm.trans hq)
    subst hfe
    exact ⟨l154d4tp_rationalComponent_eq_of_layer S i hρ hqs, by rw [hlay.2, ← pow_mul]⟩
  obtain ⟨w, hn⟩ := S.D.n_weyl
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    obtain ⟨f, -, hqf, hqs, hlay⟩ := l154d4tp_outer_untw S hFr hΦ' hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hΨ hρ h1 h2
    exact key f hqf hqs hlay
  · obtain ⟨f, -, hqf, hqs, hlay⟩ := l154d4tp_outer_tw S ⟨t, ht, Fr, hFr, hΦ⟩ i v hΨ hρ h1 h2
    exact key f hqf hqs hlay

theorem l154d4tp_levelS_E6 (S : LangSetup Tag.E6 L p)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hs : 1 ≤ s) (hq : S.D.q = 2 ^ s)
    (hc24 : (componentRoots (rootCharHom a) i).ncard = 24)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)) :
    Odd (Nat.card (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) ∧
      twoPart (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) = 2 ^ (s * 12) ∧
      twoPart (Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) = 2 ^ (s * 12) :=
  l154d4tp_levelS S hT i hs hq (fun _ _ _ _ => isPerfect_componentRootSpan_simplyLaced
    (Or.inr (Or.inl rfl)) i (l154d4tp_exists_ne_neg (by rw [hc24]; norm_num))) hc24 hρ hinner

theorem l154d4tp_layer_counts
    (S₀ : LangSetup Tag.E6 L p)
    {a : Fin Tag.E6.rank → Lˣ} (hT₀ : rootDiagUnit Tag.E6 a ∈ S₀.D.torus)
    (hap : ∀ k, a k ^ 3 = 1) (ha1 : rootDiagUnit Tag.E6 a ≠ 1)
    (i : KernelComponent (rootCharHom a)) {e : ℕ} (he : 1 ≤ e) (hq : S₀.D.q = 2 ^ e)
    (hr4 : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc24 : (componentRoots (rootCharHom a) i).ncard = 24)
    (h3 : twistInner (componentRoots (rootCharHom a) i)
      ((S₀.ρ : (Fin Tag.E6.rank → ℤ) → _)^[3])) :
    (∀ γ ∈ componentRoots (rootCharHom a) i, S₀.ρ γ ∈ componentRoots (rootCharHom a) i) ∧
      twoPart (Nat.card ↥(rationalComponent S₀.ρ S₀.Γ (rootCharHom a) i)) = 2 ^ (e * 12) ∧
      twoPart (Nat.card ↥(rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) ⊓ S₀.D.model)) =
        2 ^ (e * 12) := by
  classical
  obtain ⟨v, hv, hρ₀⟩ := exists_pinned_d4Class_E6 S₀ hT₀ hap ha1 i hr4 hc24
  refine ⟨hρ₀, ?_⟩
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      (S₀.ρ : (Fin Tag.E6.rank → ℤ) → _)
  · have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) :=
      isRootComponent_componentRoots (χ := rootCharHom a) i
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot Tag.E6).subset fun β hβ => hΨ.isRoot β hβ
    have hN : (posRoots (componentRoots (rootCharHom a) i)).ncard = 12 := by
      have := l154d4tp_ncard_eq_two_mul_ncard_posRoots hΨ hfin
      omega
    refine ⟨(l154d4tp_levelS_E6 S₀ hT₀ i he hq hc24 hρ₀ hin).2.2, ?_⟩
    rw [l154d4tp_layer_twoPart S₀ hT₀ i he hq hρ₀ hin, hN]
  · have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) :=
      isRootComponent_componentRoots (χ := rootCharHom a) i
    have h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S₀.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]) := fun h2 =>
      hin (l154d4tp_twistInner_of_two_three hΨ h2 h3)
    obtain ⟨hR, hH⟩ := l154d4tp_outer_counts S₀ i v hv hρ₀ hin h2 hq
    exact ⟨by rw [hR]; exact hH, hH⟩

end D0

section E6

open CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (mem_twistedTorusOf)


variable
  {L : Type} [Field L]
  [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154d4tp_E6 (S : LangSetup Tag.E6 L p₀) (R : FrobRoot S.D 3) {e : ℕ}
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a)) (hD0 : L154RootD0 S R)
    (he : 1 ≤ e) (hq0 : R.q0 = 2 ^ e) (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ k, a k ^ 3 = 1) (ha1 : rootDiagUnit Tag.E6 a ≠ 1)
    (hfa : R.step0 (rootDiagUnit Tag.E6 a) = rootDiagUnit Tag.E6 a)
    (hr4 : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc24 : (componentRoots (rootCharHom a) i).ncard = 24)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hinner : twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (σ : MulAut ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hσ : ∀ r, ((σ r : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) : ModGL Tag.E6 L) =
      R.step0 (r : ModGL Tag.E6 L)) :
    twoPart (fixNum (onCenterQuotient σ)) ^ 3 =
      twoPart (Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) := by
  classical
  obtain ⟨D₀, hD₀q, hD₀⟩ := hD0
  obtain ⟨S₀, hS₀D, hcube⟩ := l154td4_exists_cubeSetup S R D₀ hD₀ he hq0 hD₀q
  have hT₀ : rootDiagUnit Tag.E6 a ∈ S₀.D.torus := by
    rw [hS₀D]
    refine mem_twistedTorusOf.2 ⟨(mem_twistedTorusOf.1 hT).1, ?_⟩
    have h1 := hfa
    rw [← hD₀] at h1
    exact h1
  have hq₀ : S₀.D.q = 2 ^ e := by rw [hS₀D, hD₀q, hq0]
  have hqS : S.D.q = 2 ^ (3 * e) := by rw [R.q_eq, hq0, ← pow_mul, mul_comm]
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) :=
    isRootComponent_componentRoots (χ := rootCharHom a) i
  have h3 : twistInner (componentRoots (rootCharHom a) i)
      ((S₀.ρ : (Fin Tag.E6.rank → ℤ) → _)^[3]) := by
    obtain ⟨w, hw, hwγ⟩ := hinner
    refine ⟨w, hw, fun γ hγ => ?_⟩
    rw [← hwγ γ hγ, ← hcube γ (hΨ.isRoot γ hγ)]
    rfl
  obtain ⟨hρ₀, hR₀, hH⟩ := l154d4tp_layer_counts S₀ hT₀ hap ha1 i he hq₀ hr4 hc24 h3
  have hM : S₀.D.model ≤ S.D.model := by
    rw [hS₀D]
    exact l154d4tp_model_le R D₀ hD₀
  have hK := l154d4tp_twoPart_fixed S S₀ hM i hρ hρ₀ hR₀ hH
  obtain ⟨hZ, hQ, -⟩ := l154d4tp_levelS_E6 S hT i (by omega) hqS hc24 hρ hinner
  have hRle := l154d4tp_rationalComponent_le S i hρ
  haveI : Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
    haveI := S.finite
    exact Finite.of_injective (Subgroup.inclusion (hRle.trans inf_le_right))
      (Subgroup.inclusion_injective _)
  have hKeq : rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓ D₀.step.eqLocus (MonoidHom.id _) =
      rationalComponent S.ρ S.Γ (rootCharHom a) i ⊓ S₀.D.model := by
    rw [hS₀D]
    ext x
    constructor
    · rintro ⟨hx, hxe⟩
      exact ⟨hx, rootSpan_le_adjointGroup L _ (hRle hx).1, hxe⟩
    · rintro ⟨hx, -, hxe⟩
      exact ⟨hx, hxe⟩
  rw [← FP.twoPart_fixNum_centerQuot hZ σ, hQ,
    l154d4tp_fixNum_eq σ D₀.step (fun r => (hσ r).trans (hD₀ _).symm), hKeq, hK, ← pow_mul]
  congr 1
  ring

end E6

section Final


open CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.StandardType.ExcThreeAtTwo
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple in
theorem l154D4TwoPart_holds : L154D4TwoPart := by
  intro τ L _ _ _ p₀ S R e a i hD0 he hq0 hT hap ha1 hfa _ _ hr4 hc24 hρ hinner σ hσ
  have hℓ3 : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne Nat.prime_three hℓ3
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  cases τ with
  | G2 =>
    exfalso
    have h : compRank (componentRoots (rootCharHom a) i) ≤ 2 := compRank_le_rank _
    omega
  | F4 => exact (not_d4Shape_of_three_F4 S hpL hTp i ⟨hr4, hc24⟩).elim
  | D4 => exact (ha1 (rootDiagUnit_eq_one_of_ncard i (by rw [hc24]; decide))).elim
  | E6 =>
    exact l154d4tp_E6 S R i hD0 he hq0 hT hap ha1 hfa hr4 hc24 hρ hinner σ hσ
  | E7 => exact (not_d4Shape_of_three_E7 S hpL hTp i ⟨hr4, hc24⟩).elim
  | E8 => exact (not_d4Shape_of_three_E8 S hpL hTp i ⟨hr4, hc24⟩).elim

end Final

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
