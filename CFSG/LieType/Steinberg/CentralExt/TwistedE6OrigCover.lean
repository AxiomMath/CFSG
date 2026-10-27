module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoOriginalOuterAction
import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcDataTw
import CFSG.LocalAnalysis.StandardType.GGCanonicalToLegacy

public section

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

structure TwE6CoverData
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 E H) where
  hEN : E ≤ Subgroup.normalizer (H : Set G)
  commH : commutator H = ⊤
  lab : LargeEvenLabel
  hΛ : LargeEvenInLambda2 lab
  hSlab : S 3 lab
  hn : 1 ≤ lab.n
  h3 : 3 ∣ 2 ^ lab.n + 1
  K : Type
  fieldK : Field K
  finiteK : Finite K
  σ : K ≃+* K
  hK : Nat.card K = (2 ^ lab.n) ^ 2
  hσ : ∀ c, σ c = c ^ 2 ^ lab.n
  θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ)
  hθ : ∀ b ∈ E, ∃ φ ∈ RecipeExcLang.markIDImage (IsRoot TwistTag.E6.tag) K
      (twistedE6RootGroup K σ), LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
  ψ : ↥H →* ↥(twistedE6RootGroup K σ)
  hψθ : ∀ l : ↥H, ψ l = centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
      (ggQuotHom θ l)
  hψ : Function.Surjective ψ
  hker : ψ.ker = Subgroup.center ↥H
  hact : CompatibleAction σ hEN ψ

theorem twE6CoverData_nonempty
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 E H) :
    Nonempty (TwE6CoverData hS hmark) := by
  classical
  unfold GGInnerDiagOnLabel at hmark
  obtain ⟨hper, lab, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, hQraw⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨_, hPraw⟩ := hQraw.2.2
  obtain ⟨hSl, -, -⟩ := hPraw
  obtain ⟨htag, h3⟩ := hS lab hSl
  have hn : 1 ≤ lab.n := hlab.1
  let Qmark : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥H ⧸ Subgroup.center ↥H ≃* R,
        S 3 lab ∧ E ≤ Subgroup.normalizer (H : Set G) ∧
          ∀ b ∈ E, ∃ φ ∈ I, LargeEvenInduces θ
            (fun l l' => (l' : G) = (b : G)⁻¹ * l * (b : G)) φ
  have hrawCanon : CFSG.Assembly.LargeEvenRawDatum lab Qmark :=
    CFSG.StandardType.largeEvenRawDatum_canonical_of_legacy_mono
      (lab := lab) (Q := Qmark)
      (fun R _ I I' F hII' hQ => by
        obtain ⟨hs, hna, θ, hS, hEN, hθ⟩ := hQ
        exact ⟨hs, hna, θ, hS, hEN, fun b hb => by
          obtain ⟨φ, hφ, hind⟩ := hθ b hb
          exact ⟨φ, hII' hφ, hind⟩⟩)
      hraw
  obtain ⟨K, instF, instFin, σ, hKcard, hσpow, hQ0⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.excTwE6_raw_of_label
      (lab := lab) (Q := Qmark) htag hn hrawCanon
  obtain ⟨-, -, θ, -, hEN, hθ⟩ := hQ0
  let eR : LargeEvenCenterQuot (twistedE6RootGroup K σ) ≃* ↥(twistedE6RootGroup K σ) :=
    centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  let θ' : ↥H ⧸ Subgroup.center ↥H ≃* ↥(twistedE6RootGroup K σ) := θ.trans eR
  let ψ : ↥H →* ↥(twistedE6RootGroup K σ) := ggQuotHom θ'
  have hψθ : ∀ l : ↥H, ψ l = eR (ggQuotHom θ l) := fun _ => rfl
  have hcomp : ∀ (e : ↥E) (l : ↥H),
      MulAut.congr eR (ggBeta H θ hEN e) (ψ l) = ψ (ggGamma H hEN e l) := by
    intro e l
    have h1 : ggBeta H θ hEN e (ggQuotHom θ l) = ggQuotHom θ (ggGamma H hEN e l) :=
      ggBeta_ggQuotHom H hEN θ e l
    calc MulAut.congr eR (ggBeta H θ hEN e) (ψ l)
        = MulAut.congr eR (ggBeta H θ hEN e) (eR (ggQuotHom θ l)) := by rw [hψθ]
      _ = eR (ggBeta H θ hEN e (ggQuotHom θ l)) := by
          simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      _ = eR (ggQuotHom θ (ggGamma H hEN e l)) := by rw [h1]
      _ = ψ (ggGamma H hEN e l) := by rw [← hψθ]
  have hact : CompatibleAction σ hEN ψ := by
    intro e
    have hmem : ggBeta H θ hEN e ∈
        RecipeExcLang.markIDImage (Blueprint.Chevalley.IsRoot TwistTag.E6.tag) K
          (twistedE6RootGroup K σ) :=
      ggBeta_mem H θ hEN hθ e
    obtain ⟨w, hw⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.excTwE6_exists_twConj_of_mem_markID σ hmem
    refine ⟨RecipeExcLang.twConj K σ w, ⟨w, rfl⟩, ?_⟩
    intro l
    have hw' : MulAut.congr eR (ggBeta H θ hEN e) = RecipeExcLang.twConj K σ w := hw
    rw [← hw']
    exact hcomp e l
  exact ⟨⟨hEN, hper, lab, hlab, hSl, hn, h3, K, instF, instFin, σ, hKcard, hσpow,
    θ, hθ, ψ, hψθ, ggQuotHom_surjective θ', ker_ggQuotHom θ', hact⟩⟩

noncomputable def twE6CoverData
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (hmark : GGInnerDiagOnLabel S 3 E H) : TwE6CoverData hS hmark :=
  Classical.choice (twE6CoverData_nonempty hS hmark)

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
