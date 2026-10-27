module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Inn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Split
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType
open CFSG.StandardType.TwE6Transport


private theorem exists_hom_mulAut_of_induces {Ω : Type} [Group Ω] {S B : Subgroup Ω} {p : ℕ}
    {R : Type} [Group R] (hB : IsElemAbelian p B) {I : Set (MulAut R)}
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* R)
    (hN : B ≤ Subgroup.normalizer (S : Set Ω))
    (hind : ∀ b ∈ B, ∃ φ ∈ I,
      GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ) :
    ∃ ψ : ↥B →* MulAut R, (∀ b : ↥B, ψ b ∈ I) ∧
      ∀ b : ↥B, GLAInduces θ (fun l l' => (l' : Ω) = (b : Ω)⁻¹ * l * b) (ψ b) := by
  classical
  choose! φ hφI hφ using hind
  have hBc : ∀ u v : ↥B, (u : Ω) * v = v * u := fun u v =>
    isElemAbelian_commute hB u.2 v.2
  have hmem : ∀ (b : Ω), b ∈ B → ∀ l : ↥S, b⁻¹ * (l : Ω) * b ∈ S := by
    intro b hb l
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hN hb)) l).1 l.2
    simpa using this
  let f : ↥B → MulAut R := fun u => φ u.1
  have hf_mul : ∀ u v : ↥B, f (u * v) = f u * f v := by
    intro u v
    refine rk2_induces_unique θ (hN (B.mul_mem u.2 v.2)) (hφ _ (B.mul_mem u.2 v.2)) ?_
    intro l l' hll'
    have hl1 := hmem v v.2 l
    have hl2 := hmem u u.2 ⟨_, hl1⟩
    have e1 := hφ v.1 v.2 l ⟨_, hl1⟩ rfl
    have e2 := hφ u.1 u.2 ⟨_, hl1⟩ ⟨_, hl2⟩ rfl
    have hl' : l' = ⟨_, hl2⟩ := by
      apply Subtype.ext
      rw [hll']
      have hc : (u : Ω) * v = v * u := hBc u v
      rw [hc]
      simp [mul_assoc]
    show (φ u.1 * φ v.1) (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')
    rw [MulAut.mul_apply, e1, e2, hl']
  exact ⟨MonoidHom.mk' f hf_mul, fun u => hφI u.1 u.2, fun u => hφ u.1 u.2⟩

private theorem exists_lift_hom_twE6 {Ω : Type} [Group Ω] {B : Subgroup Ω} {p : ℕ}
    (hB : IsElemAbelian p B) {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (σ : K ≃+* K) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ φ, φ ∈ (TwE6Transport.recipeConj σ ε).range ↔ φ ∈ TwE6Delta.RecipeI K n)
    (ψ : ↥B →* MulAut (TwE6Delta.RecipeR K n))
    (hψ : ∀ b, ψ b ∈ TwE6Delta.RecipeI K n) :
    ∃ β : ↥B →* ↥(twistedE6InndiagGL K σ),
      ∀ b, twistedE6InndiagConj K σ (β b) = ((MulAut.congr ε.symm) (ψ b))⁻¹ := by
  let α : ↥B →* MulAut ↥(twistedE6RootGroup K σ) := (MulAut.congr ε.symm).toMonoidHom.comp ψ
  have hα_mem : ∀ b : ↥B, α b ∈ (RecipeExcLang.twConj K σ).range := by
    intro b
    obtain ⟨w, hw⟩ := (hε (ψ b)).2 (hψ b)
    refine ⟨w, ?_⟩
    rw [show α b = MulAut.congr ε.symm (ψ b) from rfl, ← hw, TwE6Transport.recipeConj_eq]
    refine MulEquiv.ext fun x => ?_
    apply Subtype.ext
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
      MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  have hβ_mem : ∀ b : ↥B, ∃ g : ↥(twistedE6InndiagGL K σ),
      twistedE6InndiagConj K σ g = (α b)⁻¹ := by
    intro b
    obtain ⟨w, hw⟩ := hα_mem b
    let w' : RecipeExcLang.twInndiagGroup K σ := w⁻¹
    have hw' : (w' : ModGL TwistTag.E6.tag K) ∈ twistedE6InndiagGL K σ :=
      NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ (Subgroup.inv_mem _ w.2)
    refine ⟨⟨(w' : ModGL TwistTag.E6.tag K), hw'⟩, ?_⟩
    calc twistedE6InndiagConj K σ ⟨(w' : ModGL TwistTag.E6.tag K), hw'⟩
        = RecipeExcLang.twConj K σ w' :=
          TwE6EndNode3.twistedE6InndiagConj_eq_twConj σ w' hw'
      _ = (α b)⁻¹ := by rw [show w' = w⁻¹ from rfl, map_inv, hw]
  let g : ↥B → ↥(twistedE6InndiagGL K σ) := fun b => Classical.choose (hβ_mem b)
  have hg_spec : ∀ b : ↥B, twistedE6InndiagConj K σ (g b) = (α b)⁻¹ := fun b =>
    Classical.choose_spec (hβ_mem b)
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twistedE6InndiagConj_injective Nat.prime_two hn hK σ hσ
  have hcomm : ∀ u v : ↥B, α u * α v = α v * α u := by
    intro u v
    rw [← map_mul, ← map_mul,
      show u * v = v * u from Subtype.ext (isElemAbelian_commute hB u.2 v.2)]
  have hg_one : g 1 = 1 := by
    apply hinj
    calc twistedE6InndiagConj K σ (g 1) = (α 1)⁻¹ := hg_spec 1
      _ = 1 := by rw [map_one, inv_one]
      _ = twistedE6InndiagConj K σ 1 := by rw [map_one]
  have hg_mul : ∀ u v : ↥B, g (u * v) = g u * g v := by
    intro u v
    apply hinj
    calc twistedE6InndiagConj K σ (g (u * v)) = (α (u * v))⁻¹ := hg_spec _
      _ = ((α u) * (α v))⁻¹ := by rw [map_mul]
      _ = ((α v) * (α u))⁻¹ := by rw [hcomm u v]
      _ = (α u)⁻¹ * (α v)⁻¹ := by rw [mul_inv_rev]
      _ = twistedE6InndiagConj K σ (g u) * twistedE6InndiagConj K σ (g v) := by
            rw [hg_spec, hg_spec]
      _ = twistedE6InndiagConj K σ (g u * g v) := by rw [map_mul]
  exact ⟨MonoidHom.mk' g hg_mul, hg_spec⟩

private theorem conj_dmodel_twE6 {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    {K : Type} [Field K] [Finite K] {n : ℕ} (σ : K ≃+* K)
    (θ : ↥S ⧸ Subgroup.center ↥S ≃* TwE6Delta.RecipeR K n)
    {ψ : ↥B →* MulAut (TwE6Delta.RecipeR K n)}
    (hψ : ∀ b : ↥B, GLAInduces θ (fun l l' => (l' : Ω) = (b : Ω)⁻¹ * l * b) (ψ b))
    (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n)
    {β : ↥B →* ↥(twistedE6InndiagGL K σ)}
    (hβ : ∀ b, twistedE6InndiagConj K σ (β b) = ((MulAut.congr ε.symm) (ψ b))⁻¹)
    (π : ↥S →* ↥(twistedE6RootGroup K σ))
    (hπ : ∀ s, π s = ε.symm (θ (QuotientGroup.mk s))) :
    ∀ (b : ↥B) (s t : ↥S), (t : Ω) = (b : Ω)⁻¹ * s * b →
      ((π t : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        ((β b : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K)⁻¹ *
          ((π s : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
          ((β b : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) := by
  intro b s t hst
  have hstep : ψ b (θ (QuotientGroup.mk s)) = θ (QuotientGroup.mk t) := hψ b s t hst
  have hαβ : MulAut.congr ε.symm (ψ b) = twistedE6InndiagConj K σ ((β b)⁻¹) := by
    rw [map_inv, hβ b, inv_inv]
  have h3 : (ε.symm (ψ b (θ (QuotientGroup.mk s))) : ModGL TwistTag.E6.tag K) =
      ((MulAut.congr ε.symm (ψ b)) (π s) : ModGL TwistTag.E6.tag K) := by
    rw [hπ s, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have h4 : ((MulAut.congr ε.symm (ψ b)) (π s) : ModGL TwistTag.E6.tag K) =
      ((β b : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K)⁻¹ *
        ((π s : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
        ((β b : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) := by
    rw [hαβ, twistedE6InndiagConj_apply]
    simp
  calc ((π t : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K)
      = (ε.symm (θ (QuotientGroup.mk t)) : ModGL TwistTag.E6.tag K) := by rw [hπ t]
    _ = (ε.symm (ψ b (θ (QuotientGroup.mk s))) : ModGL TwistTag.E6.tag K) := by rw [hstep]
    _ = ((MulAut.congr ε.symm (ψ b)) (π s) : ModGL TwistTag.E6.tag K) := h3
    _ = ((β b : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K)⁻¹ *
          ((π s : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
          ((β b : ↥(twistedE6InndiagGL K σ)) : ModGL TwistTag.E6.tag K) := h4

private theorem faithful_twE6 {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hinj : Function.Injective (twistedE6InndiagConj K σ)) :
    ∀ g ∈ twistedE6InndiagGL K σ,
      (∀ h ∈ twistedE6RootGroup K σ, g * h = h * g) → g = 1 := by
  intro g hg hgc
  have hsub : (⟨g, hg⟩ : ↥(twistedE6InndiagGL K σ)) = 1 := by
    apply hinj
    refine MulEquiv.ext fun h => ?_
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply]
    have h1 : twistedE6InndiagConj K σ (1 : ↥(twistedE6InndiagGL K σ)) = 1 := map_one _
    rw [h1, MulAut.one_apply]
    change g * (h : ModGL TwistTag.E6.tag K) * g⁻¹ = (h : ModGL TwistTag.E6.tag K)
    rw [hgc h h.2, mul_assoc, mul_inv_cancel, mul_one]
  exact congrArg Subtype.val hsub

theorem exists_dmodel_twE6 {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 3 S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .twE6)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 3 lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F ≃+* F),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ lab.n) ∧ 3 ∣ 2 ^ lab.n + 1 ∧
      Nonempty (S172DModel S B (twistedE6RootGroup F σ) (twistedE6InndiagGL F σ)) := by
  classical
  obtain ⟨-, lab', hlab', hraw⟩ := hmark
  obtain ⟨-, -, -, -, -, -, _, ⟨hlabEq, -, -, -⟩⟩ := rk2_rawDatum_exists hraw
  rw [hlabEq] at hraw
  obtain ⟨t, r, n⟩ := lab
  subst htag
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfin, hKcard, -, -, θ, -, hsplit, hN, hind⟩ := hraw
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hlab.1 hKcard
  have hpq : 3 ∣ 2 ^ n + 1 :=
    Y10F.dvd_two_pow_add_one_of_split16_of_twA_or_twE6 hsplit (Or.inr rfl)
  obtain ⟨ψ, hψI, hψ⟩ := exists_hom_mulAut_of_induces (p := 3) hcfg.elem θ hN hind
  obtain ⟨β, hβ⟩ := exists_lift_hom_twE6 hcfg.elem hlab.1 σ hKcard hσ ε hε ψ hψI
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twistedE6InndiagConj_injective Nat.prime_two hlab.1 hKcard σ hσ
  let G₀ : Subgroup (ModGL TwistTag.E6.tag K) := twistedE6RootGroup K σ
  let Ghat : Subgroup (ModGL TwistTag.E6.tag K) := twistedE6InndiagGL K σ
  let π : ↥S →* ↥G₀ :=
    (θ.trans ε.symm).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))
  have hπ : ∀ s : ↥S, π s = ε.symm (θ (QuotientGroup.mk s)) := fun s => rfl
  have hsurj : Function.Surjective π :=
    (θ.trans ε.symm).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center ↥S := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (θ.trans ε.symm) (QuotientGroup.mk s) = 1 ↔ s ∈ Subgroup.center ↥S
    rw [← map_one (θ.trans ε.symm), (θ.trans ε.symm).injective.eq_iff,
      QuotientGroup.eq_one_iff]
  have hconj := conj_dmodel_twE6 (K := K) (n := n) σ θ hψ ε hβ π hπ
  have hle : G₀ ≤ Ghat := fun _ hg => Subgroup.mem_sup_left hg
  have hfaithful : ∀ g ∈ Ghat, (∀ h ∈ G₀, g * h = h * g) → g = 1 := faithful_twE6 hinj
  exact ⟨K, hKfield, hKfin, σ, hKcard, hσ, hpq,
    ⟨⟨π, β, hsurj, hker, hconj, hle, hfaithful⟩⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
