module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCorrectedSourceAction
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalA2Pair
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusAut
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalRecipeSourceSquare
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalFieldLangSquare
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7BaseChange
public noncomputable section

namespace CFSG.StandardType.GGFinModel


open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.CTP CFSG.LieType.Universal.Unitary
  CFSG.StandardType.CompactA2Pair CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.E6
  CFSG.RankThree.PartOne.TCX.E CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
open scoped MatrixGroups commutatorElement


open CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG.GroupTheory


open CFSG.EvenSmallLie.TwoE6 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.StandardType.TableBExc.E6Three
set_option allowUnsafeReducibility true in
attribute [local reducible] TwistTag.tag langTag


set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem original_qTwo_pair_forall_fields_of_corrected_a2_roots
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} :
    letI := D.fieldK
    letI := D.finiteK
    TwE6ToralCoords 1 D.hEN D.ψ κ →
    ∀ (r s : MulAut Bs) (α γ : Fin Tag.E6.rank → ℤ),
      IsA2Pair α γ →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      D.twoKernelInG ⊓ Subgroup.centralizer
        (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥ →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
        Nat.card K = (2 ^ f) ^ 2 →
        Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
        ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
          (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  letI := D.fieldK
  letI := D.finiteK
  intro hκ r s α γ hpair hHr hHs hfree
  obtain ⟨M, ζ0, hζ0, β, mu, hmu, hμΓ, hζ0o, hsource, hact, hmarking⟩ :=
    exists_original_qTwo_native_residual_square hκ D.hK4 D.hσ D.hψ D.hker
  obtain ⟨w, Ψ, ρ, c, theta, hρ, hframe, hwα, hwγ, hinj, hc, hmin, hcanonical,
      hphi, hΓ, hwhole, hB0, hB1, hfields⟩ :=
    exists_twisted_originalU_model_marked_pair_at_a2_pair (n := 0) M
      Nat.prime_three (by decide) (by decide) (Or.inr (by decide)) hpair
  let θ := β.toMonoidHom.comp theta
  let phi := (MulAut.conj M.D.g0).symm.toMonoidHom.comp
    ((ggIotaK .twistedE6 0 1 (by decide)).comp theta)
  have hμθ : mu.comp (isogenyStd.comp θ) = phi := by
    apply MonoidHom.ext
    intro A
    exact hsource (theta A)
  have hθQ : Function.Injective (D.joinedScMap.comp θ) := by
    intro A B hAB
    have hsc : D.scMap (θ A) = D.scMap (θ B) :=
      D.joinedQuotientMap_injective hAB
    have hn := congrArg (centralTwoQuotientMap D.stdCover_ker_le_center) hsc
    rw [D.scMap_spec.2.2, D.scMap_spec.2.2] at hn
    apply hphi
    change phi A = phi B
    rw [← hμθ]
    exact congrArg mu hn
  let Hr := MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)
  let Hs := MonoidHom.eqLocus (s : Bs →* Bs) (MonoidHom.id Bs)
  let ar := fun b : ↥Hr => zetaVec (τ := Tag.E6) ζ0 hζ0
    (Multiplicative.toAdd (κ (b : Bs)))
  let as := fun b : ↥Hs => zetaVec (τ := Tag.E6) ζ0 hζ0
    (Multiplicative.toAdd (κ (b : Bs)))
  have hkr : famKernel (Set.range ar) = {α, -α} :=
    hκ.famKernel_ggHyperplane hpair.isRoot_fst hHr hζ0 hζ0o
  have hks : famKernel (Set.range as) = {γ, -γ} :=
    hκ.famKernel_ggHyperplane hpair.isRoot_snd hHs hζ0 hζ0o
  have ht (v : Fin Tag.E6.rank → ZMod 3) :
      ∃ k : ℕ, zetaVec (τ := Tag.E6) ζ0 hζ0 v ^ (3 ^ k) = 1 := by
    refine ⟨1, ?_⟩
    apply funext
    intro i
    simp only [Pi.pow_apply, Pi.one_apply, pow_one, zetaVec_apply]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ0, one_pow]
  obtain ⟨ρF, hFrob⟩ := frobeniusOnRoots_proved (langTag .twistedE6) GGL M.D
  letI : DistribMulAction (WeylGroup Tag.E6) (Fin Tag.E6.rank → ℤ) :=
    CFSG.LieType.Chevalley.instDistribMulActionWeylGroup
  let σroots : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ := fun i j =>
    w • chainRoot chain13 i j
  have hrev : ∀ i j : Fin 3, i ≠ j →
      ρF (σroots i j) = σroots j i := by
    intro i j hij
    dsimp only [σroots]
    rw [twisted_rho_neg_of_plus M Nat.prime_three (by decide) (by decide) hFrob
      (hframe.isRoot i j hij)]
    exact (hframe.neg i j).symm
  obtain ⟨hres0, hres1⟩ := twisted_donor_compact_blocks_eq_model_residuals M
    Nat.prime_three (by decide) (Or.inr (by decide)) w Ψ ρ hρ hframe theta hcanonical
      ρF hFrob hrev ar as (fun b => ht _) (fun b => ht _)
      (hwα.symm ▸ hkr) (hwγ.symm ▸ hks)
  have hNativeR :
      ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
        ⨅ b : ↥Hr, MonoidHom.eqLocus
          (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
          (MonoidHom.id stdGroup)) =
        (B12 (actualQuadraticSubfield 1) 2 1).map (isogenyStd.comp θ) := by
    apply Subgroup.map_injective hmu
    rw [hmarking r, Subgroup.map_map, hμθ]
    exact hres0
  have hNativeS :
      ggOTwoPrime ((⊤ : Subgroup stdGroup) ⊓
        ⨅ b : ↥Hs, MonoidHom.eqLocus
          (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker (b : Bs)).toMonoidHom
          (MonoidHom.id stdGroup)) =
        (B23 (actualQuadraticSubfield 1) 2 1).map (isogenyStd.comp θ) := by
    apply Subgroup.map_injective hmu
    rw [hmarking s, Subgroup.map_map, hμθ]
    exact hres1
  have hfixed : (D.joinedScMap.comp θ).range ≤ Subgroup.centralizer
      (((ggHyperplane Bs r ⊓ ggHyperplane Bs s).subgroupOf Bs).map D.joinedActor :
        Set D.joinedTwoQuotient) := by
    rintro y ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro a ⟨b, hb, rfl⟩
    let aB := zetaVec (τ := Tag.E6) ζ0 hζ0 (Multiplicative.toAdd (κ b))
    have haB : rootDiagUnit Tag.E6 aB ∈ e6IsogenyAlgebraic.range := by
      rw [range_e6IsogenyAlgebraic]
      exact CFSG.StandardType.ExcFrames.rootDiagUnit_mem_adjointGroup aB
    obtain ⟨d, hd⟩ := haB
    have hchar0 : rootChar aB (σroots 0 1) = 1 := by
      change rootChar aB (w • chainRoot chain13 0 1) = 1
      rw [hwα]
      apply (CFSG.StandardType.NoOffTwE6Three.rootChar_zetaVec_eq_one_iff
        hζ0o hζ0 (Multiplicative.toAdd (κ b)) α).2
      exact (hHr b).1 hb.1
    have hchar1 : rootChar aB (σroots 1 2) = 1 := by
      change rootChar aB (w • chainRoot chain13 1 2) = 1
      rw [hwγ]
      apply (CFSG.StandardType.NoOffTwE6Three.rootChar_zetaVec_eq_one_iff
        hζ0o hζ0 (Multiplicative.toAdd (κ b)) γ).2
      exact (hHs b).1 hb.2
    have hval : D.scAction b (θ A) = θ A :=
      qTwo_corrected_whole_donor_fixed_of_two_root_chars β (D.scAction b)
        (originalStdAction D.hK4 D.σ D.hσ D.hEN D.ψ D.hψ D.hker b)
        mu M.D.g0 hsource (D.scAction_spec b) aB (hact b)
        Ψ ρ σroots hρ hframe c d hc hd theta hmin hchar0 hchar1 A
    have hcomm := (D.joinedScMap_action b (θ A)).trans (congrArg D.joinedScMap hval)
    change D.joinedActor b * D.joinedScMap (θ A) =
      D.joinedScMap (θ A) * D.joinedActor b
    exact mul_inv_eq_iff_eq_mul.mp hcomm
  exact original_joined_compact_pair_of_native_markings_forall_fields D hBs θ hθQ
    hfixed hfree hNativeR hNativeS

@[expose] noncomputable def original_qTwo_cover_view
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn1 : D.lab.n = 1)
    (hmark1 : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X) :
    ExcTwE6CoverData hmark1 where
  hEN := D.hEN
  commH := D.commH
  K := D.K
  fieldK := D.fieldK
  finiteK := D.finiteK
  σ := D.σ
  hK4 := by simpa [hn1] using D.hK
  hσ := fun c => by simpa [hn1] using D.hσ c
  ψ := D.ψ
  hψ := D.hψ
  hker := D.hker
  hact := D.hact

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem original_qTwo_pair_forall_fields_of_same_cover
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn1 : D.lab.n = 1)
    (hmark1 : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X)
    (hBs : IsElemAbelian 3 Bs)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} :
    letI := D.fieldK
    letI := D.finiteK
    TwE6ToralCoords D.lab.n D.hEN D.ψ κ →
    ∀ (r s : MulAut Bs) (α γ : Fin Tag.E6.rank → ℤ),
      IsA2Pair α γ →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (original_qTwo_cover_view D hn1 hmark1).twoKernelInG ⊓ Subgroup.centralizer
        (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥ →
      ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
        Nat.card K = (2 ^ f) ^ 2 →
        Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
        ∃ W : Subgroup G, UnitaryBlockStandardPair K 2 f W
          (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  letI := D.fieldK
  letI := D.finiteK
  intro hκ r s α γ hpair hHr hHs hfree
  have hκ1 : TwE6ToralCoords 1 D.hEN D.ψ κ := by
    simpa only [hn1] using hκ
  exact original_qTwo_pair_forall_fields_of_corrected_a2_roots
    (original_qTwo_cover_view D hn1 hmark1) hBs hκ1 r s α γ hpair hHr hHs hfree


set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem original_qTwo_residuals_commute_of_orthogonal_roots
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {hmark : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X}
    (D : ExcTwE6CoverData hmark) (hBs : IsElemAbelian 3 Bs)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} :
    letI := D.fieldK
    letI := D.finiteK
    TwE6ToralCoords 1 D.hEN D.ψ κ →
    ∀ (r s : MulAut Bs) (α γ : Fin Tag.E6.rank → ℤ),
      IsRoot Tag.E6 α → IsRoot Tag.E6 γ →
      CFSG.LieType.Steinberg.Adjoint.iform (τ := .E6) α γ = 0 →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      D.twoKernelInG ⊓ Subgroup.centralizer
        (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥ →
      ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs s, a * b = b * a := by
  letI := D.fieldK
  letI := D.finiteK
  intro hκ r s α γ hα hγ horthRoots hHr hHs hfree
  obtain ⟨M, ζ0, hζ0, β, mu, hmu, hμΓ, hζ0o, hsource, hact, hmarking⟩ :=
    exists_original_qTwo_native_residual_square hκ D.hK4 D.hσ D.hψ D.hker
  let Hr := MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)
  let Hs := MonoidHom.eqLocus (s : Bs →* Bs) (MonoidHom.id Bs)
  let ar := fun b : ↥Hr => zetaVec (τ := Tag.E6) ζ0 hζ0 (Multiplicative.toAdd (κ (b : Bs)))
  let as := fun b : ↥Hs => zetaVec (τ := Tag.E6) ζ0 hζ0 (Multiplicative.toAdd (κ (b : Bs)))
  have hkr : famKernel (Set.range ar) = {α, -α} := hκ.famKernel_ggHyperplane hα hHr hζ0 hζ0o
  have hks : famKernel (Set.range as) = {γ, -γ} := hκ.famKernel_ggHyperplane hγ hHs hζ0 hζ0o
  have ht (v : Fin Tag.E6.rank → ZMod 3) :
      ∃ k : ℕ, zetaVec (τ := Tag.E6) ζ0 hζ0 v ^ (3 ^ k) = 1 := by
    refine ⟨1, ?_⟩
    apply funext
    intro i
    simp only [Pi.pow_apply, Pi.one_apply, pow_one, zetaVec_apply]
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ0, one_pow]
  have horth : ∀ u ∈ famKernel (Set.range ar), ∀ v ∈ famKernel (Set.range as),
      dotProduct u (Matrix.mulVec Tag.E6.symmetrizedCartan v) = 0 := by
    intro u hu v hv
    rw [hkr] at hu
    rw [hks] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · rw [hu, hv, dotProduct_mulVec_eq_iform]
      exact horthRoots
    · rw [hu, hv, dotProduct_mulVec_eq_iform,
        CFSG.LieType.Chevalley.iform_neg_right (τ := Tag.E6), horthRoots, neg_zero]
    · rw [hu, hv, dotProduct_mulVec_eq_iform,
        CFSG.LieType.Chevalley.iform_neg_left (τ := Tag.E6), horthRoots, neg_zero]
    · rw [hu, hv, dotProduct_mulVec_eq_iform,
        CFSG.LieType.Chevalley.iform_neg_left (τ := Tag.E6),
        CFSG.LieType.Chevalley.iform_neg_right (τ := Tag.E6), horthRoots, neg_zero, neg_zero]
  have hΓadj : M.D.Γ ≤ adjointGroup Tag.E6 GGL :=
    (Subgroup.commutator_le_self M.D.model).trans inf_le_left
  have hrescomm := ResidualA2Pair.commutation_of_orthogonal_families
    (Or.inr (Or.inl rfl)) Nat.prime_three (by decide) ar as
    (fun b => ht _) (fun b => ht _) M.D.Γ hΓadj horth
  apply original_residuals_commute_of_native D hBs r s hfree
  intro a ha c hc
  apply hmu
  rw [map_mul, map_mul]
  apply hrescomm
  · rw [← hmarking r]
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  · rw [← hmarking s]
    exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem original_qTwo_residuals_commute_of_same_cover
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn1 : D.lab.n = 1)
    (hmark1 : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs X)
    (hBs : IsElemAbelian 3 Bs)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} :
    letI := D.fieldK
    letI := D.finiteK
    TwE6ToralCoords D.lab.n D.hEN D.ψ κ →
    ∀ (r s : MulAut Bs) (α γ : Fin Tag.E6.rank → ℤ),
      IsRoot Tag.E6 α → IsRoot Tag.E6 γ →
      CFSG.LieType.Steinberg.Adjoint.iform (τ := .E6) α γ = 0 →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (γ j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (original_qTwo_cover_view D hn1 hmark1).twoKernelInG ⊓ Subgroup.centralizer
        (ggHyperplane Bs r ⊓ ggHyperplane Bs s : Set G) = ⊥ →
      ∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ ggRankOneIn X Bs s, a * b = b * a := by
  letI := D.fieldK
  letI := D.finiteK
  intro hκ r s α γ hα hγ horth hHr hHs hfree
  have hκ1 : TwE6ToralCoords 1 D.hEN D.ψ κ := by
    simpa only [hn1] using hκ
  exact original_qTwo_residuals_commute_of_orthogonal_roots
    (original_qTwo_cover_view D hn1 hmark1) hBs hκ1 r s α γ hα hγ horth hHr hHs hfree

end CFSG.StandardType.GGFinModel
