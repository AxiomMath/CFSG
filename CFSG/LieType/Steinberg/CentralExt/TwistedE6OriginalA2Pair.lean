module
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6OriginalResidualCommutation
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoReflectionFrame
public import CFSG.LieType.Chevalley.WeylRoots
public noncomputable section
namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TableBExc.E6Three CFSG.RankThree.PartOne.KE8F
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.ClassicalInvolution.Phan
  CFSG.HardMathSupport.Timmesfeld.LangTorus
set_option allowUnsafeReducibility true in
attribute [local reducible] TwistTag.tag langTag Tag.rank

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem TwE6CoverData.original_pair_forall_fields_of_a2_roots
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} :
    letI := D.fieldK
    letI := D.finiteK
    letI : NeZero D.lab.n := ⟨by omega⟩
    TwE6ToralCoords D.lab.n D.hEN D.ψ κ →
    ∀ (r s : MulAut Bs) (α β : Fin Tag.E6.rank → ℤ),
      IsA2Pair α β →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      ∃ θG : Su (actualQuadraticSubfield D.lab.n) 2 D.lab.n 3 →* G,
        Function.Injective θG ∧ θG.range ≤ X ∧
        (B12 (actualQuadraticSubfield D.lab.n) 2 D.lab.n).map θG = ggRankOneIn X Bs r ∧
        (B23 (actualQuadraticSubfield D.lab.n) 2 D.lab.n).map θG = ggRankOneIn X Bs s ∧
        ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ),
          Nat.card K = (2 ^ f) ^ 2 →
          Nat.card (ggRankOneIn X Bs r) = 2 ^ f * ((2 ^ f) ^ 2 - 1) →
          UnitaryBlockStandardPair K 2 f θG.range
            (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) := by
  letI := D.fieldK
  letI := D.finiteK
  letI : NeZero D.lab.n := ⟨by omega⟩
  intro hκ r s α β hpair hHr hHs
  obtain ⟨ι, e, g, M, ζ0, hζ0, he, hMg, hMw, hζ0o, mu, hmu, hμΓ, hact, hmark⟩ :=
    hκ.exists_original_field_lang_residual_square D.hn D.hK D.h3 D.hσ D.hψ
      (le_of_eq D.hker) (D.psi_odd_kernel hn3)
  obtain ⟨η, T, hη, hminT, hT⟩ := D.exists_original_recipe_source_square hn3 ι
  obtain ⟨w, Ψ, ρ, c, theta, hρ, hframe, hwα, hwβ, hinj, hc, hmin, hcanonical,
      hphi, hΓ, hwhole, hB0, hB1, hfields⟩ :=
    exists_twisted_originalU_model_marked_pair_at_a2_pair (n := 0) M
      Nat.prime_three (by decide) D.h3 (Or.inr D.h3) hpair
  let phi := (MulAut.conj M.D.g0).symm.toMonoidHom.comp
    ((ggIotaK .twistedE6 0 D.lab.n D.hn).comp theta)
  let θX : Su (actualQuadraticSubfield D.lab.n) 2 D.lab.n 3 →* ↥X :=
    (D.scMap hn3).comp (T.toMonoidHom.comp theta)
  have hμθ : mu.comp θX = phi := by
    apply MonoidHom.ext
    intro u
    rw [hmu]
    change (MulAut.conj M.D.g0).symm
      (baseChangeGL (e.comp (algebraMap D.K (AlgebraicClosure D.K)))
        ((D.ψ (D.scMap hn3 (T (theta u))) : twistedE6RootGroup D.K D.σ) :
          ModGL Tag.E6 D.K)) = _
    rw [he, hT]
    rfl
  have hθX : Function.Injective θX := by
    intro u v huv
    apply hphi
    change phi u = phi v
    rw [← hμθ]
    exact congrArg mu huv
  have hμker : mu.ker = D.ψ.ker := by
    rw [hmu, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj M.D.g0).symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (baseChangeGL_injective _),
      MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _)]
  let Hr := MonoidHom.eqLocus (r : Bs →* Bs) (MonoidHom.id Bs)
  let Hs := MonoidHom.eqLocus (s : Bs →* Bs) (MonoidHom.id Bs)
  let ar := fun b : ↥Hr => zetaVec (τ := Tag.E6) ζ0 hζ0
    (Multiplicative.toAdd (κ (b : Bs)))
  let as := fun b : ↥Hs => zetaVec (τ := Tag.E6) ζ0 hζ0
    (Multiplicative.toAdd (κ (b : Bs)))
  have hkr : famKernel (Set.range ar) = {α, -α} :=
    hκ.famKernel_ggHyperplane hpair.isRoot_fst hHr hζ0 hζ0o
  have hks : famKernel (Set.range as) = {β, -β} :=
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
    w • CFSG.RankThree.E6.chainRoot (τ := Tag.E6) CFSG.RankThree.E6.chain13 i j
  have hrev : ∀ i j : Fin 3, i ≠ j →
      ρF (σroots i j) = σroots j i := by
    intro i j hij
    dsimp only [σroots]
    rw [twisted_rho_neg_of_plus M Nat.prime_three (by decide) D.h3 hFrob
      (hframe.isRoot i j hij)]
    exact (hframe.neg i j).symm
  obtain ⟨hres0, hres1⟩ := twisted_donor_compact_blocks_eq_model_residuals M
    Nat.prime_three (by decide) (Or.inr D.h3) w Ψ ρ hρ hframe theta hcanonical
      ρF hFrob hrev ar as (fun b => ht _) (fun b => ht _)
      (hwα.symm ▸ hkr) (hwβ.symm ▸ hks)
  have hidem (Y : Subgroup (ModGL Tag.E6 GGL)) : ggOTwoPrime (ggOTwoPrime Y) = ggOTwoPrime Y := by
    apply le_antisymm (ggOTwoPrime_le _)
    rw [ggOTwoPrime, Subgroup.closure_le]
    intro y hy
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hy, hy.2⟩
  have hgenerated (C : Subgroup (Su (actualQuadraticSubfield D.lab.n) 2 D.lab.n 3))
      (Y : Subgroup (ModGL Tag.E6 GGL)) (hCY : ggOTwoPrime Y = C.map phi) :
      ggOTwoPrime (C.map θX) = C.map θX := by
    rw [← ggOTwoPrime_map_of_injective θX hθX]
    congr 1
    apply Subgroup.map_injective (f := phi) hphi
    rw [ggOTwoPrime_map_of_injective phi hphi, ← hCY, hidem]
  have hR (t : MulAut Bs) : (ggRankOneIn X Bs t).subgroupOf X =
      ggOTwoPrime ((X ⊓ Subgroup.centralizer (ggHyperplane Bs t : Set G)).subgroupOf X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le
        (show ggRankOneIn X Bs t ≤ X from (ggOTwoPrime_le _).trans inf_le_left),
      ggOTwoPrime_map_of_injective X.subtype X.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rfl
  have hmarked (t : MulAut Bs)
      (C : Subgroup (Su (actualQuadraticSubfield D.lab.n) 2 D.lab.n 3))
      (Y : Subgroup (ModGL Tag.E6 GGL)) (hCY : ggOTwoPrime Y = C.map phi)
      (hY : ((ggRankOneIn X Bs t).subgroupOf X).map mu = ggOTwoPrime Y) :
      (ggRankOneIn X Bs t).subgroupOf X = C.map θX := by
    rw [hR]
    apply ggOTwoPrime_eq_of_map_eq_of_central_odd_kernel mu
      (hμker.symm ▸ le_of_eq D.hker) (hμker.symm ▸ D.psi_odd_kernel hn3)
      _ _ (hgenerated C Y hCY)
    rw [← hR, hY, hCY, Subgroup.map_map, hμθ]
  have hmark0 := hmarked r (B12 (actualQuadraticSubfield D.lab.n) 2 D.lab.n)
    _ hres0 (hmark r)
  have hmark1 := hmarked s (B23 (actualQuadraticSubfield D.lab.n) 2 D.lab.n)
    _ hres1 (hmark s)
  let θG := X.subtype.comp θX
  have hθG : Function.Injective θG := X.subtype_injective.comp hθX
  have hmarkG0 : (B12 (actualQuadraticSubfield D.lab.n) 2 D.lab.n).map θG = ggRankOneIn X Bs r := by
    rw [← Subgroup.map_map, ← hmark0, Subgroup.map_subgroupOf_eq_of_le
      (show ggRankOneIn X Bs r ≤ X from (ggOTwoPrime_le _).trans inf_le_left)]
  have hmarkG1 : (B23 (actualQuadraticSubfield D.lab.n) 2 D.lab.n).map θG = ggRankOneIn X Bs s := by
    rw [← Subgroup.map_map, ← hmark1, Subgroup.map_subgroupOf_eq_of_le
      (show ggRankOneIn X Bs s ≤ X from (ggOTwoPrime_le _).trans inf_le_left)]
  have hkerG : θG.ker ≤ Subgroup.center (Su (actualQuadraticSubfield D.lab.n) 2 D.lab.n 3) := by
    rw [(MonoidHom.ker_eq_bot_iff θG).mpr hθG]
    exact bot_le
  have hstd : UnitaryBlockStandardPair (actualQuadraticSubfield D.lab.n) 2 D.lab.n
      θG.range (ggRankOneIn X Bs r) (ggRankOneIn X Bs s) :=
    CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hkerG hmarkG0 hmarkG1
  refine ⟨θG, hθG, ?_, hmarkG0, hmarkG1, ?_⟩
  · rintro z ⟨u, rfl⟩
    exact (θX u).2
  · intro K _ _ _ f hK hR
    exact ggPhanNSAPairAux_stdPair_of_card (card_actualQuadraticSubfield D.hn) hK hstd hR

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
theorem TwE6CoverData.original_pair_concl_of_root_positions
    {G : Type} [Group G] [Finite G] {X Bs : Subgroup G} [Fact (IsElemAbelian 3 Bs)]
    {S : ℕ → LargeEvenLabel → Prop}
    {hS : ∀ lab, S 3 lab → lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1}
    {hmark : GGInnerDiagOnLabel S 3 Bs X}
    (D : TwE6CoverData hS hmark) (hn3 : 3 ≤ D.lab.n)
    {κ : ↥Bs →* Multiplicative (Fin 6 → ZMod 3)} :
    letI := D.fieldK
    letI := D.finiteK
    TwE6ToralCoords D.lab.n D.hEN D.ψ κ → GGNoTransvection 3 Bs →
    ∀ (r s : MulAut Bs), r ∈ ggAutomizer X Bs → GGIsReflection 3 r →
      s ∈ ggAutomizer X Bs → GGIsReflection 3 s →
    ∀ (α β : Fin Tag.E6.rank → ℤ),
      IsRoot Tag.E6 α → IsRoot Tag.E6 β → α ≠ β → α ≠ -β →
      (∀ b : ↥Bs, Multiplicative.toAdd (κ (r b)) =
        ExcSplitRootGen.excRefl (τ := .E6) (p := 3) α (Multiplicative.toAdd (κ b))) →
      (∀ b : ↥Bs, Multiplicative.toAdd (κ (s b)) =
        ExcSplitRootGen.excRefl (τ := .E6) (p := 3) β (Multiplicative.toAdd (κ b))) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs r ↔
        ∑ j, (α j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      (∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (β j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0) →
      GGPairConcl Bs X r s := by
  letI := D.fieldK
  letI := D.finiteK
  intro hκ hNT r s hrA hr hsA hs α β hα hβ hne hneg hra hsb hHr hHs
  constructor
  · intro hcomm
    exact D.original_residuals_commute hn3 hκ r s α β hα hβ hne hneg hra hsb hHr hHs hcomm
  · intro hnot K _ _ _ f hK hR
    obtain ⟨β', hβ', hpair⟩ := hκ.exists_isA2Pair_of_not_commute hNT hrA hr hsA hs hα hβ hra hsb hnot
    have hHs' : ∀ b : ↥Bs, (b : G) ∈ ggHyperplane Bs s ↔
        ∑ j, (β' j : ZMod 3) * Multiplicative.toAdd (κ b) j = 0 := by
      rcases hβ' with rfl | rfl
      · exact hHs
      · intro b
        rw [hHs b]
        simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_eq_zero]
    obtain ⟨θG, _, _, _, _, hfields⟩ :=
      D.original_pair_forall_fields_of_a2_roots hn3 hκ r s α β' hpair hHr hHs'
    exact ⟨θG.range, hfields K f hK hR⟩

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover
