module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Reduce
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusLang
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusStab
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Inner
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang
import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgebraicZMod
public import CFSG.HardMathSupport.Lang.TwE6Step3.FixedSplit
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
open CFSG.RankThree.PartOne.KE (d4Nodes)

set_option linter.unusedSectionVars false

section Main


theorem d4t2tm_lang_torus {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L} {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (v w : WeylGroup Tag.E6)
    (θ : ModGL Tag.E6 L →* ModGL Tag.E6 L)
    (hθ : ∀ b : Fin Tag.E6.rank → Lˣ,
      θ (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 (d4t2tlTuple Fr w b))
    {U : Subgroup (ModGL Tag.E6 L)}
    (hU : U = rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)))
    (hθU : ∀ u ∈ U, θ u ∈ U) :
    ∀ s ∈ torusGroup Tag.E6 L ⊓ U, ∃ t ∈ torusGroup Tag.E6 L ⊓ U, t⁻¹ * θ t = s := by
  subst hU
  have hθH : ∀ h ∈ torusGroup Tag.E6 L, θ h ∈ torusGroup Tag.E6 L := by
    intro h hh
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    rw [hθ b]
    exact rootDiagUnit_mem_torusGroup _
  have hcomm : ∀ x ∈ torusGroup Tag.E6 L ⊓
      rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)),
      ∀ y ∈ torusGroup Tag.E6 L ⊓
        rootSpan Tag.E6 L ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx.1
    exact rootDiagUnit_mul_comm_of_mem_torusGroup a hy.1
  have hk : 0 < Nat.card (WeylGroup Tag.E6) := Nat.card_pos
  have hqk : 2 ≤ q ^ (2 * Nat.card (WeylGroup Tag.E6)) :=
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (2 * Nat.card (WeylGroup Tag.E6)) := Nat.pow_le_pow_right (by omega) (by omega)
  refine d4t2tl_lang_of_pow θ hcomm (fun x hx => ⟨hθH x hx.1, hθU x hx.2⟩)
    (k := 2 * Nat.card (WeylGroup Tag.E6))
    (N := q ^ (2 * Nat.card (WeylGroup Tag.E6)) - 1) ?_
    (d4t2tl_div_torus_inf_rootSpan v (by omega))
  intro x hx
  rw [d4t2tl_iterate_torus hFr w θ hθ hx.1]
  congr 1
  omega

theorem d4t2tm_class {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus)
    (hap : ∀ i, a i ^ 3 = 1) (hall : (kernelRoots (rootCharHom a)).ncard = 24) :
    ∃ (i : KernelComponent (rootCharHom a)) (v : WeylGroup .E6),
      kernelRoots (rootCharHom a) = componentRoots (rootCharHom a) i ∧
      componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots .E6 (d4Nodes .E6) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  classical
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => hγ.1
  obtain ⟨α, hα⟩ : (kernelRoots (rootCharHom a)).Nonempty := by
    rw [← Set.ncard_pos hfin, hall]
    norm_num
  let i : KernelComponent (rootCharHom a) := ⟦⟨α, hα⟩⟧
  obtain ⟨hr, hc⟩ := d4t2_class_of_card h3 hap hall i
  have hsub : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) :=
    fun γ hγ => hγ.1
  have hker : kernelRoots (rootCharHom a) = componentRoots (rootCharHom a) i :=
    (Set.eq_of_subset_of_ncard_le hsub (hall.trans hc.symm).le hfin).symm
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      (rootDiagUnitHom Tag.E6 L).map_pow a 3
    have h2 : a ^ 3 = 1 := funext fun j => by rw [Pi.pow_apply, hap j, Pi.one_apply]
    rw [← h1, h2, CFSG.LieType.Chevalley.rootDiagUnit_one]
  obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime Nat.prime_three h3 facts_E6 kacCount_E6_four
    (by decide) (by decide)
    (fun y hy => far_d4_E6 y fun z hz => by
      have h := hy z hz
      rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
    ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
  exact ⟨i, v, hker, hv, hρ⟩

theorem d4t2tm_datum {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 L t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 L t h)⁻¹)
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hq : S.D.q = ℓ ^ f) :
    S.D.Φ = twistHom TwistTag.E6 L (iterateFrobenius L ℓ f) ∧
      ∀ c, iterateFrobenius L ℓ f c = c ^ S.D.q := by
  obtain ⟨t, ht, Fr, hFr, hΦ⟩ := hS
  cases t with
  | D4 => exact absurd ht (by decide)
  | E6 =>
  have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹ := hΦ
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  subst hFr'
  refine ⟨?_, hFr⟩
  ext g
  rw [hΦ' g]
  rfl

theorem d4t2TorusPart_of_spinPerfect
    (hperf : D4T2FixedSpinPerfect) : D4T2TorusPart := by
  intro L _ _ p₀ S hS hAlg l f hl hf hq hl3 h3 h3q a hT hap hall F₀ hF₀mod hF₀M hab hcard hdF
  classical
  obtain ⟨hch, halg⟩ := S.exists_charP_isAlgebraic_zmod hAlg hl hf hq
  haveI := hch
  haveI : Fact l.Prime := ⟨hl⟩
  have hd1 : rootDiagUnit .E6 a ≠ 1 := d4t2_rootDiagUnit_ne_one hall
  obtain ⟨g₁, hg₁, hg₁T⟩ := d4t2_plane_toral hl3 halg hd1 hF₀M hab hcard hdF
  obtain ⟨hΦtw, hFr⟩ := d4t2tm_datum S hS hq
  obtain ⟨Fr, hFrdef⟩ : ∃ Fr : L →+* L, Fr = iterateFrobenius L l f := ⟨_, rfl⟩
  rw [← hFrdef] at hΦtw hFr
  have hfix : ∀ x ∈ F₀, S.D.n * S.D.Φ x * S.D.n⁻¹ = x := fun x hx =>
    (S.D.mem_model.1 (hF₀mod hx)).2
  obtain ⟨y, w', hyC, hyn, hyT⟩ := d4t2ts_stable_torus_E6 f hf (Φ := S.D.Φ)
    (by rw [hΦtw, hFrdef]) S.D.g0_mem S.D.lang hfix hdF hg₁ hg₁T
  obtain ⟨θ, hθdef⟩ : ∃ θ : ModGL Tag.E6 L →* ModGL Tag.E6 L,
      θ = twFrob TwistTag.E6 (canonicalRep (coxeterSystem Tag.E6) L w') Fr := ⟨_, rfl⟩
  have hθapp : ∀ x, θ x = canonicalRep (coxeterSystem Tag.E6) L w' * S.D.Φ x *
      (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ := by
    intro x
    rw [hθdef, hΦtw]
    rfl
  have hθtuple : ∀ b : Fin Tag.E6.rank → Lˣ,
      θ (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 (d4t2tlTuple Fr w' b) := by
    intro b
    rw [hθdef]
    exact d4t2tl_twFrob_tuple Fr w' b
  have hstepconj : ∀ x : ModGL Tag.E6 L, S.D.step (y * x * y⁻¹) = y * θ x * y⁻¹ := by
    intro x
    have h1 : S.D.step (y * x * y⁻¹) =
        S.D.n * (S.D.Φ y * S.D.Φ x * (S.D.Φ y)⁻¹) * S.D.n⁻¹ := by
      change S.D.n * S.D.Φ (y * x * y⁻¹) * S.D.n⁻¹ = _
      rw [map_mul, map_mul, map_inv]
    rw [h1, hθapp x]
    calc S.D.n * (S.D.Φ y * S.D.Φ x * (S.D.Φ y)⁻¹) * S.D.n⁻¹
        = (S.D.n * S.D.Φ y) * S.D.Φ x * (S.D.n * S.D.Φ y)⁻¹ := by group
      _ = (y * canonicalRep (coxeterSystem Tag.E6) L w') * S.D.Φ x *
          (y * canonicalRep (coxeterSystem Tag.E6) L w')⁻¹ := by rw [hyn]
      _ = y * (canonicalRep (coxeterSystem Tag.E6) L w' * S.D.Φ x *
          (canonicalRep (coxeterSystem Tag.E6) L w')⁻¹) * y⁻¹ := by group
  obtain ⟨i, v, hker, hv, hρ⟩ := d4t2tm_class S h3 hT hap hall
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup (ModGL Tag.E6 L),
      U = rootSpan Tag.E6 L (componentRoots (rootCharHom a) i) := ⟨_, rfl⟩
  have hUker : rootSpan Tag.E6 L (rootCharKernel a) = U := by
    rw [hUdef, ← hker]
    rfl
  have hyN : ∀ z, z ∈ U ↔ y * z * y⁻¹ ∈ U := fun z => by
    have h := Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer_rootSpan a hyC) z
    rwa [hUker] at h
  have hyN' : ∀ z, z ∈ U ↔ y⁻¹ * z * y ∈ U := fun z => by
    have h := Subgroup.mem_normalizer_iff.1
      (toralCentralizer_le_normalizer_rootSpan a (inv_mem hyC)) z
    rwa [hUker, inv_inv] at h
  have hstepU : ∀ u ∈ U, S.D.step u ∈ U := fun u hu => by
    rw [hUdef] at hu ⊢
    exact step_mem_rootSpan S (T := componentRoots (rootCharHom a) i) (fun γ hγ => hγ.1.1) hρ hu
  have hθU : ∀ u ∈ U, θ u ∈ U := by
    intro u hu
    have h2 := hstepU _ ((hyN u).1 hu)
    rw [hstepconj u] at h2
    exact (hyN (θ u)).2 h2
  have hq2 : 2 ≤ S.D.q := S.hqpow.1.one_lt
  have hlangHU := d4t2tm_lang_torus hq2 hFr v w' θ hθtuple (U := U)
    (by rw [hUdef, hv]) hθU
  have hHcomm : ∀ x ∈ torusGroup Tag.E6 L, ∀ z ∈ torusGroup Tag.E6 L, x * z = z * x := by
    intro x hx z hz
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
    exact rootDiagUnit_mul_comm_of_mem_torusGroup b hz
  have hHQ : torusGroup Tag.E6 L ≤ Subgroup.normalizer (U : Set (ModGL Tag.E6 L)) := by
    rw [hUdef]
    exact CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan
      (S := componentRoots (rootCharHom a) i) (fun γ hγ => hγ.1.1)
  have hθH : ∀ h ∈ torusGroup Tag.E6 L, θ h ∈ torusGroup Tag.E6 L := by
    intro h hh
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
    rw [hθtuple b]
    exact rootDiagUnit_mem_torusGroup _
  have hPperf : ⁅U ⊓ S.D.model, U ⊓ S.D.model⁆ = U ⊓ S.D.model := by
    by_cases hin : twistInner (kernelRoots (rootCharHom a))
        (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))
    · have h := hperf S hS hAlg hl hf hq hl3 h3 h3q hT hap hall hin
      rw [hker, ← hUdef] at h
      exact h
    · have hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
          (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) := by
        rwa [← hker]
      have hqs := d4t2out_rootSpan_model_quasisimple S hS (by omega) hq h3q hT hap i v hv
        hker.le hρ hnin
      rw [hUdef]
      exact Subgroup.isPerfect_iff.1 hqs.1.1
  have hPΓ : U ⊓ S.D.model ≤ S.Γ :=
    calc U ⊓ S.D.model = ⁅U ⊓ S.D.model, U ⊓ S.D.model⁆ := hPperf.symm
      _ ≤ ⁅S.D.model, S.D.model⁆ := Subgroup.commutator_mono inf_le_right inf_le_right
  have hPC : U ⊓ S.D.model ≤ Subgroup.centralizer {rootDiagUnit .E6 a} := fun x hx => by
    have h : x ∈ toralCentralizer .E6 L a :=
      rootSpan_rootCharKernel_le_toralCentralizer a (by rw [hUker]; exact hx.1)
    exact (Subgroup.mem_inf.1 h).2
  have hTame := langSetup_hTame_of_prime S Nat.prime_three h3 (fun h => absurd h (by decide))
    hT hap hd1
  have hPcomp : U ⊓ S.D.model ≤
      sSup {J | CFSG.Open.IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 a})} := by
    refine (perfect_le_iSup_rationalComponent_of_prime S Nat.prime_three hT hap hd1 hTame
      (U ⊓ S.D.model) (le_inf hPΓ hPC) hPperf).trans (iSup_le fun j => ?_)
    exact le_sSup (isComponentOf_rationalComponent S hT j.1 j.2)
  intro x hx
  obtain ⟨hxΓC, hxM⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxΓ, -⟩ := Subgroup.mem_inf.1 hxΓC
  have hxmodel : x ∈ S.D.model := S.Γ_le_model hxΓ
  have hxstep : S.D.step x = x := (S.D.mem_model.1 hxmodel).2
  have hx'M : y⁻¹ * x * y ∈ toralRootGroup .E6 L a := by
    have h := (Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a (inv_mem hyC)) x).1
      hxM
    rwa [inv_inv] at h
  have hm : y⁻¹ * x * y ∈ torusGroup Tag.E6 L ⊔ U := by
    rw [← hUker]
    exact hx'M
  have hθx : θ (y⁻¹ * x * y) = y⁻¹ * x * y := by
    have h := hstepconj (y⁻¹ * x * y)
    rw [show y * (y⁻¹ * x * y) * y⁻¹ = x by group, hxstep] at h
    calc θ (y⁻¹ * x * y) = y⁻¹ * (y * θ (y⁻¹ * x * y) * y⁻¹) * y := by group
      _ = y⁻¹ * x * y := by rw [← h]
  obtain ⟨t, htH, -, u, huU, huθ, hxtu⟩ :=
    exists_fixed_split θ hHcomm hHQ hθH hθU hlangHU hm hθx
  obtain ⟨t₁, ht₁def⟩ : ∃ t₁ : ModGL Tag.E6 L, t₁ = y * t * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨u₁, hu₁def⟩ : ∃ u₁ : ModGL Tag.E6 L, u₁ = y * u * y⁻¹ := ⟨_, rfl⟩
  have hxe : x = t₁ * u₁ := by
    calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
      _ = y * (t * u) * y⁻¹ := by rw [hxtu]
      _ = t₁ * u₁ := by rw [ht₁def, hu₁def]; group
  have hu₁U : u₁ ∈ U := by
    rw [hu₁def]
    exact (hyN u).1 huU
  have hu₁fix : S.D.step u₁ = u₁ := by
    rw [hu₁def, hstepconj u, huθ]
  have hu₁P : u₁ ∈ U ⊓ S.D.model := by
    refine Subgroup.mem_inf.2 ⟨hu₁U, S.D.mem_model.2 ⟨?_, hu₁fix⟩⟩
    rw [hUdef] at hu₁U
    exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _ hu₁U
  have ht₁Γ : t₁ ∈ S.Γ := by
    have h : t₁ = x * u₁⁻¹ := by rw [hxe]; group
    rw [h]
    exact mul_mem hxΓ (inv_mem (hPΓ hu₁P))
  have ht₁C : t₁ ∈ Subgroup.centralizer (F₀ : Set (ModGL Tag.E6 L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := hHcomm _ (hyT g hg) t htH
    rw [ht₁def]
    calc g * (y * t * y⁻¹) = y * ((y⁻¹ * g * y) * t) * y⁻¹ := by group
      _ = y * (t * (y⁻¹ * g * y)) * y⁻¹ := by rw [h1]
      _ = y * t * y⁻¹ * g := by group
  rw [hxe]
  exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨ht₁Γ, ht₁C⟩))
    (Subgroup.mem_sup_left (hPcomp hu₁P))

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
