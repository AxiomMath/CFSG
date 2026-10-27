module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6Center

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {K : Type} [Field K]


theorem torus_commutator_mem_closure_odd_of_commute {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hbr : rootChar b e6HighestRoot = 1) {v : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hvt : v * t = t * v) {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hx : (x : ModGL TwistTag.E6.tag K) =
      rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ *
        (v : ModGL TwistTag.E6.tag K)⁻¹) :
    x ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} := by
  set h' : graphFixedRootGroup TwistTag.E6 K σ.toRingHom := ⟨_, hb⟩
  obtain ⟨hh, hho⟩ := torus_mem_oddCentralizer hf hK ht hb hbr
  have e : x = h' * (v * h'⁻¹ * v⁻¹) := by
    refine Subtype.ext ?_
    rw [hx]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h']
    group
  rw [e]
  exact mul_mem (subset_closure ⟨hh, hho⟩) (subset_closure (conj_inv_mem_oddCentralizer hh hho hvt))

theorem orbit_mem_closure_odd_of_torus {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (hαp : 0 < height α)
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hbC : rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hbr : rootChar b e6HighestRoot = 1) (hbα : rootChar b α ≠ 1)
    (hbρα : rootChar b (permLattice TwistTag.E6.perm α) ≠ 1)
    {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈
      rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
        twistedFixedGroup TwistTag.E6 K σ.toRingHom) :
    x ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} := by
  have hbO : ∀ β ∈ TwistTag.E6.diagramOrbit α, rootChar b β ≠ 1 := by
    intro β hβ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hβ
    rw [Finset.mem_range, show TwistTag.E6.order = 2 from rfl] at hk
    interval_cases k
    · exact hbα
    · rw [pow_one]
      exact hbρα
  have hOroot : ∀ β ∈ TwistTag.E6.diagramOrbit α, IsRoot TwistTag.E6.tag β ∧ 0 < height β :=
    fun β hβ => ⟨TwistTag.E6.isRoot_of_mem_diagramOrbit hα hβ,
      by rw [TwistTag.E6.height_of_mem_diagramOrbit hβ]; exact hαp⟩
  have hOcl : ∀ β ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      ∀ γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)), ∀ a c : ℕ,
        1 ≤ a → 1 ≤ c → IsRoot TwistTag.E6.tag (a • β + c • γ) →
          a • β + c • γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) :=
    fun β hβ γ hγ a c ha hc hr =>
      absurd hr (TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hα hβ hγ ha hc)
  set A := rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
    twistedFixedGroup TwistTag.E6 K σ.toRingHom with hA
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hbΓ : rootDiagUnit TwistTag.E6.tag b ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ hbC
  have hnorm : ∀ v ∈ A, rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ ∈
      A := by
    intro v hv
    obtain ⟨hvO, hvΓ⟩ := Subgroup.mem_inf.1 hv
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hbΓ hvΓ) (inv_mem hbΓ)⟩
    have hmap := map_rootSpan_of_forall
      (f := (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom)
      (S := (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)))
      fun β hβ => map_conj_rootDiagUnit_rootSubgroup b (hOroot β hβ).1
    rw [← hmap]
    exact ⟨v, hvO, rfl⟩
  have hfree : ∀ v ∈ A, rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      v → v = 1 := by
    intro v hv hfix
    have h1 := mem_rootSpan_of_rootDiagUnit_conj_eq (B := {b}) hOroot hOcl
      (Subgroup.mem_inf.1 hv).1 fun b' hb' => by
        rw [Set.mem_singleton_iff.1 hb']
        exact hfix
    have hempty : {β | β ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) ∧
        ∀ b' ∈ ({b} : Set (Fin TwistTag.E6.tag.rank → Kˣ)), rootChar b' β = 1} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun β hβ => hbO β hβ.1 (hβ.2 b rfl)
    rw [hempty] at h1
    have hbot : rootSpan TwistTag.E6.tag K (∅ : Set (Fin TwistTag.E6.tag.rank → ℤ)) = ⊥ :=
      iSup₂_eq_bot.2 fun β hβ => absurd hβ (Set.notMem_empty β)
    rw [hbot] at h1
    exact Subgroup.mem_bot.1 h1
  obtain ⟨v, hvA, hxv⟩ := exists_eq_mul_conj_inv_of_fixedPointFree hnorm hfree hx
  have hvU : v ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨rootSpan_mono (T := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β})
      (fun β hβ => hOroot β hβ) (Subgroup.mem_inf.1 hvA).1, (Subgroup.mem_inf.1 hvA).2⟩
  exact torus_commutator_mem_closure_odd hf hK ht hbC hbr hvU hxv

theorem twistedE6PairX_mem_closure_odd [CharP K 2] {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    (hσσ : ∀ x, σ.toRingHom (σ.toRingHom x) = x)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {δ : Fin TwistTag.E6.tag.rank → ℤ} (hδ : IsRoot TwistTag.E6.tag δ)
    (hρδ : permLattice TwistTag.E6.perm δ ≠ δ)
    (hδr : ¬IsRoot TwistTag.E6.tag (δ + e6HighestRoot)) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (hbr : rootChar b e6HighestRoot = 1) (hbδ : rootChar b δ ≠ 1)
    (hbρ : rootChar b (permLattice TwistTag.E6.perm δ) =
      Units.map σ.toRingHom.toMonoidHom (rootChar b δ)) (s : K) :
    (⟨twistedE6PairX σ.toRingHom δ s, twistedE6PairX_mem_graphFixedRootGroup hσσ hδ s⟩ :
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ∈
      closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
        c * t = t * c ∧ Odd (orderOf c)} := by
  obtain ⟨a, ha⟩ := exists_twistedE6PairX_eq_conj σ.toRingHom hδ hbδ hbρ s
  set v : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨twistedE6PairX σ.toRingHom δ a, twistedE6PairX_mem_graphFixedRootGroup hσσ hδ a⟩
  have hvt : v * t = t * v := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, ht, v]
    exact (commute_twistedE6PairX_e6HighestRoot σ.toRingHom hδ hρδ hδr a 1).eq
  exact torus_commutator_mem_closure_odd_of_commute hf hK ht hb hbr hvt ha

theorem fixedRoot_mem_closure_odd_of_torus [CharP K 2] {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K}
    (hσσ : ∀ x, σ.toRingHom (σ.toRingHom x) = x) {t₀ : K} (ht₀ : t₀ + σ.toRingHom t₀ = 1)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    (hT : ∀ δ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag δ →
      permLattice TwistTag.E6.perm δ ≠ δ → ∃ b : Fin TwistTag.E6.tag.rank → Kˣ,
        rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧
        rootChar b e6HighestRoot = 1 ∧ rootChar b δ ≠ 1 ∧
        rootChar b (permLattice TwistTag.E6.perm δ) ≠ 1 ∧
        rootChar b (permLattice TwistTag.E6.perm δ) =
          Units.map σ.toRingHom.toMonoidHom (rootChar b δ))
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (hγp : 0 < height γ)
    (hργ : permLattice TwistTag.E6.perm γ = γ)
    {x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hx : (x : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K {γ} ⊓
      twistedFixedGroup TwistTag.E6 K σ.toRingHom) :
    x ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨hxr, hxΓ⟩ := Subgroup.mem_inf.1 hx
  rw [CFSG.LieType.Chevalley.rootSpan_singleton] at hxr
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hxr
  have hF := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hxΓ).2
  rw [← hc, twistHom_pinnedX_eq_of_charTwo h2 _ hγ, hργ] at hF
  have hσc : σ.toRingHom c = c := pinnedX_injective _ _ _ hF
  obtain ⟨δ, ε, rfl, ⟨hδ, hρδ, hδr⟩, ⟨hε, hρε, hεr⟩, hne, h1, h2', h3, h4, h5, h6, h7⟩ :=
    exists_twistedE6TwoDecomp hγ hγp hργ
  have hcomm := commutator_twistedE6PairX σ.toRingHom hδ hε hγ hργ hne h1 h2' h3 h4 h5 h6 h7 1
    (c * t₀)
  have hval : 1 * (c * t₀) + σ.toRingHom (1 * (c * t₀)) = c := by
    rw [one_mul, map_mul, hσc, ← mul_add, ht₀, mul_one]
  rw [hval] at hcomm
  obtain ⟨bδ, hbδC, hbδr, hbδ, -, hbδρ⟩ := hT δ hδ hρδ
  obtain ⟨bε, hbεC, hbεr, hbε, -, hbερ⟩ := hT ε hε hρε
  have hy₁ := twistedE6PairX_mem_closure_odd hf hK hσσ ht hδ hρδ hδr hbδC hbδr hbδ hbδρ 1
  have hy₂ := twistedE6PairX_mem_closure_odd hf hK hσσ ht hε hρε hεr hbεC hbεr hbε hbερ (c * t₀)
  set y₁ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨twistedE6PairX σ.toRingHom δ 1, twistedE6PairX_mem_graphFixedRootGroup hσσ hδ 1⟩
  set y₂ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    ⟨twistedE6PairX σ.toRingHom ε (c * t₀), twistedE6PairX_mem_graphFixedRootGroup hσσ hε _⟩
  have e : x = ⁅y₁, y₂⁆ := by
    refine Subtype.ext ?_
    rw [← hc, ← hcomm, commutatorElement_def, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, y₁, y₂]
  rw [e, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hy₁ hy₂) (inv_mem hy₁)) (inv_mem hy₂)

theorem graphFixedPosUnipotent_le_closure_odd_of_torus [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    (hT : ∀ δ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag δ →
      permLattice TwistTag.E6.perm δ ≠ δ → ∃ b : Fin TwistTag.E6.tag.rank → Kˣ,
        rootDiagUnit TwistTag.E6.tag b ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧
        rootChar b e6HighestRoot = 1 ∧ rootChar b δ ≠ 1 ∧
        rootChar b (permLattice TwistTag.E6.perm δ) ≠ 1 ∧
        rootChar b (permLattice TwistTag.E6.perm δ) =
          Units.map σ.toRingHom.toMonoidHom (rootChar b δ))
    {u : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hu : (u : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom) :
    u ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} := by
  have hσ2 := twistedE6_sigma_pow_order hK hσ
  have hσσ : ∀ x, σ.toRingHom (σ.toRingHom x) = x := fun x => by
    have h := congrArg (fun g : K ≃+* K => g x) hσ2
    simpa [TwistTag.order, pow_two] using h
  obtain ⟨d₀, hd₀⟩ := exists_twistedE6_sigma_ne hf hK hσ
  have hτ : d₀ + σ.toRingHom d₀ ≠ 0 := by
    intro h
    apply hd₀
    have e : σ.toRingHom d₀ = -d₀ := by linear_combination h
    rw [show σ d₀ = σ.toRingHom d₀ from rfl, e, CharTwo.neg_eq]
  have hστ : σ.toRingHom (d₀ + σ.toRingHom d₀) = d₀ + σ.toRingHom d₀ := by
    rw [map_add, hσσ, add_comm]
  have ht₀ : d₀ * (d₀ + σ.toRingHom d₀)⁻¹ + σ.toRingHom (d₀ * (d₀ + σ.toRingHom d₀)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, hστ, ← add_mul, mul_inv_cancel₀ hτ]
  set S := {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom | c * t = t * c ∧ Odd (orderOf c)}
  obtain ⟨hposS, hposρ, hposcl⟩ := posRoots_twistedE6_facts
  obtain ⟨k, O, hO, hrange⟩ := exists_ordering_posOrbits TwistTag.E6
  have hbij := bijOn_prod_graphFixed (K := K) (σ := σ.toRingHom) σ.surjective hposS hposρ hposcl
    O hO hrange
  obtain ⟨w, -, hw⟩ := hbij.surjOn hu
  suffices h : (u : ModGL TwistTag.E6.tag K) ∈
      (closure S).map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype by
    obtain ⟨y, hy, hyu⟩ := h
    rwa [show u = y from Subtype.ext hyu.symm]
  rw [← hw]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  have hOj : O j ∈ TwistTag.E6.diagramRootOrbits ∧ (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆
      {α | IsRoot TwistTag.E6.tag α ∧ 0 < height α} := by
    have h : O j ∈ Set.range O := Set.mem_range_self j
    rw [hrange] at h
    exact h
  obtain ⟨hwO, hwΓ⟩ := Subgroup.mem_inf.1 (w j).2
  have hwU : (w j : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨rootSpan_mono hOj.2 hwO, hwΓ⟩
  refine ⟨⟨w j, graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hwU⟩, ?_, rfl⟩
  obtain ⟨α, hα, hαO⟩ := hOj.1
  have hαp : 0 < height α :=
    (hOj.2 (by rw [← hαO]; exact TwistTag.E6.self_mem_diagramOrbit α)).2
  by_cases hρα : permLattice TwistTag.E6.perm α = α
  ·
    have hO1 : O j = {α} := by rw [← hαO, diagramOrbit_eq_singleton_of_fixed hρα]
    refine fixedRoot_mem_closure_odd_of_torus hf hK hσσ ht₀ ht hT hα hαp hρα
      (Subgroup.mem_inf.2 ⟨?_, hwΓ⟩)
    have h : ∀ y : ModGL TwistTag.E6.tag K, y ∈ rootSpan TwistTag.E6.tag K (O j : Set _) →
        y ∈ rootSpan TwistTag.E6.tag K {α} := by
      intro y hy
      rwa [hO1, Finset.coe_singleton] at hy
    exact h _ hwO
  ·
    obtain ⟨b, hbC, hbr, hbα, hbρα, -⟩ := hT α hα hρα
    refine orbit_mem_closure_odd_of_torus hf hK ht hα hαp hbC hbr hbα hbρα
      (Subgroup.mem_inf.2 ⟨?_, hwΓ⟩)
    rw [hαO]
    exact hwO

theorem graphFixedPosUnipotent_le_closure_odd_two [CharP K 2] [Finite K] (hK : Nat.card K = 4)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2) {t : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (ht : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    {u : graphFixedRootGroup TwistTag.E6 K σ.toRingHom}
    (hu : (u : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ.toRingHom) :
    u ∈ closure {c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom |
      c * t = t * c ∧ Odd (orderOf c)} :=
  graphFixedPosUnipotent_le_closure_odd_of_torus (f := 1) le_rfl (by rw [hK]; norm_num)
    (fun c => by rw [hσ]; norm_num) ht (fun _ hδ hρδ => exists_twistedE6TorusTwo hK hσ hδ hρδ) hu

theorem innerCentralizerCriterion_twistedE6_longRoot' [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    InnerCentralizerCriterion (⟨pinnedX TwistTag.E6.tag K e6HighestRoot 1,
      pinnedX_e6HighestRoot_mem_graphFixedRootGroup σ.toRingHom 1 (map_one _)⟩ :
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact innerCentralizerCriterion_twistedE6_of_posUnipotent_le le_rfl hK hσ fun u hu =>
      graphFixedPosUnipotent_le_closure_odd_two (by rw [hK]; norm_num)
        (fun c => by rw [hσ]; norm_num) (by rfl) hu
  · exact innerCentralizerCriterion_twistedE6_longRoot h hK hσ

end CFSG.SeitzReduction
