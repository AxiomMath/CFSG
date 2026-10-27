module

public import CFSG.HardMathSupport.Lang.Triality.HeightCoord
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable (t : TwistTag) {K : Type} [Field K] [Finite K] (σ : K →+* K)

@[expose] def layerSub (k : ℕ) : Subgroup ↥(graphFixedRootGroup t K σ) :=
  (heightSeries t.tag K (k : ℤ)).comap (graphFixedRootGroup t K σ).subtype

theorem mem_layerSub {k : ℕ} {x : ↥(graphFixedRootGroup t K σ)} :
    x ∈ layerSub t σ k ↔ (x : ModGL t.tag K) ∈ heightSeries t.tag K (k : ℤ) := Iff.rfl

@[expose] def rootsAt (h : ℤ) : Set (Fin t.tag.rank → ℤ) := {α | IsRoot t.tag α ∧ height α = h}

theorem finite_rootsAt (h : ℤ) : (rootsAt t h).Finite :=
  (finite_setOf_isRoot t.tag).subset fun _ hα => hα.1

open Classical in
@[expose] noncomputable def orbitsAt (h : ℤ) : Finset (Finset (Fin t.tag.rank → ℤ)) :=
  (finite_rootsAt t h).toFinset.image t.diagramOrbit

theorem mem_orbitsAt {h : ℤ} {O : Finset (Fin t.tag.rank → ℤ)} :
    O ∈ orbitsAt t h ↔ ∃ α, IsRoot t.tag α ∧ height α = h ∧ t.diagramOrbit α = O := by
  classical
  simp only [orbitsAt, Finset.mem_image, Set.Finite.mem_toFinset]
  exact ⟨fun ⟨α, hα, h⟩ => ⟨α, hα.1, hα.2, h⟩, fun ⟨α, h1, h2, h⟩ => ⟨α, ⟨h1, h2⟩, h⟩⟩

@[expose] noncomputable def repOf (h : ℤ) (O : ↥(orbitsAt t h)) : Fin t.tag.rank → ℤ :=
  Classical.choose ((mem_orbitsAt t).1 O.2)

theorem repOf_spec (h : ℤ) (O : ↥(orbitsAt t h)) :
    IsRoot t.tag (repOf t h O) ∧ height (repOf t h O) = h ∧
      t.diagramOrbit (repOf t h O) = O.1 :=
  Classical.choose_spec ((mem_orbitsAt t).1 O.2)

@[expose] noncomputable def layerCoord (h : ℤ) (hh : 0 < h) (x : ModGL t.tag K) : ↥(orbitsAt t h) → K :=
  fun O => rootCoord (α := repOf t h O)
    ⟨(repOf_spec t h O).1, by rw [(repOf_spec t h O).2.1]; exact hh⟩ x

theorem mem_heightSeries_of_height_eq {α : Fin t.tag.rank → ℤ} {h : ℤ} (hα : height α = h)
    {x : ModGL t.tag K} (hx : x ∈ heightSeries t.tag K h) : x ∈ heightSeries t.tag K (height α) :=
  hα ▸ hx

@[expose] noncomputable def layerHom (h : ℕ) (hh : 0 < (h : ℤ)) :
    ↥(layerSub t σ h) →* Multiplicative (↥(orbitsAt t (h : ℤ)) → K) where
  toFun x := Multiplicative.ofAdd (layerCoord t (h : ℤ) hh ((x.1 : ↥(graphFixedRootGroup t K σ)) :
    ModGL t.tag K))
  map_one' := by
    refine congrArg Multiplicative.ofAdd (funext fun O => ?_)
    exact rootCoord_one _
  map_mul' x y := by
    refine congrArg Multiplicative.ofAdd (funext fun O => ?_)
    have hx := mem_heightSeries_of_height_eq t (repOf_spec t (h : ℤ) O).2.1 x.2
    have hy := mem_heightSeries_of_height_eq t (repOf_spec t (h : ℤ) O).2.1 y.2
    exact rootCoord_mul _ hx hy

theorem permLattice_pow_succ (π : Equiv.Perm (Fin t.tag.rank)) (k : ℕ)
    (v : Fin t.tag.rank → ℤ) :
    permLattice (π ^ (k + 1)) v = permLattice π (permLattice (π ^ k) v) := by
  funext i
  have : (π ^ (k + 1)).symm i = (π ^ k).symm (π.symm i) := by
    rw [pow_succ', ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.Perm.inv_def]
  simp [permLattice, this]

theorem rootCoord_congr {x : ModGL t.tag K} {α α' : Fin t.tag.rank → ℤ} (h : α = α')
    (hα : IsRoot t.tag α ∧ 0 < height α) (hα' : IsRoot t.tag α' ∧ 0 < height α') :
    rootCoord hα x = rootCoord hα' x := by
  subst h
  rfl

theorem rootCoord_perm_eq_zero {x : ModGL t.tag K} (hxΓ : x ∈ twistedFixedGroup t K σ)
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β ∧ 0 < height β)
    (hβ' : IsRoot t.tag (permLattice t.perm β) ∧ 0 < height (permLattice t.perm β))
    (hx : x ∈ heightSeries t.tag K (height β)) (h0 : rootCoord hβ x = 0) :
    rootCoord hβ' x = 0 := by
  obtain ⟨ε, hε⟩ := rootCoord_twistHom t σ hβ hβ'
  have hF : twistHom t K σ x = x := (Subgroup.mem_inf.1 hxΓ).2
  calc rootCoord hβ' x = rootCoord hβ' (twistHom t K σ x) := by rw [hF]
    _ = ε * σ (rootCoord hβ x) := hε x hx
    _ = 0 := by rw [h0, map_zero, mul_zero]

theorem rootCoord_orbit_eq_zero {x : ModGL t.tag K} (hxΓ : x ∈ twistedFixedGroup t K σ)
    {β₀ : Fin t.tag.rank → ℤ} (hβ₀ : IsRoot t.tag β₀ ∧ 0 < height β₀)
    (hx : x ∈ heightSeries t.tag K (height β₀)) (h0 : rootCoord hβ₀ x = 0)
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ t.diagramOrbit β₀)
    (hα' : IsRoot t.tag α ∧ 0 < height α) : rootCoord hα' x = 0 := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hα
  have hroot : ∀ k : ℕ, IsRoot t.tag (permLattice (t.perm ^ k) β₀) ∧
      0 < height (permLattice (t.perm ^ k) β₀) := fun k =>
    ⟨hβ₀.1.permLattice (t.cartan_perm_pow k), by rw [height_permLattice]; exact hβ₀.2⟩
  have key : ∀ k : ℕ, rootCoord (hroot k) x = 0 := by
    intro k
    induction k with
    | zero =>
      have e : permLattice (t.perm ^ 0) β₀ = β₀ := by
        funext i
        simp [permLattice, ← Equiv.Perm.inv_def]
      rw [rootCoord_congr t e (hroot 0) hβ₀]
      exact h0
    | succ k ih =>
      have e : permLattice (t.perm ^ (k + 1)) β₀ = permLattice t.perm (permLattice (t.perm ^ k) β₀) :=
        permLattice_pow_succ t _ _ _
      have hρ : IsRoot t.tag (permLattice t.perm (permLattice (t.perm ^ k) β₀)) ∧
          0 < height (permLattice t.perm (permLattice (t.perm ^ k) β₀)) :=
        ⟨(hroot k).1.permLattice t.cartan_perm, by rw [height_permLattice]; exact (hroot k).2⟩
      have hx' : x ∈ heightSeries t.tag K (height (permLattice (t.perm ^ k) β₀)) := by
        rw [height_permLattice]
        exact hx
      rw [rootCoord_congr t e (hroot (k + 1)) hρ]
      exact rootCoord_perm_eq_zero t σ hxΓ (hroot k) hρ hx' ih
  exact key k

theorem layerHom_ker_le (h : ℕ) (hh : 0 < (h : ℤ)) :
    (layerHom t σ h hh).ker.map (layerSub t σ h).subtype ≤ layerSub t σ (h + 1) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxΓ : ((x.1 : ↥(graphFixedRootGroup t K σ)) : ModGL t.tag K) ∈ twistedFixedGroup t K σ :=
    graphFixedRootGroup_le t K σ x.1.2
  have hcoord : ∀ (α : Fin t.tag.rank → ℤ) (hα : IsRoot t.tag α ∧ 0 < height α),
      height α = (h : ℤ) → rootCoord hα ((x.1 : ↥(graphFixedRootGroup t K σ)) : ModGL t.tag K) = 0 := by
    intro α hα hαh
    have hO : t.diagramOrbit α ∈ orbitsAt t (h : ℤ) := (mem_orbitsAt t).2 ⟨α, hα.1, hαh, rfl⟩
    set O : ↥(orbitsAt t (h : ℤ)) := ⟨t.diagramOrbit α, hO⟩ with hOdef
    have hrep := repOf_spec t (h : ℤ) O
    have hc : layerCoord t (h : ℤ) hh ((x.1 : ↥(graphFixedRootGroup t K σ)) : ModGL t.tag K) O =
        0 := by
      have := congrArg Multiplicative.toAdd hx
      exact congrFun this O
    have hxU : ((x.1 : ↥(graphFixedRootGroup t K σ)) : ModGL t.tag K) ∈
        heightSeries t.tag K (height (repOf t (h : ℤ) O)) :=
      mem_heightSeries_of_height_eq t hrep.2.1 x.2
    refine rootCoord_orbit_eq_zero t σ hxΓ
      ⟨hrep.1, by rw [hrep.2.1]; exact hh⟩ hxU hc ?_ hα
    rw [hrep.2.2]
    exact t.self_mem_diagramOrbit α
  have := mem_heightSeries_succ_of_coord_eq_zero x.2 hcoord
  exact_mod_cast this

theorem rootCoord_conj_fieldActor (σ : K ≃+* K) (δ : K ≃+* K)
    (u : ↥(graphFixedRootGroup t K σ.toRingHom))
    (hu : (u : ModGL t.tag K) ∈ posUnipotent t.tag K)
    (x : ↥(graphFixedRootGroup t K σ.toRingHom)) (α : Fin t.tag.rank → ℤ)
    (hα : IsRoot t.tag α ∧ 0 < height α)
    (hx : (x : ModGL t.tag K) ∈ heightSeries t.tag K (height α)) :
    rootCoord hα (((MulAut.conj u * fieldActor (t := t) σ δ) x :
        ↥(graphFixedRootGroup t K σ.toRingHom)) : ModGL t.tag K) =
      δ (rootCoord hα (x : ModGL t.tag K)) := by
  have hc : (((MulAut.conj u * fieldActor (t := t) σ δ) x :
        ↥(graphFixedRootGroup t K σ.toRingHom)) : ModGL t.tag K) =
      (u : ModGL t.tag K) * Units.map (entrywiseHom δ.toRingHom) (x : ModGL t.tag K) *
        (u : ModGL t.tag K)⁻¹ := by
    rfl
  have hg : Units.map (entrywiseHom δ.toRingHom) (x : ModGL t.tag K) ∈
      heightSeries t.tag K (height α) :=
    map_heightSeries_le (Units.map (entrywiseHom δ.toRingHom)) id (fun γ hγ => hγ) (fun γ => rfl)
      (fun γ _ c => ⟨δ c, Units.ext (entrywise_pinnedX δ.toRingHom γ c)⟩) _ hx
  rw [hc, rootCoord_conj hα hu hg, rootCoord_entrywise δ.toRingHom hα hx]
  rfl

end CFSG.HardMathSupport.Lang.Triality
