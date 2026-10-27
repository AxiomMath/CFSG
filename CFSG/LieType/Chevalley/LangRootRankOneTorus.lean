module

public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} {K : Type} [Field K]

variable (τ) in
@[expose] def pinnedWord
    (β : Fin τ.rank → ℤ) : List (Fin τ.rank) :=
  ((pinnedData τ β).2.1.map τ.idx).reverse

theorem pinnedWeyl_eq_list_prod
    (R : Type) [CommRing R] (β : Fin τ.rank → ℤ) :
    pinnedWeyl τ R β = ((pinnedWord τ β).map fun i => weylElt τ R i 1).prod := by
  rw [pinnedWeyl, pinnedWord, List.map_reverse, List.map_map]
  rfl

theorem wordProd_reverse_smul
    (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd ω.reverse • v = ω.foldl (fun v i => reflect τ i v) v := by
  induction ω generalizing v with
  | nil => simp
  | cons i ω ih =>
    rw [List.reverse_cons, CoxeterSystem.wordProd_append, mul_smul,
      CoxeterSystem.wordProd_singleton, simple_smul, List.foldl_cons, ih]

theorem wordProd_pinnedWord_smul
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    (coxeterSystem τ).wordProd (pinnedWord τ β) •
      (Pi.single (pinnedData τ β).1 1 : Fin τ.rank → ℤ) = β := by
  rw [pinnedWord, wordProd_reverse_smul, List.foldl_map]
  exact foldl_reflect_pinnedData hβ

theorem exceptional_Lang_root_rank_one_torus_transport
    (τ : Tag) (K : Type) [Field K]
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootRankOneGroup τ K β = rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) ∧
    (∀ c : Kˣ, rootTorusSL2 τ K β c ∈ torusGroup τ K) ∧
    (∀ c : Kˣ, ∃ h : rootWeylSL2 τ K β c ∈ monomialSubgroup τ K,
      weylQuotientHom τ K ⟨_, h⟩ = rootReflection β) ∧
    (∀ v : Fin τ.rank → ℤ, rootReflection β • v = v - (2 * iform β v / iform β β) • β ∧
      2 * iform β v / iform β β * iform β β = 2 * iform β v) ∧
    (∀ c : Kˣ, (∀ i, (rootTorusSL2 τ K β c : Module.End K (RootModule τ K)) (hVec τ K i) =
        hVec τ K i) ∧
      ∀ γ, IsRoot τ γ → (rootTorusSL2 τ K β c : Module.End K (RootModule τ K)) (rootVec τ K γ) =
        ((c ^ (2 * iform β γ / iform β β) : Kˣ) : K) • rootVec τ K γ) ∧
    (∀ t ∈ torusGroup τ K, ∃! a : Fin τ.rank → Kˣ, t = rootDiagUnit τ a) ∧
    (∀ a : Fin τ.rank → Kˣ, ∀ γ, IsRoot τ γ → ∀ z : K,
      rootDiagUnit τ a * pinnedX τ K γ z * (rootDiagUnit τ a)⁻¹ =
        pinnedX τ K γ (((∏ i, a i ^ γ i : Kˣ) : K) * z)) ∧
    ∀ a : Fin τ.rank → Kˣ, (∏ i, a i ^ β i) = 1 →
      ∀ g ∈ rootRankOneGroup τ K β, rootDiagUnit τ a * g = g * rootDiagUnit τ a := by
  set j := (pinnedData τ β).1 with hj
  set ω := pinnedWord τ β with hω
  set w := (coxeterSystem τ).wordProd ω with hwdef
  have hw : w • (Pi.single j 1 : Fin τ.rank → ℤ) = β := wordProd_pinnedWord_smul hβ
  have hW : pinnedWeyl τ K β = (ω.map fun i => weylElt τ K i 1).prod :=
    pinnedWeyl_eq_list_prod K β
  have hL : rootRankOneGroup τ K β = rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := by
    have h2 : (simpleRootSL2 τ K j).range =
        rootSubgroup τ K (Pi.single j 1) ⊔ rootSubgroup τ K (-Pi.single j 1) := by
      rw [range_simpleRootSL2, Subgroup.closure_union, rootSubgroup, rootSubgroup,
        show pinnedX τ K (Pi.single j 1) = xUnit τ K j from funext (pinnedX_single τ K j),
        show pinnedX τ K (-Pi.single j 1) = yUnit τ K j from funext (pinnedX_neg_single τ K j)]
    rw [rootRankOneGroup, rootSL2, MonoidHom.range_comp, h2, Subgroup.map_sup, hW,
      map_conj_prod_weylElt_rootSubgroup K ω (isRoot_single τ j),
      map_conj_prod_weylElt_rootSubgroup K ω (isRoot_neg_single τ j), smul_neg, ← hwdef, hw]
  have hWN : pinnedWeyl τ K β ∈
      Subgroup.normalizer (torusGroup τ K : Set (Module.End K (RootModule τ K))ˣ) := by
    rw [hW]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    rw [← canonicalRep_simple (coxeterSystem τ) K i]
    exact canonicalRep_mem_normalizer _
  have hWM : pinnedWeyl τ K β ∈ monomialSubgroup τ K := by
    rw [hW]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_monomialSubgroup i
  have hWmaps : MapsRootLines (pinnedWeyl τ K β) w := by
    rw [hW]
    exact mapsRootLines_list_prod ω
  have hd : ∀ c : Kˣ, rootTorusSL2 τ K β c =
      pinnedWeyl τ K β * torusElt τ K j c * (pinnedWeyl τ K β)⁻¹ := fun c => by
    rw [rootTorusSL2, rootSL2_apply, simpleRootSL2_HSL]
  have hdH : ∀ c : Kˣ, rootTorusSL2 τ K β c ∈ torusGroup τ K := fun c => by
    rw [hd]
    exact (Subgroup.mem_normalizer_iff.1 hWN _).1 (torusElt_mem_torusGroup j c)
  have hn : ∀ c : Kˣ, rootWeylSL2 τ K β c = rootTorusSL2 τ K β c *
      (pinnedWeyl τ K β * weylElt τ K j 1 * (pinnedWeyl τ K β)⁻¹) := fun c => by
    rw [rootWeylSL2, nSL_eq_HSL_mul, map_mul, rootTorusSL2, rootSL2_apply β WSL, simpleRootSL2_WSL]
  have hnN : ∀ c : Kˣ, rootWeylSL2 τ K β c ∈ monomialSubgroup τ K := fun c => by
    rw [hn]
    exact mul_mem (Subgroup.mem_sup_left (hdH c))
      (mul_mem (mul_mem hWM (weylElt_mem_monomialSubgroup j)) (inv_mem hWM))
  have hnmaps : ∀ c : Kˣ, MapsRootLines (rootWeylSL2 τ K β c) (rootReflection β) := fun c => by
    rw [hn, rootReflection_eq_conj hw]
    have := (mapsRootLines_of_mem_torusGroup (hdH c)).mul
      ((hWmaps.mul (mapsRootLines_weylElt j)).mul hWmaps.inv)
    rwa [one_mul] at this
  have hv : ∀ c : Kˣ, ∀ γ, IsRoot τ γ →
      (rootTorusSL2 τ K β c : Module.End K (RootModule τ K)) (rootVec τ K γ) =
        ((c ^ (2 * iform β γ / iform β β) : Kˣ) : K) • rootVec τ K γ := by
    intro c γ hγ
    obtain ⟨u, hu⟩ := hWmaps.inv γ hγ
    have e2 : 2 * iform β γ / iform β β = ∑ k, τ.cartan j k * (w⁻¹ • γ) k := by
      rw [← corootPair_smul_single, hw, corootPair]
    have e1 : (torusElt τ K j c : Module.End K (RootModule τ K))
        ((((pinnedWeyl τ K β)⁻¹ : (Module.End K (RootModule τ K))ˣ) :
          Module.End K (RootModule τ K)) (rootVec τ K γ)) =
        ((c ^ (2 * iform β γ / iform β β) : Kˣ) : K) •
          ((((pinnedWeyl τ K β)⁻¹ : (Module.End K (RootModule τ K))ˣ) :
            Module.End K (RootModule τ K)) (rootVec τ K γ)) := by
      rw [hu, map_smul, torusElt_rootVec j c (IsRoot.smul hγ w⁻¹), smul_comm, e2]
    rw [hd, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, e1,
      map_smul, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hH : ∀ t ∈ torusGroup τ K, ∃! a : Fin τ.rank → Kˣ, t = rootDiagUnit τ a := by
    intro t ht
    have hrange : torusGroup τ K ≤ (rootDiagUnitHom τ K).range := by
      rw [torusGroup, Subgroup.closure_le]
      rintro _ ⟨⟨i, u⟩, rfl⟩
      exact ⟨_, (torusElt_eq_rootDiagUnit i u).symm⟩
    obtain ⟨a, ha⟩ := hrange ht
    have ha' : t = rootDiagUnit τ a := ha.symm
    exact ⟨a, ha', fun b hb => rootDiagUnit_injective (hb.symm.trans ha')⟩
  have hconj : ∀ a : Fin τ.rank → Kˣ, ∀ γ, IsRoot τ γ → ∀ z : K,
      rootDiagUnit τ a * pinnedX τ K γ z * (rootDiagUnit τ a)⁻¹ =
        pinnedX τ K γ (((∏ i, a i ^ γ i : Kˣ) : K) * z) :=
    fun a γ hγ z => rootDiagUnit_conj_pinnedX a hγ z
  have hcent : ∀ a : Fin τ.rank → Kˣ, (∏ i, a i ^ β i) = 1 →
      ∀ g ∈ rootRankOneGroup τ K β, rootDiagUnit τ a * g = g * rootDiagUnit τ a := by
    intro a ha g hg
    have hneg : (∏ i, a i ^ (-β) i) = 1 := by
      simp only [Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib, ha, inv_one]
    have hroot : ∀ γ, IsRoot τ γ → (∏ i, a i ^ γ i) = 1 →
        rootSubgroup τ K γ ≤ Subgroup.centralizer {rootDiagUnit τ a} := by
      intro γ hγ hχ
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨z, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h1 := hconj a γ hγ z
      rw [hχ, Units.val_one, one_mul] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    have hle : rootRankOneGroup τ K β ≤ Subgroup.centralizer {rootDiagUnit τ a} := by
      rw [hL]
      exact sup_le (hroot β hβ ha) (hroot (-β) (IsRoot.neg hβ) hneg)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm
  refine ⟨hL, hdH, fun c => ⟨hnN c, weylQuotientHom_eq (hnmaps c)⟩, fun v => ⟨?_, ?_⟩,
    fun c => ⟨fun i => (torusGroup_le_diagonalGroup (hdH c)).1 i, hv c⟩, hH, hconj, hcent⟩
  · exact rootReflection_smul hβ v
  · exact corootPair_mul hβ v

end CFSG.LieType.Chevalley
