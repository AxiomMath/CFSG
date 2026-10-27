module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6Y
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignTori
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotAlignLevi

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

local instance twistedE6PilotAlignToriNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotAlignToriNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotAlignToriNeZeroE6' : NeZero Tag.E6.rank := ⟨by decide⟩

local instance twistedE6PilotAlignToriNeZeroFolded : NeZero TwistTag.E6.foldedTag.rank :=
  ⟨by decide⟩

variable {K : Type} [Field K]

@[expose] def relTuple (B : Fin Tag.F4.rank → Kˣ) : Fin TwistTag.E6.tag.rank → Kˣ :=
  fun i => B (e6IndexToF4 i)

variable (K) in
@[expose] def relTupleHom : (Fin Tag.F4.rank → Kˣ) →* (Fin TwistTag.E6.tag.rank → Kˣ) where
  toFun := relTuple
  map_one' := rfl
  map_mul' _ _ := rfl

theorem rootChar_relTuple (B : Fin Tag.F4.rank → Kˣ) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar (relTuple B) γ = rootChar B (e6ToF4 γ) := by
  change ∏ i : Fin 6, B (e6IndexToF4 i) ^ γ i = ∏ a : Fin 4, B a ^ e6ToF4 γ a
  rw [Fin.prod_univ_six, Fin.prod_univ_four]
  change B 3 ^ γ 0 * B 0 ^ γ 1 * B 2 ^ γ 2 * B 1 ^ γ 3 * B 2 ^ γ 4 * B 3 ^ γ 5 =
    B 0 ^ γ 1 * B 1 ^ γ 3 * B 2 ^ (γ 2 + γ 4) * B 3 ^ (γ 0 + γ 5)
  rw [zpow_add, zpow_add]
  simp only [mul_assoc, mul_left_comm]

@[expose] def relNodeSet (I : Finset (Fin Tag.F4.rank)) : Finset (Fin TwistTag.E6.tag.rank) :=
  I.biUnion fun a => TwistTag.E6.orbit (f4FoldedIndex a)

theorem mem_relNodeSet {I : Finset (Fin Tag.F4.rank)} {i : Fin TwistTag.E6.tag.rank} :
    i ∈ relNodeSet I ↔ e6IndexToF4 i ∈ I := by
  rw [relNodeSet, Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hi⟩
    rwa [(mem_orbit_f4FoldedIndex_iff i a).1 hi]
  · intro h
    exact ⟨_, h, (mem_orbit_f4FoldedIndex_iff i _).2 rfl⟩

theorem relCoord_check : ∀ γ ∈ rootFinset TwistTag.E6.tag, ∀ i : Fin TwistTag.E6.tag.rank,
    e6ToF4 γ (e6IndexToF4 i) = 0 → γ i = 0 := by
  decide +kernel

theorem e6ToF4_eq_zero_of_forall_not_mem_relNodeSet {I : Finset (Fin Tag.F4.rank)}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (h : ∀ i ∉ relNodeSet I, γ i = 0) {a : Fin Tag.F4.rank}
    (ha : a ∉ I) : e6ToF4 γ a = 0 := by
  rw [e6ToF4_apply_eq_sum]
  refine Finset.sum_eq_zero fun i hi => h i fun hi' => ha ?_
  rw [← (mem_orbit_f4FoldedIndex_iff i a).1 hi]
  exact mem_relNodeSet.1 hi'

theorem forall_e6ToF4_eq_zero_iff {I : Finset (Fin Tag.F4.rank)}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) :
    (∀ a ∉ I, e6ToF4 γ a = 0) ↔ ∀ i ∉ relNodeSet I, γ i = 0 :=
  ⟨fun h i hi =>
    relCoord_check γ (mem_rootFinset.2 hγ) i (h _ fun h' => hi (mem_relNodeSet.2 h')),
    fun h _ ha => e6ToF4_eq_zero_of_forall_not_mem_relNodeSet h ha⟩

variable (K) in
@[expose] noncomputable def relLeviTorus (A : Subgroup Kˣ) (I : Finset (Fin Tag.F4.rank)) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  (Subgroup.pi Set.univ fun a => if a ∈ I then ⊥ else A).map
    ((rootDiagUnitHom TwistTag.E6.tag K).comp (relTupleHom K))

theorem mem_relLeviTorus {A : Subgroup Kˣ} {I : Finset (Fin Tag.F4.rank)}
    {g : ModGL TwistTag.E6.tag K} :
    g ∈ relLeviTorus K A I ↔
      ∃ B ∈ F4Pilot.leviTupleSet A I, rootDiagUnit TwistTag.E6.tag (relTuple B) = g := by
  simp only [relLeviTorus, mem_map, mem_pi, Set.mem_univ, true_implies]
  constructor
  · rintro ⟨B, hB, rfl⟩
    refine ⟨B, ⟨fun j hj => ?_, fun i => ?_⟩, rfl⟩
    · have h := hB j
      split_ifs at h
      exact mem_bot.1 h
    · have h := hB i
      split_ifs at h with hi
      · rw [mem_bot] at h
        rw [h]
        exact one_mem A
      · exact h
  · rintro ⟨B, ⟨hB1, hBA⟩, rfl⟩
    refine ⟨B, fun i => ?_, rfl⟩
    split_ifs with hi
    · rw [mem_bot]
      exact hB1 i hi
    · exact hBA i

theorem rootDiagUnit_relTuple_mem_relLeviTorus {A : Subgroup Kˣ} {I : Finset (Fin Tag.F4.rank)}
    {B : Fin Tag.F4.rank → Kˣ} (hB : B ∈ F4Pilot.leviTupleSet A I) :
    rootDiagUnit TwistTag.E6.tag (relTuple B) ∈ relLeviTorus K A I :=
  mem_relLeviTorus.2 ⟨B, hB, rfl⟩

theorem relLeviTorus_mono {A A' : Subgroup Kˣ} (hA : A ≤ A') {I I' : Finset (Fin Tag.F4.rank)}
    (hI : I ⊆ I') : relLeviTorus K A I' ≤ relLeviTorus K A' I := by
  intro g hg
  obtain ⟨B, ⟨hB1, hBA⟩, rfl⟩ := mem_relLeviTorus.1 hg
  exact rootDiagUnit_relTuple_mem_relLeviTorus ⟨fun j hj => hB1 j (hI hj), fun i => hA (hBA i)⟩

theorem relLeviTorus_anti {A : Subgroup Kˣ} {I I' : Finset (Fin Tag.F4.rank)} (hI : I ⊆ I') :
    relLeviTorus K A I' ≤ relLeviTorus K A I :=
  relLeviTorus_mono le_rfl hI

theorem relLeviTorus_le_centralizer_self (A : Subgroup Kˣ) (I : Finset (Fin Tag.F4.rank)) :
    relLeviTorus K A I ≤ centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K)) := by
  intro g hg
  obtain ⟨B, -, rfl⟩ := mem_relLeviTorus.1 hg
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨B', -, rfl⟩ := mem_relLeviTorus.1 hh
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

variable (K) in
@[expose] noncomputable def relTorus {k : Type} [Field k] (ι : k →+* K)
    (I : Finset (Fin Tag.F4.rank)) : Subgroup (ModGL TwistTag.E6.tag K) :=
  relLeviTorus K (Units.map ι.toMonoidHom).range I

@[expose] def relWeight : Fin Tag.F4.rank → Fin TwistTag.E6.tag.rank → ℤ :=
  (![![1, 2, 2, 3, 2, 1], ![2, 3, 4, 6, 4, 2], ![3, 4, 6, 8, 6, 3], ![2, 2, 3, 4, 3, 2]] :
    Fin 4 → Fin 6 → ℤ)

theorem relWeight_check : ∀ b : Fin Tag.F4.rank,
    permLattice TwistTag.E6.perm (relWeight b) = relWeight b ∧
      ∀ l : Fin TwistTag.E6.tag.rank, ∑ j, relWeight b j * TwistTag.E6.tag.cartan j l =
        if e6IndexToF4 l = b then 1 else 0 := by
  decide

theorem relWeight_iform_check : ∀ (b : Fin Tag.F4.rank) (l : Fin TwistTag.E6.tag.rank),
    iform (relWeight b) (Pi.single l 1) = if e6IndexToF4 l = b then 1 else 0 := by
  decide

theorem iform_relWeight (b : Fin Tag.F4.rank) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    iform (relWeight b) v = e6ToF4 v b := by
  rw [F4Pilot.iform_eq_sum_mul_iform_single, e6ToF4_apply_eq_sum]
  simp only [relWeight_iform_check, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (mem_orbit_f4FoldedIndex_iff i b).symm

theorem frameTorusElt_relWeight (b : Fin Tag.F4.rank) (c : Kˣ) :
    frameTorusElt TwistTag.E6.tag K (relWeight b) c =
      rootDiagUnit TwistTag.E6.tag (relTuple (Pi.mulSingle b c)) := by
  have hs : ∀ i : Fin TwistTag.E6.tag.rank, TwistTag.E6.tag.symmetrizer i i = 1 := by decide
  rw [frameTorusElt]
  simp only [hs, one_mul]
  rw [list_prod_torusElt_eq_rootDiagUnit, cartanChar_zpow']
  congr 1
  funext l
  rw [(relWeight_check b).2 l, relTuple]
  split_ifs with h
  · rw [h, Pi.mulSingle_eq_same, zpow_one]
  · rw [Pi.mulSingle_eq_of_ne h, zpow_zero]

section C0

theorem rootDiagUnit_relTuple_mem_C0 {σ : K →+* K} {B : Fin Tag.F4.rank → Kˣ}
    (hB : ∀ a, Units.map σ.toMonoidHom (B a) = B a) :
    rootDiagUnit TwistTag.E6.tag (relTuple B) ∈ graphFixedRootGroup TwistTag.E6 K σ := by
  let H : Subgroup (Fin Tag.F4.rank → Kˣ) := (graphFixedRootGroup TwistTag.E6 K σ).comap
    ((rootDiagUnitHom TwistTag.E6.tag K).comp (relTupleHom K))
  have hsingle : ∀ b, Pi.mulSingle b (B b) ∈ H := fun b => by
    change rootDiagUnit TwistTag.E6.tag (relTuple (Pi.mulSingle b (B b))) ∈
      graphFixedRootGroup TwistTag.E6 K σ
    rw [← frameTorusElt_relWeight]
    exact frameTorusElt_mem_graphFixedRootGroup σ (relWeight_check b).1 (hB b)
  have hBH : B ∈ H := by
    rw [← Finset.univ_prod_mulSingle B]
    exact Subgroup.prod_mem H fun b _ => hsingle b
  exact hBH

theorem relLeviTorus_le_C0 {σ : K →+* K} {A : Subgroup Kˣ}
    (hA : ∀ c ∈ A, Units.map σ.toMonoidHom c = c) (I : Finset (Fin Tag.F4.rank)) :
    relLeviTorus K A I ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  intro g hg
  obtain ⟨B, ⟨-, hBA⟩, rfl⟩ := mem_relLeviTorus.1 hg
  exact rootDiagUnit_relTuple_mem_C0 fun a => hA _ (hBA a)

end C0

section Kill

theorem rootDiagUnit_relTuple_conj_pinnedX (B : Fin Tag.F4.rank → Kˣ)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ) (c : K) :
    rootDiagUnit TwistTag.E6.tag (relTuple B) * pinnedX TwistTag.E6.tag K γ c *
        (rootDiagUnit TwistTag.E6.tag (relTuple B))⁻¹ =
      pinnedX TwistTag.E6.tag K γ ((rootChar B (e6ToF4 γ) : K) * c) := by
  rw [rootDiagUnit_conj_pinnedX _ hγ, rootChar_relTuple]

theorem rootSubgroup_le_centralizer_relLeviTorus {A : Subgroup Kˣ} {I : Finset (Fin Tag.F4.rank)}
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (h : ∀ a ∉ I, e6ToF4 γ a = 0) :
    rootSubgroup TwistTag.E6.tag K γ ≤
      centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K)) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro t ht
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨B, ⟨hB1, -⟩, rfl⟩ := mem_relLeviTorus.1 ht
  have hconj := rootDiagUnit_relTuple_conj_pinnedX B hγ c
  have h1 : rootChar B (e6ToF4 γ) = 1 := Finset.prod_eq_one fun a _ => by
    by_cases ha : a ∈ I
    · rw [hB1 a ha, one_zpow]
    · rw [h a ha, zpow_zero]
  rw [h1, Units.val_one, one_mul] at hconj
  exact mul_inv_eq_iff_eq_mul.1 hconj

end Kill

variable (K) in
@[expose] noncomputable def relLevi
    (I : Finset (Fin Tag.F4.rank)) : Subgroup (ModGL TwistTag.E6.tag K) :=
  rootSpan TwistTag.E6.tag K
    (F4Pilot.signedSimpleRoots (relNodeSet I : Set (Fin TwistTag.E6.tag.rank)))

theorem e6ToF4_eq_zero_of_mem_signedSimpleRoots {I : Finset (Fin Tag.F4.rank)}
    {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ F4Pilot.signedSimpleRoots (relNodeSet I : Set (Fin TwistTag.E6.tag.rank))) :
    ∀ a ∉ I, e6ToF4 α a = 0 := by
  obtain ⟨j, hj, rfl | rfl⟩ := hα <;> refine fun a ha => e6ToF4_eq_zero_of_forall_not_mem_relNodeSet
    (fun i hi => ?_) ha <;> have hij : i ≠ j := fun h => hi (h ▸ hj)
  · exact Pi.single_eq_of_ne hij _
  · rw [Pi.neg_apply, Pi.single_eq_of_ne hij, neg_zero]

theorem relLevi_le_centralizer_relLeviTorus
    (A : Subgroup Kˣ)
    (I : Finset (Fin Tag.F4.rank)) :
    relLevi K I ≤ centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K)) :=
  iSup₂_le fun _ hα => rootSubgroup_le_centralizer_relLeviTorus
    (F4Pilot.isRoot_of_mem_signedSimpleRoots hα) (e6ToF4_eq_zero_of_mem_signedSimpleRoots hα)

theorem relTuple_mulSingle_zero (u : Kˣ) :
    relTuple (Pi.mulSingle (0 : Fin Tag.F4.rank) u) =
      Pi.mulSingle (1 : Fin TwistTag.E6.tag.rank) u := by
  funext i
  revert i
  change ∀ i : Fin 6, (Pi.mulSingle (0 : Fin 4) u : Fin 4 → Kˣ) (e6IndexToF4 i) =
    (Pi.mulSingle (1 : Fin 6) u : Fin 6 → Kˣ) i
  intro i
  fin_cases i <;> rfl

theorem relTuple_mulSingle_three (u : Kˣ) :
    relTuple (Pi.mulSingle (3 : Fin Tag.F4.rank) u) = d4CentralDiag u u := by
  funext i
  revert i
  change ∀ i : Fin 6, (Pi.mulSingle (3 : Fin 4) u : Fin 4 → Kˣ) (e6IndexToF4 i) =
    (Pi.mulSingle (0 : Fin 6) u * Pi.mulSingle (5 : Fin 6) u : Fin 6 → Kˣ) i
  intro i
  fin_cases i <;> simp <;> rfl

theorem eq_mulSingle_of_forall_ne {B : Fin Tag.F4.rank → Kˣ} {b : Fin Tag.F4.rank}
    (h : ∀ j, j ≠ b → B j = 1) : B = Pi.mulSingle b (B b) := by
  funext j
  by_cases hj : j = b
  · subst hj
    exact (Pi.mulSingle_eq_same (M := fun _ : Fin Tag.F4.rank => Kˣ) j (B j)).symm
  · rw [h j hj]
    exact (Pi.mulSingle_eq_of_ne (M := fun _ : Fin Tag.F4.rank => Kˣ) hj (B b)).symm

theorem eq_mulSingle_zero_of_mem_leviTupleSet {A : Subgroup Kˣ} {B : Fin Tag.F4.rank → Kˣ}
    (hB : B ∈ F4Pilot.leviTupleSet A {1, 2, 3}) : B = Pi.mulSingle 0 (B 0) :=
  eq_mulSingle_of_forall_ne fun j hj => hB.1 j (by revert j; decide)

theorem eq_mulSingle_three_of_mem_leviTupleSet {A : Subgroup Kˣ} {B : Fin Tag.F4.rank → Kˣ}
    (hB : B ∈ F4Pilot.leviTupleSet A {0, 1, 2}) : B = Pi.mulSingle 3 (B 3) :=
  eq_mulSingle_of_forall_ne fun j hj => hB.1 j (by revert j; decide)

theorem mulSingle_mem_leviTupleSet {A : Subgroup Kˣ} {I : Finset (Fin Tag.F4.rank)}
    {b : Fin Tag.F4.rank} (hb : b ∉ I) {u : Kˣ} (hu : u ∈ A) :
    Pi.mulSingle b u ∈ F4Pilot.leviTupleSet A I :=
  F4Pilot.mulSingle_mem_leviTupleSet hb hu

theorem relTorus_X_eq_thetaTorus {k : Type} [Field k] (ι : k →+* K) :
    relTorus K ι {1, 2, 3} = E6GraphLevi.thetaTorus ι := by
  ext g
  rw [relTorus, mem_relLeviTorus]
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (hB.2 0)
    refine ⟨c, ?_⟩
    rw [eq_mulSingle_zero_of_mem_leviTupleSet hB, relTuple_mulSingle_zero, ← hc]
    rfl
  · rintro ⟨c, rfl⟩
    refine ⟨Pi.mulSingle 0 (Units.map ι.toMonoidHom c),
      mulSingle_mem_leviTupleSet (by decide) ⟨c, rfl⟩, ?_⟩
    rw [relTuple_mulSingle_zero]
    rfl

theorem relTorus_Y_eq_shortRootTorus {k : Type} [Field k] (ι : k →+* K) :
    relTorus K ι {0, 1, 2} = shortRootTorus ι := by
  ext g
  rw [relTorus, mem_relLeviTorus, mem_shortRootTorus]
  constructor
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (hB.2 3)
    refine ⟨c, ?_⟩
    rw [eq_mulSingle_three_of_mem_leviTupleSet hB, relTuple_mulSingle_three, ← hc]
    rfl
  · rintro ⟨c, rfl⟩
    refine ⟨Pi.mulSingle 3 (Units.map ι.toMonoidHom c),
      mulSingle_mem_leviTupleSet (by decide) ⟨c, rfl⟩, ?_⟩
    rw [relTuple_mulSingle_three]
    rfl

@[expose] def xPrimeTuple (c : Kˣ) : Fin Tag.F4.rank → Kˣ :=
  Pi.mulSingle 1 c⁻¹ * Pi.mulSingle 2 c

variable (K) in
@[expose] def xPrimeHom : Kˣ →* (Fin Tag.F4.rank → Kˣ) :=
  (MonoidHom.mulSingle (fun _ : Fin Tag.F4.rank => Kˣ) 1).comp (invMonoidHom (α := Kˣ)) *
    MonoidHom.mulSingle (fun _ : Fin Tag.F4.rank => Kˣ) 2

variable (K) in
@[expose] noncomputable def xPrimeTorus (A : Subgroup Kˣ) : Subgroup (ModGL TwistTag.E6.tag K) :=
  A.map (((rootDiagUnitHom TwistTag.E6.tag K).comp (relTupleHom K)).comp (xPrimeHom K))

theorem mem_xPrimeTorus {A : Subgroup Kˣ} {g : ModGL TwistTag.E6.tag K} :
    g ∈ xPrimeTorus K A ↔ ∃ c ∈ A, rootDiagUnit TwistTag.E6.tag (relTuple (xPrimeTuple c)) = g := by
  rw [xPrimeTorus, mem_map]
  rfl

theorem mulSingle_apply_mem {A : Subgroup Kˣ} {b : Fin Tag.F4.rank} {u : Kˣ} (hu : u ∈ A)
    (i : Fin Tag.F4.rank) : (Pi.mulSingle b u : Fin Tag.F4.rank → Kˣ) i ∈ A := by
  by_cases h : i = b
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact hu
  · rw [Pi.mulSingle_eq_of_ne h]
    exact one_mem A

theorem xPrimeTorus_le_relLeviTorus {A : Subgroup Kˣ} {I : Finset (Fin Tag.F4.rank)}
    (hI : I ⊆ {0, 3}) : xPrimeTorus K A ≤ relLeviTorus K A I := by
  intro g hg
  obtain ⟨c, hc, rfl⟩ := mem_xPrimeTorus.1 hg
  refine rootDiagUnit_relTuple_mem_relLeviTorus ⟨fun j hj => ?_, fun i => ?_⟩
  · have h := hI hj
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rw [xPrimeTuple, Pi.mul_apply, Pi.mulSingle_eq_of_ne (by rcases h with rfl | rfl <;> decide),
      Pi.mulSingle_eq_of_ne (by rcases h with rfl | rfl <;> decide), mul_one]
  · rw [xPrimeTuple, Pi.mul_apply]
    exact mul_mem (mulSingle_apply_mem (inv_mem hc) i) (mulSingle_apply_mem hc i)

variable (K) in
@[expose] noncomputable def neighbourTorus (A : Subgroup Kˣ) :
    F4Pilot.AmalgamNeighbour → Subgroup (ModGL TwistTag.E6.tag K)
  | .X => relLeviTorus K A {1, 2, 3}
  | .Y => relLeviTorus K A {0, 1, 2}
  | .X' => xPrimeTorus K A

theorem neighbourTorus_le_relLeviTorus (A : Subgroup Kˣ) (N : F4Pilot.AmalgamNeighbour)
    {I : Finset (Fin Tag.F4.rank)} (hI : I ⊆ N.nodes) :
    neighbourTorus K A N ≤ relLeviTorus K A I := by
  cases N
  · exact relLeviTorus_anti hI
  · exact relLeviTorus_anti hI
  · exact xPrimeTorus_le_relLeviTorus hI

theorem neighbourTorus_X_Y {k : Type} [Field k] (ι : k →+* K) :
    neighbourTorus K (Units.map ι.toMonoidHom).range .X = E6GraphLevi.thetaTorus ι ∧
      neighbourTorus K (Units.map ι.toMonoidHom).range .Y = shortRootTorus ι :=
  ⟨relTorus_X_eq_thetaTorus ι, relTorus_Y_eq_shortRootTorus ι⟩

theorem e6IndexToF4_values :
    e6IndexToF4 (0 : Fin TwistTag.E6.tag.rank) = 3 ∧
      e6IndexToF4 (1 : Fin TwistTag.E6.tag.rank) = 0 ∧
      e6IndexToF4 (2 : Fin TwistTag.E6.tag.rank) = 2 ∧
      e6IndexToF4 (3 : Fin TwistTag.E6.tag.rank) = 1 ∧
      e6IndexToF4 (4 : Fin TwistTag.E6.tag.rank) = 2 ∧
      e6IndexToF4 (5 : Fin TwistTag.E6.tag.rank) = 3 := by
  decide

theorem xPrimeTuple_values (c : Kˣ) :
    xPrimeTuple c 0 = 1 ∧ xPrimeTuple c 1 = c⁻¹ ∧ xPrimeTuple c 2 = c ∧ xPrimeTuple c 3 = 1 := by
  simp only [xPrimeTuple, Pi.mul_apply, Pi.mulSingle_apply]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := { decide := true })

theorem relTuple_xPrimeTuple (c : Kˣ) :
    relTuple (xPrimeTuple c) = (![1, 1, c, c⁻¹, c, 1] : Fin 6 → Kˣ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := e6IndexToF4_values
  obtain ⟨x0, x1, x2, x3⟩ := xPrimeTuple_values c
  funext j
  revert j
  change ∀ j : Fin 6, xPrimeTuple c (e6IndexToF4 j) = (![1, 1, c, c⁻¹, c, 1] : Fin 6 → Kˣ) j
  intro j
  fin_cases j
  · exact (congrArg _ h0).trans x3
  · exact (congrArg _ h1).trans x0
  · exact (congrArg _ h2).trans x2
  · exact (congrArg _ h3).trans x1
  · exact (congrArg _ h4).trans x2
  · exact (congrArg _ h5).trans x3

section XPrime

theorem twistedE6RelWeyl_relWordXPrime :
    twistedE6RelWeyl K relWordXPrime =
      weylElt TwistTag.E6.tag K 3 1 * weylElt TwistTag.E6.tag K 1 1 := by
  have h : (relWordXPrime.flatMap fun a => TwistTag.E6.orbitWord a) = [3, 1] := by decide
  rw [twistedE6RelWeyl, h]
  simp

theorem relWordXPrime_conj_rootDiagUnit (c : Kˣ) :
    twistedE6RelWeyl K relWordXPrime *
        rootDiagUnit TwistTag.E6.tag (relTuple (Pi.mulSingle 0 c)) *
        (twistedE6RelWeyl K relWordXPrime)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (relTuple (xPrimeTuple c)) := by
  rw [twistedE6RelWeyl_relWordXPrime]
  calc weylElt TwistTag.E6.tag K 3 1 * weylElt TwistTag.E6.tag K 1 1 *
        rootDiagUnit TwistTag.E6.tag (relTuple (Pi.mulSingle 0 c)) *
        (weylElt TwistTag.E6.tag K 3 1 * weylElt TwistTag.E6.tag K 1 1)⁻¹ =
      weylElt TwistTag.E6.tag K 3 1 * (weylElt TwistTag.E6.tag K 1 1 *
        rootDiagUnit TwistTag.E6.tag (relTuple (Pi.mulSingle 0 c)) *
        (weylElt TwistTag.E6.tag K 1 1)⁻¹) * (weylElt TwistTag.E6.tag K 3 1)⁻¹ := by group
    _ = _ := by
      rw [E6Pilot.weylElt_one_conj_rootDiagUnit_eq, E6Pilot.weylElt_one_conj_rootDiagUnit_eq,
        relTuple_mulSingle_zero, relTuple_xPrimeTuple]
      congr 1
      funext j
      revert j
      change ∀ j : Fin 6, (Pi.mulSingle (1 : Fin 6) c : Fin 6 → Kˣ) j *
          (Pi.mulSingle (1 : Fin 6) c : Fin 6 → Kˣ) 1 ^ (-Tag.E6.cartan 1 j) *
          ((Pi.mulSingle (1 : Fin 6) c : Fin 6 → Kˣ) 3 *
            (Pi.mulSingle (1 : Fin 6) c : Fin 6 → Kˣ) 1 ^ (-Tag.E6.cartan 1 3)) ^
            (-Tag.E6.cartan 3 j) = (![1, 1, c, c⁻¹, c, 1] : Fin 6 → Kˣ) j
      intro j
      fin_cases j
      · show 1 * c ^ (-(0 : ℤ)) * (1 * c ^ (-(-1 : ℤ))) ^ (-(0 : ℤ)) = 1
        group
      · show c * c ^ (-(2 : ℤ)) * (1 * c ^ (-(-1 : ℤ))) ^ (-(-1 : ℤ)) = 1
        group
      · show 1 * c ^ (-(0 : ℤ)) * (1 * c ^ (-(-1 : ℤ))) ^ (-(-1 : ℤ)) = c
        group
      · show 1 * c ^ (-(-1 : ℤ)) * (1 * c ^ (-(-1 : ℤ))) ^ (-(2 : ℤ)) = c⁻¹
        group
      · show 1 * c ^ (-(0 : ℤ)) * (1 * c ^ (-(-1 : ℤ))) ^ (-(-1 : ℤ)) = c
        group
      · show 1 * c ^ (-(0 : ℤ)) * (1 * c ^ (-(-1 : ℤ))) ^ (-(0 : ℤ)) = 1
        group

theorem map_conj_relWordXPrime_neighbourTorus_X (A : Subgroup Kˣ) :
    (neighbourTorus K A .X).map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom =
      neighbourTorus K A .X' := by
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨B, hB, rfl⟩ := mem_relLeviTorus.1 hx
    rw [eq_mulSingle_zero_of_mem_leviTupleSet hB, relWordXPrime_conj_rootDiagUnit]
    exact mem_xPrimeTorus.2 ⟨B 0, hB.2 0, rfl⟩
  · intro hg
    obtain ⟨c, hc, rfl⟩ := mem_xPrimeTorus.1 hg
    exact ⟨_, rootDiagUnit_relTuple_mem_relLeviTorus (mulSingle_mem_leviTupleSet (by decide) hc),
      relWordXPrime_conj_rootDiagUnit c⟩

end XPrime

end CFSG.SeitzReduction.TwistedE6Pilot
