module

public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner
public import CFSG.LieType.Chevalley.C2E6NativeF4Coxeter
public import CFSG.LieType.Chevalley.C2E6StandardFixedBorelOrder
public import CFSG.LieType.Chevalley.F4FieldTwoEuclid

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.RelativeRoots

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

@[expose] def nativeWord : Fin 4 → List (Fin Tag.E6.rank) :=
  ![[⟨1, by decide⟩], [⟨3, by decide⟩], [⟨2, by decide⟩, ⟨4, by decide⟩],
    [⟨0, by decide⟩, ⟨5, by decide⟩]]

theorem orbitWord_foldedIndex (i : Fin 4) :
    TwistTag.E6.orbitWord (foldedIndex i) = nativeWord i := by
  fin_cases i <;> rfl

theorem list_prod_simple_smul
    (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    (l.map fun j => simple Tag.E6 j).prod • v = l.foldr (fun k w => reflect Tag.E6 k w) v := by
  induction l with
  | nil => simp
  | cons j l ih => rw [List.map_cons, List.prod_cons, mul_smul, ih, simple_smul]; rfl

theorem nativeRefl_smul
    (i : Fin 4) (v : Fin Tag.E6.rank → ℤ) :
    nativeRefl i • v = (nativeWord i).foldr (fun k w => reflect Tag.E6 k w) v := by
  rw [nativeRefl_eq, TwistTag.orbitReflection, orbitWord_foldedIndex, ← list_prod_simple_smul]
  rfl

theorem e6ToF4_zero : e6ToF4 (0 : Fin Tag.E6.rank → ℤ) = 0 := by
  funext k
  fin_cases k <;> rfl

theorem e6ToF4_add (v w : Fin Tag.E6.rank → ℤ) : e6ToF4 (v + w) = e6ToF4 v + e6ToF4 w := by
  funext k
  fin_cases k
  · rfl
  · rfl
  · exact add_add_add_comm (v ⟨2, by decide⟩) (w ⟨2, by decide⟩) (v ⟨4, by decide⟩)
      (w ⟨4, by decide⟩)
  · exact add_add_add_comm (v ⟨0, by decide⟩) (w ⟨0, by decide⟩) (v ⟨5, by decide⟩)
      (w ⟨5, by decide⟩)

@[expose] def e6ToF4Hom : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.F4.rank → ℤ) where
  toFun := e6ToF4
  map_zero' := e6ToF4_zero
  map_add' := e6ToF4_add

theorem e6ToF4_reflect_check : ∀ (i : Fin 4) (j : Fin Tag.E6.rank),
    e6ToF4 ((nativeWord i).foldr (fun k w => reflect Tag.E6 k w) (Pi.single j 1)) =
      reflect .F4 i (e6ToF4 (Pi.single j 1)) := by
  decide +kernel

theorem e6ToF4_nativeRefl_smul
    (i : Fin 4) (v : Fin Tag.E6.rank → ℤ) :
    e6ToF4 (nativeRefl i • v) = simple .F4 i • e6ToF4 v := by
  let f : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.F4.rank → ℤ) :=
    { toFun := fun v => e6ToF4 (nativeRefl i • v)
      map_zero' := by rw [smul_zero, e6ToF4_zero]
      map_add' := fun v w => by rw [smul_add, e6ToF4_add] }
  let g : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.F4.rank → ℤ) :=
    { toFun := fun v => simple .F4 i • e6ToF4 v
      map_zero' := by rw [e6ToF4_zero, smul_zero]
      map_add' := fun v w => by rw [e6ToF4_add, smul_add] }
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
    have hx : (Pi.single j x : Fin Tag.E6.rank → ℤ) = x • Pi.single j 1 := by
      funext k
      by_cases h : k = j
      · subst h
        simp
      · simp [h]
    rw [hx, map_zsmul, map_zsmul]
    congr 1
    change e6ToF4 (nativeRefl i • Pi.single j 1) = simple .F4 i • e6ToF4 (Pi.single j 1)
    rw [nativeRefl_smul]
    exact (e6ToF4_reflect_check i j).trans (simple_smul (τ := .F4) i _).symm
  exact DFunLike.congr_fun hfg v

@[expose] def relProj (β : Fin TwistTag.E6.tag.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  e6ToF4 β

theorem isRoot_relProj
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) :
    IsRoot Tag.F4 (relProj β) :=
  isRoot_e6ToF4 hβ

theorem exists_relProj_fibre
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot Tag.F4 r) :
    ∃ β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β ∧ relProj β = r ∧
      ∀ β' : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β' →
        (relProj β' = r ↔ β' = β ∨ β' = permLattice TwistTag.E6.perm β) :=
  exists_e6ToF4_fibre hr

theorem relProj_permLattice (β : Fin TwistTag.E6.tag.rank → ℤ) :
    relProj (permLattice TwistTag.E6.perm β) = relProj β :=
  e6ToF4_permLattice β

theorem permLattice_permLattice_perm (β : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm β) = β :=
  permLattice_permLattice_rhoE6 β

theorem relProj_add (v w : Fin TwistTag.E6.tag.rank → ℤ) :
    relProj (v + w) = relProj v + relProj w :=
  e6ToF4_add v w

theorem relProj_zero : relProj 0 = 0 :=
  e6ToF4_zero

@[expose] def relProjHom : (Fin TwistTag.E6.tag.rank → ℤ) →+ (Fin Tag.F4.rank → ℤ) where
  toFun := relProj
  map_zero' := relProj_zero
  map_add' := relProj_add

theorem relProj_nsmul_add_nsmul (a b : ℕ) (v w : Fin TwistTag.E6.tag.rank → ℤ) :
    relProj (a • v + b • w) = a • relProj v + b • relProj w := by
  change relProjHom (a • v + b • w) = a • relProjHom v + b • relProjHom w
  rw [map_add, map_nsmul, map_nsmul]

theorem height_relProj (β : Fin TwistTag.E6.tag.rank → ℤ) : height (relProj β) = height β := by
  have key : ∀ γ : Fin 6 → ℤ,
      ∑ j : Fin 4, (![γ 1, γ 3, γ 2 + γ 4, γ 0 + γ 5] : Fin 4 → ℤ) j = ∑ j, γ j := by
    intro γ
    simp only [Fin.sum_univ_four, Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  exact key β

abbrev nativeReflT
    (i : Fin 4) : WeylGroup TwistTag.E6.tag :=
  nativeRefl i

theorem relProj_nativeRefl_smul
    (i : Fin 4) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    relProj (nativeReflT i • v) = simple .F4 i • relProj v :=
  e6ToF4_nativeRefl_smul i v

@[expose] def IsLift
    (w : WeylGroup .F4) (w' : WeylGroup TwistTag.E6.tag) : Prop :=
  w' ∈ relWeylTwist TwistTag.E6 ∧ ∀ v, relProj (w' • v) = w • relProj v

theorem nativeReflT_mem
    (i : Fin 4) : nativeReflT i ∈ relWeylTwist TwistTag.E6 := by
  have h := (nativeSimple i).2
  rwa [coe_nativeSimple_eq_nativeRefl] at h

theorem isLift_nativeRefl
    (i : Fin 4) : IsLift (simple .F4 i) (nativeReflT i) :=
  ⟨nativeReflT_mem i, relProj_nativeRefl_smul i⟩

theorem IsLift.mul
    {a b : WeylGroup .F4} {a' b' : WeylGroup TwistTag.E6.tag} (ha : IsLift a a')
    (hb : IsLift b b') : IsLift (a * b) (a' * b') :=
  ⟨mul_mem ha.1 hb.1, fun v => by rw [mul_smul, ha.2, hb.2, mul_smul]⟩

theorem IsLift.inv
    {a : WeylGroup .F4} {a' : WeylGroup TwistTag.E6.tag} (ha : IsLift a a') :
    IsLift a⁻¹ a'⁻¹ := by
  refine ⟨inv_mem ha.1, fun v => ?_⟩
  have h := ha.2 (a'⁻¹ • v)
  rw [smul_inv_smul] at h
  rw [h, inv_smul_smul]

theorem exists_relWeylTwist_lift
    (w : WeylGroup .F4) : ∃ w', IsLift w w' := by
  set H : Subgroup (WeylGroup .F4) :=
    { carrier := {w | ∃ w', IsLift w w'}
      one_mem' := ⟨1, one_mem _, fun v => by rw [one_smul, one_smul]⟩
      mul_mem' := by
        rintro a b ⟨a', ha⟩ ⟨b', hb⟩
        exact ⟨a' * b', ha.mul hb⟩
      inv_mem' := by
        rintro a ⟨a', ha⟩
        exact ⟨a'⁻¹, ha.inv⟩ }
  have htop : H = ⊤ := by
    rw [eq_top_iff, ← (coxeterSystem .F4).subgroup_closure_range_simple, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, isLift_nativeRefl i⟩
  exact (htop ▸ Subgroup.mem_top w : w ∈ H)

theorem diagramOrbit_eq_pair (α : Fin TwistTag.E6.tag.rank → ℤ) :
    TwistTag.E6.diagramOrbit α = {α, permLattice TwistTag.E6.perm α} := by
  have h2 : Finset.range TwistTag.E6.order = {0, 1} := by decide
  rw [TwistTag.diagramOrbit, h2, Finset.image_insert, Finset.image_singleton, pow_zero, pow_one]
  rfl

theorem relProj_eq_of_mem_diagramOrbit {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : β ∈ TwistTag.E6.diagramOrbit α) : relProj β = relProj α := by
  rw [diagramOrbit_eq_pair, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · rfl
  · exact relProj_permLattice α

@[expose] def relFibre (r : Fin Tag.F4.rank → ℤ) : Set (Fin TwistTag.E6.tag.rank → ℤ) :=
  {β | IsRoot TwistTag.E6.tag β ∧ relProj β = r}

theorem relFibre_relProj
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) :
    relFibre (relProj α) = ↑(TwistTag.E6.diagramOrbit α) := by
  obtain ⟨β, -, -, hfib⟩ := exists_relProj_fibre (isRoot_relProj hα)
  have hαβ := (hfib α hα).1 rfl
  ext γ
  rw [Finset.mem_coe, diagramOrbit_eq_pair, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hγ, hγα⟩
    rcases (hfib γ hγ).1 hγα with h | h <;> rcases hαβ with h' | h' <;> rw [h, h']
    · exact Or.inl rfl
    · exact Or.inr (permLattice_permLattice_perm β).symm
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨hα, rfl⟩
    · exact ⟨hα.permLattice TwistTag.E6.cartan_perm, relProj_permLattice α⟩

theorem relFibre_subset_isRoot (r : Fin Tag.F4.rank → ℤ) :
    ∀ β ∈ relFibre r, IsRoot TwistTag.E6.tag β :=
  fun _ hβ => hβ.1

theorem exists_relFibre_eq
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot Tag.F4 r) :
    ∃ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α ∧ relProj α = r ∧
      relFibre r = ↑(TwistTag.E6.diagramOrbit α) := by
  obtain ⟨α, hα, rfl, -⟩ := exists_relProj_fibre hr
  exact ⟨α, hα, rfl, relFibre_relProj hα⟩

@[expose] def relRoot (O : TwistTag.E6.diagramRootOrbits) : Fin Tag.F4.rank → ℤ :=
  relProj O.2.choose

theorem relRoot_eq {O : TwistTag.E6.diagramRootOrbits} {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ (O : Finset (Fin TwistTag.E6.tag.rank → ℤ))) : relRoot O = relProj β := by
  rw [← O.2.choose_spec.2] at hβ
  exact (relProj_eq_of_mem_diagramOrbit hβ).symm

theorem isRoot_relRoot
    (O : TwistTag.E6.diagramRootOrbits) : IsRoot Tag.F4 (relRoot O) :=
  isRoot_relProj O.2.choose_spec.1

theorem coe_eq_relFibre
    (O : TwistTag.E6.diagramRootOrbits) :
    ((O : Finset (Fin TwistTag.E6.tag.rank → ℤ)) : Set (Fin TwistTag.E6.tag.rank → ℤ)) =
      relFibre (relRoot O) := by
  rw [relRoot, relFibre_relProj O.2.choose_spec.1, O.2.choose_spec.2]

theorem relRoot_bijective
    : Function.Bijective fun O : TwistTag.E6.diagramRootOrbits =>
    (⟨relRoot O, isRoot_relRoot O⟩ : {r // IsRoot Tag.F4 r}) := by
  refine ⟨fun O₁ O₂ h => ?_, fun ⟨r, hr⟩ => ?_⟩
  · have h' : relRoot O₁ = relRoot O₂ := congrArg Subtype.val h
    exact Subtype.ext (Finset.coe_injective (by rw [coe_eq_relFibre, coe_eq_relFibre, h']))
  · obtain ⟨β, hβ, hβr, -⟩ := exists_relProj_fibre hr
    exact ⟨⟨TwistTag.E6.diagramOrbit β, β, hβ, rfl⟩,
      Subtype.ext ((relRoot_eq (TwistTag.E6.self_mem_diagramOrbit β)).trans hβr)⟩

theorem height_relRoot (O : TwistTag.E6.diagramRootOrbits) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ (O : Finset (Fin TwistTag.E6.tag.rank → ℤ))) : height (relRoot O) = height β := by
  rw [relRoot_eq hβ, height_relProj]

abbrev relRootGroup
    (r : Fin Tag.F4.rank → ℤ) : Subgroup (ModGL TwistTag.E6.tag K) :=
  rootSpan TwistTag.E6.tag K (relFibre r) ⊓ twistedFixedGroup TwistTag.E6 K barHom

theorem relFibre_smul
    {w : WeylGroup .F4} {w' : WeylGroup TwistTag.E6.tag} (h : IsLift w w')
    (r : Fin Tag.F4.rank → ℤ) : relFibre (w • r) = (fun β => w' • β) '' relFibre r := by
  ext γ
  constructor
  · rintro ⟨hγ, hγr⟩
    refine ⟨w'⁻¹ • γ, ⟨IsRoot.smul hγ _, ?_⟩, smul_inv_smul w' γ⟩
    have h' := h.2 (w'⁻¹ • γ)
    rw [smul_inv_smul, hγr] at h'
    exact (MulAction.injective w h').symm
  · rintro ⟨β, ⟨hβ, hβr⟩, rfl⟩
    exact ⟨IsRoot.smul hβ w', by rw [h.2, hβr]⟩

theorem map_conj_eq_of_mem {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hg hy) (inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, mul_mem (mul_mem (inv_mem hg) hx) hg, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem canonicalRep_mem_fixed
    {w' : WeylGroup TwistTag.E6.tag}
    (hw : w' ∈ relWeylTwist TwistTag.E6) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K w' ∈ twistedFixedGroup TwistTag.E6 K barHom :=
  canonicalRep_mem_twistedFixedGroup TwistTag.E6 K barHom ((mem_relWeylTwist TwistTag.E6).1 hw)

theorem canonicalRep_mem_root
    {w' : WeylGroup TwistTag.E6.tag}
    (hw : w' ∈ relWeylTwist TwistTag.E6) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K w' ∈ graphFixedRootGroup TwistTag.E6 K barHom :=
  canonicalRep_mem_graphFixedRootGroup (K := K) (σ := barHom) hw

theorem map_conj_relRootGroup
    {w : WeylGroup .F4} {w' : WeylGroup TwistTag.E6.tag}
    (h : IsLift w w') (r : Fin Tag.F4.rank → ℤ) :
    (relRootGroup r).map
        (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K w')).toMonoidHom =
      relRootGroup (w • r) := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    (canonical_weyl_root_transport TwistTag.E6.tag K).1 w' _ (relFibre_subset_isRoot r),
    ← relFibre_smul h, map_conj_eq_of_mem (canonicalRep_mem_fixed h.1)]

theorem nativeRep_mem_root
    (i : Fin 4) :
    nativeRep i ∈ graphFixedRootGroup TwistTag.E6 K barHom :=
  canonicalRep_mem_root (isLift_nativeRefl i).1

theorem map_conj_nativeRep_relRootGroup
    (i : Fin 4) (r : Fin Tag.F4.rank → ℤ) :
    (relRootGroup r).map (MulAut.conj (nativeRep i)).toMonoidHom =
      relRootGroup (simple .F4 i • r) :=
  map_conj_relRootGroup (isLift_nativeRefl i) r

theorem card_diagramOrbit_eq_one_iff : ∀ k : Fin 72,
    ((TwistTag.E6.diagramOrbit (e6Root k)).card = 1 ↔
      f4Euclid (relProj (e6Root k)) ⬝ᵥ f4Euclid (relProj (e6Root k)) = 2) := by
  decide +kernel

theorem card_relRootGroup
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot Tag.F4 r) :
    Nat.card (relRootGroup r) = if f4Euclid r ⬝ᵥ f4Euclid r = 2 then 2 else 4 := by
  obtain ⟨α, hα, rfl, hfib⟩ := exists_relFibre_eq hr
  obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
  have h := card_rootSpan_orbit (⟨e6Root k, isRoot_e6Root k, rfl⟩ :
    TwistTag.E6.diagramOrbit (e6Root k) ∈ TwistTag.E6.diagramRootOrbits)
  rw [relRootGroup, hfib, h]
  exact if_congr (card_diagramOrbit_eq_one_iff k) rfl rfl

theorem comm_and_mul_self_of_mulEquiv {M L : Type*} [Group M] [AddCommGroup L]
    (e : Multiplicative L ≃* M) (h2 : ∀ c : L, c + c = 0) :
    (∀ x y : M, x * y = y * x) ∧ ∀ x : M, x * x = 1 := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · obtain ⟨c, rfl⟩ := e.surjective x
    obtain ⟨d, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨c, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_one e]
    congr 1
    exact Multiplicative.toAdd.injective (h2 (Multiplicative.toAdd c))

theorem relRootGroup_elementary
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot Tag.F4 r) :
    (∀ x ∈ relRootGroup r, ∀ y ∈ relRootGroup r, x * y = y * x) ∧
      ∀ x ∈ relRootGroup r, x * x = 1 := by
  obtain ⟨α, hα, rfl, hfib⟩ := exists_relFibre_eq hr
  obtain ⟨w, hw, a, hOa, -, -⟩ := (diagram_root_orbit_reduction TwistTag.E6).1 α hα
  have hset : relRootGroup (relProj α) = rootSpan TwistTag.E6.tag K
      ((fun i => w • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) '' ↑(TwistTag.E6.orbit a)) ⊓
        twistedFixedGroup TwistTag.E6 K barHom := by
    rw [relRootGroup, hfib, hOa, Finset.coe_image]
  have hK : ∀ c : K, c + c = 0 := fun c => CharTwo.add_self_eq_zero c
  obtain ⟨hcomm, hsq⟩ := comm_and_mul_self_of_mulEquiv (orbitConjEquiv TwistTag.E6 barHom a hw)
    fun c => Subtype.ext (hK c)
  rw [hset]
  exact ⟨fun x hx y hy => congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩),
    fun x hx => congrArg Subtype.val (hsq ⟨x, hx⟩)⟩

theorem relFibre_finite
    (r : Fin Tag.F4.rank → ℤ) : (relFibre r).Finite :=
  (finite_setOf_isRoot TwistTag.E6.tag).subset (relFibre_subset_isRoot r)

theorem relProj_eq_of_mem_relFibre {r : Fin Tag.F4.rank → ℤ} {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ relFibre r) : relProj β = r :=
  hβ.2

theorem bijOn_prod_congr {M : Type*} [Group M] {k : ℕ} {A B : Fin k → Subgroup M} (h : A = B)
    {T : Set M} (hA : Set.BijOn (fun u : (j : Fin k) → A j => (List.ofFn fun j => (u j : M)).prod)
      Set.univ T) :
    Set.BijOn (fun u : (j : Fin k) → B j => (List.ofFn fun j => (u j : M)).prod) Set.univ T := by
  subst h
  exact hA

theorem bijOn_prod_relRootGroup
    {k : ℕ} (e : Fin k → Fin Tag.F4.rank → ℤ)
    (he : Function.Injective e) (hrange : Set.range e = {r | IsRoot Tag.F4 r ∧ 0 < height r}) :
    Set.BijOn (fun u : (j : Fin k) → relRootGroup (e j) =>
        (List.ofFn fun j => (u j : ModGL TwistTag.E6.tag K)).prod)
      Set.univ (graphFixedPosUnipotent TwistTag.E6 K barHom) := by
  have hpos : ∀ j, IsRoot Tag.F4 (e j) ∧ 0 < height (e j) := fun j => by
    have h : e j ∈ Set.range e := Set.mem_range_self j
    rw [hrange] at h
    exact h
  obtain ⟨O, hO⟩ : ∃ O : Fin k → Finset (Fin TwistTag.E6.tag.rank → ℤ),
      ∀ j, (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) = relFibre (e j) :=
    ⟨fun j => (relFibre_finite (e j)).toFinset, fun j => Set.Finite.coe_toFinset _⟩
  have hOinj : Function.Injective O := by
    intro i j hij
    obtain ⟨β, hβ, hβr, -⟩ := exists_relProj_fibre (hpos i).1
    have hmem : β ∈ relFibre (e i) := ⟨hβ, hβr⟩
    rw [← hO i, hij, hO j] at hmem
    exact he (hβr.symm.trans hmem.2)
  have hOrange : Set.range O = {O' | O' ∈ TwistTag.E6.diagramRootOrbits ∧
      (O' : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ posRootSet} := by
    ext O'
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨α, hα, hαr, hfib⟩ := exists_relFibre_eq (hpos j).1
      refine ⟨⟨α, hα, Finset.coe_injective ((hfib.symm.trans (hO j).symm))⟩, fun β hβ => ?_⟩
      rw [hO j] at hβ
      refine ⟨hβ.1, ?_⟩
      rw [← height_relProj, hβ.2]
      exact (hpos j).2
    · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
      have hαpos := (hsub (TwistTag.E6.self_mem_diagramOrbit α)).2
      have hr : relProj α ∈ Set.range e := by
        rw [hrange]
        exact ⟨isRoot_relProj hα, by rw [height_relProj]; exact hαpos⟩
      obtain ⟨j, hj⟩ := hr
      exact ⟨j, Finset.coe_injective (by rw [hO j, hj, relFibre_relProj hα])⟩
  have hbij := bijOn_prod_graphFixed (t := TwistTag.E6) (K := K) barHom_surjective
    (fun α hα => hα) posRootSet_perm posRootSet_closed O hOinj hOrange
  have hfam : (fun j => rootSpan TwistTag.E6.tag K (O j : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊓
      twistedFixedGroup TwistTag.E6 K barHom) = fun j => relRootGroup (e j) :=
    funext fun j => by rw [hO j]
  exact bijOn_prod_congr hfam hbij

theorem card_graphFixedPosUnipotent :
    Nat.card (graphFixedPosUnipotent TwistTag.E6 K barHom) = 2 ^ 36 :=
  card_stdUnipotent0

theorem ncard_posRoots_long :
    {r : Fin Tag.F4.rank → ℤ | IsRoot .F4 r ∧ 0 < height r ∧
      f4Euclid r ⬝ᵥ f4Euclid r = 2}.ncard = 12 := by
  have hS : {r : Fin Tag.F4.rank → ℤ | IsRoot .F4 r ∧ 0 < height r ∧
      f4Euclid r ⬝ᵥ f4Euclid r = 2} = (fun k : Fin 48 => Tag.F4.rootCertificate.root k) ''
        ↑((Finset.univ : Finset (Fin 48)).filter fun k : Fin 48 =>
          0 < height (Tag.F4.rootCertificate.root k) ∧
            f4Euclid (Tag.F4.rootCertificate.root k) ⬝ᵥ
              f4Euclid (Tag.F4.rootCertificate.root k) = 2) := by
    ext v
    constructor
    · rintro ⟨hv, hh, hl⟩
      obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hv
      exact ⟨k, by simpa using ⟨hh, hl⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨isRoot_f4_iff.2 ⟨k, rfl⟩, by simpa using hk⟩
  rw [hS, Set.ncard_image_of_injective _ f4_rootCertificate_root_injective, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_posRoots_short :
    {r : Fin Tag.F4.rank → ℤ | IsRoot .F4 r ∧ 0 < height r ∧
      f4Euclid r ⬝ᵥ f4Euclid r = 1}.ncard = 12 := by
  have hS : {r : Fin Tag.F4.rank → ℤ | IsRoot .F4 r ∧ 0 < height r ∧
      f4Euclid r ⬝ᵥ f4Euclid r = 1} = (fun k : Fin 48 => Tag.F4.rootCertificate.root k) ''
        ↑((Finset.univ : Finset (Fin 48)).filter fun k : Fin 48 =>
          0 < height (Tag.F4.rootCertificate.root k) ∧
            f4Euclid (Tag.F4.rootCertificate.root k) ⬝ᵥ
              f4Euclid (Tag.F4.rootCertificate.root k) = 1) := by
    ext v
    constructor
    · rintro ⟨hv, hh, hl⟩
      obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hv
      exact ⟨k, by simpa using ⟨hh, hl⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨isRoot_f4_iff.2 ⟨k, rfl⟩, by simpa using hk⟩
  rw [hS, Set.ncard_image_of_injective _ f4_rootCertificate_root_injective, Set.ncard_coe_finset]
  decide +kernel

end CFSG.LieType.Chevalley.C2E6Std.RelativeRoots
