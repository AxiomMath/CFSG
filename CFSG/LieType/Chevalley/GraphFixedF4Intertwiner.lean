module

public import CFSG.LieType.Chevalley.RootOps.Cert.E6Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.E6Tab
public import CFSG.LieType.Chevalley.RootOps.Cert.F4Simple
public import CFSG.LieType.Chevalley.RootOps.Cert.F4Tab

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley.RootWalk
open CFSG.LieType.Ree (vecBEq vecBEq_iff)

@[expose] def e6ToF4 (β : Fin Tag.E6.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  (![β ⟨1, by decide⟩, β ⟨3, by decide⟩, β ⟨2, by decide⟩ + β ⟨4, by decide⟩,
    β ⟨0, by decide⟩ + β ⟨5, by decide⟩] : Fin 4 → ℤ)

@[expose] def f4IndexOrbit : Fin Tag.F4.rank → List (Fin Tag.E6.rank) :=
  (![[⟨1, by decide⟩], [⟨3, by decide⟩], [⟨2, by decide⟩, ⟨4, by decide⟩],
    [⟨0, by decide⟩, ⟨5, by decide⟩]] : Fin 4 → List (Fin Tag.E6.rank))

@[expose] def e6IndexToF4 : Fin Tag.E6.rank → Fin Tag.F4.rank :=
  (![⟨3, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
    ⟨3, by decide⟩] : Fin 6 → Fin Tag.F4.rank)

@[expose] def f4IndexRep : Fin Tag.F4.rank → Fin Tag.E6.rank :=
  (![⟨1, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩] : Fin 4 → Fin Tag.E6.rank)

@[expose] def rhoE6 : Equiv.Perm (Fin Tag.E6.rank) :=
  TwistTag.E6.perm

@[expose] def e6LabelPerm : Label Tag.E6 ≃ Label Tag.E6 :=
  labelPerm TwistTag.E6.perm TwistTag.E6.cartan_perm

@[expose] def e6DiagramEnd (K : Type*) [Field K] : Module.End K (RootModule Tag.E6 K) :=
  (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))

theorem e6DiagramEnd_apply {K : Type*} [Field K] (v : RootModule Tag.E6 K) (b : Label Tag.E6) :
    e6DiagramEnd K v b = v (e6LabelPerm.symm b) :=
  Finsupp.equivMapDomain_apply _ _ _

theorem mem_f4IndexOrbit_iff (i : Fin Tag.E6.rank) (j : Fin Tag.F4.rank) :
    i ∈ f4IndexOrbit j ↔ e6IndexToF4 i = j := by
  revert i j
  decide

theorem nodup_f4IndexOrbit (j : Fin Tag.F4.rank) : (f4IndexOrbit j).Nodup := by
  revert j
  decide

theorem e6IndexToF4_f4IndexRep (j : Fin Tag.F4.rank) : e6IndexToF4 (f4IndexRep j) = j := by
  revert j
  decide

theorem f4IndexRep_e6IndexToF4 (i : Fin Tag.E6.rank) :
    f4IndexRep (e6IndexToF4 i) = i ∨ f4IndexRep (e6IndexToF4 i) = rhoE6 i := by
  revert i
  decide

theorem e6IndexToF4_rhoE6 (i : Fin Tag.E6.rank) : e6IndexToF4 (rhoE6 i) = e6IndexToF4 i := by
  revert i
  decide

theorem e6ToF4_permLattice (β : Fin Tag.E6.rank → ℤ) :
    e6ToF4 (permLattice rhoE6 β) = e6ToF4 β := by
  have h0 : rhoE6.symm ⟨0, by decide⟩ = ⟨5, by decide⟩ := by decide
  have h1 : rhoE6.symm ⟨1, by decide⟩ = ⟨1, by decide⟩ := by decide
  have h2 : rhoE6.symm ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  have h3 : rhoE6.symm ⟨3, by decide⟩ = ⟨3, by decide⟩ := by decide
  have h4 : rhoE6.symm ⟨4, by decide⟩ = ⟨2, by decide⟩ := by decide
  have h5 : rhoE6.symm ⟨5, by decide⟩ = ⟨0, by decide⟩ := by decide
  funext j
  fin_cases j
  · show β (rhoE6.symm ⟨1, by decide⟩) = β ⟨1, by decide⟩
    rw [h1]
  · show β (rhoE6.symm ⟨3, by decide⟩) = β ⟨3, by decide⟩
    rw [h3]
  · show β (rhoE6.symm ⟨2, by decide⟩) + β (rhoE6.symm ⟨4, by decide⟩) =
      β ⟨2, by decide⟩ + β ⟨4, by decide⟩
    rw [h2, h4]
    exact add_comm _ _
  · show β (rhoE6.symm ⟨0, by decide⟩) + β (rhoE6.symm ⟨5, by decide⟩) =
      β ⟨0, by decide⟩ + β ⟨5, by decide⟩
    rw [h0, h5]
    exact add_comm _ _

theorem permLattice_permLattice_rhoE6 (β : Fin Tag.E6.rank → ℤ) :
    permLattice rhoE6 (permLattice rhoE6 β) = β := by
  have h : ∀ i, rhoE6.symm (rhoE6.symm i) = i := by decide
  funext i
  show β (rhoE6.symm (rhoE6.symm i)) = β i
  rw [h]

@[expose] def e6ToF4Check : Bool :=
  (List.range Tag.E6.rootCertificate.roots.length).all fun k =>
    (List.range Tag.F4.rootCertificate.roots.length).any fun m =>
      vecBEq (Tag.F4.rootCertificate.root m) (e6ToF4 (Tag.E6.rootCertificate.root k))

theorem e6ToF4Check_eq_true : e6ToF4Check = true := by decide +kernel

@[expose] def e6ToF4FibreCheck : Bool :=
  (List.range Tag.F4.rootCertificate.roots.length).all fun m =>
    (List.range Tag.E6.rootCertificate.roots.length).any fun k =>
      vecBEq (e6ToF4 (Tag.E6.rootCertificate.root k)) (Tag.F4.rootCertificate.root m) &&
        (List.range Tag.E6.rootCertificate.roots.length).all fun k' =>
          vecBEq (e6ToF4 (Tag.E6.rootCertificate.root k')) (Tag.F4.rootCertificate.root m) ==
            (vecBEq (Tag.E6.rootCertificate.root k') (Tag.E6.rootCertificate.root k) ||
              vecBEq (Tag.E6.rootCertificate.root k')
                (permLattice rhoE6 (Tag.E6.rootCertificate.root k)))

theorem e6ToF4FibreCheck_eq_true : e6ToF4FibreCheck = true := by decide +kernel

theorem isRoot_e6ToF4
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) :
    IsRoot Tag.F4 (e6ToF4 β) := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ
  have h := e6ToF4Check_eq_true
  simp only [e6ToF4Check, List.all_eq_true, List.mem_range, List.any_eq_true] at h
  obtain ⟨m, hm, hmk⟩ := h k hk
  rw [← vecBEq_iff.1 hmk]
  exact isRoot_rootCertificate_root hm

theorem exists_e6ToF4_fibre
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α) :
    ∃ β, IsRoot Tag.E6 β ∧ e6ToF4 β = α ∧ ∀ β', IsRoot Tag.E6 β' →
      (e6ToF4 β' = α ↔ β' = β ∨ β' = permLattice rhoE6 β) := by
  obtain ⟨m, hm, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h := e6ToF4FibreCheck_eq_true
  simp only [e6ToF4FibreCheck, List.all_eq_true, List.mem_range, List.any_eq_true,
    Bool.and_eq_true] at h
  obtain ⟨k, hk, hkm, hall⟩ := h m hm
  refine ⟨_, isRoot_rootCertificate_root hk, vecBEq_iff.1 hkm, fun β' hβ' => ?_⟩
  obtain ⟨k', hk', rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hβ'
  have h' := beq_iff_eq.1 (hall k' hk')
  rw [← vecBEq_iff (u := e6ToF4 (Tag.E6.rootCertificate.root k')),
    ← vecBEq_iff (u := Tag.E6.rootCertificate.root k') (v := Tag.E6.rootCertificate.root k),
    ← vecBEq_iff (u := Tag.E6.rootCertificate.root k'), h', Bool.or_eq_true]

variable (K : Type*) [CommRing K]

@[expose] def f4ToE6Module : RootModule Tag.F4 K →ₗ[K] RootModule Tag.E6 K :=
  Finsupp.linearCombination K fun b => match b with
    | .inl j => ((f4IndexOrbit j).map fun i => hVec Tag.E6 K i).sum
    | .inr α => ∑ β ∈ (rootFinset Tag.E6).filter (fun β => e6ToF4 β = α.1), rootVec Tag.E6 K β

@[expose] def f4OrbitX (j : Fin Tag.F4.rank) (c : K) : Module.End K (RootModule Tag.E6 K) :=
  ((f4IndexOrbit j).map fun i => xOp Tag.E6 K i c).prod

@[expose] def f4OrbitY (j : Fin Tag.F4.rank) (c : K) : Module.End K (RootModule Tag.E6 K) :=
  ((f4IndexOrbit j).map fun i => yOp Tag.E6 K i c).prod

@[expose] def e6LabelToF4
    : Label Tag.E6 → Label Tag.F4
  | .inl i => .inl (e6IndexToF4 i)
  | .inr β => .inr ⟨e6ToF4 β.1, isRoot_e6ToF4 β.2⟩

@[expose] def f4LabelRep
    : Label Tag.F4 → Label Tag.E6
  | .inl j => .inl (f4IndexRep j)
  | .inr α => .inr ⟨(exists_e6ToF4_fibre α.2).choose, (exists_e6ToF4_fibre α.2).choose_spec.1⟩

theorem e6LabelToF4_f4LabelRep
    (a : Label Tag.F4) : e6LabelToF4 (f4LabelRep a) = a := by
  rcases a with j | α
  · exact congrArg Sum.inl (e6IndexToF4_f4IndexRep j)
  · exact congrArg Sum.inr (Subtype.ext (exists_e6ToF4_fibre α.2).choose_spec.2.1)

theorem e6LabelToF4_e6LabelPerm
    (b : Label Tag.E6) :
    e6LabelToF4 (e6LabelPerm b) = e6LabelToF4 b := by
  rcases b with i | β
  · exact congrArg Sum.inl (e6IndexToF4_rhoE6 i)
  · exact congrArg Sum.inr (Subtype.ext (e6ToF4_permLattice β.1))

theorem f4LabelRep_e6LabelToF4
    (b : Label Tag.E6) :
    f4LabelRep (e6LabelToF4 b) = b ∨ f4LabelRep (e6LabelToF4 b) = e6LabelPerm b := by
  rcases b with i | ⟨β, hβ⟩
  · rcases f4IndexRep_e6IndexToF4 i with h | h
    · exact Or.inl (congrArg Sum.inl h)
    · exact Or.inr (congrArg Sum.inl h)
  · have hspec := (exists_e6ToF4_fibre (isRoot_e6ToF4 hβ)).choose_spec
    rcases (hspec.2.2 β hβ).1 rfl with h | h
    · exact Or.inl (congrArg Sum.inr (Subtype.ext h.symm))
    · refine Or.inr (congrArg Sum.inr (Subtype.ext ?_))
      change _ = permLattice rhoE6 β
      exact (permLattice_permLattice_rhoE6 _).symm.trans (congrArg _ h.symm)

theorem hVec_apply_eq {τ : Tag} {R : Type*} [CommRing R] (i : Fin τ.rank) (b : Label τ) :
    hVec τ R i b = if b = .inl i then 1 else 0 := by
  rw [hVec, Finsupp.single_apply]
  simp only [eq_comm]

theorem rootVec_apply_inl {τ : Tag} {R : Type*} [CommRing R] (β : Fin τ.rank → ℤ)
    (i : Fin τ.rank) : rootVec τ R β (.inl i) = 0 := by
  unfold rootVec
  split_ifs
  · simp
  · rfl

theorem rootVec_apply_inr {τ : Tag} {R : Type*} [CommRing R] (β : Fin τ.rank → ℤ)
    (γ : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    rootVec τ R β (.inr γ) = if γ.1 = β then 1 else 0 := by
  unfold rootVec
  split_ifs with hβ hγ hγ
  · subst hγ
    simp
  · have hne : (Sum.inr ⟨β, hβ⟩ : Label τ) ≠ Sum.inr γ := fun h =>
      hγ (congrArg Subtype.val (Sum.inr.inj h)).symm
    simp [hne]
  · exact absurd (hγ ▸ γ.2) hβ
  · rfl

theorem f4ToE6Module_single
    (a : Label Tag.F4) (b : Label Tag.E6) :
    f4ToE6Module K (Finsupp.single a 1) b = if e6LabelToF4 b = a then 1 else 0 := by
  rw [f4ToE6Module, Finsupp.linearCombination_single, one_smul]
  rcases a with j | ⟨α, hα⟩
  · simp only
    rw [← List.sum_toFinset _ (nodup_f4IndexOrbit j), Finsupp.finsetSum_apply]
    simp only [hVec_apply_eq]
    rcases b with i | β
    · simp only [Sum.inl.injEq, Finset.sum_ite_eq, List.mem_toFinset, mem_f4IndexOrbit_iff,
        e6LabelToF4]
    · simp [e6LabelToF4]
  · simp only
    rw [Finsupp.finsetSum_apply]
    rcases b with i | ⟨β, hβ⟩
    · simp [rootVec_apply_inl, e6LabelToF4]
    · simp only [rootVec_apply_inr, Finset.sum_ite_eq, Finset.mem_filter, mem_rootFinset.2 hβ,
        true_and, e6LabelToF4, Sum.inr.injEq, Subtype.mk.injEq]

theorem f4ToE6Module_apply
    (w : RootModule Tag.F4 K) (b : Label Tag.E6) :
    f4ToE6Module K w b = w (e6LabelToF4 b) := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add w w' hw hw' => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hw, hw']
  | single a r =>
    rw [← mul_one r, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Finsupp.smul_apply,
      f4ToE6Module_single, Finsupp.smul_apply, Finsupp.single_apply]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, eq_comm]

theorem f4ToE6Module_injective
    : Function.Injective (f4ToE6Module K) := by
  intro w w' h
  ext a
  have := congrArg (fun v => v (f4LabelRep a)) h
  simp only [f4ToE6Module_apply, e6LabelToF4_f4LabelRep] at this
  exact this

@[expose] def e6GraphFixedModule (K : Type*) [Field K] : Submodule K (RootModule Tag.E6 K) :=
  LinearMap.eqLocus (e6DiagramEnd K) LinearMap.id

theorem mem_e6GraphFixedModule {K : Type*} [Field K] {v : RootModule Tag.E6 K} :
    v ∈ e6GraphFixedModule K ↔ e6DiagramEnd K v = v :=
  LinearMap.mem_eqLocus

theorem range_f4ToE6Module
    (K : Type*) [Field K] :
    LinearMap.range (f4ToE6Module K) = e6GraphFixedModule K := by
  ext v
  rw [LinearMap.mem_range, mem_e6GraphFixedModule]
  constructor
  · rintro ⟨w, rfl⟩
    ext b
    rw [e6DiagramEnd_apply, f4ToE6Module_apply, f4ToE6Module_apply]
    have h := e6LabelToF4_e6LabelPerm (e6LabelPerm.symm b)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
  · intro hv
    have hv' : ∀ b, v (e6LabelPerm b) = v b := fun b => by
      have h := congrArg (fun u : RootModule Tag.E6 K => u (e6LabelPerm b)) hv
      simp only [e6DiagramEnd_apply, Equiv.symm_apply_apply] at h
      exact h.symm
    refine ⟨Finsupp.equivFunOnFinite.symm fun a => v (f4LabelRep a), ?_⟩
    ext b
    rw [f4ToE6Module_apply]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rcases f4LabelRep_e6LabelToF4 b with h | h
    · rw [h]
    · rw [h, hv']

theorem list_sum_map_filter {α M : Type*} [AddCommMonoid M] (l : List α) (p : α → Bool)
    (f : α → M) : ((l.filter p).map f).sum = (l.map fun x => if p x then f x else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

@[expose] def f4ToE6Pos (p : ℕ) : List (ℕ × ℤ) :=
  if h : p < Tag.F4.rank then (f4IndexOrbit ⟨p, h⟩).map fun i : Fin Tag.E6.rank => (i.val, 1)
  else ((List.range Tag.E6.rootCertificate.roots.length).filter fun k =>
      vecBEq (e6ToF4 (Tag.E6.rootCertificate.root k))
        (Tag.F4.rootCertificate.root (p - Tag.F4.rank))).map fun k => (Tag.E6.rank + k, 1)

theorem validVec_f4ToE6Pos (p : ℕ) : ValidVec Tag.E6 (f4ToE6Pos p) := by
  intro x hx
  unfold f4ToE6Pos at hx
  split_ifs at hx with h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    have := i.2
    simp only [dim]
    omega
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 (List.mem_filter.1 hk).1
    simp only [dim]
    omega

theorem f4ToE6Module_posVec
    {p : ℕ} (hp : p < dim Tag.F4) :
    f4ToE6Module K (posVec Tag.F4 K p) = vecOf Tag.E6 K (f4ToE6Pos p) := by
  unfold posVec f4ToE6Pos
  split_ifs with h
  · rw [hVec, f4ToE6Module, Finsupp.linearCombination_single, one_smul]
    simp only [vecOf, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp [posVec, i.2]
  · have hm : p - Tag.F4.rank < Tag.F4.rootCertificate.roots.length := by
      simp only [dim] at hp
      omega
    rw [CFSG.LieType.Ree.rootVec_eq_single K (isRoot_rootCertificate_root hm), f4ToE6Module,
      Finsupp.linearCombination_single, one_smul]
    simp only [vecOf, List.map_map]
    have hnd : ((List.range Tag.E6.rootCertificate.roots.length).map
        Tag.E6.rootCertificate.root).Nodup :=
      (List.nodup_range).map_on fun x hx y hy hxy =>
        rootCertificate_root_injOn (List.mem_range.1 hx) (List.mem_range.1 hy) hxy
    rw [list_sum_map_filter, Finset.sum_filter, rootFinset, List.sum_toFinset _ hnd, List.map_map]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply]
    by_cases hk : e6ToF4 (Tag.E6.rootCertificate.root k) =
        Tag.F4.rootCertificate.root (p - Tag.F4.rank)
    · rw [ite_eq_left hk, ite_eq_left (vecBEq_iff.2 hk)]
      simp [posVec]
    · rw [ite_eq_right hk, ite_eq_right fun h => hk (vecBEq_iff.1 h)]

@[expose] def f4ToE6Vec (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  v.flatMap fun x => (f4ToE6Pos x.1).map fun y => (y.1, x.2 * y.2)

theorem f4ToE6Module_vecOf
    {v : List (ℕ × ℤ)} (hv : ValidVec Tag.F4 v) :
    f4ToE6Module K (vecOf Tag.F4 K v) = vecOf Tag.E6 K (f4ToE6Vec v) := by
  induction v with
  | nil => simp [f4ToE6Vec]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, f4ToE6Module_posVec K (hv x (List.mem_cons_self ..)),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [f4ToE6Vec, List.flatMap_cons, vecOf_append, vecOf_map_mul]

theorem validVec_f4ToE6Vec (v : List (ℕ × ℤ)) : ValidVec Tag.E6 (f4ToE6Vec v) := by
  intro x hx
  obtain ⟨y, -, hy⟩ := List.mem_flatMap.1 hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  exact validVec_f4ToE6Pos _ z hz

@[expose] def simplePos (τ : Tag) (y : Bool) (i : Fin τ.rank) : ℕ :=
  if y then τ.rootCertificate.image i i else i

@[expose] def coeffVec (τ : Tag) (y : Bool) (i : Fin τ.rank) (k : ℕ) (v : List (ℕ × ℤ)) :
    List (ℕ × ℤ) :=
  if k = 0 then v else applyL (entries τ (simplePos τ y i) k) v

@[expose] def coeffOp (τ : Tag) (R : Type) [CommRing R] (y : Bool) (i : Fin τ.rank) (k : ℕ) :
    Module.End R (RootModule τ R) :=
  if y then yCoeff τ R i k else xCoeff τ R i k

theorem validVec_applyL
    {τ : Tag} {L : List Entry} (hL : ValidEntries τ L) (v : List (ℕ × ℤ)) :
    ValidVec τ (applyL L v) := by
  intro x hx
  obtain ⟨y, -, hy⟩ := List.mem_flatMap.1 hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  exact hL.colOf _ z hz

theorem coeffOp_vecOf
    {τ : Tag} (hsimple : ∀ j, simpleRow τ j = true)
    (hvalid : allValid τ = true) (R : Type) [CommRing R] (y : Bool) (i : Fin τ.rank) {k : ℕ}
    (hk : k < 4) {v : List (ℕ × ℤ)} (hv : ValidVec τ v) :
    coeffOp τ R y i k (vecOf τ R v) = vecOf τ R (coeffVec τ y i k v) ∧
      ValidVec τ (coeffVec τ y i k v) := by
  by_cases h0 : k = 0
  · subst h0
    cases y <;> simp [coeffOp, coeffVec, xCoeff_zero, yCoeff_zero, hv]
  have h1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 h0
  have h3 : k ≤ 3 := by omega
  have hi : (i : ℕ) < τ.rootCertificate.roots.length :=
    lt_of_lt_of_le i.2 rootCertificate_basis_table.1
  have hpos : simplePos τ y i < τ.rootCertificate.roots.length := by
    cases y
    · exact hi
    · exact rootCertificate_image_lt hi i
  have hL := validEntries_of_validB (validB_of_allValid hvalid hpos (mem_one_two_three h1 h3))
  have hop : coeffOp τ R y i k = entriesOp τ R (entries τ (simplePos τ y i) k) := by
    cases y
    · exact (entriesOp_eq_xCoeff (simpleRow_spec (hsimple i) h1 h3).1).symm
    · exact (entriesOp_eq_yCoeff (simpleRow_spec (hsimple i) h1 h3).2).symm
  simp only [coeffVec, h0, ↓reduceIte]
  exact ⟨by rw [hop, entriesOp_vecOf _ hv], validVec_applyL hL _⟩

theorem simpleRow_E6
    (j : Fin Tag.E6.rank) : simpleRow .E6 j = true := by
  fin_cases j
  exacts [e6_simpleRow_0, e6_simpleRow_1, e6_simpleRow_2, e6_simpleRow_3, e6_simpleRow_4,
    e6_simpleRow_5]

theorem simpleRow_F4
    (j : Fin Tag.F4.rank) : simpleRow .F4 j = true := by
  fin_cases j
  exacts [f4_simpleRow_0, f4_simpleRow_1, f4_simpleRow_2, f4_simpleRow_3]

@[expose] def normalizeTwo (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  ((normalize v).map fun x => (x.1, x.2 % 2)).filter fun x => x.2 != 0

theorem vecOf_map_emod_two
    {τ : Tag} {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    (v : List (ℕ × ℤ)) : vecOf τ R (v.map fun x => (x.1, x.2 % 2)) = vecOf τ R v := by
  induction v with
  | nil => rfl
  | cons x v ih =>
    rw [List.map_cons, vecOf_cons, vecOf_cons, ih]
    congr 2
    have e := Int.emod_add_mul_ediv x.2 2
    conv_rhs => rw [← e]
    push_cast
    rw [h2, zero_mul, add_zero]

theorem vecOf_eq_of_normalizeTwo_eq
    {τ : Tag} {R : Type*} [CommRing R] (h2 : (2 : R) = 0)
    {v w : List (ℕ × ℤ)} (h : normalizeTwo v = normalizeTwo w) : vecOf τ R v = vecOf τ R w := by
  have e : ∀ u, vecOf τ R (normalizeTwo u) = vecOf τ R u := fun u => by
    rw [normalizeTwo, vecOf_filter_ne_zero, vecOf_map_emod_two h2, vecOf_normalize]
  rw [← e v, h, e w]

@[expose] def orbitLhs (y : Bool) (I : List (Fin Tag.E6.rank)) (n p : ℕ) : List (ℕ × ℤ) :=
  match I with
  | [i] => if n < 4 then coeffVec .E6 y i n (f4ToE6Pos p) else []
  | [i, i'] => (List.range 4).flatMap fun k =>
      if k ≤ n ∧ n - k < 4 then coeffVec .E6 y i k (coeffVec .E6 y i' (n - k) (f4ToE6Pos p))
      else []
  | _ => []

@[expose] def orbitRhs (y : Bool) (j : Fin Tag.F4.rank) (n p : ℕ) : List (ℕ × ℤ) :=
  if n < 4 then f4ToE6Vec (coeffVec .F4 y j n [(p, 1)]) else []

@[expose] def intertwinerCheck (y : Bool) (I : List (Fin Tag.E6.rank)) (j : Fin Tag.F4.rank) :
    Bool :=
  (List.range (dim Tag.F4)).all fun p => (List.range 7).all fun n =>
    normalizeTwo (orbitLhs y I n p) == normalizeTwo (orbitRhs y j n p)

theorem intertwinerCheck_x0 :
    intertwinerCheck false [⟨1, by decide⟩] ⟨0, by decide⟩ = true := by decide +kernel

theorem intertwinerCheck_x1 :
    intertwinerCheck false [⟨3, by decide⟩] ⟨1, by decide⟩ = true := by decide +kernel

theorem intertwinerCheck_x2 :
    intertwinerCheck false [⟨2, by decide⟩, ⟨4, by decide⟩] ⟨2, by decide⟩ = true := by
  decide +kernel

theorem intertwinerCheck_x3 :
    intertwinerCheck false [⟨0, by decide⟩, ⟨5, by decide⟩] ⟨3, by decide⟩ = true := by
  decide +kernel

theorem intertwinerCheck_y0 :
    intertwinerCheck true [⟨1, by decide⟩] ⟨0, by decide⟩ = true := by decide +kernel

theorem intertwinerCheck_y1 :
    intertwinerCheck true [⟨3, by decide⟩] ⟨1, by decide⟩ = true := by decide +kernel

theorem intertwinerCheck_y2 :
    intertwinerCheck true [⟨2, by decide⟩, ⟨4, by decide⟩] ⟨2, by decide⟩ = true := by
  decide +kernel

theorem intertwinerCheck_y3 :
    intertwinerCheck true [⟨0, by decide⟩, ⟨5, by decide⟩] ⟨3, by decide⟩ = true := by
  decide +kernel

theorem vecOf_flatMap_range
    {τ : Tag} {R : Type*} [CommRing R] (m : ℕ)
    (f : ℕ → List (ℕ × ℤ)) :
    vecOf τ R ((List.range m).flatMap f) = ∑ k ∈ Finset.range m, vecOf τ R (f k) := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.range_succ, List.flatMap_append, vecOf_append, ih,
      Finset.sum_range_succ, List.flatMap_singleton]

theorem ext_posVec_F4
    {f g : RootModule Tag.F4 K →ₗ[K] RootModule Tag.E6 K}
    (h : ∀ p, p < dim Tag.F4 → f (posVec Tag.F4 K p) = g (posVec Tag.F4 K p)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
  simpa [posVec_eq_single hp] using h p hp

theorem posVec_eq_vecOf_single
    {τ : Tag} {R : Type*} [CommRing R] (p : ℕ) :
    posVec τ R p = vecOf τ R [(p, 1)] := by
  simp

theorem validVec_single {τ : Tag} {p : ℕ} (hp : p < dim τ) : ValidVec τ [(p, 1)] := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  exact hp

theorem f4ToE6Module_coeffOp
    (K : Type) [CommRing K] (y : Bool) (j : Fin Tag.F4.rank) {n p : ℕ}
    (hn : n < 4) (hp : p < dim Tag.F4) :
    f4ToE6Module K (coeffOp Tag.F4 K y j n (posVec Tag.F4 K p)) =
      vecOf Tag.E6 K (f4ToE6Vec (coeffVec .F4 y j n [(p, 1)])) := by
  obtain ⟨e, hv⟩ := coeffOp_vecOf simpleRow_F4 f4_allValid K y j hn (validVec_single hp)
  rw [posVec_eq_vecOf_single, e, f4ToE6Module_vecOf K hv]

theorem coeffOp_comp_of_check_single
    (K : Type) [CommRing K] (h2 : (2 : K) = 0) {y : Bool}
    {i : Fin Tag.E6.rank} {j : Fin Tag.F4.rank} (h : intertwinerCheck y [i] j = true) {n : ℕ}
    (hn : n < 4) :
    coeffOp Tag.E6 K y i n ∘ₗ f4ToE6Module K = f4ToE6Module K ∘ₗ coeffOp Tag.F4 K y j n := by
  simp only [intertwinerCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ext_posVec_F4 K fun p hp => ?_
  have e := vecOf_eq_of_normalizeTwo_eq (τ := Tag.E6) (R := K) h2 (h p hp n (by omega))
  simp only [orbitLhs, orbitRhs, hn, ↓reduceIte] at e
  rw [LinearMap.comp_apply, LinearMap.comp_apply, f4ToE6Module_posVec K hp,
    (coeffOp_vecOf simpleRow_E6 e6_allValid K y i hn (validVec_f4ToE6Pos p)).1, e,
    f4ToE6Module_coeffOp K y j hn hp]

theorem coeffOp_comp_of_check_pair
    (K : Type) [CommRing K] (h2 : (2 : K) = 0) {y : Bool}
    {i i' : Fin Tag.E6.rank} {j : Fin Tag.F4.rank} (h : intertwinerCheck y [i, i'] j = true)
    {n : ℕ} (hn : n < 7) :
    ∑ k ∈ Finset.range 4, (if k ≤ n ∧ n - k < 4 then
      (coeffOp Tag.E6 K y i k * coeffOp Tag.E6 K y i' (n - k)) ∘ₗ f4ToE6Module K else 0) =
      if n < 4 then f4ToE6Module K ∘ₗ coeffOp Tag.F4 K y j n else 0 := by
  simp only [intertwinerCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ext_posVec_F4 K fun p hp => ?_
  have e := vecOf_eq_of_normalizeTwo_eq (τ := Tag.E6) (R := K) h2 (h p hp n hn)
  simp only [orbitLhs, orbitRhs, vecOf_flatMap_range] at e
  rw [LinearMap.sum_apply]
  have hL : ∀ k ∈ Finset.range 4,
      (if k ≤ n ∧ n - k < 4 then (coeffOp Tag.E6 K y i k * coeffOp Tag.E6 K y i' (n - k)) ∘ₗ
        f4ToE6Module K else 0) (posVec Tag.F4 K p) =
      vecOf Tag.E6 K (if k ≤ n ∧ n - k < 4 then
        coeffVec .E6 y i k (coeffVec .E6 y i' (n - k) (f4ToE6Pos p)) else []) := by
    intro k hk
    split_ifs with hc
    · have hk4 : k < 4 := Finset.mem_range.1 hk
      obtain ⟨e1, hv1⟩ := coeffOp_vecOf simpleRow_E6 e6_allValid K y i' hc.2
        (validVec_f4ToE6Pos p)
      rw [LinearMap.comp_apply, Module.End.mul_apply, f4ToE6Module_posVec K hp, e1,
        (coeffOp_vecOf simpleRow_E6 e6_allValid K y i hk4 hv1).1]
    · simp
  rw [Finset.sum_congr rfl hL, e]
  split_ifs with hn4
  · rw [LinearMap.comp_apply, f4ToE6Module_coeffOp K y j hn4 hp]
  · simp

theorem single_poly_comp {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (A : ℕ → Module.End K W) (C : ℕ → Module.End K V) (T : V →ₗ[K] W)
    (h : ∀ n < 4, A n ∘ₗ T = T ∘ₗ C n) (c : K) :
    (∑ k ∈ Finset.range 4, c ^ k • A k) ∘ₗ T = T ∘ₗ ∑ m ∈ Finset.range 4, c ^ m • C m := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LinearMap.add_comp,
    LinearMap.smul_comp, LinearMap.comp_add, LinearMap.comp_smul]
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

theorem pair_poly_comp {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (A B : ℕ → Module.End K W) (C : ℕ → Module.End K V) (T : V →ₗ[K] W)
    (h : ∀ n < 7, ∑ k ∈ Finset.range 4,
      (if k ≤ n ∧ n - k < 4 then (A k * B (n - k)) ∘ₗ T else 0) =
        if n < 4 then T ∘ₗ C n else 0) (c : K) :
    ((∑ k ∈ Finset.range 4, c ^ k • A k) * (∑ l ∈ Finset.range 4, c ^ l • B l)) ∘ₗ T =
      T ∘ₗ ∑ m ∈ Finset.range 4, c ^ m • C m := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h0 h1 h2 h3 h4 h5 h6 ⊢
  norm_num at h0 h1 h2 h3 h4 h5 h6
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, LinearMap.add_comp,
    LinearMap.smul_comp, LinearMap.comp_add, LinearMap.comp_smul]
  linear_combination (norm := module) h0 + c • h1 + c ^ 2 • h2 + c ^ 3 • h3 + c ^ 4 • h4 +
    c ^ 5 • h5 + c ^ 6 • h6

theorem f4OrbitX_comp_f4ToE6Module
    (R : Type) [CommRing R] (h2 : (2 : R) = 0)
    (j : Fin Tag.F4.rank) (c : R) :
    f4OrbitX R j c ∘ₗ f4ToE6Module R = f4ToE6Module R ∘ₗ xOp Tag.F4 R j c := by
  fin_cases j
  · show [xOp Tag.E6 R ⟨1, by decide⟩ c].prod ∘ₗ f4ToE6Module R = _
    rw [List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => coeffOp_comp_of_check_single R h2 intertwinerCheck_x0 hn) c
  · show [xOp Tag.E6 R ⟨3, by decide⟩ c].prod ∘ₗ f4ToE6Module R = _
    rw [List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => coeffOp_comp_of_check_single R h2 intertwinerCheck_x1 hn) c
  · show [xOp Tag.E6 R ⟨2, by decide⟩ c, xOp Tag.E6 R ⟨4, by decide⟩ c].prod ∘ₗ
      f4ToE6Module R = _
    rw [List.prod_cons, List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff,
      xOp_eq_sum_xCoeff]
    exact pair_poly_comp R _ _ _ _
      (fun n hn => coeffOp_comp_of_check_pair R h2 intertwinerCheck_x2 hn) c
  · show [xOp Tag.E6 R ⟨0, by decide⟩ c, xOp Tag.E6 R ⟨5, by decide⟩ c].prod ∘ₗ
      f4ToE6Module R = _
    rw [List.prod_cons, List.prod_singleton, xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff,
      xOp_eq_sum_xCoeff]
    exact pair_poly_comp R _ _ _ _
      (fun n hn => coeffOp_comp_of_check_pair R h2 intertwinerCheck_x3 hn) c

theorem f4OrbitY_comp_f4ToE6Module
    (R : Type) [CommRing R] (h2 : (2 : R) = 0)
    (j : Fin Tag.F4.rank) (c : R) :
    f4OrbitY R j c ∘ₗ f4ToE6Module R = f4ToE6Module R ∘ₗ yOp Tag.F4 R j c := by
  fin_cases j
  · show [yOp Tag.E6 R ⟨1, by decide⟩ c].prod ∘ₗ f4ToE6Module R = _
    rw [List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => coeffOp_comp_of_check_single R h2 intertwinerCheck_y0 hn) c
  · show [yOp Tag.E6 R ⟨3, by decide⟩ c].prod ∘ₗ f4ToE6Module R = _
    rw [List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff]
    exact single_poly_comp R _ _ _
      (fun n hn => coeffOp_comp_of_check_single R h2 intertwinerCheck_y1 hn) c
  · show [yOp Tag.E6 R ⟨2, by decide⟩ c, yOp Tag.E6 R ⟨4, by decide⟩ c].prod ∘ₗ
      f4ToE6Module R = _
    rw [List.prod_cons, List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff,
      yOp_eq_sum_yCoeff]
    exact pair_poly_comp R _ _ _ _
      (fun n hn => coeffOp_comp_of_check_pair R h2 intertwinerCheck_y2 hn) c
  · show [yOp Tag.E6 R ⟨0, by decide⟩ c, yOp Tag.E6 R ⟨5, by decide⟩ c].prod ∘ₗ
      f4ToE6Module R = _
    rw [List.prod_cons, List.prod_singleton, yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff,
      yOp_eq_sum_yCoeff]
    exact pair_poly_comp R _ _ _ _
      (fun n hn => coeffOp_comp_of_check_pair R h2 intertwinerCheck_y3 hn) c

theorem even_E6_graph_fixed_module_F4_intertwiner
    (K : Type) [Field K] (hK : ringChar K = 2) :
    (∀ β, IsRoot Tag.E6 β → IsRoot Tag.F4 (e6ToF4 β)) ∧
    (∀ α, IsRoot Tag.F4 α → ∃ β, IsRoot Tag.E6 β ∧ e6ToF4 β = α ∧ ∀ β', IsRoot Tag.E6 β' →
      (e6ToF4 β' = α ↔ β' = β ∨ β' = permLattice TwistTag.E6.perm β)) ∧
    (∀ j, f4ToE6Module K (hVec Tag.F4 K j) =
      ((f4IndexOrbit j).map fun i => hVec Tag.E6 K i).sum) ∧
    (∀ α, IsRoot Tag.F4 α → f4ToE6Module K (rootVec Tag.F4 K α) =
      ∑ β ∈ (rootFinset Tag.E6).filter (fun β => e6ToF4 β = α), rootVec Tag.E6 K β) ∧
    (∀ v, v ∈ e6GraphFixedModule K ↔
      (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K)) v = v) ∧
    Function.Injective (f4ToE6Module K) ∧
    LinearMap.range (f4ToE6Module K) = e6GraphFixedModule K ∧
    (∀ j (c : K), f4OrbitX K j c ∘ₗ f4ToE6Module K = f4ToE6Module K ∘ₗ xOp Tag.F4 K j c) ∧
    (∀ j (c : K), f4OrbitY K j c ∘ₗ f4ToE6Module K = f4ToE6Module K ∘ₗ yOp Tag.F4 K j c) ∧
    ∀ (R : Type) [CommRing R], (2 : R) = 0 → ∀ j (c : R),
      f4OrbitX R j c ∘ₗ f4ToE6Module R = f4ToE6Module R ∘ₗ xOp Tag.F4 R j c ∧
      f4OrbitY R j c ∘ₗ f4ToE6Module R = f4ToE6Module R ∘ₗ yOp Tag.F4 R j c := by
  have : CharP K 2 := ringChar.of_eq hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  refine ⟨fun β hβ => isRoot_e6ToF4 hβ, fun α hα => exists_e6ToF4_fibre hα, fun j => ?_,
    fun α hα => ?_, fun v => mem_e6GraphFixedModule, f4ToE6Module_injective K,
    range_f4ToE6Module K, f4OrbitX_comp_f4ToE6Module K h2, f4OrbitY_comp_f4ToE6Module K h2,
    fun R _ hR j c => ⟨f4OrbitX_comp_f4ToE6Module R hR j c, f4OrbitY_comp_f4ToE6Module R hR j c⟩⟩
  · rw [hVec, f4ToE6Module, Finsupp.linearCombination_single, one_smul]
  · rw [CFSG.LieType.Ree.rootVec_eq_single K hα, f4ToE6Module, Finsupp.linearCombination_single,
      one_smul]

end CFSG.LieType.Chevalley
