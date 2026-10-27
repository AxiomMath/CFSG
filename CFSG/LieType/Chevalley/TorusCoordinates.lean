module

public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.SimpleRootSubgroups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag}

theorem list_prod_ofFn_mul {G : Type*} [Group G] :
    ∀ {n : ℕ} (f g : Fin n → G), (∀ i j, Commute (f i) (g j)) →
      (List.ofFn fun i => f i * g i).prod = (List.ofFn f).prod * (List.ofFn g).prod
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, list_prod_ofFn_mul (fun i => f i.succ) (fun i => g i.succ)
        (fun i j => h i.succ j.succ)]
    have hc : Commute (g 0) (List.ofFn fun i => f i.succ).prod :=
      Commute.list_prod_right _ _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact (h i.succ 0).symm
    rw [mul_assoc, ← mul_assoc (g 0), hc.eq]
    simp only [mul_assoc]

theorem list_prod_ofFn_mulSingle {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (i : Fin n) (x : M), (List.ofFn (Pi.mulSingle i x)).prod = x
  | 0, i, _ => i.elim0
  | n + 1, i, x => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i' => ?_) i
    · have : (fun j : Fin n => (Pi.mulSingle (0 : Fin (n + 1)) x : Fin (n + 1) → M) j.succ) =
          fun _ => 1 := by
        funext j
        exact Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j) x
      rw [this, Pi.mulSingle_eq_same]
      simp
    · have : (fun j : Fin n => (Pi.mulSingle i'.succ x : Fin (n + 1) → M) j.succ) =
          Pi.mulSingle i' x := by
        funext j
        by_cases hj : j = i'
        · subst hj
          simp
        · rw [Pi.mulSingle_eq_of_ne (fun h => hj (Fin.succ_injective _ h)),
            Pi.mulSingle_eq_of_ne hj]
      rw [this, list_prod_ofFn_mulSingle i' x, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero i').symm,
        one_mul]

theorem prod_zpow_eq_zpow_sum {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) (a : G) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add]

theorem eq_one_of_prod_zpow_eq_one {G : Type*} [CommGroup G] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℤ} (hAB : A * B = 1) {t : Fin n → G}
    (h : ∀ j, ∏ i, t i ^ A i j = 1) : t = 1 := by
  funext k
  have hk : t k = ∏ i, t i ^ ((A * B) i k) := by
    rw [hAB]
    simp [Matrix.one_apply]
  rw [hk, Pi.one_apply]
  simp only [Matrix.mul_apply, ← prod_zpow_eq_zpow_sum, zpow_mul]
  rw [Finset.prod_comm]
  simp only [Finset.prod_zpow, h, one_zpow, Finset.prod_const_one]

@[expose] def cartanInvG2 : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ := !![2, 1; 3, 2]

@[expose] def cartanInvF4 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![2, 3, 2, 1; 3, 6, 4, 2; 4, 8, 6, 3; 2, 4, 3, 2]

theorem cartan_mul_cartanInv_G2 : Tag.G2.cartan * cartanInvG2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cartan_mul_cartanInv_F4 : Tag.F4.cartan * cartanInvF4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable (τ) (R : Type*) [CommRing R]

@[expose] def torusCoordHom
    : (Fin τ.rank → Rˣ) →* torusGroup τ R where
  toFun t := ⟨(List.ofFn fun i => torusElt τ R i (t i)).prod, list_prod_mem fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact torusElt_mem_torusGroup i (t i)⟩
  map_one' := Subtype.ext (by simp [torusElt_one])
  map_mul' t u := Subtype.ext (by
    simp only [Pi.mul_apply, torusElt_mul, Subgroup.coe_mul]
    exact list_prod_ofFn_mul _ _ fun i j => torusElt_mul_comm i j (t i) (u j))

variable {τ R}

theorem coe_torusCoordHom
    (t : Fin τ.rank → Rˣ) :
    (torusCoordHom τ R t : (Module.End R (RootModule τ R))ˣ) =
      (List.ofFn fun i => torusElt τ R i (t i)).prod :=
  rfl

theorem list_prod_torusElt_rootVec
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∀ l : List (Fin τ.rank × Rˣ),
      (((l.map fun p => torusElt τ R p.1 p.2).prod : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) (rootVec τ R α) =
        (((l.map fun p => p.2 ^ (∑ k, τ.cartan p.1 k * α k)).prod : Rˣ) : R) • rootVec τ R α
  | [] => by simp
  | p :: l => by
    rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply,
      list_prod_torusElt_rootVec hα l, map_smul, torusElt_rootVec p.1 p.2 hα, smul_smul,
      List.map_cons, List.prod_cons, Units.val_mul, mul_comm]

theorem torusCoordHom_apply_rootVec_single
    (t : Fin τ.rank → Rˣ) (j : Fin τ.rank) :
    ((torusCoordHom τ R t : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) (rootVec τ R (Pi.single j 1)) =
      ((∏ i, t i ^ τ.cartan i j : Rˣ) : R) • rootVec τ R (Pi.single j 1) := by
  have h := list_prod_torusElt_rootVec (R := R) (isRoot_single τ j)
    (List.ofFn fun i => (i, t i))
  have e1 : ((List.ofFn fun i => (i, t i)).map fun p => torusElt τ R p.1 p.2) =
      List.ofFn fun i => torusElt τ R i (t i) := by
    rw [List.map_ofFn]
    rfl
  have e2 : ((List.ofFn fun i => (i, t i)).map
      fun p => p.2 ^ (∑ k, τ.cartan p.1 k * (Pi.single j 1 : Fin τ.rank → ℤ) k)) =
      List.ofFn fun i => t i ^ τ.cartan i j := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact congrArg (t i ^ ·) (sum_cartan_mul_pi_single i j)
  rw [e1, e2, Fin.prod_ofFn] at h
  rw [coe_torusCoordHom]
  exact h

theorem coe_torusCoordHom_mulSingle
    (i : Fin τ.rank) (s : Rˣ) :
    (torusCoordHom τ R (Pi.mulSingle i s) : (Module.End R (RootModule τ R))ˣ) =
      torusElt τ R i s := by
  rw [coe_torusCoordHom]
  have : (fun j => torusElt τ R j ((Pi.mulSingle i s : Fin τ.rank → Rˣ) j)) =
      (Pi.mulSingle i (torusElt τ R i s) : Fin τ.rank → (Module.End R (RootModule τ R))ˣ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, torusElt_one]
  rw [this, list_prod_ofFn_mulSingle]

theorem torusCoordHom_surjective
    : Function.Surjective (torusCoordHom τ R) := by
  have hle : torusGroup τ R ≤ (torusCoordHom τ R).range.map (torusGroup τ R).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, s⟩, rfl⟩
    exact ⟨torusCoordHom τ R (Pi.mulSingle i s), ⟨_, rfl⟩, coe_torusCoordHom_mulSingle i s⟩
  intro g
  obtain ⟨y, ⟨t, rfl⟩, hy⟩ := hle g.2
  exact ⟨t, Subtype.ext hy⟩

theorem torusCoordHom_injective_of_mul_eq_one
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hB : τ.cartan * B = 1) : Function.Injective (torusCoordHom τ R) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  refine eq_one_of_prod_zpow_eq_one hB fun j => Units.ext ?_
  have h := torusCoordHom_apply_rootVec_single (R := R) t j
  rw [ht, OneMemClass.coe_one, Units.val_one, Module.End.one_apply,
    rootVec_eq_single_of_isRoot (isRoot_single τ j)] at h
  have h' := congrArg (fun v : RootModule τ R =>
    v (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩)) h
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h'
  rw [Units.val_one, ← h']

theorem G2_F4_torus_coordinates
    (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4) (R : Type*) [CommRing R] :
    ∃ e : (Fin τ.rank → Rˣ) ≃* torusGroup τ R, ∀ t,
      (e t : (Module.End R (RootModule τ R))ˣ) =
        (List.ofFn fun i => torusElt τ R i (t i)).prod := by
  have hinj : Function.Injective (torusCoordHom τ R) := by
    rcases hτ with rfl | rfl
    · exact torusCoordHom_injective_of_mul_eq_one cartan_mul_cartanInv_G2
    · exact torusCoordHom_injective_of_mul_eq_one cartan_mul_cartanInv_F4
  exact ⟨MulEquiv.ofBijective _ ⟨hinj, torusCoordHom_surjective⟩, fun t => rfl⟩

end CFSG.LieType.Chevalley
