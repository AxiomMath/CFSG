module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Weights

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

section WeightsE

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

@[expose] def refE (τ : Tag) (j : Fin τ.rank) (x : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  fun i => x i - τ.cartan i j * x j

@[expose] def wtE (ρ : Representation k (adjointGroup τ K) V) (x : Fin τ.rank → ℤ) :
    Submodule k V where
  carrier := {v | ∀ (i : Fin τ.rank) (t : Kˣ), ρ (dC τ K i t) v = kpow (k := k) K t (x i) • v}
  add_mem' := fun {a b} ha hb i t => by rw [map_add, ha i t, hb i t, smul_add]
  zero_mem' := fun i t => by simp
  smul_mem' := fun c v hv i t => by rw [map_smul, hv i t, smul_comm]

theorem wt_nC_E (ρ : Representation k (adjointGroup τ K) V) (j : Fin τ.rank)
    {x : Fin τ.rank → ℤ} {v : V} (hv : v ∈ wtE ρ x) : ρ (nC τ K j) v ∈ wtE ρ (refE τ j x) := by
  intro i t
  have hnn : nC τ K j * nC τ K j = 1 :=
    mul_eq_one_iff_eq_inv.2 (nC_inv_eq (τ := τ) (K := K) j).symm
  have e1 : dC τ K i t * nC τ K j =
      nC τ K j * (dC τ K i t * dC τ K j (t ^ (-τ.cartan i j))) := by
    have h := nC_mul_dC_mul_nC (τ := τ) (K := K) j i t
    calc dC τ K i t * nC τ K j = nC τ K j * (nC τ K j * dC τ K i t * nC τ K j) := by
          rw [← mul_assoc, ← mul_assoc, hnn, one_mul]
      _ = _ := by rw [h]
  have h1 : ρ (dC τ K i t) (ρ (nC τ K j) v) =
      ρ (nC τ K j) (ρ (dC τ K i t) (ρ (dC τ K j (t ^ (-τ.cartan i j))) v)) := by
    rw [act_mul, e1, ← act_mul, ← act_mul]
  rw [h1, hv j _, map_smul, hv i t, map_smul, map_smul, smul_smul, kpow_zpow_unit,
    ← kpow_add]
  congr 2
  simp only [refE]
  ring

@[expose] def nProd (τ : Tag) (K : Type) [Field K]
    (l : List (Fin τ.rank)) : adjointGroup τ K :=
  (l.map (nC τ K)).prod

theorem nProd_nil : nProd τ K [] = 1 := rfl

theorem nProd_cons (j : Fin τ.rank) (l : List (Fin τ.rank)) :
    nProd τ K (j :: l) = nC τ K j * nProd τ K l := by
  simp [nProd]

theorem wt_nProd (ρ : Representation k (adjointGroup τ K) V) (l : List (Fin τ.rank))
    {x : Fin τ.rank → ℤ} {v : V} (hv : v ∈ wtE ρ x) :
    ρ (nProd τ K l) v ∈ wtE ρ (l.foldr (refE τ) x) := by
  induction l with
  | nil => rw [nProd_nil, map_one, Module.End.one_apply]; exact hv
  | cons j l ih =>
    rw [nProd_cons, ← act_mul, List.foldr_cons]
    exact wt_nC_E ρ j ih

theorem refE_comb (j : Fin τ.rank) (a b : ℤ) (x y : Fin τ.rank → ℤ) :
    refE τ j (a • x - b • y) = a • refE τ j x - b • refE τ j y := by
  ext i
  simp only [refE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem foldr_refE_comb (l : List (Fin τ.rank)) (a b : ℤ) (x y : Fin τ.rank → ℤ) :
    l.foldr (refE τ) (a • x - b • y) = a • l.foldr (refE τ) x - b • l.foldr (refE τ) y := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, refE_comb]

@[expose] def wclsE (τ : Tag) (K : Type) [Field K] (k : Type) [Field k] [Algebra K k]
    (x : Fin τ.rank → ℤ) : Fin τ.rank × Kˣ → k :=
  fun p => kpow (k := k) K p.2 (x p.1)

theorem wtE_le_gen (ρ : Representation k (adjointGroup τ K) V) (x : Fin τ.rank → ℤ) :
    wtE ρ x ≤ ⨅ p : Fin τ.rank × Kˣ,
      Module.End.maxGenEigenspace (ρ (dC τ K p.1 p.2)) (wclsE τ K k x p) := by
  intro v hv
  rw [Submodule.mem_iInf]
  intro p
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  exact hv p.1 p.2

theorem dvd_of_wclsE_eq {x x' : Fin τ.rank → ℤ} (h : wclsE τ K k x = wclsE τ K k x')
    (i : Fin τ.rank) : ((Nat.card Kˣ : ℕ) : ℤ) ∣ x i - x' i := by
  obtain ⟨g, hg⟩ := (inferInstance : IsCyclic Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have h1 := congrFun h (i, g)
  simp only [wclsE, kpow] at h1
  have h2 : (algebraMap K k (g : K)) ^ (x i - x' i) = 1 := by
    rw [zpow_sub₀ (by simpa using g.ne_zero), h1,
      div_self (zpow_ne_zero _ (by simpa using g.ne_zero))]
  have h3 : ((g ^ (x i - x' i) : Kˣ) : K) = 1 := by
    apply (algebraMap K k).injective
    rw [map_one, Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact h2
  have h4 : g ^ (x i - x' i) = 1 := Units.ext h3
  rw [← hord]
  exact orderOf_dvd_iff_zpow_eq_one.2 h4

theorem linearIndependent_of_wtE
    (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    (ρ : Representation k (adjointGroup τ K) V) {ι : Type*} (v : ι → V)
    (x : ι → Fin τ.rank → ℤ) (hv : ∀ p, v p ∈ wtE ρ (x p))
    (hin : ∀ c : Fin τ.rank × Kˣ → k,
      LinearIndependent k (fun p : {p : ι // wclsE τ K k (x p) = c} => v p.1)) :
    LinearIndependent k v := by
  classical
  set G : (Fin τ.rank × Kˣ → k) → Submodule k V := fun c =>
    ⨅ p : Fin τ.rank × Kˣ, Module.End.maxGenEigenspace (ρ (dC τ K p.1 p.2)) (c p) with hG
  have hind : iSupIndep G := iSupIndep_gen hw ρ
  have hle : ∀ c, Submodule.span k (Set.range (fun p : {p : ι // wclsE τ K k (x p) = c} => v p.1))
      ≤ G c := by
    intro c
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have := wtE_le_gen ρ (x p.1) (hv p.1)
    rw [p.2] at this
    exact this
  have hsig := linearIndependent_iUnion_finite (R := k)
    (f := fun (c : Fin τ.rank × Kˣ → k) (p : {p : ι // wclsE τ K k (x p) = c}) => v p.1) hin
    (fun c t _ hct => (hind.disjoint_biSup hct).mono (hle c) (iSup₂_mono fun i _ => hle i))
  let e : (Σ c : Fin τ.rank × Kˣ → k, {p : ι // wclsE τ K k (x p) = c}) ≃ ι :=
    Equiv.sigmaFiberEquiv (fun p => wclsE τ K k (x p))
  exact (linearIndependent_equiv e).1 hsig

end WeightsE

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
