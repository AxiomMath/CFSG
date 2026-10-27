module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Rank1
public import CFSG.LieType.Steinberg.Minuscule.Unipotent

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

@[expose] def kp (K : Type) [Field K] {k : Type} [Field k] [Algebra K k] (t : Kˣ) (e : ℤ) : k :=
  (algebraMap K k (t : K)) ^ e

theorem kp_add (t : Kˣ) (e f : ℤ) : kp (k := k) K t (e + f) = kp K t e * kp K t f := by
  unfold kp
  rw [zpow_add₀ (by simp)]

theorem kp_zpow_unit (t : Kˣ) (e f : ℤ) : kp (k := k) K (t ^ e) f = kp K t (e * f) := by
  unfold kp
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_mul]

theorem kp_inv_unit (t : Kˣ) (f : ℤ) : kp (k := k) K t⁻¹ f = kp K t (-f) := by
  have := kp_zpow_unit (k := k) (K := K) t (-1) f
  rw [zpow_neg_one] at this
  rw [this]; congr 1; ring

theorem kp_mul_card (t : Kˣ) (M : ℕ) (hM : Nat.card Kˣ = M) (c : ℤ) :
    kp (k := k) K t (M * c) = 1 := by
  unfold kp
  rw [zpow_mul, zpow_natCast]
  have h : (algebraMap K k (t : K)) ^ M = 1 := by
    have h1 : t ^ M = 1 := by rw [← hM]; exact pow_card_eq_one'
    have h2 := congrArg (fun u : Kˣ => algebraMap K k (u : K)) h1
    simpa using h2
  rw [h, one_zpow]

@[expose] def refE (j : N6) (x : N6 → ℤ) : N6 → ℤ :=
  fun i => x i - Tag.cartan .E6 i j * x j

@[expose] def wt (ρ : Representation k ↥(e6Data_valid.minGroup K) V) (x : N6 → ℤ) :
    Submodule k V where
  carrier := {v | ∀ (i : N6) (t : Kˣ), ρ (e6Data_valid.hm K i t) v = kp (k := k) K t (x i) • v}
  add_mem' := fun {a b} ha hb i t => by rw [map_add, ha i t, hb i t, smul_add]
  zero_mem' := fun i t => by simp
  smul_mem' := fun c v hv i t => by rw [map_smul, hv i t, smul_comm]

theorem neg_one_unit_eq_one : (-1 : Kˣ) = 1 := Units.ext (by rw [Units.val_neg, Units.val_one]; exact CharTwo.neg_eq (1 : K))

theorem nm_mul_nm (j : N6) : e6Data_valid.nm K j * e6Data_valid.nm K j = 1 := by
  rw [← pow_two, e6Data_valid.nm_sq K j, neg_one_unit_eq_one, e6Data_valid.hm_one]

theorem nm_inv (j : N6) : (e6Data_valid.nm K j)⁻¹ = e6Data_valid.nm K j :=
  inv_eq_of_mul_eq_one_right (nm_mul_nm (K := K) j)

theorem wt_nm (ρ : Representation k ↥(e6Data_valid.minGroup K) V) (j : N6)
    {x : N6 → ℤ} {v : V} (hv : v ∈ wt ρ x) : ρ (e6Data_valid.nm K j) v ∈ wt ρ (refE j x) := by
  intro i t
  have hnn := nm_mul_nm (K := K) j
  have h : e6Data_valid.nm K j * e6Data_valid.hm K i t * e6Data_valid.nm K j =
      e6Data_valid.hm K i t * e6Data_valid.hm K j (t ^ (-Tag.cartan .E6 i j)) := by
    have := e6Data_valid.nm_conj_hm K j i t
    rwa [nm_inv] at this
  have e1 : e6Data_valid.hm K i t * e6Data_valid.nm K j =
      e6Data_valid.nm K j * (e6Data_valid.hm K i t * e6Data_valid.hm K j (t ^ (-Tag.cartan .E6 i j))) := by
    calc e6Data_valid.hm K i t * e6Data_valid.nm K j
        = e6Data_valid.nm K j * (e6Data_valid.nm K j * e6Data_valid.hm K i t * e6Data_valid.nm K j) := by
          rw [← mul_assoc, ← mul_assoc, hnn, one_mul]
      _ = _ := by rw [h]
  have h1 : ρ (e6Data_valid.hm K i t) (ρ (e6Data_valid.nm K j) v) =
      ρ (e6Data_valid.nm K j) (ρ (e6Data_valid.hm K i t)
        (ρ (e6Data_valid.hm K j (t ^ (-Tag.cartan .E6 i j))) v)) := by
    rw [act_mul, e1, ← act_mul, ← act_mul]
  rw [h1, hv j _, map_smul, hv i t, map_smul, map_smul, smul_smul, kp_zpow_unit, ← kp_add]
  congr 2
  simp only [refE]
  ring

variable (K) in
@[expose] def nProd (l : List N6) : ↥(e6Data_valid.minGroup K) :=
  (l.map (e6Data_valid.nm K)).prod

theorem nProd_nil : nProd K [] = 1 := rfl

theorem nProd_cons (j : N6) (l : List N6) :
    nProd K (j :: l) = e6Data_valid.nm K j * nProd K l := by
  simp [nProd]

theorem wt_nProd (ρ : Representation k ↥(e6Data_valid.minGroup K) V) (l : List N6)
    {x : N6 → ℤ} {v : V} (hv : v ∈ wt ρ x) :
    ρ (nProd K l) v ∈ wt ρ (l.foldr refE x) := by
  induction l with
  | nil => rw [nProd_nil, map_one, Module.End.one_apply]; exact hv
  | cons j l ih =>
    rw [nProd_cons, ← act_mul, List.foldr_cons]
    exact wt_nm ρ j ih

theorem refE_comb (j : N6) (a b : ℤ) (x y : N6 → ℤ) :
    refE j (a • x - b • y) = a • refE j x - b • refE j y := by
  ext i
  simp only [refE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem foldr_refE_comb (l : List N6) (a b : ℤ) (x y : N6 → ℤ) :
    l.foldr refE (a • x - b • y) = a • l.foldr refE x - b • l.foldr refE y := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, refE_comb]

@[expose] def wcls (K : Type) [Field K] (k : Type) [Field k] [Algebra K k]
    (x : N6 → ℤ) : N6 × Kˣ → k :=
  fun p => kp (k := k) K p.2 (x p.1)

theorem wt_le_gen (ρ : Representation k ↥(e6Data_valid.minGroup K) V) (x : N6 → ℤ) :
    wt ρ x ≤ ⨅ p : N6 × Kˣ,
      Module.End.maxGenEigenspace (ρ (e6Data_valid.hm K p.1 p.2)) (wcls K k x p) := by
  intro v hv
  rw [Submodule.mem_iInf]
  intro p
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  exact hv p.1 p.2

theorem iSupIndep_gen (ρ : Representation k ↥(e6Data_valid.minGroup K) V) :
    iSupIndep fun c : N6 × Kˣ → k =>
      ⨅ p : N6 × Kˣ, Module.End.maxGenEigenspace (ρ (e6Data_valid.hm K p.1 p.2)) (c p) := by
  apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
  intro p q φ
  apply Module.End.mapsTo_maxGenEigenspace_of_comm
  have hc : e6Data_valid.hm K q.1 q.2 * e6Data_valid.hm K p.1 p.2 =
      e6Data_valid.hm K p.1 p.2 * e6Data_valid.hm K q.1 q.2 :=
    e6Data_valid.torus_commute K q.1 p.1 (e6Data_valid.hm_mem_torus K _ _)
      (e6Data_valid.hm_mem_torus K _ _)
  have := congrArg ρ hc
  rw [map_mul, map_mul] at this
  exact this

theorem dvd_of_wcls_eq {x x' : N6 → ℤ} (h : wcls K k x = wcls K k x')
    (i : N6) : ((Nat.card Kˣ : ℕ) : ℤ) ∣ x i - x' i := by
  obtain ⟨g, hg⟩ := (inferInstance : IsCyclic Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have h1 := congrFun h (i, g)
  simp only [wcls, kp] at h1
  have h2 : (algebraMap K k (g : K)) ^ (x i - x' i) = 1 := by
    rw [zpow_sub₀ (by simp), h1,
      div_self (zpow_ne_zero _ (by simp))]
  have h3 : ((g ^ (x i - x' i) : Kˣ) : K) = 1 := by
    apply (algebraMap K k).injective
    rw [map_one, Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact h2
  have h4 : g ^ (x i - x' i) = 1 := Units.ext h3
  rw [← hord]
  exact orderOf_dvd_iff_zpow_eq_one.2 h4

theorem linearIndependent_of_wt (ρ : Representation k ↥(e6Data_valid.minGroup K) V) {ι : Type*}
    (v : ι → V) (x : ι → N6 → ℤ) (hv : ∀ p, v p ∈ wt ρ (x p))
    (hin : ∀ c : N6 × Kˣ → k,
      LinearIndependent k (fun p : {p : ι // wcls K k (x p) = c} => v p.1)) :
    LinearIndependent k v := by
  classical
  set G : (N6 × Kˣ → k) → Submodule k V := fun c =>
    ⨅ p : N6 × Kˣ, Module.End.maxGenEigenspace (ρ (e6Data_valid.hm K p.1 p.2)) (c p) with hG
  have hind : iSupIndep G := iSupIndep_gen ρ
  have hle : ∀ c, Submodule.span k (Set.range (fun p : {p : ι // wcls K k (x p) = c} => v p.1))
      ≤ G c := by
    intro c
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have := wt_le_gen ρ (x p.1) (hv p.1)
    rw [p.2] at this
    exact this
  have hsig := linearIndependent_iUnion_finite (R := k)
    (f := fun (c : N6 × Kˣ → k) (p : {p : ι // wcls K k (x p) = c}) => v p.1) hin
    (fun c t _ hct => (hind.disjoint_biSup hct).mono (hle c) (iSup₂_mono fun i _ => hle i))
  let e : (Σ c : N6 × Kˣ → k, {p : ι // wcls K k (x p) = c}) ≃ ι :=
    Equiv.sigmaFiberEquiv (fun p => wcls K k (x p))
  exact (linearIndependent_equiv e).1 hsig

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
