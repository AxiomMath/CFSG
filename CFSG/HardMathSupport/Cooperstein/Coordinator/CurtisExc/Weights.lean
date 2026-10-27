module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.SmithCurtisChevType

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

section Weights

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

@[expose] def mExp (τ : Tag) (i : Fin τ.rank) (ν : Fin τ.rank → ℤ) : ℤ :=
  ∑ j, τ.cartan i j * ν j

@[expose] def kpow (K : Type) [Field K] {k : Type} [Field k] [Algebra K k] (t : Kˣ) (e : ℤ) : k :=
  (algebraMap K k (t : K)) ^ e

theorem kpow_add (t : Kˣ) (e f : ℤ) : kpow (k := k) K t (e + f) = kpow K t e * kpow K t f := by
  unfold kpow
  rw [zpow_add₀ (by simpa using t.ne_zero)]

@[expose] def wtSpace (ρ : Representation k (adjointGroup τ K) V) (ν : Fin τ.rank → ℤ) :
    Submodule k V where
  carrier := {v | ∀ (i : Fin τ.rank) (t : Kˣ),
    ρ (dC τ K i t) v = kpow (k := k) K t (mExp τ i ν) • v}
  add_mem' := fun {a b} ha hb i t => by rw [map_add, ha i t, hb i t, smul_add]
  zero_mem' := fun i t => by simp
  smul_mem' := fun c v hv i t => by rw [map_smul, hv i t, smul_comm]

theorem mExp_reflect (j i : Fin τ.rank) (ν : Fin τ.rank → ℤ) :
    mExp τ i (reflect τ j ν) = mExp τ i ν - τ.cartan i j * mExp τ j ν := by
  unfold mExp reflect
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_sub,
    Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem nC_inv_eq (j : Fin τ.rank) : (nC τ K j)⁻¹ = nC τ K j := by
  apply Subtype.ext
  show ((weylElt τ K j 1)⁻¹ : ModGL τ K) = weylElt τ K j 1
  rw [weylElt_inv]
  congr 1
  exact Units.ext (by simp [CharTwo.neg_eq])

theorem nC_mul_dC_mul_nC (j i : Fin τ.rank) (t : Kˣ) :
    nC τ K j * dC τ K i t * nC τ K j = dC τ K i t * dC τ K j (t ^ (-τ.cartan i j)) := by
  apply Subtype.ext
  have h := weylElt_one_mul_torusElt_mul_inv (τ := τ) (R := K) j i t
  have e : (weylElt τ K j 1)⁻¹ = weylElt τ K j 1 := by
    rw [weylElt_inv]
    congr 1
    exact Units.ext (by simp [CharTwo.neg_eq])
  rw [e] at h
  exact h

theorem kpow_zpow_unit (t : Kˣ) (e f : ℤ) : kpow (k := k) K (t ^ e) f = kpow K t (e * f) := by
  unfold kpow
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_mul]

theorem wt_nC (ρ : Representation k (adjointGroup τ K) V) (j : Fin τ.rank)
    {ν : Fin τ.rank → ℤ} {v : V} (hv : v ∈ wtSpace ρ ν) :
    ρ (nC τ K j) v ∈ wtSpace ρ (reflect τ j ν) := by
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
    ← kpow_add, mExp_reflect]
  congr 2
  ring

theorem wt_nWC (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    (ρ : Representation k (adjointGroup τ K) V) (w : WeylGroup τ) {ν : Fin τ.rank → ℤ} {v : V}
    (hv : v ∈ wtSpace ρ ν) : ρ (nWC τ K w) v ∈ wtSpace ρ (w • ν) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  revert ν v
  induction ω with
  | nil =>
    intro ν v hv
    have h1 : nWC τ K ((coxeterSystem τ).wordProd []) = 1 := (chevDatum τ K 2 hw).nW_one
    rw [h1, (coxeterSystem τ).wordProd_nil, one_smul, map_one, Module.End.one_apply]
    exact hv
  | cons s ω ih =>
    intro ν v hv
    have hred : (coxeterSystem τ).IsReduced ω := by simpa using hω.drop 1
    have hlen : (coxeterSystem τ).length ((coxeterSystem τ).simple s * (coxeterSystem τ).wordProd ω) =
        (coxeterSystem τ).length ((coxeterSystem τ).wordProd ω) + 1 := by
      rw [← (coxeterSystem τ).wordProd_cons, hω.eq, hred.eq, List.length_cons]
    have hnW : nWC τ K ((coxeterSystem τ).wordProd (s :: ω)) =
        nC τ K s * nWC τ K ((coxeterSystem τ).wordProd ω) := by
      rw [(coxeterSystem τ).wordProd_cons]
      exact (chevDatum τ K 2 hw).nW_simple_mul _ _ hlen
    have hsm : (coxeterSystem τ).wordProd (s :: ω) • ν =
        reflect τ s ((coxeterSystem τ).wordProd ω • ν) := by
      rw [(coxeterSystem τ).wordProd_cons, mul_smul, simple_smul]
    rw [hsm, hnW, ← act_mul]
    exact wt_nC ρ s (ih hred hv)

@[expose] def wcls (τ : Tag) (K : Type) [Field K] (k : Type) [Field k] [Algebra K k]
    (ν : Fin τ.rank → ℤ) : Fin τ.rank × Kˣ → k :=
  fun p => kpow (k := k) K p.2 (mExp τ p.1 ν)

theorem wtSpace_le_gen (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    (ρ : Representation k (adjointGroup τ K) V) (ν : Fin τ.rank → ℤ) :
    wtSpace ρ ν ≤ ⨅ p : Fin τ.rank × Kˣ,
      Module.End.maxGenEigenspace (ρ (dC τ K p.1 p.2)) (wcls τ K k ν p) := by
  intro v hv
  rw [Submodule.mem_iInf]
  intro p
  apply Module.End.eigenspace_le_maxGenEigenspace
  rw [Module.End.mem_eigenspace_iff]
  exact hv p.1 p.2

theorem iSupIndep_gen (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    (ρ : Representation k (adjointGroup τ K) V) :
    iSupIndep fun c : Fin τ.rank × Kˣ → k =>
      ⨅ p : Fin τ.rank × Kˣ, Module.End.maxGenEigenspace (ρ (dC τ K p.1 p.2)) (c p) := by
  apply Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
  intro p q φ
  apply Module.End.mapsTo_maxGenEigenspace_of_comm
  have hc : dC τ K q.1 q.2 * dC τ K p.1 p.2 = dC τ K p.1 p.2 * dC τ K q.1 q.2 :=
    (chevDatum τ K 2 hw).H_comm _ (dC_mem_H _ _) _ (dC_mem_H _ _)
  have := congrArg ρ hc
  rw [map_mul, map_mul] at this
  exact this

theorem dvd_of_wcls_eq {ν ν' : Fin τ.rank → ℤ} (h : wcls τ K k ν = wcls τ K k ν')
    (i : Fin τ.rank) : ((Nat.card Kˣ : ℕ) : ℤ) ∣ mExp τ i ν - mExp τ i ν' := by
  obtain ⟨g, hg⟩ := (inferInstance : IsCyclic Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have h1 := congrFun h (i, g)
  simp only [wcls, kpow] at h1
  have h2 : (algebraMap K k (g : K)) ^ (mExp τ i ν - mExp τ i ν') = 1 := by
    rw [zpow_sub₀ (by simpa using g.ne_zero), h1, div_self (zpow_ne_zero _ (by simpa using g.ne_zero))]
  have h3 : ((g ^ (mExp τ i ν - mExp τ i ν') : Kˣ) : K) = 1 := by
    apply (algebraMap K k).injective
    rw [map_one, Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact h2
  have h4 : g ^ (mExp τ i ν - mExp τ i ν') = 1 := Units.ext h3
  rw [← hord]
  exact orderOf_dvd_iff_zpow_eq_one.2 h4

theorem linearIndependent_of_wcls
    (hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α)
    (ρ : Representation k (adjointGroup τ K) V) {ι : Type*} (v : ι → V)
    (ν : ι → Fin τ.rank → ℤ) (hv : ∀ p, v p ∈ wtSpace ρ (ν p))
    (hin : ∀ c : Fin τ.rank × Kˣ → k,
      LinearIndependent k (fun p : {p : ι // wcls τ K k (ν p) = c} => v p.1)) :
    LinearIndependent k v := by
  classical
  set G : (Fin τ.rank × Kˣ → k) → Submodule k V := fun c =>
    ⨅ p : Fin τ.rank × Kˣ, Module.End.maxGenEigenspace (ρ (dC τ K p.1 p.2)) (c p) with hG
  have hind : iSupIndep G := iSupIndep_gen hw ρ
  have hle : ∀ c, Submodule.span k (Set.range (fun p : {p : ι // wcls τ K k (ν p) = c} => v p.1))
      ≤ G c := by
    intro c
    rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    have := wtSpace_le_gen hw ρ (ν p.1) (hv p.1)
    rw [p.2] at this
    exact this
  have hsig := linearIndependent_iUnion_finite (R := k)
    (f := fun (c : Fin τ.rank × Kˣ → k) (p : {p : ι // wcls τ K k (ν p) = c} ) => v p.1) hin
    (fun c t _ hct => (hind.disjoint_biSup hct).mono (hle c) (iSup₂_mono fun i _ => hle i))
  let e : (Σ c : Fin τ.rank × Kˣ → k, {p : ι // wcls τ K k (ν p) = c}) ≃ ι :=
    Equiv.sigmaFiberEquiv (fun p => wcls τ K k (ν p))
  exact (linearIndependent_equiv e).1 hsig

end Weights

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
