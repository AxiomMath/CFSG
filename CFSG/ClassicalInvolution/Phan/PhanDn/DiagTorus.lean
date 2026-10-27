module

public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.LieType.Steinberg.CentralExt.SUThree

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ : K ≃+* K}

variable (F σ) in
@[expose] noncomputable def diagHom (n : ℕ) :
    (Fin n → normOne σ) →* ((Fin n → K) ≃ₗ[F] (Fin n → K)) where
  toFun t := LinearEquiv.piCongrRight fun i =>
    Units.mulLeftLinearEquiv F K ((t i : normOne σ) : Kˣ)
  map_one' := by
    ext v i
    simp
  map_mul' t s := by
    ext v i
    simp

@[simp] theorem diagHom_apply (n : ℕ) (t : Fin n → normOne σ)
    (x : Fin n → K) (i : Fin n) :
    diagHom F σ n t x i = (((t i : normOne σ) : Kˣ) : K) * x i := by
  simp [diagHom]

theorem diagHom_injective (n : ℕ) :
    Function.Injective (diagHom F σ n) := by
  intro t s h
  funext i
  have h' := congrFun (congrArg (fun e : (Fin n → K) ≃ₗ[F] (Fin n → K) =>
    e (Pi.single i (1 : K))) h) i
  rw [diagHom_apply, diagHom_apply] at h'
  exact Subtype.ext (Units.ext (by simpa using h'))

theorem diagHom_mem_orthogonalGroup (E : QuadExt F K σ) (n : ℕ) (t : Fin n → normOne σ) :
    diagHom F σ n t ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  apply (algebraMap F K).injective
  rw [algebraMap_Qn, algebraMap_Qn]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : σ ((((t i : normOne σ) : Kˣ) : K)) * ((((t i : normOne σ) : Kˣ) : K)) = 1 :=
    (mem_normOne σ).1 (t i).2
  calc ((((t i : normOne σ) : Kˣ) : K)) * x i *
        (σ ((((t i : normOne σ) : Kˣ) : K) * x i))
      = (((((t i : normOne σ) : Kˣ) : K)) * σ ((((t i : normOne σ) : Kˣ) : K))) *
          (x i * σ (x i)) := by
        rw [map_mul, mul_mul_mul_comm]
    _ = x i * σ (x i) := by
        rw [mul_comm ((((t i : normOne σ) : Kˣ) : K))
          (σ ((((t i : normOne σ) : Kˣ) : K))), h, one_mul]

variable (F σ) in
@[expose] noncomputable def diagTorusV (n : ℕ) :
    Subgroup ((Fin n → K) ≃ₗ[F] (Fin n → K)) :=
  (diagHom F σ n).range

variable (F σ) in
@[expose] noncomputable def diagSingle (n : ℕ) (i : Fin n) :
    normOne σ →* ((Fin n → K) ≃ₗ[F] (Fin n → K)) :=
  (diagHom F σ n).comp (MonoidHom.mulSingle (fun _ : Fin n => normOne σ) i)

theorem diagSingle_apply (n : ℕ) (i : Fin n) (u : normOne σ) :
    diagSingle F σ n i u = diagHom F σ n (Pi.mulSingle i u) :=
  rfl

theorem diagSingle_mem_diagTorusV (n : ℕ) (i : Fin n) (u : normOne σ) :
    diagSingle F σ n i u ∈ diagTorusV F σ n :=
  ⟨Pi.mulSingle i u, rfl⟩

theorem diagSingle_commute (n : ℕ) (i j : Fin n)
    (u v : normOne σ) :
    Commute (diagSingle F σ n i u) (diagSingle F σ n j v) := by
  rw [diagSingle_apply, diagSingle_apply]
  show diagHom F σ n (Pi.mulSingle i u) * diagHom F σ n (Pi.mulSingle j v) =
    diagHom F σ n (Pi.mulSingle j v) * diagHom F σ n (Pi.mulSingle i u)
  rw [← map_mul, ← map_mul, mul_comm]

private theorem iSup_mulSingle_eq_top (n : ℕ) :
    (⨆ i : Fin n, (MonoidHom.mulSingle (fun _ : Fin n => normOne σ) i).range) = ⊤ := by
  rw [eq_top_iff]
  intro t _
  have ht : t = ∏ i, Pi.mulSingle i (t i) := (Finset.univ_prod_mulSingle t).symm
  rw [ht]
  exact Subgroup.prod_mem _ (fun i _ => Subgroup.mem_iSup_of_mem i (Set.mem_range_self (t i)))

theorem diagTorusV_eq_iSup (n : ℕ) :
    diagTorusV F σ n = ⨆ i, (diagSingle F σ n i).range := by
  rw [diagTorusV, ← Subgroup.map_top (f := diagHom F σ n), ← iSup_mulSingle_eq_top (σ := σ) n,
    Subgroup.map_iSup]
  exact iSup_congr fun i => by rw [MonoidHom.map_range]; rfl

end CFSG.ClassicalInvolution.PhanDn
