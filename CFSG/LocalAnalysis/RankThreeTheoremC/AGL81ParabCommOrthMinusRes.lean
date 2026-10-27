module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusBlock
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusSchur

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ}
  {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

section Perp

variable {t : ℕ} (S : SemiData K r b c)

theorem isResPerp_iff (ht : t ≤ r)
    (hflag : ∀ v : 𝕍, S.F v ∈ tailFlag K (Fin 2 → K) r t ↔ v ∈ tailFlag K (Fin 2 → K) r t)
    (v : 𝕍) : IsResPerp ht (S.F v) ↔ IsResPerp ht v := by
  have key : ∀ x : 𝕍, IsResPerp ht x ↔ ∀ w ∈ tailFlag K (Fin 2 → K) r t,
      polar (quadTail r (minusTailForm K b c)) x w = 0 := fun x =>
    (polar_tailFlag_eq_zero_iff (qB := minusTailForm K b c) ht).symm
  rw [key, key]
  constructor
  · intro h w hw
    have h1 := h (S.F w) ((hflag w).2 hw)
    rw [polar_map_semilin S.F S.σ S.μ S.hFQ] at h1
    have := (mul_eq_zero.1 h1).resolve_left S.hμ
    exact (map_eq_zero_iff _ S.σ.injective).1 this
  · intro h w hw
    have hw' : S.F.symm w ∈ tailFlag K (Fin 2 → K) r t :=
      (hflag (S.F.symm w)).1 (by rwa [AddEquiv.apply_symm_apply])
    have h1 := h _ hw'
    have h2 := polar_map_semilin S.F S.σ S.μ S.hFQ v (S.F.symm w)
    rw [AddEquiv.apply_symm_apply, h1, map_zero, mul_zero] at h2
    exact h2

end Perp

section Res

variable {t : ℕ} (S : SemiData K r b c) (ht : t ≤ r)

@[expose] def resFun (u : (Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K)) :
    (Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K) :=
  orthResProj K (Fin 2 → K) ht (S.F (orthResIncl K (Fin 2 → K) ht u))

theorem resFun_add (u v : (Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K)) :
    resFun S ht (u + v) = resFun S ht u + resFun S ht v := by
  simp only [resFun, map_add]

theorem resFun_smul (a : K) (u : (Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K)) :
    resFun S ht (a • u) = S.σ a • resFun S ht u := by
  rw [resFun, map_smul, S.hF, map_smul]
  rfl

variable (hflag : ∀ v : (Fin r ⊕ Fin r → K) × (Fin 2 → K),
  S.F v ∈ tailFlag K (Fin 2 → K) r t ↔ v ∈ tailFlag K (Fin 2 → K) r t)
include hflag

theorem resFun_inj : Function.Injective (resFun S ht) := by
  have hadd := resFun_add S ht
  have hinj : Function.Injective (AddMonoidHom.mk' (resFun S ht) hadd) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hu' : resFun S ht u = 0 := hu
    have hv : IsResPerp ht (S.F (orthResIncl K (Fin 2 → K) ht u)) :=
      (isResPerp_iff S ht hflag _).2 (isResPerp_orthResIncl ht u)
    have h1 := mem_tailFlag_of_orthResProj_eq_zero ht hv hu'
    have h2 : orthResIncl K (Fin 2 → K) ht u ∈ tailFlag K (Fin 2 → K) r t := (hflag _).1 h1
    have h3 := orthResProj_eq_zero_of_mem ht h2
    rwa [orthResProj_orthResIncl] at h3
  exact hinj

theorem resFun_quad (u : (Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K)) :
    quadTail (r - t) (minusTailForm K b c) (resFun S ht u) =
      S.μ * S.σ (quadTail (r - t) (minusTailForm K b c) u) := by
  have hv : IsResPerp ht (S.F (orthResIncl K (Fin 2 → K) ht u)) :=
    (isResPerp_iff S ht hflag _).2 (isResPerp_orthResIncl ht u)
  have h1 := quadTail_eq_of_isResPerp (qA := minusTailForm K b c) ht hv
  have h2 := quadTail_eq_of_isResPerp (qA := minusTailForm K b c) ht
    (isResPerp_orthResIncl (K := K) (A := Fin 2 → K) ht u)
  rw [orthResProj_orthResIncl] at h2
  rw [resFun, ← h1, S.hFQ, h2]

@[expose] noncomputable def resEquiv :
    ((Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K)) ≃+
      ((Fin (r - t) ⊕ Fin (r - t) → K) × (Fin 2 → K)) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (resFun S ht) (resFun_add S ht))
    ⟨resFun_inj S ht hflag, Finite.injective_iff_surjective.1 (resFun_inj S ht hflag)⟩

end Res

section ResComm

variable (S : SemiData K r b c) (hd : OrthCuts r d)
  (hflag : ∀ v : (Fin r ⊕ Fin r → K) × (Fin 2 → K),
    S.F v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) ↔
    v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)))
include hflag

theorem resFun_comm (g : ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) ×
      (Fin 2 → K)) ≃ₗ[K] ((Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) ×
      (Fin 2 → K)))
    (x y : ↥(orthParab r (minusTailForm K b c) d))
    (hx : ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) =
      orthLeviRes K (Fin 2 → K) hd.last g)
    (hy : orthResHom (minusTailForm K b c) hd y = g)
    (hconj : ∀ v, ((y : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        𝕍 ≃ₗ[K] 𝕍) v =
      S.F (((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍)
        (S.F.symm v)))
    (u : (Fin (r - d (Fin.last s)) ⊕ Fin (r - d (Fin.last s)) → K) × (Fin 2 → K)) :
    resFun S hd.last (g u) = g (resFun S hd.last u) := by
  set Y : 𝕍 ≃ₗ[K] 𝕍 := ((y : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    𝕍 ≃ₗ[K] 𝕍) with hY
  set X : 𝕍 ≃ₗ[K] 𝕍 := ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    𝕍 ≃ₗ[K] 𝕍) with hX
  have hYlo : ∀ w ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)),
      Y w ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) := mapsTo_of_mem_orthParab y.2 (Fin.last s)
  have h1 : g (resFun S hd.last u) = orthResMat hd.last Y (resFun S hd.last u) := by
    rw [← hy, orthResHom_apply]
  rw [h1, orthResMat_apply, show resFun S hd.last u = orthResProj K (Fin 2 → K) hd.last
    (S.F (orthResIncl K (Fin 2 → K) hd.last u)) from rfl]
  set v := S.F (orthResIncl K (Fin 2 → K) hd.last u) with hv
  have hvp : IsResPerp hd.last v :=
    (isResPerp_iff S hd.last hflag _).2 (isResPerp_orthResIncl hd.last u)
  have hw0 := sub_orthResIncl_mem hd.last hvp
  have e1 : orthResIncl K (Fin 2 → K) hd.last (orthResProj K (Fin 2 → K) hd.last v) =
      v - (v - orthResIncl K (Fin 2 → K) hd.last (orthResProj K (Fin 2 → K) hd.last v)) := by
    abel
  have e2 : orthResProj K (Fin 2 → K) hd.last (Y (orthResIncl K (Fin 2 → K) hd.last
      (orthResProj K (Fin 2 → K) hd.last v))) = orthResProj K (Fin 2 → K) hd.last (Y v) := by
    rw [e1, map_sub, map_sub, orthResProj_eq_zero_of_mem hd.last (hYlo _ hw0), sub_zero]
  rw [e2]
  have e3 : Y v = S.F (X (orthResIncl K (Fin 2 → K) hd.last u)) := by
    rw [hconj, AddEquiv.symm_apply_apply]
  have e4 : X (orthResIncl K (Fin 2 → K) hd.last u) =
      orthResIncl K (Fin 2 → K) hd.last (g u) := by
    rw [hx, orthLeviRes_apply, orthResExt_apply, orthResProj_orthResIncl, map_sub, add_sub_cancel]
    rfl
  rw [e3, e4]
  rfl

end ResComm

section ResScalar

variable (S : SemiData K r b c) (hd : OrthCuts r d)
  (hflag : ∀ v : (Fin r ⊕ Fin r → K) × (Fin 2 → K),
    S.F v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) ↔
    v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)))
include hflag

theorem res_sigma_and_scalar (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (hm : 1 ≤ r - d (Fin.last s))
    (hrel : ∀ g ∈ orthDerived (quadTail (r - d (Fin.last s)) (minusTailForm K b c)),
      ∀ u, resFun S hd.last (g u) = g (resFun S hd.last u)) :
    (∀ a : K, S.σ a = a) ∧ ∃ a : K, a ≠ 0 ∧ ∀ u, resFun S hd.last u = a • u :=
  schur_tail hm hirr (resEquiv S hd.last hflag) S.σ (fun a v => resFun_smul S hd.last a v) S.μ
    (fun v => resFun_quad S hd.last hflag v) hrel

theorem scalarMod_res {a : K} (ha : ∀ u, resFun S hd.last u = a • u) {v : 𝕍}
    (hv : IsResPerp hd.last v) :
    S.F v - a • v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) := by
  set π := orthResProj K (Fin 2 → K) hd.last with hπ
  set ι := orthResIncl K (Fin 2 → K) hd.last with hι
  have hw0 := sub_orthResIncl_mem hd.last hv
  have hFw0 : S.F (v - ι (π v)) ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) :=
    (hflag _).2 hw0
  have hFι : IsResPerp hd.last (S.F (ι (π v))) :=
    (isResPerp_iff S hd.last hflag _).2 (isResPerp_orthResIncl hd.last _)
  have hdiff : IsResPerp hd.last (S.F (ι (π v)) - a • ι (π v)) := by
    intro i
    have h1 := hFι i
    have h2 := isResPerp_orthResIncl (K := K) (A := Fin 2 → K) hd.last (π v) i
    simp only [Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h1, h2, mul_zero, sub_zero]
  have hdz : π (S.F (ι (π v)) - a • ι (π v)) = 0 := by
    rw [map_sub, map_smul, orthResProj_orthResIncl]
    have := ha (π v)
    rw [resFun] at this
    rw [this, sub_self]
  have h3 := mem_tailFlag_of_orthResProj_eq_zero hd.last hdiff hdz
  have h4 : S.F v - a • v = (S.F (ι (π v)) - a • ι (π v)) + S.F (v - ι (π v)) -
      a • (v - ι (π v)) := by
    rw [map_sub]
    simp only [smul_sub]
    abel
  rw [h4]
  exact Submodule.sub_mem _ (Submodule.add_mem _ h3 hFw0) (Submodule.smul_mem _ _ hw0)

end ResScalar

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
